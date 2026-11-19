"""ReproBit's own producer for section-less i386 COFF weak-alias objects.

Some classic images give one function two link names: a C++ operator and a
plain C function, for example.  A linker without ``/ALTERNATENAME`` (LINK 5.0)
still resolves COFF *weak externals*: a symbol of storage class 105 whose one
auxiliary record names a default symbol and a search characteristic.  A
compiler of that era cannot emit one and the toolchain has no assembler, so a
project has to write the object itself.

ReproBit does not run a project's script to do that.  A producer-graph node of
role ``coff-weak-alias`` declares the alias set; the runtime writes the object
in the current run from that declaration alone, and the declaration pins the
digest of the bytes.  Nothing here reads a reference image or any other input,
so the object adds no trust about the original: only that the linker resolves
weak externals as the COFF specification describes.

Byte layout (all integers little-endian), for aliases ``(weak_i, default_i)``
in declared order and ``D`` the distinct defaults in first-appearance order:

* ``IMAGE_FILE_HEADER`` (20 bytes): machine ``0x014c`` (i386), zero sections,
  timestamp 0, symbol table at offset 20, ``len(D) + 2 * len(aliases)``
  symbols, no optional header, characteristics 0.
* One 18-byte symbol per default in ``D``: value 0, section 0 (undefined),
  type 0, storage class 2 (external), no auxiliary record.
* Per alias, an 18-byte symbol for ``weak_i``: value 0, section 0, type 0,
  storage class 105 (weak external), one auxiliary record; then the 18-byte
  auxiliary record: the symbol-table index of ``default_i``, the search
  characteristic, and ten zero bytes.
* The string table: its 4-byte size (counting itself), then each name longer
  than eight bytes, NUL-terminated, in symbol-table order.  A name of at most
  eight bytes is stored in its symbol, NUL-padded; a longer one is stored as
  four zero bytes and its string-table offset.
"""

from __future__ import annotations

import re
import struct
from enum import StrEnum
from typing import Annotated, Final, Literal

from pydantic import Field, model_validator

from reprobit.model import Digest, StrictModel

COFF_WEAK_ALIAS_FORMAT: Final = "coff-weak-alias-v1"
# The provenance operation of a ReproBit-written weak-alias object.
COFF_WEAK_ALIAS_OPERATION = "coff_weak_alias"
IMAGE_FILE_MACHINE_I386 = 0x014C
IMAGE_SYM_CLASS_EXTERNAL = 2
IMAGE_SYM_CLASS_WEAK_EXTERNAL = 105
_HEADER = struct.Struct("<HHIIIHH")
_SYMBOL = struct.Struct("<8sIhHBB")
_WEAK_AUXILIARY = struct.Struct("<II10s")
_MAX_ALIASES = 4096
# A COFF symbol name is a NUL-free byte string.  The declaration keeps to the
# printable ASCII MSVC decoration uses, without ``=``, so ``WEAK=DEFAULT`` and
# the CMake import's argv split stay unambiguous.
_SYMBOL_NAME = re.compile(r"[!-<>-~]{1,1024}")


class CoffWeakAliasError(ValueError):
    """Raised when a weak-alias declaration or object is not the supported form."""


class CoffWeakSearch(StrEnum):
    """The three weak-external search characteristics of the COFF specification.

    What a real LINK 5.0 (RTM) does with each, measured by the link fixture in
    ``tests/test_coff_weak_alias.py`` (``decoy.lib`` holds a member that
    defines the weak name):

    * ``alias`` (3): the weak name resolves to its default in every arrangement
      measured, and no library member is pulled for it.
    * ``nolibrary`` (1): depends on link order.  When the default is defined by
      a command-line object and the reference comes from a library member
      pulled later (lrr's matching build), the weak name resolves to its
      default and no library is searched for it.  When the reference comes
      from a command-line object, LINK searches the libraries for the weak
      name and pulls a member that defines it; with none, the reference is
      unresolved (LNK2001).
    * ``library`` (2): in that same lrr-shaped arrangement, LINK pulls the
      library member that defines the weak name.

    The producer writes whichever one a declaration names.
    """

    NOLIBRARY = "nolibrary"
    LIBRARY = "library"
    ALIAS = "alias"


_SEARCH_CHARACTERISTICS = {
    CoffWeakSearch.NOLIBRARY: 1,
    CoffWeakSearch.LIBRARY: 2,
    CoffWeakSearch.ALIAS: 3,
}
_SEARCH_BY_CHARACTERISTICS = {value: key for key, value in _SEARCH_CHARACTERISTICS.items()}


def _symbol(value: str, *, label: str) -> str:
    if not isinstance(value, str) or _SYMBOL_NAME.fullmatch(value) is None:
        raise CoffWeakAliasError(f"{label} {value!r} is not a printable COFF symbol name")
    return value


class CoffWeakAlias(StrictModel):
    """One weak external and the symbol it defaults to."""

    weak: Annotated[str, Field(min_length=1, max_length=1024)]
    default: Annotated[str, Field(min_length=1, max_length=1024)]

    @model_validator(mode="after")
    def validate_names(self) -> CoffWeakAlias:
        _symbol(self.weak, label="weak symbol")
        _symbol(self.default, label="default symbol")
        if self.weak == self.default:
            raise CoffWeakAliasError(f"weak symbol {self.weak!r} names itself as its default")
        return self


def validate_alias_set(aliases: tuple[CoffWeakAlias, ...]) -> tuple[CoffWeakAlias, ...]:
    """Refuse alias sets whose object would be ambiguous to a linker."""

    if not aliases:
        raise CoffWeakAliasError("a weak-alias object declares no aliases")
    if len(aliases) > _MAX_ALIASES:
        raise CoffWeakAliasError(f"a weak-alias object declares more than {_MAX_ALIASES} aliases")
    weak_names = [item.weak for item in aliases]
    duplicates = sorted({name for name in weak_names if weak_names.count(name) > 1})
    if duplicates:
        raise CoffWeakAliasError(f"weak symbols are declared more than once: {duplicates}")
    chained = sorted({item.weak for item in aliases} & {item.default for item in aliases})
    if chained:
        # The object would hold the name both as an undefined external and as
        # a weak external; LINK has no defined reading of that.
        raise CoffWeakAliasError(f"weak symbols are also defaults: {chained}")
    return aliases


def synthesize_coff_weak_alias(
    aliases: tuple[CoffWeakAlias, ...],
    *,
    search: CoffWeakSearch = CoffWeakSearch.NOLIBRARY,
) -> bytes:
    """Return the exact object bytes for one validated alias set."""

    validate_alias_set(aliases)
    characteristics = _SEARCH_CHARACTERISTICS[CoffWeakSearch(search)]
    strings = bytearray()

    def name(text: str) -> bytes:
        raw = text.encode("ascii")
        if len(raw) <= 8:
            return raw.ljust(8, b"\0")
        offset = 4 + len(strings)
        strings.extend(raw + b"\0")
        return struct.pack("<II", 0, offset)

    symbols = bytearray()
    default_index: dict[str, int] = {}
    count = 0
    for alias in aliases:
        if alias.default in default_index:
            continue
        default_index[alias.default] = count
        symbols += _SYMBOL.pack(name(alias.default), 0, 0, 0, IMAGE_SYM_CLASS_EXTERNAL, 0)
        count += 1
    for alias in aliases:
        symbols += _SYMBOL.pack(name(alias.weak), 0, 0, 0, IMAGE_SYM_CLASS_WEAK_EXTERNAL, 1)
        symbols += _WEAK_AUXILIARY.pack(default_index[alias.default], characteristics, bytes(10))
        count += 2
    header = _HEADER.pack(IMAGE_FILE_MACHINE_I386, 0, 0, _HEADER.size, count, 0, 0)
    return header + bytes(symbols) + struct.pack("<I", 4 + len(strings)) + bytes(strings)


def read_coff_weak_alias(data: bytes) -> tuple[CoffWeakSearch, tuple[CoffWeakAlias, ...]]:
    """Read back an object of exactly the form :func:`synthesize_coff_weak_alias` writes.

    Any other COFF object, including a valid one laid out differently, is
    refused: the reader exists to compare a project's own output with
    ReproBit's, so it accepts only bytes ReproBit would write.
    """

    def fail(message: str) -> CoffWeakAliasError:
        return CoffWeakAliasError(f"not a ReproBit weak-alias object: {message}")

    if len(data) < _HEADER.size + 4:
        raise fail("truncated")
    machine, sections, timestamp, pointer, count, optional, flags = _HEADER.unpack_from(data)
    if (machine, sections, timestamp, pointer, optional, flags) != (
        IMAGE_FILE_MACHINE_I386,
        0,
        0,
        _HEADER.size,
        0,
        0,
    ):
        raise fail("the file header is not an i386, section-less, timestamp-0 header")
    strings_offset = _HEADER.size + count * _SYMBOL.size
    if strings_offset + 4 > len(data):
        raise fail("the symbol table is truncated")
    (strings_size,) = struct.unpack_from("<I", data, strings_offset)
    if strings_size < 4 or strings_offset + strings_size != len(data):
        raise fail("the string table does not end the file")
    strings = data[strings_offset + 4 :]

    def name(raw: bytes) -> str:
        if raw[:4] == b"\0\0\0\0":
            (offset,) = struct.unpack_from("<I", raw, 4)
            if not 4 <= offset < strings_size:
                raise fail("a string-table offset is outside the table")
            end = strings.find(b"\0", offset - 4)
            if end < 0:
                raise fail("a long name is not NUL-terminated")
            text = strings[offset - 4 : end]
        else:
            text = raw.rstrip(b"\0")
            if b"\0" in text:
                raise fail("a short name has an embedded NUL")
        try:
            return text.decode("ascii")
        except UnicodeDecodeError as error:
            raise fail("a symbol name is not ASCII") from error

    defaults: dict[int, str] = {}
    aliases: list[CoffWeakAlias] = []
    search: CoffWeakSearch | None = None
    index = 0
    while index < count:
        raw_name, value, section, symbol_type, storage, auxiliary = _SYMBOL.unpack_from(
            data, _HEADER.size + index * _SYMBOL.size
        )
        if (value, section, symbol_type) != (0, 0, 0):
            raise fail(f"symbol {index} is not an undefined, untyped symbol")
        if storage == IMAGE_SYM_CLASS_EXTERNAL and auxiliary == 0 and not aliases:
            defaults[index] = name(raw_name)
            index += 1
            continue
        if storage != IMAGE_SYM_CLASS_WEAK_EXTERNAL or auxiliary != 1 or index + 1 >= count:
            raise fail(f"symbol {index} is neither a leading default nor a weak external")
        tag, characteristics, padding = _WEAK_AUXILIARY.unpack_from(
            data, _HEADER.size + (index + 1) * _SYMBOL.size
        )
        if padding != bytes(10) or tag not in defaults:
            raise fail(f"weak external {index} has a malformed auxiliary record")
        current = _SEARCH_BY_CHARACTERISTICS.get(characteristics)
        if current is None or (search is not None and current is not search):
            raise fail(f"weak external {index} has an unsupported search characteristic")
        search = current
        try:
            aliases.append(CoffWeakAlias(weak=name(raw_name), default=defaults[tag]))
        except ValueError as error:
            raise fail(str(error)) from error
        index += 2
    if search is None:
        raise fail("it holds no weak external")
    result = tuple(aliases)
    try:
        expected = synthesize_coff_weak_alias(result, search=search)
    except CoffWeakAliasError as error:
        raise fail(str(error)) from error
    if expected != data:
        raise fail("its layout differs from the canonical layout of the same alias set")
    return search, result


class CoffWeakAliasDeclaration(StrictModel):
    """A producer-graph node's complete authority for one weak-alias object.

    ``output_digest`` and ``output_size`` pin the bytes; a graph whose pin
    differs from what this ReproBit writes for the same alias set fails to
    load, so a change to the producer can never silently change an output.
    """

    format: Literal["coff-weak-alias-v1"] = COFF_WEAK_ALIAS_FORMAT
    machine: Literal["i386"] = "i386"
    search: CoffWeakSearch = CoffWeakSearch.NOLIBRARY
    aliases: Annotated[tuple[CoffWeakAlias, ...], Field(min_length=1, max_length=_MAX_ALIASES)]
    output_digest: Digest
    output_size: Annotated[int, Field(ge=_HEADER.size + 4)]

    @model_validator(mode="after")
    def validate_pin(self) -> CoffWeakAliasDeclaration:
        payload = synthesize_coff_weak_alias(self.aliases, search=self.search)
        if Digest.from_bytes(payload) != self.output_digest or len(payload) != self.output_size:
            raise CoffWeakAliasError(
                "weak-alias output pin differs from the bytes this producer writes "
                f"(sha256 {Digest.from_bytes(payload).value}, {len(payload)} bytes)"
            )
        return self

    def payload(self) -> bytes:
        """Return the pinned object bytes."""

        return synthesize_coff_weak_alias(self.aliases, search=self.search)


def declare_coff_weak_alias(
    aliases: tuple[CoffWeakAlias, ...],
    *,
    search: CoffWeakSearch = CoffWeakSearch.NOLIBRARY,
) -> CoffWeakAliasDeclaration:
    """Return a declaration whose pin is the bytes of ``aliases``."""

    payload = synthesize_coff_weak_alias(aliases, search=search)
    return CoffWeakAliasDeclaration(
        search=search,
        aliases=aliases,
        output_digest=Digest.from_bytes(payload),
        output_size=len(payload),
    )


def parse_alias_argument(value: str) -> CoffWeakAlias:
    """Parse one ``WEAK=DEFAULT`` command-line alias."""

    weak, separator, default = value.partition("=")
    if not separator or not weak or not default or "=" in default:
        raise CoffWeakAliasError(f"weak alias {value!r} is not one WEAK=DEFAULT pair")
    _symbol(weak, label="weak symbol")
    _symbol(default, label="default symbol")
    if weak == default:
        raise CoffWeakAliasError(f"weak symbol {weak!r} names itself as its default")
    return CoffWeakAlias(weak=weak, default=default)


__all__ = [
    "COFF_WEAK_ALIAS_FORMAT",
    "COFF_WEAK_ALIAS_OPERATION",
    "CoffWeakAlias",
    "CoffWeakAliasDeclaration",
    "CoffWeakAliasError",
    "CoffWeakSearch",
    "declare_coff_weak_alias",
    "parse_alias_argument",
    "read_coff_weak_alias",
    "synthesize_coff_weak_alias",
    "validate_alias_set",
]
