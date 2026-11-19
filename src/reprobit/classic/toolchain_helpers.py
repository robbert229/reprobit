"""Classic compiler algorithms: compiler helpers read from the authenticated toolchain library.

MSVC 5.0 code calls a few routines of its C runtime with their own register
conventions: ``__ftol`` (an x87 value to a 64-bit integer, truncating),
``__chkstk`` (allocating a frame of a page or more), ``__CIacos`` and its
kin (intrinsic math).  The linker takes each from the CRT library the link
names; lrr links ``libc.lib``.  A proof that meets a direct call to one of
them cannot treat it as an ordinary C callee (no decoration states its
convention) and need not assume a model of it: the helper's exact bytes are
in the toolchain's library, which is authenticated.

:class:`HelperLibrary` holds the bytes of ``lib/libc.lib`` only after they
match a reviewed authority (size and SHA-256) of the toolchain profile; the
build passes the reviewed table, `msvc50_authorities.
MSVC50_LIBRARY_AUTHORITIES`, whose digest is the library's in the profile's
reviewed ``lib`` tree (`reprobit.toolchain_helper_library`).  :meth:`HelperLibrary.
helper` resolves a symbol as the linker does, through the archive's first
linker member (the symbol index), to the one member that defines it; that
member's definition must be external, in a code section, and the helper's
body is that section's bytes from the symbol's value to the section's end.
The region simulator runs those bytes inline at every call
(`region_simulation.run_helper`), and the record pins the library's digest
and the body's.

A section may have relocations (``__isctype`` reads the ``__pctype``
global; ``__CIacos`` calls and jumps into the helpers of ``common.obj``).
Each DIR32 or REL32 field of the body is kept by its offset, its target
named as the linker resolves it (:func:`linker_name`: an external by name, a
static qualified by its member and section); any other relocation type is
refused.  Every compiler helper a REL32 field names is resolved here too,
breadth first, while the closure stays within MAX_HELPER_MEMBERS bodies and
MAX_HELPER_DEPTH calls deep, and each body of the closure carries the whole
closure (``HelperCode.linked``); a C function or an import a field names is
never resolved, so a run that reaches it is refused as reaching the
environment.  Only a whole-function proof runs a relocated body, and the
record then pins the digest of its fields and of every body in its closure.

The one assumption is the one every installed body already rests on: the
linked image's helper is that library member's section with its relocations
applied to the symbols the linker resolves them to -- the same definition a
name has wherever the program names it, and a static of the member placed
with that member -- so the bytes and addresses the proof ran are the ones
the program runs.  Nothing here carries a helper's bytes into a record.
"""

from __future__ import annotations

import hashlib
import json
from collections.abc import Mapping
from dataclasses import dataclass
from typing import Any, Protocol, cast

from reprobit.binary import ByteIdentityError, require
from reprobit.coff_format import CoffObject, coff_body, detailed_relocations

from .region_simulation import HelperCode, callee_stack_pop

HELPER_LIBRARY = "lib/libc.lib"
_CODE = 0x00000020
_EXTERNAL = 2


class HelperLibraryError(ByteIdentityError):
    """A helper library or a helper in it cannot be admitted."""


class FileAuthority(Protocol):
    """A reviewed file: its exact size and SHA-256."""

    @property
    def size(self) -> int: ...

    @property
    def sha256(self) -> str: ...


def compiler_helper(symbol: object) -> bool:
    """Whether a direct callee's name is a compiler or runtime helper's (``__name``).

    Exactly the callees the region simulator refuses as ordinary C functions
    (`region_simulation.callee_stack_pop`) whose name starts with two
    underscores and is not an import slot.
    """
    return (
        isinstance(symbol, str)
        and symbol.startswith("__")
        and not symbol.startswith("__imp_")
        and callee_stack_pop(symbol) is None
    )


@dataclass(frozen=True)
class HelperBody:
    """One helper resolved in the library: where it came from and its verified code."""

    library: str
    library_sha256: str
    member: str
    code: HelperCode

    def pin(self) -> dict[str, Any]:
        """What a record pins: the library, its digest, the member and the body's digest."""
        pin: dict[str, Any] = {
            "symbol": self.code.symbol,
            "library": self.library,
            "library_sha256": self.library_sha256,
            "member": self.member,
            "body_sha256": self.code.sha256,
            "body_length": len(self.code.code),
        }
        if self.code.relocations:
            # Only a relocated body pins its fields and its closure, so every
            # self-contained helper's pin is the one records made before.
            pin["relocations_sha256"] = relocations_digest(self.code.relocations)
            pin["linked"] = [
                {
                    "symbol": code.symbol,
                    "body_sha256": code.sha256,
                    "body_length": len(code.code),
                    "relocations_sha256": relocations_digest(code.relocations),
                }
                for code in sorted(self.code.linked.values(), key=lambda item: item.symbol)
                if code.symbol != self.code.symbol
            ]
        return pin


class HelperLibrary:
    """An authenticated toolchain library a proof may read compiler helpers from.

    Construct it with :func:`authenticate_helper_library`, or in a build
    with `reprobit.toolchain_helper_library`; both refuse bytes that differ
    from the reviewed authority.
    """

    def __init__(self, profile: str, path: str, data: bytes, authority: FileAuthority):
        digest = hashlib.sha256(data).hexdigest()
        if len(data) != authority.size or digest != authority.sha256:
            raise HelperLibraryError(
                f"the toolchain library {path} of {profile} is not the reviewed one "
                f"({len(data)} bytes, SHA-256 {digest})"
            )
        self.profile = profile
        self.path = path
        self.data = data
        self.sha256 = digest
        self._members = _archive_members(data, path)
        self._index = _linker_index(self._members, path)
        self._resolved: dict[str, HelperBody] = {}

    def helper(self, symbol: str) -> HelperBody:
        """The verified body of ``symbol``, or a refusal saying why it is not admitted.

        A body whose section has relocations carries them (`HelperCode.
        relocations`), and every compiler helper its REL32 fields name is
        resolved here too, transitively, while the closure stays within
        MAX_HELPER_MEMBERS bodies and MAX_HELPER_DEPTH calls deep; one beyond
        those bounds, or one the library does not admit, stays unresolved and
        a run that reaches it is refused.
        """
        resolved = self._resolve(symbol)
        if resolved.code.relocations:
            self._link(resolved)
        return resolved

    def _resolve(self, symbol: str) -> HelperBody:
        if symbol in self._resolved:
            return self._resolved[symbol]
        where = f"the compiler helper {symbol} in {self.path}"
        offsets = self._index.get(symbol, [])
        if len(offsets) != 1:
            raise HelperLibraryError(
                f"{where}: the library's symbol index names {len(offsets)} members for it"
            )
        name, data = self._members[offsets[0]]
        try:
            coff = CoffObject(data)
        except ByteIdentityError as exc:
            raise HelperLibraryError(f"{where}: its member {name} is not a COFF object") from exc
        definitions = [
            entry
            for entry in coff.symbols.values()
            if entry["name"] == symbol and entry["section"] > 0 and entry["storage"] == _EXTERNAL
        ]
        if len(definitions) != 1:
            raise HelperLibraryError(f"{where}: its member {name} does not define it once")
        definition = definitions[0]
        section = coff.sections[definition["section"] - 1]
        if not section["characteristics"] & _CODE:
            raise HelperLibraryError(f"{where}: it is not defined in a code section")
        body = bytes(coff_body(coff, section))
        start = definition["value"]
        if not 0 <= start < len(body):
            raise HelperLibraryError(f"{where}: its value lies outside its section")
        code = body[start:]
        relocations = _body_relocations(coff, section, start, name, where)
        resolved = HelperBody(
            self.path,
            self.sha256,
            name,
            HelperCode(symbol, code, hashlib.sha256(code).hexdigest(), relocations, {}),
        )
        self._resolved[symbol] = resolved
        return resolved

    def _link(self, root: HelperBody) -> None:
        """Resolve the compiler helpers ``root``'s REL32 fields name, breadth first, bounded.

        Every body of the closure gets the whole closure as its ``linked``
        map, so a helper it reaches finds its own callees there too.
        """
        if root.code.linked:
            return
        members = {root.code.symbol: root}
        frontier = [(root, 0)]
        while frontier:
            body, depth = frontier.pop(0)
            for target in sorted(_called_helpers(body.code)):
                if target in members or depth + 1 > MAX_HELPER_DEPTH:
                    continue
                if len(members) >= MAX_HELPER_MEMBERS:
                    frontier.clear()
                    break
                try:
                    callee = self._resolve(target)
                except HelperLibraryError:
                    continue
                members[target] = callee
                frontier.append((callee, depth + 1))
        for body in members.values():
            linked = cast(dict[str, HelperCode], body.code.linked)
            if not linked:
                linked.update({symbol: member.code for symbol, member in members.items()})

    def closure(self, body: HelperBody) -> list[HelperBody]:
        """Every body a run of ``body`` may reach: itself and its resolved helpers, sorted."""
        seen = {body.code.symbol: body}
        for symbol in body.code.linked:
            seen[symbol] = self._resolved[symbol]
        return [seen[symbol] for symbol in sorted(seen)]

    def helpers(self, symbols: list[str]) -> dict[str, HelperBody]:
        """Every symbol's verified body (sorted), refusing at the first that is not admitted."""
        return {symbol: self.helper(symbol) for symbol in sorted(set(symbols))}


MAX_HELPER_MEMBERS = 8
MAX_HELPER_DEPTH = 4
_DIR32 = 0x0006
_REL32 = 0x0014


def relocations_digest(relocations: Mapping[int, Any]) -> str:
    """The SHA-256 of a body's relocated fields, in a canonical text."""
    text = json.dumps(
        [
            [offset, list(target) if isinstance(target, tuple) else target]
            for offset, target in sorted(relocations.items())
        ],
        separators=(",", ":"),
    )
    return hashlib.sha256(text.encode()).hexdigest()


def linker_name(row: Mapping[str, Any], member: str) -> str:
    """The name a relocation's target has in the linked image.

    An external symbol is one definition the linker resolves by name, the
    same in every object that names it (the caller's own ``__pctype`` read
    is the helper's); a static or section symbol is private to its member,
    so it is qualified by the member and section, which no linker name can
    be (``|`` is not a C identifier character).
    """
    if row["target_storage"] == _EXTERNAL:
        return cast(str, row["target"])
    return f"{member}|{row['target_section']}|{row['target']}"


def _body_relocations(
    coff: CoffObject, section: Any, start: int, member: str, where: str
) -> dict[int, Any]:
    """A helper body's relocated fields by offset in the body (from ``start``)."""
    found: dict[int, Any] = {}
    for row in detailed_relocations(coff, section):
        offset = row["offset"] - start
        if offset < 0:
            continue  # a field of the code before the symbol, outside the body
        if row["type"] == _REL32:
            if row["target_section"] == section["number"]:
                raise HelperLibraryError(
                    f"{where}: a PC-relative field at {offset} names its own section"
                )
            found[offset] = ("rel32", linker_name(row, member))
        elif row["type"] == _DIR32:
            found[offset] = linker_name(row, member)
        else:
            raise HelperLibraryError(
                f"{where}: a relocation of type 0x{row['type']:04x} at {offset} is neither a DIR32 "
                "nor a REL32 field"
            )
    return found


def _called_helpers(code: HelperCode) -> set[str]:
    """The compiler helpers a body's REL32 fields name (its calls and tail jumps)."""
    return {
        target[1]
        for target in code.relocations.values()
        if isinstance(target, tuple) and compiler_helper(target[1])
    }


def authenticate_helper_library(
    profile: str,
    data: bytes,
    authorities: Mapping[str, Mapping[str, FileAuthority]],
    *,
    path: str = HELPER_LIBRARY,
) -> HelperLibrary:
    """The library ``path`` of ``profile``, refused unless its bytes are the reviewed ones.

    ``authorities`` is the reviewed table (profile, then path); the build
    passes `msvc50_authorities.MSVC50_LIBRARY_AUTHORITIES`, a test its own
    for a synthetic library.
    """
    authority = authorities.get(profile, {}).get(path)
    if authority is None:
        raise HelperLibraryError(f"no reviewed authority covers {path} of the profile {profile}")
    return HelperLibrary(profile, path, data, authority)


def _archive_members(data: bytes, path: str) -> dict[int, tuple[str, bytes]]:
    """Every member of a COFF archive by the offset of its header: (raw name, data)."""
    require(data.startswith(b"!<arch>\n"), f"{path} is not a COFF archive")
    members: dict[int, tuple[str, bytes]] = {}
    long_names = b""
    offset = 8
    while offset < len(data):
        header = data[offset : offset + 60]
        require(
            len(header) == 60 and header[58:60] == b"`\n",
            f"{path}: an archive member header at {offset} is invalid",
        )
        size_text = header[48:58].strip()
        require(size_text.isdigit(), f"{path}: an archive member size at {offset} is invalid")
        size = int(size_text)
        body = data[offset + 60 : offset + 60 + size]
        require(len(body) == size, f"{path}: the archive member at {offset} is truncated")
        raw = header[:16].rstrip()
        if raw == b"//":
            long_names = body
        name = raw.decode("latin-1")
        if raw.startswith(b"/") and raw[1:].isdigit() and long_names:
            start = int(raw[1:])
            end = long_names.find(b"\0", start)
            name = long_names[start : end if end >= 0 else len(long_names)].decode("latin-1")
        members[offset] = (name.rstrip("/") if name not in ("/", "//") else name, body)
        offset += 60 + size + (size & 1)
    require(offset == len(data), f"{path}: the archive ends inside a member")
    return members


def _linker_index(members: Mapping[int, tuple[str, bytes]], path: str) -> dict[str, list[int]]:
    """The first linker member: each symbol to the header offsets of the members defining it."""
    first = next(iter(members.items()), None)
    require(first is not None and first[1][0] == "/", f"{path} has no linker member")
    body = first[1][1] if first is not None else b""
    require(len(body) >= 4, f"{path}: the linker member is truncated")
    count = int.from_bytes(body[:4], "big")
    table_end = 4 + 4 * count
    require(len(body) >= table_end, f"{path}: the linker member's offsets are truncated")
    names = body[table_end:].split(b"\0")
    require(len(names) >= count, f"{path}: the linker member's names are truncated")
    index: dict[str, list[int]] = {}
    for number in range(count):
        at = int.from_bytes(body[4 + 4 * number : 8 + 4 * number], "big")
        require(at in members, f"{path}: the linker member names a member at {at} that is not one")
        index.setdefault(names[number].decode("latin-1"), []).append(at)
    return index


__all__ = [
    "HELPER_LIBRARY",
    "FileAuthority",
    "HelperBody",
    "HelperLibrary",
    "HelperLibraryError",
    "authenticate_helper_library",
    "compiler_helper",
]
