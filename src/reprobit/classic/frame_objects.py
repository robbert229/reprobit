"""Classic compiler algorithms: the donor's frame objects and their extents (a14).

A whole-function proof (:mod:`reprobit.classic.function_validation`) whose
frame passes a stack address to a call needs, under its assumption a14, the
*extent* of every local object such an address may point into: the
contiguous range of the frame the object occupies.  This module derives the
extents from what the donor object and the compiler's own products carry,
or refuses.

The locals.  The function's ``.debug$S`` child opens with its procedure
record; every ``S_BPREL32`` record of MSVC 5.0 (``S_BPREL32_ST``, 0x1006:
offset i32, type u32, name) places one local or parameter at a constant
offset from the frame's base.  In a frame-pointer-free function (the FPO
record's cbFrame 0) that base is the entry ESP: the parameters lie in the
words [ESP0 + 4, E) above the return address, E = ESP0 + 4 + 4 cdwParams,
and the locals in the block [B, ESP0) the prologue allocates,
B = ESP0 - 4 cdwLocals.  A local kept in a register (``S_REGISTER``) has
no stack memory; a static (``S_LDATA32``) is not in the frame.

A parameter's word may be reused once the parameter is dead: MSVC 5.0 then
keeps a local there (`tooltip_draw`'s ``i`` in ``mouseY``'s word).  Such a
*homed* local's record is 4 bytes above its slot.  The compiler names every
stack slot by its listing offset L (``/FAs``: ``_mouseY$ = 16``,
``_i$ = 16``).  A name in the parameter words is addressed at ESP0 + L - 4
(``_i$[esp+K]`` with K = depth - 4, as for a parameter), and one in the
locals block at ESP0 + L.  The ``S_BPREL32`` record carries L - 4 for a
parameter but L for every other name, a homed local included: ``mouseY``
is recorded at ESP0+12 and ``i`` at ESP0+16, but the code keeps both at
ESP0+12.  So a record is read by what it names:

- a parameter: the first n ``S_BPREL32``/``S_REGISTER`` records, all in the
  procedure's own scope (CodeView emits the parameters first, in order).
  n is the parameter count of the procedure's ``LF_PROCEDURE_ST`` type
  (0x1008), equal to its ``LF_ARGLIST_ST`` (0x1201) entry count, less a
  trailing ``T_NOTYPE`` (``...``).  It lies at ESP0 + offset, in [4, E);
- any later record at a positive offset: a homed local, at ESP0 + offset - 4,
  in [4, E);
- any other: a local at ESP0 + offset, in [B, ESP0).

A record outside its range is refused, and so is a function with a record
at a positive offset whose procedure type is not available (it is read from
the same type records as the sizes).  The rule was checked against MSVC
5.0's own listings over lrr's 214 matching-build units (4,149
frame-pointer-free functions): every parameter record is L - 4, every other
record is L, and every scalar homed local whose addressing could be decided
from an adjacent access (298 accesses) is addressed as a parameter is.

The sizes.  A type index below 0x1000 is a CodeView primitive, whose size
the index itself fixes (`PRIMITIVE_SIZES`: ``T_INT4`` 4, ``T_REAL64`` 8, a
32-bit near pointer 4, ...); ``T_VOID``, the 16-bit and far pointer modes and
every primitive outside the table are refused.  A user-defined index names a
type record.  An object compiled with ``/Z7`` carries the records itself, in
its one ``.debug$T`` section; one compiled with ``/Zi`` (lrr's, and every
donor ReproBit compiles with ``/Fd``) carries only an ``LF_TYPESERVER``
record naming the PDB the compiler wrote the types to, with that PDB's
signature and age.  The type server is then a separate input, the compiler's
own product of the same compile: it is admitted only when its PDB info
stream carries exactly the signature and age the object records
(`read_type_server`).  The sizes of the MSVC 5.0 type leaves:

- ``LF_ARRAY_ST`` (0x1003): its size field, in bytes (all dimensions);
- ``LF_STRUCTURE_ST``/``LF_CLASS_ST`` (0x1005/0x1004) and ``LF_UNION_ST``
  (0x1006): its size field, ``sizeof`` with padding.  A forward reference
  (property bit 0x80) is resolved to the one definition of the same kind
  and name in the same stream; none or several is refused;
- ``LF_POINTER_ST`` (0x1002): 4 for a 32-bit near pointer or reference,
  anything else refused;
- ``LF_MODIFIER_ST`` (0x1001, ``const``/``volatile``): its type's size;
- ``LF_ENUM_ST`` (0x1007): its underlying type's size.

Every other leaf -- a procedure, a field list, a bit field -- is refused.
Every local's size must be known, not only an escaping one's: two locals of
disjoint scopes may share bytes, so an unknown local could overlap an
escaping one.

The extents.  Locals whose ranges overlap (MSVC 5.0 reuses the bytes of
sibling scopes) are merged into one *frame object*, the union of their
ranges (`FrameObjects`): a pointer into either lies in the union, so a
callee given it reaches no byte outside.  Locals that only touch are kept
apart.
"""

from __future__ import annotations

import math
import struct
from dataclasses import dataclass
from typing import Any, cast

from reprobit.binary import require
from reprobit.coff_format import CoffObject, coff_body
from reprobit.small_msf import SMALL_MSF_MAGIC

from .coff import _comdat_child
from .debug import (
    CODEVIEW_BPREL_RECORD_TYPES,
    CODEVIEW_END_RECORD_TYPE,
    CODEVIEW_FIRST_TYPE_INDEX,
    CODEVIEW_LF_PROCEDURE_ST,
    CODEVIEW_LF_TYPESERVER,
    CODEVIEW_REGISTER_RECORD_TYPES,
    CODEVIEW_TYPE_SIGNATURES,
    codeview_type_records,
    parse_codeview_symbol_stream,
)
from .foundation import sha256_bytes

# The procedure records a function's `.debug$S` opens with, both widths.
_PROCEDURE_RECORDS = frozenset({516, 517, 0x100A, 0x100B})
# The MSVC 5.0 procedure records, whose type index is a u32 at payload offset 24.
_PROCEDURE_ST_RECORDS = frozenset({0x100A, 0x100B})
_BPREL32 = 512  # CodeView 4: offset i32, type u16
_BPREL32_ST = 0x1006  # MSVC 5.0: offset i32, type u32
_BLOCK32 = 519  # S_BLOCK32: opens a nested scope, closed by S_END
# A homed local's record is this many bytes above its slot (see the module docstring).
HOMED_RECORD_BIAS = 4

# Direct primitives (mode 0) by index, and the 32-bit near pointer mode.
PRIMITIVE_SIZES = {
    0x10: 1,  # T_CHAR
    0x11: 2,  # T_SHORT
    0x12: 4,  # T_LONG
    0x13: 8,  # T_QUAD
    0x20: 1,  # T_UCHAR
    0x21: 2,  # T_USHORT
    0x22: 4,  # T_ULONG
    0x23: 8,  # T_UQUAD
    0x30: 1,  # T_BOOL08
    0x31: 2,  # T_BOOL16
    0x32: 4,  # T_BOOL32
    0x40: 4,  # T_REAL32
    0x41: 8,  # T_REAL64
    0x42: 10,  # T_REAL80
    0x70: 1,  # T_RCHAR
    0x71: 2,  # T_WCHAR
    0x72: 2,  # T_INT2
    0x73: 2,  # T_UINT2
    0x74: 4,  # T_INT4
    0x75: 4,  # T_UINT4
    0x76: 8,  # T_INT8
    0x77: 8,  # T_UINT8
}
_PRIMITIVE_NEAR32_MODE = 4
_T_VOID = 0x03

LF_MODIFIER_ST = 0x1001
LF_POINTER_ST = 0x1002
LF_ARRAY_ST = 0x1003
LF_CLASS_ST = 0x1004
LF_STRUCTURE_ST = 0x1005
LF_UNION_ST = 0x1006
LF_ENUM_ST = 0x1007
LF_ARGLIST_ST = 0x1201
_T_NOTYPE = 0x0000  # an argument list's trailing entry for `...`
_CV_PTR_NEAR32 = 0x0A
_FORWARD_REFERENCE = 0x80
_AGGREGATES = (LF_CLASS_ST, LF_STRUCTURE_ST, LF_UNION_ST)
_NUMERIC_LEAVES = {
    0x8000: ("<b", 1),  # LF_CHAR
    0x8001: ("<h", 2),  # LF_SHORT
    0x8002: ("<H", 2),  # LF_USHORT
    0x8003: ("<i", 4),  # LF_LONG
    0x8004: ("<I", 4),  # LF_ULONG
}
_MAX_TYPE_DEPTH = 64

# PDB 2.00 (SmallMSF): the info stream of MSVC 5.0's PDB and its TPI stream.
PDB_VC50_VERSION = 19960307
TPI_VC50_VERSION = 19961031
_TPI_VC50_HEADER_SIZE = 56
_MSF_PAGE_SIZES = frozenset({1024, 2048, 4096})
_DELETED_STREAM = 0xFFFFFFFF


@dataclass(frozen=True)
class FrameLocal:
    """One ``S_BPREL32`` record: a local or parameter at ESP0 + ``start``.

    ``start`` is where the code keeps it: for a homed local, 4 below the
    offset its record carries (see the module docstring).
    """

    name: str
    start: int
    size: int
    type_index: int


@dataclass(frozen=True)
class FrameObject:
    """One frame object: the union of locals whose ranges overlap.

    It occupies [ESP0 + ``start``, ESP0 + ``start`` + ``size``).
    """

    start: int
    size: int
    names: tuple[str, ...]

    @property
    def end(self) -> int:
        return self.start + self.size

    def pin(self) -> list[int]:
        return [self.start, self.size]


@dataclass(frozen=True)
class FrameObjects:
    """The donor's frame objects (a14), sorted by start, pairwise disjoint."""

    objects: tuple[FrameObject, ...]
    # How the sizes were read: the SHA-256 of every type record a size
    # needed, sorted (the build re-derives them; the pins compare extents).
    type_records: tuple[str, ...] = ()

    def __post_init__(self) -> None:
        for left, right in zip(self.objects, self.objects[1:], strict=False):
            require(left.end <= right.start, "frame objects overlap")

    def by_start(self, start: int) -> FrameObject:
        found = [item for item in self.objects if item.start == start]
        require(len(found) == 1, f"no frame object starts at ESP0{start:+d}")
        return found[0]

    def holding(self, offset: int, width: int) -> FrameObject | None:
        """The object an access [ESP0 + offset, + width) lies in, or None outside every object.

        An access that lies partly inside an object is refused.
        """
        for item in self.objects:
            if item.start < offset + width and offset < item.end:
                require(
                    item.start <= offset and offset + width <= item.end,
                    f"a stack access at ESP0{offset:+d} ({width} bytes) straddles the frame "
                    f"object [ESP0{item.start:+d}, ESP0{item.end:+d}) of "
                    f"{', '.join(item.names)}",
                )
                return item
        return None

    def pointees(self, offset: int) -> tuple[FrameObject, ...]:
        """The objects a pointer ESP0 + ``offset`` may point into, the first its own.

        A pointer inside an object points into it; one at an object's end may
        also be one past the end of the object before it, which then escapes
        too.  A pointer that is neither is in no object: ().
        """
        inside = [item for item in self.objects if item.start <= offset < item.end]
        ending = [item for item in self.objects if item.end == offset]
        return tuple(inside + ending)


def _numeric_leaf(record: bytes, at: int, context: str) -> tuple[int, int]:
    """A CodeView numeric leaf at ``at``: (value, the offset after it)."""
    require(at + 2 <= len(record), f"{context}: a numeric leaf is truncated")
    leaf = int.from_bytes(record[at : at + 2], "little")
    if leaf < 0x8000:
        return leaf, at + 2
    form = _NUMERIC_LEAVES.get(leaf)
    require(form is not None, f"{context}: the numeric leaf 0x{leaf:04x} is unsupported")
    fmt, width = form  # type: ignore[misc]
    require(at + 2 + width <= len(record), f"{context}: a numeric leaf is truncated")
    return int(struct.unpack_from(fmt, record, at + 2)[0]), at + 2 + width


def _pascal_name(record: bytes, at: int, context: str) -> str:
    require(at < len(record), f"{context}: a type record has no name")
    count = record[at]
    require(at + 1 + count <= len(record), f"{context}: a type record's name is truncated")
    return record[at + 1 : at + 1 + count].decode("latin1")


@dataclass(frozen=True)
class TypeServer:
    """The type records of one PDB type server: its identity and its TPI records."""

    signature: int
    age: int
    records: tuple[bytes, ...]


def _msf_streams(data: bytes, context: str) -> list[bytes | None]:
    """Every stream of a PDB 2.00 SmallMSF file, read strictly."""
    require(data[: len(SMALL_MSF_MAGIC)] == SMALL_MSF_MAGIC, f"{context}: not a PDB 2.00 file")
    require(len(data) >= 64, f"{context}: the MSF header is truncated")
    page_size, _fpm, page_count, directory_size = struct.unpack_from("<IHHI", data, 44)
    require(page_size in _MSF_PAGE_SIZES, f"{context}: the MSF page size is unsupported")
    require(
        page_count > 0 and len(data) == page_count * page_size,
        f"{context}: the MSF file size does not match its page count",
    )
    require(directory_size >= 4, f"{context}: the MSF directory is truncated")
    directory_pages = math.ceil(directory_size / page_size)
    require(60 + 2 * directory_pages <= page_size, f"{context}: the MSF directory is too long")

    def read(pages: list[int], size: int) -> bytes:
        require(
            all(0 < page < page_count for page in pages) and len(set(pages)) == len(pages),
            f"{context}: an MSF stream names an invalid page",
        )
        return b"".join(data[page * page_size : (page + 1) * page_size] for page in pages)[:size]

    directory = read(
        [int.from_bytes(data[60 + 2 * i : 62 + 2 * i], "little") for i in range(directory_pages)],
        directory_size,
    )
    count = int.from_bytes(directory[0:2], "little")
    cursor = 4
    require(cursor + 8 * count <= len(directory), f"{context}: the MSF directory is truncated")
    sizes = [
        int.from_bytes(directory[cursor + 8 * i : cursor + 8 * i + 4], "little")
        for i in range(count)
    ]
    cursor += 8 * count
    streams: list[bytes | None] = []
    for size in sizes:
        if size == _DELETED_STREAM:
            streams.append(None)
            continue
        pages = math.ceil(size / page_size)
        require(cursor + 2 * pages <= len(directory), f"{context}: the MSF directory is truncated")
        numbers = [
            int.from_bytes(directory[cursor + 2 * i : cursor + 2 * i + 2], "little")
            for i in range(pages)
        ]
        cursor += 2 * pages
        streams.append(read(numbers, size))
    require(cursor == len(directory), f"{context}: the MSF directory does not parse to exhaustion")
    return streams


def read_type_server(data: bytes, context: str = "type server") -> TypeServer:
    """The identity and type records of an MSVC 5.0 PDB (its info and TPI streams)."""
    streams = _msf_streams(data, context)
    require(len(streams) > 2, f"{context}: the PDB has no TPI stream")
    info = streams[1] or b""
    stream = streams[2] or b""
    require(len(info) >= 12, f"{context}: the PDB info stream is truncated")
    version, signature, age = struct.unpack_from("<III", info, 0)
    require(
        version == PDB_VC50_VERSION, f"{context}: the PDB info version {version} is not MSVC 5.0's"
    )
    require(len(stream) >= 20, f"{context}: the TPI stream is truncated")
    tpi_version, header, ti_min, ti_mac, record_bytes = struct.unpack_from("<IIIII", stream, 0)
    require(
        tpi_version == TPI_VC50_VERSION and header == _TPI_VC50_HEADER_SIZE,
        f"{context}: the TPI stream is not MSVC 5.0's",
    )
    require(
        ti_min == CODEVIEW_FIRST_TYPE_INDEX and ti_mac >= ti_min,
        f"{context}: the TPI type-index range is invalid",
    )
    require(
        len(stream) == header + record_bytes,
        f"{context}: the TPI record bytes do not exhaust the stream",
    )
    records = []
    cursor = header
    while cursor < len(stream):
        require(cursor + 4 <= len(stream), f"{context}: a type record header is truncated")
        length = int.from_bytes(stream[cursor : cursor + 2], "little")
        require(
            length >= 2 and cursor + 2 + length <= len(stream),
            f"{context}: a type record length is out of range",
        )
        records.append(stream[cursor : cursor + 2 + length])
        cursor += 2 + length
    require(
        len(records) == ti_mac - ti_min,
        f"{context}: the TPI record count differs from its type range",
    )
    return TypeServer(signature, age, tuple(records))


def object_type_records(
    donor: CoffObject, type_server: bytes | None, context: str
) -> tuple[tuple[bytes, ...] | None, str]:
    """The type records the donor's user-defined type indices name, and where they came from.

    The object's one ``.debug$T`` section either holds the records (``/Z7``)
    or names a PDB type server by signature and age (``/Zi``); the type
    server's bytes must then be supplied, and must carry that signature and
    age.  None (with the reason) when the records are not available.
    """
    streams = [bytes(coff_body(donor, s)) for s in donor.sections if s["name"] == ".debug$T"]
    if len(streams) != 1:
        return None, f"the object has {len(streams)} type streams, not one"
    require(
        len(streams[0]) >= 4
        and int.from_bytes(streams[0][:4], "little") in CODEVIEW_TYPE_SIGNATURES,
        f"{context}: the object's type stream signature is not CodeView's",
    )
    types = codeview_type_records(streams[0], f"{context} debug$T")
    servers = [
        item for item in types if int.from_bytes(item[2:4], "little") in CODEVIEW_LF_TYPESERVER
    ]
    if not servers:
        return tuple(types), "object"
    require(
        len(types) == 1 and int.from_bytes(servers[0][2:4], "little") == CODEVIEW_LF_TYPESERVER[0],
        f"{context}: the object's type stream holds a type server among other records",
    )
    record = servers[0]
    require(len(record) >= 12, f"{context}: the LF_TYPESERVER record is truncated")
    signature, age = struct.unpack_from("<II", record, 4)
    name = _pascal_name(record, 12, context)
    if type_server is None:
        return None, (
            f"the object's types are in the PDB type server {name!r} (signature "
            f"0x{signature:08x}, age {age}), which is not supplied"
        )
    server = read_type_server(type_server, f"{context} type server")
    require(
        (server.signature, server.age) == (signature, age),
        f"{context}: the supplied type server has signature 0x{server.signature:08x} and age "
        f"{server.age}, but the object names 0x{signature:08x} and age {age}",
    )
    return server.records, "type server"


class TypeSizes:
    """The sizes of type indices, read from one stream of type records."""

    def __init__(self, records: tuple[bytes, ...], context: str) -> None:
        self.records = records
        self.context = context
        # The digests of every type record a size was read from.
        self.used: set[str] = set()

    def record(self, index: int) -> bytes:
        position = index - CODEVIEW_FIRST_TYPE_INDEX
        require(
            0 <= position < len(self.records),
            f"{self.context}: the type 0x{index:x} names no available type record",
        )
        record = self.records[position]
        self.used.add(sha256_bytes(record))
        return record

    def size(self, index: int, depth: int = 0) -> int:
        require(depth <= _MAX_TYPE_DEPTH, f"{self.context}: the type 0x{index:x} nests too deeply")
        if index < CODEVIEW_FIRST_TYPE_INDEX:
            return primitive_size(index, self.context)
        record = self.record(index)
        require(len(record) >= 4, f"{self.context}: the type record 0x{index:x} is truncated")
        leaf = int.from_bytes(record[2:4], "little")
        where = f"{self.context}: the type 0x{index:x}"
        if leaf == LF_MODIFIER_ST:
            require(len(record) >= 10, f"{where} is truncated")
            return self.size(int.from_bytes(record[4:8], "little"), depth + 1)
        if leaf == LF_POINTER_ST:
            # MSVC 5.0 lays it out as the pointee's type, then the attributes.
            require(len(record) >= 12, f"{where} is truncated")
            attributes = int.from_bytes(record[8:12], "little")
            require(
                attributes & 0x1F == _CV_PTR_NEAR32 and (attributes >> 5) & 7 in (0, 1),
                f"{where} is a pointer of attributes 0x{attributes:x}, not a 32-bit near pointer",
            )
            return 4
        if leaf == LF_ARRAY_ST:
            require(len(record) >= 14, f"{where} is truncated")
            size, _after = _numeric_leaf(record, 12, where)
            require(size > 0, f"{where} is an array of size {size}")
            return size
        if leaf in _AGGREGATES:
            return self._aggregate_size(index, record, leaf, where)
        require(
            leaf == LF_ENUM_ST, f"{where} is leaf 0x{leaf:04x}, which has no size this reader knows"
        )
        require(len(record) >= 16, f"{where} is truncated")
        properties = int.from_bytes(record[6:8], "little")
        require(not properties & _FORWARD_REFERENCE, f"{where} is a forward-referenced enum")
        return self.size(int.from_bytes(record[8:12], "little"), depth + 1)

    def _aggregate_layout(self, record: bytes, leaf: int, where: str) -> tuple[int, int, str]:
        """(property, size, name) of a class, structure or union record."""
        size_at = 20 if leaf in (LF_CLASS_ST, LF_STRUCTURE_ST) else 12
        require(len(record) >= size_at + 2, f"{where} is truncated")
        properties = int.from_bytes(record[6:8], "little")
        size, after = _numeric_leaf(record, size_at, where)
        return properties, size, _pascal_name(record, after, where)

    def _aggregate_size(self, index: int, record: bytes, leaf: int, where: str) -> int:
        properties, size, name = self._aggregate_layout(record, leaf, where)
        if properties & _FORWARD_REFERENCE:
            definitions = []
            for position, other in enumerate(self.records):
                if len(other) < 4 or int.from_bytes(other[2:4], "little") != leaf:
                    continue
                other_where = f"{self.context}: the type 0x{position + CODEVIEW_FIRST_TYPE_INDEX:x}"
                other_properties, other_size, other_name = self._aggregate_layout(
                    other, leaf, other_where
                )
                if other_name == name and not other_properties & _FORWARD_REFERENCE:
                    definitions.append((other, other_size))
            require(
                len(definitions) == 1,
                f"{where} is a forward reference to {name!r}, which has {len(definitions)} "
                "definitions in the type records",
            )
            self.used.add(sha256_bytes(definitions[0][0]))
            size = definitions[0][1]
        require(size > 0, f"{where} ({name!r}) has size {size}")
        return size


def primitive_size(index: int, context: str) -> int:
    """The size of a CodeView primitive type index, or a refusal."""
    mode = (index >> 8) & 7
    require(index >> 11 == 0, f"{context}: the primitive type 0x{index:x} is malformed")
    if mode == _PRIMITIVE_NEAR32_MODE:
        return 4
    require(
        mode == 0,
        f"{context}: the primitive type 0x{index:x} is a 16-bit or far pointer",
    )
    require(index != _T_VOID, f"{context}: a local of type void has no size")
    size = PRIMITIVE_SIZES.get(index)
    require(size is not None, f"{context}: the primitive type 0x{index:x} has no known size")
    return int(size)  # type: ignore[arg-type]


def parameter_count(
    stream: bytes, procedure: dict[str, Any], sizes: TypeSizes, context: str
) -> int:
    """How many of the procedure's first location records are its parameters.

    The procedure record's type index names an ``LF_PROCEDURE_ST`` record
    (return type u32, calling convention u8, reserved u8, parameter count
    u16, argument list u32); its ``LF_ARGLIST_ST`` (count u32, then a u32
    type per entry) must have as many entries.  A trailing ``T_NOTYPE``
    entry is ``...``, which has no record.  Anything else is refused.
    """
    require(
        procedure["type"] in _PROCEDURE_ST_RECORDS,
        f"{context}: the procedure record of type 0x{procedure['type']:x} is CodeView 4's, "
        "whose parameter records this reader does not tell from its locals",
    )
    payload = stream[procedure["offset"] + 4 : procedure["offset"] + procedure["size"]]
    type_index = int.from_bytes(payload[24:28], "little")
    require(
        type_index >= CODEVIEW_FIRST_TYPE_INDEX,
        f"{context}: the procedure type 0x{type_index:x} is not a type record",
    )
    record = sizes.record(type_index)
    leaf = int.from_bytes(record[2:4], "little")
    require(
        leaf == CODEVIEW_LF_PROCEDURE_ST and len(record) >= 16,
        f"{context}: the procedure type 0x{type_index:x} is leaf 0x{leaf:04x}, not LF_PROCEDURE",
    )
    count = int.from_bytes(record[10:12], "little")
    arguments_index = int.from_bytes(record[12:16], "little")
    require(
        arguments_index >= CODEVIEW_FIRST_TYPE_INDEX,
        f"{context}: the argument list 0x{arguments_index:x} is not a type record",
    )
    arguments = sizes.record(arguments_index)
    require(
        len(arguments) >= 8 and int.from_bytes(arguments[2:4], "little") == LF_ARGLIST_ST,
        f"{context}: the type 0x{arguments_index:x} is not an LF_ARGLIST",
    )
    entries = int.from_bytes(arguments[4:8], "little")
    require(
        len(arguments) == 8 + 4 * entries and entries == count,
        f"{context}: the argument list 0x{arguments_index:x} has {entries} entries in "
        f"{len(arguments)} bytes, but the procedure counts {count} parameters",
    )
    types = [
        int.from_bytes(arguments[8 + 4 * index : 12 + 4 * index], "little")
        for index in range(entries)
    ]
    require(
        _T_NOTYPE not in types[:-1],
        f"{context}: the argument list 0x{arguments_index:x} has `...` before its last entry",
    )
    return entries - (1 if types and types[-1] == _T_NOTYPE else 0)


def frame_locals(
    donor: CoffObject,
    primary: dict[str, Any],
    type_server: bytes | None,
    *,
    base: int,
    params_end: int,
    context: str,
) -> tuple[tuple[FrameLocal, ...], tuple[str, ...]]:
    """Every ``S_BPREL32`` local of the donor function with its extent (see the module docstring).

    ``base`` is B, the bottom of the locals block (ESP0 - 4 cdwLocals), and
    ``params_end`` E, the end of the parameter words.  A parameter must lie
    in [4, E), a homed local (at its record's offset less 4) in [4, E) and
    any other local in [B, 0).  Returns the locals and the digests of the
    type records their sizes and the parameter count needed.
    """
    stream = bytes(coff_body(donor, _comdat_child(donor, primary, ".debug$S")))
    records = parse_codeview_symbol_stream(stream, f"{context} debug$S")
    require(
        bool(records) and records[0]["type"] in _PROCEDURE_RECORDS,
        f"{context}: the debug$S does not open with a procedure record",
    )
    sizes: TypeSizes | None = None
    reason = ""

    def type_sizes() -> TypeSizes | None:
        nonlocal sizes, reason
        if sizes is None and not reason:
            available, reason = object_type_records(donor, type_server, context)
            if available is not None:
                sizes = TypeSizes(available, context)
        return sizes

    # Every location record in order: (record, offset or None in a register,
    # type index, whether it is in the procedure's own scope).
    locations: list[tuple[dict[str, Any], int | None, int, bool]] = []
    depth = 0
    for item in records[1:]:
        kind = item["type"]
        if kind == _BLOCK32:
            depth += 1
        elif kind == CODEVIEW_END_RECORD_TYPE:
            depth -= 1
        elif kind in CODEVIEW_REGISTER_RECORD_TYPES:
            locations.append((item, None, 0, depth == 0))
        elif kind in CODEVIEW_BPREL_RECORD_TYPES:
            payload = stream[item["offset"] + 4 : item["offset"] + item["size"]]
            wide = kind == _BPREL32_ST
            locations.append(
                (
                    item,
                    int.from_bytes(payload[0:4], "little", signed=True),
                    int.from_bytes(payload[4 : 8 if wide else 6], "little"),
                    depth == 0,
                )
            )
    parameters = 0
    if any(offset is not None and offset > 0 for _item, offset, _type, _top in locations):
        known = type_sizes()
        require(
            known is not None,
            f"{context}: a record at a positive offset is a parameter or a local homed in a "
            f"parameter's word, which only the procedure's type tells apart, and the types are "
            f"unknown: {reason}",
        )
        parameters = parameter_count(stream, records[0], cast(TypeSizes, known), context)
        require(
            len(locations) >= parameters
            and all(top for _item, _offset, _type, top in locations[:parameters]),
            f"{context}: the procedure's {parameters} parameters are not its first "
            "location records in its own scope",
        )
    found = []
    for position, (item, offset, type_index, _top) in enumerate(locations):
        if offset is None:
            continue
        where = f"{context}: the local {item['name']!r} (ESP0{offset:+d}, type 0x{type_index:x})"
        if type_index < CODEVIEW_FIRST_TYPE_INDEX:
            size = primitive_size(type_index, where)
        else:
            require(
                item["type"] == _BPREL32_ST,
                f"{where} has a CodeView 4 user type, which this reader does not read",
            )
            known = type_sizes()
            require(
                known is not None,
                f"{where} has a user-defined type whose size is unknown: {reason}",
            )
            size = cast(TypeSizes, known).size(type_index)
        if position < parameters:
            start = offset
            require(
                offset >= 4 and offset + size <= params_end,
                f"{context}: the parameter {item['name']!r} (ESP0{offset:+d}, type "
                f"0x{type_index:x}) of {size} bytes lies outside the parameter words "
                f"[ESP0+4, ESP0{params_end:+d})",
            )
        elif offset > 0:
            start = offset - HOMED_RECORD_BIAS
            require(
                start >= 4 and start + size <= params_end,
                f"{where}, homed in a parameter's word at ESP0{start:+d}, of {size} bytes lies "
                f"outside the parameter words [ESP0+4, ESP0{params_end:+d})",
            )
        else:
            start = offset
            require(
                base <= offset and offset + size <= 0,
                f"{where} of {size} bytes lies outside the locals block [ESP0{base:+d}, ESP0)",
            )
        found.append(FrameLocal(item["name"], start, size, type_index))
    used = tuple(sorted(sizes.used)) if sizes is not None else ()
    return tuple(found), used


def merge_frame_objects(
    local_records: tuple[FrameLocal, ...], type_records: tuple[str, ...] = ()
) -> FrameObjects:
    """The frame objects: the locals whose ranges overlap, merged (see the module docstring)."""
    merged: list[FrameObject] = []
    for item in sorted(local_records, key=lambda local: (local.start, local.size, local.name)):
        if merged and item.start < merged[-1].end:
            last = merged[-1]
            end = max(last.end, item.start + item.size)
            merged[-1] = FrameObject(last.start, end - last.start, (*last.names, item.name))
        else:
            merged.append(FrameObject(item.start, item.size, (item.name,)))
    return FrameObjects(tuple(merged), type_records)


def donor_frame_objects(
    donor: CoffObject,
    primary: dict[str, Any],
    type_server: bytes | None,
    *,
    base: int,
    params_end: int,
    context: str,
) -> FrameObjects:
    """The donor function's frame objects (a14), or a refusal naming what is missing."""
    local_records, used = frame_locals(
        donor, primary, type_server, base=base, params_end=params_end, context=context
    )
    return merge_frame_objects(local_records, used)


__all__ = [
    "HOMED_RECORD_BIAS",
    "PRIMITIVE_SIZES",
    "FrameLocal",
    "FrameObject",
    "FrameObjects",
    "TypeServer",
    "TypeSizes",
    "donor_frame_objects",
    "frame_locals",
    "merge_frame_objects",
    "object_type_records",
    "parameter_count",
    "primitive_size",
    "read_type_server",
]
