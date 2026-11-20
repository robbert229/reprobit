"""A function-isolated view of an MSVC object compiled without /Gy.

A compile without ``/Gy`` places every function that is not a COMDAT in one
plain ``.text`` section, and their FPO records in one plain ``.debug$F``
section.  A function there is the range from its symbol to the next function
symbol of the section (or the section end), with the relocations inside that
range; MSVC 5.0 pads each such range with NOP fill to a 16-byte multiple,
exactly as it pads a ``/Gy`` COMDAT body.  With ``/Zi`` the section also
carries one group of COFF line numbers per function (a sentinel row naming
the function, then rows at section offsets), the function's ``.bf``, ``.lf``
and ``.ef`` symbols, and one procedure block (a procedure record through its
``S_END``) per function in the object's plain ``.debug$S`` stream.

The ReproBit producers place and replace a function as a COMDAT.  This module
gives them one: :func:`isolate_functions` writes the same object with every
function of a plain ``.text`` section moved into its own COMDAT section
(selection 1, as ``/Gy`` writes it), followed by an associative ``.debug$S``
child holding its procedure block and an associative ``.debug$F`` child
holding its FPO record, all appended after the object's own sections.  Its
line group, labels and markers move with it, rebased to the function's start.
Symbol indices, relocation records and every other section stay as they
were.

:meth:`IsolatedObject.project` maps a producer's output back: each function's
body, relocations, line rows, label values, procedure block and FPO record go
back to their own places in the shared sections.  A body keeps its range's
length, or a shorter body whose NOP fill still ends at the range's end;
nothing else may change.  The projection is accepted only when isolating it
again gives exactly the producer's output, so the view is a bijection on
every object it accepts.  The object itself must be laid out as MSVC lays out
an object (each section's data, relocations and line numbers in section
order, then the symbol and string tables), which is checked by writing it
again.
"""

from __future__ import annotations

import struct
from dataclasses import dataclass, field
from typing import Any

from reprobit.binary import ByteIdentityError, require
from reprobit.coff_format import (
    RELOCATION_WIDTHS,
    CoffObject,
    coff_body,
    coff_table,
    detailed_relocations,
    section_definitions,
)

LNK_COMDAT = 0x1000
_UNINITIALIZED = 0x80
_FUNCTION_TYPE = 0x20
_FUNCTION_STORAGE = (2, 3)
_MARKER_STORAGE = 101
_DIR32NB = 0x0007
_SECREL = 0x000B
_FPO_RECORD_SIZE = 16
# MSVC 5.0 pads a function to a 16-byte multiple with NOP fill.
_FILL_BYTE = 0x90
_SLOT_ALIGNMENT = 16
_SELECT_NODUPLICATES = 1
_SELECT_ASSOCIATIVE = 5
_CODEVIEW_SIGNATURE_SIZE = 4
# CodeView procedure records (CV4 and MSVC 5.0's length-prefixed-name forms)
# and the other records that open a scope closed by S_END.
_PROCEDURE_RECORDS = frozenset({0x0204, 0x0205, 0x100A, 0x100B})
_SCOPE_RECORDS = _PROCEDURE_RECORDS | {0x0206, 0x0207, 0x0208}
_SCOPE_END = 0x0006
# Where each procedure record's offset field lies, relocated (SECREL) to its
# function: after a 16-bit type index in CV4's records, a 32-bit one in
# MSVC 5.0's.
_PROCEDURE_OFFSET_FIELD = {0x0204: 30, 0x0205: 30, 0x100A: 32, 0x100B: 32}


@dataclass(frozen=True, slots=True)
class _Slot:
    """One function of a plain .text section and its seats in the view."""

    section: int
    start: int
    end: int
    function_index: int
    view_section: int
    lines: tuple[int, int]
    debug: tuple[int, int] | None
    view_debug_section: int | None
    fpo: tuple[int, int] | None
    view_fpo_section: int | None


@dataclass(slots=True)
class _Section:
    header: bytearray
    raw: bytes
    relocations: bytes
    lines: bytes


@dataclass(slots=True)
class _Stream:
    """The plain .debug$S stream cut into kept pieces and procedure blocks."""

    number: int
    # (start, end, owning slot's function index or None for a kept piece)
    pieces: list[tuple[int, int, int | None]] = field(default_factory=list)


def defined_in_plain_text(data: bytes, symbol: str) -> bool:
    """Whether ``symbol`` is a function defined in a plain (non-COMDAT) .text section."""

    try:
        coff = CoffObject(data)
    except (ByteIdentityError, UnicodeError, ValueError):
        return False
    return any(
        item["name"] == symbol
        and item["type"] == _FUNCTION_TYPE
        and item["storage"] in _FUNCTION_STORAGE
        and 0 < item["section"] <= len(coff.sections)
        and _plain_text(coff.sections[item["section"] - 1])
        for item in coff.symbols.values()
    )


def _plain_text(section: dict[str, Any]) -> bool:
    return bool(
        str(section["name"]).startswith(".text")
        and not section["characteristics"] & LNK_COMDAT
        and section["raw_size"]
    )


def _sections_of(coff: CoffObject) -> list[_Section]:
    result = []
    for section in coff.sections:
        offset = section["header_offset"]
        result.append(
            _Section(
                header=bytearray(coff.data[offset : offset + 40]),
                raw=bytes(coff_body(coff, section)),
                relocations=coff_table(coff, section, "relocations"),
                lines=coff_table(coff, section, "lines"),
            )
        )
    return result


def _symbol_records(coff: CoffObject) -> list[bytearray]:
    return [
        bytearray(coff.data[coff.symbol_offset + index * 18 : coff.symbol_offset + index * 18 + 18])
        for index in range(coff.symbol_count)
    ]


def _sentinel_row(lines: bytes, function_index: int) -> int | None:
    for row in range(len(lines) // 6):
        if struct.unpack_from("<IH", lines, row * 6) == (function_index, 0):
            return row
    return None


def _serialize(template: CoffObject, sections: list[_Section], symbols: list[bytearray]) -> bytes:
    """Write an object in MSVC's own layout.

    Each section's raw data, relocations and line numbers follow the section
    table in section order, then the symbol table and the template's string
    table.  A function definition record's line pointer is the file offset of
    its sentinel row in its section's line table (zero without one).
    """

    cursor = 20 + 40 * len(sections)
    chunks: list[bytes] = []
    headers = bytearray()
    line_pointers: list[int] = []
    for section in sections:
        header = bytearray(section.header)
        uninitialized = bool(int.from_bytes(header[36:40], "little") & _UNINITIALIZED)
        pointers = []
        for payload in (b"" if uninitialized else section.raw, section.relocations, section.lines):
            pointers.append(cursor if payload else 0)
            if payload:
                chunks.append(payload)
                cursor += len(payload)
        line_pointers.append(pointers[2])
        raw_size = int.from_bytes(header[16:20], "little") if uninitialized else len(section.raw)
        struct.pack_into(
            "<IIIIHH",
            header,
            16,
            raw_size,
            pointers[0],
            pointers[1],
            pointers[2],
            len(section.relocations) // 10,
            len(section.lines) // 6,
        )
        headers += header
    records = [bytearray(record) for record in symbols]
    index = 0
    while index < len(records):
        record = records[index]
        (number,) = struct.unpack_from("<h", record, 12)
        (kind,) = struct.unpack_from("<H", record, 14)
        storage, auxiliary = record[16], record[17]
        if kind == _FUNCTION_TYPE and storage in _FUNCTION_STORAGE and auxiliary and number > 0:
            row = _sentinel_row(sections[number - 1].lines, index)
            pointer = 0 if row is None else line_pointers[number - 1] + row * 6
            struct.pack_into("<I", records[index + 1], 8, pointer)
        index += 1 + auxiliary
    file_header = bytearray(template.data[:20])
    struct.pack_into("<H", file_header, 2, len(sections))
    struct.pack_into("<II", file_header, 8, cursor, len(records))
    strings = template.data[template.string_offset : template.string_end]
    return bytes(file_header + headers + b"".join(chunks) + b"".join(records) + strings)


def _set_definition(symbols: list[bytearray], index: int, section: _Section) -> None:
    """Re-state a section-definition record's length and relocation and line counts."""

    struct.pack_into(
        "<IHH",
        symbols[index + 1],
        0,
        len(section.raw),
        len(section.relocations) // 10,
        len(section.lines) // 6,
    )


def _definition_symbol(
    name: str, number: int, section: _Section, associated: int, selection: int
) -> list[bytearray]:
    record = bytearray(18)
    record[0:8] = name.encode("ascii").ljust(8, b"\0")
    struct.pack_into("<IhHBB", record, 8, 0, number, 0, 3, 1)
    auxiliary = bytearray(18)
    struct.pack_into(
        "<IHHIHB",
        auxiliary,
        0,
        len(section.raw),
        len(section.relocations) // 10,
        len(section.lines) // 6,
        0,
        associated,
        selection,
    )
    return [record, auxiliary]


def _relocation(offset: int, symbol_index: int, kind: int) -> bytes:
    return struct.pack("<IIH", offset, symbol_index, kind)


def _rebased(table: bytes, delta: int) -> bytes:
    out = bytearray()
    for at in range(0, len(table), 10):
        offset, symbol_index, kind = struct.unpack_from("<IIH", table, at)
        out += _relocation(offset + delta, symbol_index, kind)
    return bytes(out)


def _relocations_within(table: bytes, start: int, end: int) -> bytes:
    """The records of a relocation table whose offsets lie in [start, end), rebased to start."""

    out = bytearray()
    for at in range(0, len(table), 10):
        offset, symbol_index, kind = struct.unpack_from("<IIH", table, at)
        if start <= offset < end:
            out += _relocation(offset - start, symbol_index, kind)
    return bytes(out)


def _lines_rebased(lines: bytes, delta: int) -> bytes:
    out = bytearray()
    for at in range(0, len(lines), 6):
        address, number = struct.unpack_from("<IH", lines, at)
        out += struct.pack("<IH", address if number == 0 else address + delta, number)
    return bytes(out)


class IsolatedObject:
    """One object compiled without /Gy, its function-isolated view and the way back."""

    def __init__(self, data: bytes) -> None:
        coff = CoffObject(data)
        self.original = data
        self._coff = coff
        require(
            _serialize(coff, _sections_of(coff), _symbol_records(coff)) == data,
            "the object is not laid out as MSVC lays out an object",
        )
        self._definitions = {
            int(item["section"]): index
            for index, item in coff.symbols.items()
            if 0 < item["section"] <= len(coff.sections)
            and item["storage"] == 3
            and item["aux_count"] >= 1
            and item["name"] == coff.sections[item["section"] - 1]["name"]
        }
        plain = [section for section in coff.sections if _plain_text(section)]
        require(bool(plain), "the object holds no function in a plain .text section")
        functions: dict[int, list[tuple[int, int]]] = {}
        for index, item in coff.symbols.items():
            if (
                item["type"] == _FUNCTION_TYPE
                and item["storage"] in _FUNCTION_STORAGE
                and 0 < item["section"] <= len(coff.sections)
                and _plain_text(coff.sections[item["section"] - 1])
            ):
                functions.setdefault(int(item["section"]), []).append((int(item["value"]), index))
        owners = {index for starts in functions.values() for _, index in starts}
        fpo_records = self._fpo_records(coff, owners)
        self._stream = self._procedure_blocks(coff, owners)
        blocks = {
            owner: (start, end)
            for start, end, owner in (self._stream.pieces if self._stream else [])
            if owner is not None
        }
        slots: list[_Slot] = []
        next_section = len(coff.sections) + 1
        for section in plain:
            number = int(section["number"])
            starts = sorted(functions.get(number, []))
            require(bool(starts), f"plain .text section {number} defines no function")
            require(
                starts[0][0] == 0,
                f"plain .text section {number} holds bytes before its first function",
            )
            require(
                len({start for start, _ in starts}) == len(starts),
                f"two functions of plain .text section {number} share an offset",
            )
            ends = [start for start, _ in starts[1:]] + [int(section["raw_size"])]
            groups = self._line_groups(coff, section, starts, ends)
            for (start, function_index), end in zip(starts, ends, strict=True):
                debug = blocks.get(function_index)
                fpo = fpo_records.get(function_index)
                view_section = next_section
                next_section += 1
                view_debug: int | None = next_section if debug is not None else None
                next_section += debug is not None
                view_fpo: int | None = next_section if fpo is not None else None
                next_section += fpo is not None
                slots.append(
                    _Slot(
                        section=number,
                        start=start,
                        end=end,
                        function_index=function_index,
                        view_section=view_section,
                        lines=groups[function_index],
                        debug=debug,
                        view_debug_section=view_debug,
                        fpo=fpo,
                        view_fpo_section=view_fpo,
                    )
                )
        self.slots = tuple(slots)
        # The shared sections the view takes records out of.
        self._shared = {slot.section for slot in slots} | {
            slot.fpo[0] for slot in slots if slot.fpo is not None
        }
        if self._stream is not None:
            self._shared.add(self._stream.number)
        for number in self._shared:
            section = coff.sections[number - 1]
            definition = self._definitions.get(number)
            require(
                definition is None
                or struct.unpack_from("<IHH", coff.data, coff.symbol_offset + (definition + 1) * 18)
                == (section["raw_size"], section["relocation_count"], section["line_count"]),
                f"section {number}'s definition record does not state its size and counts",
            )
        self._placement = self._symbol_placement(coff)
        self._require_relocation_ranges(coff)
        self.view = self._isolate(coff)

    @staticmethod
    def _fpo_records(coff: CoffObject, owners: set[int]) -> dict[int, tuple[int, int]]:
        """Each plain-.text function's FPO record: (plain .debug$F section, record offset)."""

        definitions = section_definitions(coff)
        result: dict[int, tuple[int, int]] = {}
        for section in coff.sections:
            if section["name"] != ".debug$F" or section["characteristics"] & LNK_COMDAT:
                continue
            number = int(section["number"])
            require(
                number not in definitions or definitions[number]["selection"] == 0,
                f"plain .debug$F section {number} is a COMDAT",
            )
            require(
                section["raw_size"] % _FPO_RECORD_SIZE == 0,
                f"plain .debug$F section {number} is not a whole number of FPO records",
            )
            rows = detailed_relocations(coff, section)
            require(
                [row["offset"] for row in rows]
                == list(range(0, int(section["raw_size"]), _FPO_RECORD_SIZE))
                and all(row["type"] == _DIR32NB and row["addend"] == 0 for row in rows),
                f"plain .debug$F section {number} does not relocate each record's start to "
                "its function",
            )
            for row in rows:
                if row["symbol_index"] in owners:
                    require(
                        row["symbol_index"] not in result,
                        f"function {row['target']!r} has two FPO records",
                    )
                    result[int(row["symbol_index"])] = (number, int(row["offset"]))
        return result

    @staticmethod
    def _procedure_blocks(coff: CoffObject, owners: set[int]) -> _Stream | None:
        """Cut the plain .debug$S stream into kept pieces and each function's block."""

        streams = [
            section
            for section in coff.sections
            if section["name"] == ".debug$S" and not section["characteristics"] & LNK_COMDAT
        ]
        if not streams:
            return None
        require(len(streams) == 1, "the object has more than one plain .debug$S stream")
        section = streams[0]
        raw = bytes(coff_body(coff, section))
        rows = detailed_relocations(coff, section)
        require(
            [row["offset"] for row in rows] == sorted(row["offset"] for row in rows),
            "the plain .debug$S relocations are not in stream order",
        )
        secrel = {row["offset"]: row for row in rows if row["type"] == _SECREL}
        stream = _Stream(int(section["number"]))
        require(len(raw) >= _CODEVIEW_SIGNATURE_SIZE, "the plain .debug$S stream is truncated")
        kept_start = 0
        cursor = _CODEVIEW_SIGNATURE_SIZE
        depth = 0
        block: tuple[int, int] | None = None
        seen: set[int] = set()
        while cursor < len(raw):
            require(cursor + 4 <= len(raw), "a .debug$S record is truncated")
            length, kind = struct.unpack_from("<HH", raw, cursor)
            end = cursor + 2 + length
            require(length >= 2 and end <= len(raw), "a .debug$S record overruns its stream")
            if depth == 0 and kind in _PROCEDURE_RECORDS:
                row = secrel.get(cursor + _PROCEDURE_OFFSET_FIELD[kind])
                if row is not None and row["symbol_index"] in owners:
                    require(
                        row["symbol_index"] not in seen,
                        f"function {row['target']!r} has two procedure blocks",
                    )
                    seen.add(int(row["symbol_index"]))
                    if kept_start < cursor:
                        stream.pieces.append((kept_start, cursor, None))
                    block = (cursor, int(row["symbol_index"]))
            if kind in _SCOPE_RECORDS:
                depth += 1
            elif kind == _SCOPE_END:
                require(depth > 0, "a .debug$S S_END closes no scope")
                depth -= 1
                if depth == 0 and block is not None:
                    stream.pieces.append((block[0], end, block[1]))
                    kept_start = end
                    block = None
            cursor = end
        require(depth == 0 and block is None, "a .debug$S scope is not closed")
        if kept_start < len(raw):
            stream.pieces.append((kept_start, len(raw), None))
        for row in rows:
            require(
                any(
                    start <= row["offset"] and row["offset"] + row["width"] <= end
                    for start, end, _ in stream.pieces
                ),
                "a .debug$S relocation straddles a procedure block",
            )
        return stream

    @staticmethod
    def _line_groups(
        coff: CoffObject,
        section: dict[str, Any],
        starts: list[tuple[int, int]],
        ends: list[int],
    ) -> dict[int, tuple[int, int]]:
        """Each function's (first row, row count) in its section's line table."""

        lines = coff_table(coff, section, "lines")
        groups: dict[int, tuple[int, int]] = {index: (0, 0) for _, index in starts}
        ranges = {index: (start, end) for (start, index), end in zip(starts, ends, strict=True)}
        order = []
        current: int | None = None
        for row in range(len(lines) // 6):
            address, number = struct.unpack_from("<IH", lines, row * 6)
            if number == 0:
                require(
                    address in groups and groups[address] == (0, 0),
                    f"a line group of plain .text section {section['number']} names no "
                    "function of it, or one twice",
                )
                current = int(address)
                groups[current] = (row, 1)
                order.append(ranges[current][0])
                continue
            require(current is not None, "a line row precedes every function's sentinel")
            assert current is not None
            start, end = ranges[current]
            require(
                start <= address < end,
                f"a line row at {address} lies outside its function",
            )
            first, count = groups[current]
            groups[current] = (first, count + 1)
        require(order == sorted(order), "the line groups are not in function order")
        return groups

    def _slot_at(self, section: int, value: int) -> _Slot:
        for slot in self.slots:
            if slot.section == section and slot.start <= value < slot.end:
                return slot
        raise ByteIdentityError(f"offset {value} of section {section} lies in no function")

    def _symbol_placement(self, coff: CoffObject) -> dict[int, tuple[_Slot, bool]]:
        """Each symbol of a plain .text section: its function's slot and whether its
        value is an offset (a .lf marker's value is a line count)."""

        plain = {slot.section for slot in self.slots}
        by_function = {slot.function_index: slot for slot in self.slots}
        placement: dict[int, tuple[_Slot, bool]] = {}
        current: _Slot | None = None
        for index, item in coff.symbols.items():
            number = int(item["section"])
            if number not in plain or self._definitions.get(number) == index:
                continue
            if index in by_function:
                placement[index] = (by_function[index], True)
            elif item["storage"] == _MARKER_STORAGE:
                if item["name"] == ".bf":
                    current = self._slot_at(number, int(item["value"]))
                    require(
                        item["value"] == current.start,
                        f"a .bf marker at {item['value']} does not open its function",
                    )
                require(
                    current is not None and current.section == number,
                    f"the marker {item['name']!r} follows no .bf of its section",
                )
                assert current is not None
                if item["name"] == ".ef":
                    require(
                        current.start < item["value"] <= current.end,
                        f"an .ef marker at {item['value']} lies outside its function",
                    )
                placement[index] = (current, item["name"] != ".lf")
            else:
                require(
                    item["aux_count"] == 0,
                    f"the symbol {item['name']!r} of a plain .text section has auxiliary records",
                )
                placement[index] = (self._slot_at(number, int(item["value"])), True)
        return placement

    def _require_relocation_ranges(self, coff: CoffObject) -> None:
        plain = {slot.section for slot in self.slots}
        for section in coff.sections:
            if section["number"] not in plain:
                continue
            order = []
            for row in detailed_relocations(coff, section):
                slot = self._slot_at(int(section["number"]), int(row["offset"]))
                require(
                    row["offset"] + row["width"] <= slot.end,
                    f"a relocation at {row['offset']} straddles two functions",
                )
                order.append(slot.start)
            require(
                order == sorted(order),
                f"plain .text section {section['number']}'s relocations are not grouped by "
                "function",
            )

    def _isolate(self, coff: CoffObject) -> bytes:
        sections = _sections_of(coff)
        symbols = _symbol_records(coff)
        appended: list[_Section] = []
        appended_symbols: list[bytearray] = []
        moved_fpo: dict[int, set[int]] = {}
        stream = self._stream
        stream_raw = sections[stream.number - 1].raw if stream else b""
        stream_rows = sections[stream.number - 1].relocations if stream else b""
        for slot in self.slots:
            text = sections[slot.section - 1]
            header = bytearray(text.header)
            struct.pack_into("<I", header, 36, int.from_bytes(header[36:40], "little") | LNK_COMDAT)
            first, count = slot.lines
            body = _Section(
                header,
                text.raw[slot.start : slot.end],
                _relocations_within(text.relocations, slot.start, slot.end),
                _lines_rebased(text.lines[first * 6 : (first + count) * 6], -slot.start),
            )
            appended.append(body)
            appended_symbols += _definition_symbol(
                _section_name(header), slot.view_section, body, 0, _SELECT_NODUPLICATES
            )
            if slot.debug is not None and stream is not None:
                start, end = slot.debug
                debug_header = bytearray(sections[stream.number - 1].header)
                struct.pack_into(
                    "<I",
                    debug_header,
                    36,
                    int.from_bytes(debug_header[36:40], "little") | LNK_COMDAT,
                )
                child = _Section(
                    debug_header,
                    stream_raw[start:end],
                    _relocations_within(stream_rows, start, end),
                    b"",
                )
                appended.append(child)
                appended_symbols += _definition_symbol(
                    ".debug$S",
                    int(slot.view_debug_section or 0),
                    child,
                    slot.view_section,
                    _SELECT_ASSOCIATIVE,
                )
            if slot.fpo is not None:
                fpo_section, record = slot.fpo
                frame = sections[fpo_section - 1]
                fpo_header = bytearray(frame.header)
                struct.pack_into(
                    "<I", fpo_header, 36, int.from_bytes(fpo_header[36:40], "little") | LNK_COMDAT
                )
                ordinal = record // _FPO_RECORD_SIZE
                child = _Section(
                    fpo_header,
                    frame.raw[record : record + _FPO_RECORD_SIZE],
                    _rebased(frame.relocations[ordinal * 10 : ordinal * 10 + 10], -record),
                    b"",
                )
                appended.append(child)
                appended_symbols += _definition_symbol(
                    ".debug$F",
                    int(slot.view_fpo_section or 0),
                    child,
                    slot.view_section,
                    _SELECT_ASSOCIATIVE,
                )
                moved_fpo.setdefault(fpo_section, set()).add(record)
        for index, (slot, offset) in self._placement.items():
            value = struct.unpack_from("<I", symbols[index], 8)[0]
            struct.pack_into(
                "<Ih", symbols[index], 8, value - slot.start if offset else value, slot.view_section
            )
        for number in {slot.section for slot in self.slots}:
            sections[number - 1].raw = b""
            sections[number - 1].relocations = b""
            sections[number - 1].lines = b""
        for number, records in moved_fpo.items():
            frame = sections[number - 1]
            kept_raw = bytearray()
            kept_rows = bytearray()
            for record in range(0, len(frame.raw), _FPO_RECORD_SIZE):
                if record in records:
                    continue
                ordinal = record // _FPO_RECORD_SIZE
                kept_rows += _rebased(
                    frame.relocations[ordinal * 10 : ordinal * 10 + 10], len(kept_raw) - record
                )
                kept_raw += frame.raw[record : record + _FPO_RECORD_SIZE]
            frame.raw, frame.relocations = bytes(kept_raw), bytes(kept_rows)
        if stream is not None:
            kept = bytearray()
            kept_rows = bytearray()
            for start, end, owner in stream.pieces:
                if owner is None:
                    kept_rows += _rebased(_relocations_within(stream_rows, start, end), len(kept))
                    kept += stream_raw[start:end]
            sections[stream.number - 1].raw = bytes(kept)
            sections[stream.number - 1].relocations = bytes(kept_rows)
        for number in self._shared:
            if number in self._definitions:
                _set_definition(symbols, self._definitions[number], sections[number - 1])
        return _serialize(coff, sections + appended, symbols + appended_symbols)

    def project(self, composed: bytes) -> bytes:
        """Map a producer's output on the view back onto the original object."""

        view = CoffObject(self.view)
        output = CoffObject(composed)
        coff = self._coff
        require(
            len(output.sections) == len(view.sections) and output.symbol_count == view.symbol_count,
            "the composed view changed the object's section or symbol table",
        )
        sections = _sections_of(coff)
        symbols = _symbol_records(coff)
        composed_sections = _sections_of(output)
        padded: dict[int, int] = {}
        texts: dict[int, list[tuple[bytes, bytes, bytes]]] = {}
        blocks: dict[int, _Section] = {}
        for slot in self.slots:
            target = composed_sections[slot.view_section - 1]
            body = target.raw
            size = slot.end - slot.start
            require(
                len(body) == size
                or (
                    0 < len(body) < size
                    and -(-len(body) // _SLOT_ALIGNMENT) * _SLOT_ALIGNMENT == size
                ),
                f"the composed body of {coff.symbols[slot.function_index]['name']!r} is "
                f"{len(body)} bytes and does not fit its {size}-byte range",
            )
            if len(body) < size:
                padded[slot.view_section] = size
                body += bytes([_FILL_BYTE]) * (size - len(body))
            for row in detailed_relocations(output, output.sections[slot.view_section - 1]):
                require(
                    row["symbol_index"] < coff.symbol_count,
                    "a composed relocation names a symbol only the view defines",
                )
                require(
                    row["type"] in RELOCATION_WIDTHS and row["offset"] + row["width"] <= size,
                    "a composed relocation lies outside its function's range",
                )
            texts.setdefault(slot.section, []).append(
                (
                    body,
                    _rebased(target.relocations, slot.start),
                    _lines_rebased(target.lines, slot.start),
                )
            )
            if slot.view_debug_section is not None:
                blocks[slot.function_index] = composed_sections[slot.view_debug_section - 1]
            if slot.fpo is not None:
                fpo_section, record = slot.fpo
                record_body = composed_sections[int(slot.view_fpo_section or 0) - 1].raw
                require(
                    len(record_body) == _FPO_RECORD_SIZE,
                    "a composed FPO child is not one FPO record",
                )
                raw = bytearray(sections[fpo_section - 1].raw)
                raw[record : record + _FPO_RECORD_SIZE] = record_body
                sections[fpo_section - 1].raw = bytes(raw)
        for number, pieces in texts.items():
            sections[number - 1].raw = b"".join(body for body, _, _ in pieces)
            sections[number - 1].relocations = b"".join(rows for _, rows, _ in pieces)
            sections[number - 1].lines = b"".join(lines for _, _, lines in pieces)
        stream = self._stream
        if stream is not None:
            kept = composed_sections[stream.number - 1]
            raw = bytearray()
            rows = bytearray()
            cursor = 0
            for start, end, owner in stream.pieces:
                if owner is None:
                    length = end - start
                    rows += _rebased(
                        _relocations_within(kept.relocations, cursor, cursor + length),
                        len(raw),
                    )
                    raw += kept.raw[cursor : cursor + length]
                    cursor += length
                else:
                    block = blocks[owner]
                    rows += _rebased(block.relocations, len(raw))
                    raw += block.raw
            sections[stream.number - 1].raw = bytes(raw)
            sections[stream.number - 1].relocations = bytes(rows)
        for index, (slot, offset) in self._placement.items():
            item = output.symbols[index]
            require(
                item["section"] == slot.view_section,
                f"the composed view moved the symbol {item['name']!r} out of its function",
            )
            value = int(item["value"])
            struct.pack_into(
                "<Ih", symbols[index], 8, value + slot.start if offset else value, slot.section
            )
            if item["aux_count"]:
                symbols[index + 1] = bytearray(
                    output.data[
                        output.symbol_offset + (index + 1) * 18 : output.symbol_offset
                        + (index + 2) * 18
                    ]
                )
        for number in self._shared:
            if number in self._definitions:
                _set_definition(symbols, self._definitions[number], sections[number - 1])
        projected = _serialize(coff, sections, symbols)
        again = IsolatedObject(projected).view
        require(
            _comparable(CoffObject(again)) == _comparable(output, padded),
            "the composed view is not the view of any object: it changed bytes outside its "
            "functions' own records",
        )
        return projected


def _section_name(header: bytes | bytearray) -> str:
    return header[0:8].rstrip(b"\0").decode("ascii")


def _comparable(coff: CoffObject, padded: dict[int, int] | None = None) -> tuple[Any, ...]:
    """An object's content, independent of where its file places each table.

    ``padded`` maps a section to the length its body takes once its NOP fill
    reaches the end of its function's range.  A function definition record's
    line pointer is a file offset, so it is compared as the row it names.
    """

    padded = padded or {}
    sections = []
    for section in coff.sections:
        body = bytes(coff_body(coff, section))
        size = padded.get(int(section["number"]))
        if size is not None:
            body += bytes([_FILL_BYTE]) * (size - len(body))
        sections.append(
            (
                section["name"],
                section["characteristics"],
                body,
                coff_table(coff, section, "relocations"),
                coff_table(coff, section, "lines"),
            )
        )
    symbols = [bytes(record) for record in _symbol_records(coff)]
    for index, item in coff.symbols.items():
        if (
            item["type"] == _FUNCTION_TYPE
            and item["storage"] in _FUNCTION_STORAGE
            and item["aux_count"]
            and item["section"] > 0
        ):
            record = bytearray(symbols[index + 1])
            pointer = struct.unpack_from("<I", record, 8)[0]
            section = coff.sections[item["section"] - 1]
            row = (
                (pointer - section["line_offset"]) // 6 if pointer and section["line_count"] else -1
            )
            struct.pack_into("<i", record, 8, row)
            symbols[index + 1] = bytes(record)
    definitions = section_definitions(coff)
    for number, size in padded.items():
        definition = definitions.get(number)
        if definition is not None:
            at = int(definition["symbol_index"]) + 1
            record = bytearray(symbols[at])
            struct.pack_into("<I", record, 0, size)
            symbols[at] = bytes(record)
    return (coff.data[:2], coff.data[4:8], coff.data[18:20], tuple(sections), tuple(symbols))


def isolate_functions(data: bytes) -> IsolatedObject:
    """The function-isolated view of an object compiled without /Gy (see module docstring)."""

    return IsolatedObject(data)


__all__ = ["IsolatedObject", "defined_in_plain_text", "isolate_functions"]
