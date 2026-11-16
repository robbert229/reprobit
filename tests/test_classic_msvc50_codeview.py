"""MSVC 5.0 object conventions the classic producers must read.

MSVC 5.0 writes CodeView symbol records with 32-bit type indices (the `_ST`
forms, 0x1001-0x100B) and pads each function's COMDAT to a 16-byte multiple
with NOP fill after the code, while its procedure, FPO and symbol records keep
the code's own length. The record bytes below are from MSVC 5.0 objects.
"""

from __future__ import annotations

import pytest

from reprobit.binary import ByteIdentityError
from reprobit.classic.debug import (
    CODEVIEW_LOCAL_LOCATION_RECORD_TYPES,
    CODEVIEW_PROCEDURE_RECORD_TYPES,
    _codeview_local_location,
    codeview_procedure_identity,
    codeview_register_field_offset,
    fpo_proc_size_fits,
    parse_codeview_symbol_stream,
)


def _record(record_type: int, payload: bytes) -> bytes:
    return (len(payload) + 2).to_bytes(2, "little") + record_type.to_bytes(2, "little") + payload


def _name(text: str) -> bytes:
    return bytes([len(text)]) + text.encode("latin1")


# S_GPROC32_ST: parent, end, next, length, debug start, debug end, type (u32),
# offset, segment, flags, name.
GPROC32_ST = bytes.fromhex(
    "000000000000000000000000390100000000000031010000f301000000000000000000"
) + _name("_xf_texture_name_format")
BPREL32_ST = bytes.fromhex("040000001a120000") + _name("request")
REGISTER_ST = bytes.fromhex("991000001200") + _name("this")
BLOCK32 = bytes.fromhex("0000000000000000ef010000530000000000") + _name("")
LABEL32 = bytes.fromhex("10000000000000") + _name("$L123")
CONSTANT_ST_SMALL = bytes.fromhex("9f1300000100") + _name("XLAT_SERVER")
CONSTANT_ST_LONG = bytes.fromhex("9f130000038000000100") + _name("BIG")


def test_msvc50_symbol_records_parse_to_their_names() -> None:
    stream = b"".join(
        (
            _record(0x100B, GPROC32_ST),
            _record(0x1006, BPREL32_ST),
            _record(0x1001, REGISTER_ST),
            _record(0x0207, BLOCK32),
            _record(0x0209, LABEL32),
            _record(0x1002, CONSTANT_ST_SMALL),
            _record(0x1002, CONSTANT_ST_LONG),
            _record(0x0006, b""),
            _record(0x0006, b""),
        )
    )
    records = parse_codeview_symbol_stream(stream, "test")
    assert [(item["type"], item["name"]) for item in records] == [
        (0x100B, "_xf_texture_name_format"),
        (0x1006, "request"),
        (0x1001, "this"),
        (0x0207, ""),
        (0x0209, "$L123"),
        (0x1002, "XLAT_SERVER"),
        (0x1002, "BIG"),
        (0x0006, ""),
        (0x0006, ""),
    ]
    assert 0x100B in CODEVIEW_PROCEDURE_RECORD_TYPES


def test_an_unknown_numeric_leaf_is_refused() -> None:
    payload = bytes.fromhex("9f1300000f8000") + _name("X")
    with pytest.raises(ByteIdentityError, match="numeric leaf"):
        parse_codeview_symbol_stream(_record(0x1002, payload), "test")


def test_msvc50_procedure_identity_ignores_extent_but_not_offset() -> None:
    longer = bytearray(GPROC32_ST)
    longer[12:16] = (0x140).to_bytes(4, "little")
    assert codeview_procedure_identity(0x100B, GPROC32_ST) == codeview_procedure_identity(
        0x100B, bytes(longer)
    )
    moved = bytearray(GPROC32_ST)
    moved[28:32] = (8).to_bytes(4, "little")
    assert codeview_procedure_identity(0x100B, GPROC32_ST) != codeview_procedure_identity(
        0x100B, bytes(moved)
    )


def test_msvc50_local_records_decode_their_locations() -> None:
    assert {0x1001, 0x1006} <= CODEVIEW_LOCAL_LOCATION_RECORD_TYPES
    assert _codeview_local_location(0x1006, BPREL32_ST, "test") == (0x121A, {"bp_offset": 4})
    assert _codeview_local_location(0x1001, REGISTER_ST, "test") == (0x1099, {"register": 18})
    assert codeview_register_field_offset(0x1001) == 4
    assert codeview_register_field_offset(2) == 2


def test_msvc50_alignment_fill_after_the_procedure_is_admitted() -> None:
    body = b"\xc3" * 313 + b"\x90" * 7
    assert fpo_proc_size_fits(320, 320, None)
    assert fpo_proc_size_fits(313, 320, body)
    assert not fpo_proc_size_fits(313, 320, None)
    assert not fpo_proc_size_fits(313, 320, b"\xc3" * 314 + b"\x90" * 6)
    assert not fpo_proc_size_fits(304, 320, b"\xc3" * 304 + b"\x90" * 16)
    assert not fpo_proc_size_fits(313, 319, b"\xc3" * 313 + b"\x90" * 6)
