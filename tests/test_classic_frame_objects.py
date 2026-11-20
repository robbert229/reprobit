"""The frame-objects pass of a whole-function proof (a14) and the extents it needs.

`function_validation.prove_function` runs the frame-objects pass only after
every earlier pass refuses because a stack address escapes.  It keeps a
private frame and makes memory of only the frame objects whose address
escapes, at their extents (`classic.frame_objects`): every other slot stays
a private slot, related like any other.  The programs are hand-encoded
IA-32 (each listing in the comment above it; a call's PC-relative field
holds 0, the addend the closed set admits).

1. Extents: CodeView locals, primitive sizes, MSVC 5.0 type records in the
   object or in the PDB type server it names (bound by signature and age),
   overlapping locals merged; parameters told from locals by the procedure's
   type, and a local homed in a dead parameter's word placed 4 below its
   record (a real MSVC 5.0 compile, `tests/fixtures/frame_objects`).
2. Proofs: swapped slots beside an escaping array or structure; a structure
   argument built through a register copy of ESP; refusals for an extent the
   replacement does not keep, an unknown size, an access or a stored pointer
   outside its object, a stack address in no local (stored, not only held),
   and a stack access at a variable offset.
3. The record: authored and dispatched with the donor's type server, pinning
   a14 and its escaping objects.
4. Grind and the build: grind authors the record with the PDB its donor
   compile wrote, and the build composes it from its own donor compile's PDB;
   a missing PDB, or one another compile wrote, refuses.
"""

from __future__ import annotations

import struct
from pathlib import Path
from types import SimpleNamespace
from typing import Any, cast

import pytest
from test_classic_function_validation import _extern_donor
from test_classic_register_bijection_reencoding_full import TARGET_SYMBOL, make_coff

from reprobit.binary import ByteIdentityError
from reprobit.classic.coff import _comdat_child
from reprobit.classic.debug import parse_codeview_symbol_stream
from reprobit.classic.frame_objects import (
    FrameLocal,
    FrameObjects,
    TypeSizes,
    donor_frame_objects,
    frame_locals,
    merge_frame_objects,
    object_type_records,
    primitive_size,
    read_type_server,
)
from reprobit.classic.function_validation import (
    FrameFacts,
    parse_fpo_data,
    proof_summary,
    prove_function,
)
from reprobit.classic.region_simulation import ObjectModel
from reprobit.classic_donors import merge_candidate_constraints
from reprobit.classic_project import (
    ClassicDispatchMaterials,
    ClassicFamilyDispatcher,
    ClassicProjectError,
)
from reprobit.coff_format import CoffObject, coff_body
from reprobit.discovery_authoring import DiscoveryAuthoringError
from reprobit.discovery_function_validation import build_function_validation_rewriting
from reprobit.model import Digest

T_INT4 = 0x74
T_RCHAR = 0x70
T_REAL64 = 0x41
T_32PVOID = 0x403
SIGNATURE = 0x6AFE5730
AGE = 42
PDB_MAGIC = b"Microsoft C/C++ program database 2.00\r\n\x1aJG\0\0"


def _code(text: str) -> bytes:
    return bytes.fromhex(text.replace(" ", ""))


# --- fixtures: type records, a type server, CodeView locals ------------------------------


def _type_record(leaf: int, payload: bytes) -> bytes:
    body = struct.pack("<H", leaf) + payload
    while (len(body) + 2) % 4:
        body += bytes([0xF4 - (len(body) + 2) % 4])
    return struct.pack("<H", len(body)) + body


def _name(text: str) -> bytes:
    return bytes([len(text)]) + text.encode()


def _array(element: int, size: int) -> bytes:
    return _type_record(0x1003, struct.pack("<IIH", element, 0x11, size) + _name(""))


def _structure(size: int, name: str, properties: int = 0, leaf: int = 0x1005) -> bytes:
    return _type_record(leaf, struct.pack("<HHIIIH", 2, properties, 0, 0, 0, size) + _name(name))


def _union(size: int, name: str, properties: int = 0) -> bytes:
    return _type_record(0x1006, struct.pack("<HHIH", 2, properties, 0, size) + _name(name))


def _pointer(referent: int, attributes: int = 0x0A) -> bytes:
    return _type_record(0x1002, struct.pack("<II", referent, attributes))


def _modifier(modified: int) -> bytes:
    return _type_record(0x1001, struct.pack("<IH", modified, 1))


def _enum(underlying: int) -> bytes:
    return _type_record(0x1007, struct.pack("<HHII", 3, 0, underlying, 0) + _name("E"))


def _arglist(types: list[int]) -> bytes:
    return _type_record(0x1201, struct.pack(f"<I{len(types)}I", len(types), *types))


def _procedure(arguments: int, count: int, leaf: int = 0x1008) -> bytes:
    """LF_PROCEDURE_ST: return type, convention, reserved, parameter count, argument list."""
    return _type_record(leaf, struct.pack("<IBBHI", 0x03, 0, 0, count, arguments))


# The fixture's types: char[16] (0x1000) and `void f(int)`'s argument list
# (0x1001) and procedure (0x1002), which the procedure record names.
REP_TYPES = [_array(T_RCHAR, 16), _arglist([T_INT4]), _procedure(0x1001, 1)]
REP_PROCEDURE_TYPE = 0x1002


def _pdb(records: list[bytes], signature: int = SIGNATURE, age: int = AGE) -> bytes:
    """A PDB 2.00 SmallMSF file of 1 KiB pages: header, directory, then streams 0-2."""
    page = 1024
    info = struct.pack("<III", 19960307, signature, age)
    body = b"".join(records)
    tpi = (
        struct.pack("<IIIII", 19961031, 56, 0x1000, 0x1000 + len(records), len(body))
        + bytes(36)
        + body
    )
    streams = [b"", info, tpi]
    lists = []
    next_page = 2
    for stream in streams:
        count = -(-len(stream) // page)
        lists.append(list(range(next_page, next_page + count)))
        next_page += count
    directory = (
        struct.pack("<HH", len(streams), 0)
        + b"".join(struct.pack("<II", len(stream), 0) for stream in streams)
        + b"".join(struct.pack("<H", number) for numbers in lists for number in numbers)
    )
    data = bytearray(next_page * page)
    header = PDB_MAGIC + struct.pack("<IHHIIH", page, 1, next_page, len(directory), 0, 1)
    data[: len(header)] = header
    data[page : page + len(directory)] = directory
    for stream, numbers in zip(streams, lists, strict=True):
        for index, number in enumerate(numbers):
            chunk = stream[index * page : (index + 1) * page]
            data[number * page : number * page + len(chunk)] = chunk
    return bytes(data)


def _type_server_stream(signature: int = SIGNATURE, age: int = AGE) -> bytes:
    """An object's `.debug$T` under /Zi: one LF_TYPESERVER record."""
    return struct.pack("<I", 2) + _type_record(
        0x0016, struct.pack("<II", signature, age) + _name("fixture.c.obj.pdb")
    )


def _object_types(records: list[bytes]) -> bytes:
    """An object's `.debug$T` under /Z7: the records themselves."""
    return struct.pack("<I", 2) + b"".join(records)


def _debug_s(
    body_length: int,
    local_records: list[tuple[str, int, int]],
    procedure_type: int = REP_PROCEDURE_TYPE,
    *,
    codeview4: bool = False,
) -> bytes:
    """S_GPROC32_ST naming ``procedure_type``, one S_BPREL32_ST per (name, offset,
    type), S_END.  A name "{" opens an S_BLOCK32 scope and "}" closes it."""
    records = bytearray()

    def record(kind: int, payload: bytes) -> None:
        records.extend(struct.pack("<HH", len(payload) + 2, kind))
        records.extend(payload)

    if codeview4:
        proc = bytearray(33)
        struct.pack_into("<III", proc, 12, body_length, 0, body_length - 1)
        record(0x0205, bytes(proc) + _name("_fixture"))
    else:
        proc = bytearray(35)
        struct.pack_into("<IIII", proc, 12, body_length, 0, body_length - 1, procedure_type)
        record(0x100B, bytes(proc) + _name("_fixture"))
    for name, offset, type_index in local_records:
        if name == "{":
            record(0x0207, bytes(18) + _name(""))
        elif name == "}":
            record(0x0006, b"")
        else:
            record(0x1006, struct.pack("<iI", offset, type_index) + _name(name))
    record(0x0006, b"")
    return bytes(records)


def _coff(
    body: bytes,
    local_records: list[tuple[str, int, int]],
    *,
    types: bytes | None,
    locals_words: int,
    params: int,
    codeview4: bool = False,
) -> bytes:
    """A donor (or reference) object with an FPO record of the given frame."""
    data = bytearray(
        make_coff(
            body=body,
            relocations=(),
            lines=((0, 10),),
            debug_stream=_debug_s(len(body), local_records, codeview4=codeview4),
            types=types,
        )
    )
    coff = CoffObject(bytes(data))
    fpo = next(section for section in coff.sections if section["name"] == ".debug$F")
    struct.pack_into("<IH", data, fpo["raw_offset"] + 8, locals_words, params)
    return bytes(data)


# --- 1. extents --------------------------------------------------------------------------


def test_primitive_sizes_come_from_the_index_alone() -> None:
    assert primitive_size(T_INT4, "x") == 4
    assert primitive_size(T_REAL64, "x") == 8
    assert primitive_size(T_RCHAR, "x") == 1
    assert primitive_size(T_32PVOID, "x") == 4  # a 32-bit near pointer to void
    with pytest.raises(ByteIdentityError, match=r"void has no size"):
        primitive_size(0x03, "x")
    with pytest.raises(ByteIdentityError, match=r"16-bit or far pointer"):
        primitive_size(0x174, "x")  # a 16-bit near pointer
    with pytest.raises(ByteIdentityError, match=r"no known size"):
        primitive_size(0x60, "x")


def test_type_records_give_arrays_structures_pointers_and_enums_their_sizes() -> None:
    records = [
        _array(T_RCHAR, 1024),  # 0x1000
        _structure(12, "Point3F"),  # 0x1001
        _pointer(0x1001),  # 0x1002
        _modifier(0x1001),  # 0x1003: const Point3F
        _enum(T_INT4),  # 0x1004
        _union(8, "U"),  # 0x1005
        _structure(0, "Late", properties=0x80),  # 0x1006: a forward reference
        _structure(24, "Late"),  # 0x1007: its definition
    ]
    sizes = TypeSizes(tuple(records), "x")
    assert [sizes.size(index) for index in range(0x1000, 0x1008)] == [
        1024, 12, 4, 12, 4, 8, 24, 24
    ]  # fmt: skip


def test_a_forward_reference_without_one_definition_is_refused() -> None:
    sizes = TypeSizes((_structure(0, "Gone", properties=0x80),), "x")
    with pytest.raises(ByteIdentityError, match=r"has 0 definitions"):
        sizes.size(0x1000)
    twice = (_structure(0, "Two", 0x80), _structure(4, "Two"), _structure(8, "Two"))
    with pytest.raises(ByteIdentityError, match=r"has 2 definitions"):
        TypeSizes(twice, "x").size(0x1000)


def test_a_leaf_without_a_size_and_a_far_pointer_are_refused() -> None:
    procedure = _type_record(0x1008, struct.pack("<IBBHI", T_INT4, 0, 0, 0, 0))
    with pytest.raises(ByteIdentityError, match=r"leaf 0x1008"):
        TypeSizes((procedure,), "x").size(0x1000)
    with pytest.raises(ByteIdentityError, match=r"not a 32-bit near pointer"):
        TypeSizes((_pointer(T_INT4, attributes=0x0B),), "x").size(0x1000)
    with pytest.raises(ByteIdentityError, match=r"names no available type record"):
        TypeSizes((), "x").size(0x1000)


def test_the_type_server_must_carry_the_signature_and_age_the_object_names() -> None:
    donor = CoffObject(
        _coff(REP_D, REP_LOCALS, types=_type_server_stream(), locals_words=7, params=1)
    )
    records, source = object_type_records(donor, _pdb(REP_TYPES), "x")
    assert source == "type server" and records is not None and len(records) == 3
    with pytest.raises(ByteIdentityError, match=r"has signature 0x00000001 and age 42"):
        object_type_records(donor, _pdb([], signature=1), "x")
    with pytest.raises(ByteIdentityError, match=r"and age 7, but the object names"):
        object_type_records(donor, _pdb([], age=7), "x")
    missing, reason = object_type_records(donor, None, "x")
    assert missing is None and "fixture.c.obj.pdb" in reason and "not supplied" in reason


def test_the_type_server_reader_is_strict() -> None:
    server = read_type_server(_pdb([_array(T_RCHAR, 16), _structure(8, "S")]))
    assert (server.signature, server.age, len(server.records)) == (SIGNATURE, AGE, 2)
    with pytest.raises(ByteIdentityError, match=r"not a PDB 2.00 file"):
        read_type_server(b"\0" * 2048)
    truncated = _pdb([_array(T_RCHAR, 16)])
    with pytest.raises(ByteIdentityError, match=r"file size does not match"):
        read_type_server(truncated[:-1])


def test_an_object_compiled_with_z7_carries_its_own_types() -> None:
    donor = CoffObject(
        _coff(REP_D, REP_LOCALS, types=_object_types(REP_TYPES), locals_words=7, params=1)
    )
    objects = donor_frame_objects(
        donor, donor.function_section(TARGET_SYMBOL), None, base=-28, params_end=8, context="x"
    )
    assert [item.pin() for item in objects.objects] == [[-16, 16], [4, 4]]


def test_locals_that_overlap_merge_and_locals_that_touch_do_not() -> None:
    merged = merge_frame_objects(
        (
            FrameLocal("timer", -196, 4, T_INT4),
            FrameLocal("oldCamera", -196, 4, T_32PVOID),
            FrameLocal("i", -200, 4, T_INT4),
            FrameLocal("pair", -208, 8, T_REAL64),
            FrameLocal("low", -204, 2, 0x11),
        )
    )
    assert [(item.start, item.size, item.names) for item in merged.objects] == [
        (-208, 8, ("pair", "low")),
        (-200, 4, ("i",)),
        (-196, 4, ("oldCamera", "timer")),
    ]
    # A pointer at a boundary may point into the object starting there or be
    # one past the end of the object before it: both escape.
    assert [item.start for item in merged.pointees(-200)] == [-200, -208]
    assert merged.pointees(-210) == ()


def _extents(
    local_records: list[tuple[str, int, int]],
    types: list[bytes] | None = REP_TYPES,
    *,
    codeview4: bool = False,
) -> FrameObjects:
    """The frame objects of the fixture's frame (7 local words, 1 parameter) with these records."""
    donor = CoffObject(
        _coff(
            REP_D,
            local_records,
            types=_type_server_stream(),
            locals_words=7,
            params=1,
            codeview4=codeview4,
        )
    )
    return donor_frame_objects(
        donor,
        donor.function_section(TARGET_SYMBOL),
        None if types is None else _pdb(types),
        base=-28,
        params_end=8,
        context="x",
    )


def test_a_local_outside_the_fpo_frame_is_refused() -> None:
    with pytest.raises(ByteIdentityError, match=r"the parameter 'bx' .* outside the parameter"):
        _extents([("bx", 12, T_INT4)])
    with pytest.raises(
        ByteIdentityError,
        match=r"'bx' \(ESP0\+12, .*\), homed in a parameter's word at ESP0\+8, of 4 bytes lies "
        r"outside the parameter words \[ESP0\+4, ESP0\+8\)",
    ):
        _extents([("n", 4, T_INT4), ("bx", 12, T_INT4)])
    with pytest.raises(ByteIdentityError, match=r"'t' .* lies outside the locals block"):
        _extents([("n", 4, T_INT4), ("t", -32, T_INT4)])


def test_a_record_after_the_parameters_at_a_positive_offset_is_homed_4_below_it() -> None:
    # `void f(int a, int b)` (E = 12): `x`'s record says ESP0+8, but MSVC 5.0
    # keeps a local homed in a parameter's word 4 bytes below its record, in
    # `a`'s word; `y` (ESP0+12, past the parameters) shares `b`'s word.  Each
    # merges with its parameter.
    types = [_array(T_RCHAR, 16), _arglist([T_INT4, T_INT4]), _procedure(0x1001, 2)]
    donor = CoffObject(
        _coff(
            REP_D,
            [("a", 4, T_INT4), ("b", 8, T_INT4), ("x", 8, T_INT4), ("y", 12, T_INT4)],
            types=_type_server_stream(),
            locals_words=7,
            params=2,
        )
    )
    local_records, used = frame_locals(
        donor,
        donor.function_section(TARGET_SYMBOL),
        _pdb(types),
        base=-28,
        params_end=12,
        context="x",
    )
    assert [(item.name, item.start) for item in local_records] == [
        ("a", 4),
        ("b", 8),
        ("x", 4),
        ("y", 8),
    ]
    assert len(used) == 2  # the procedure and its argument list
    objects = merge_frame_objects(local_records, used)
    assert [(item.pin(), item.names) for item in objects.objects] == [
        ([4, 4], ("a", "x")),
        ([8, 4], ("b", "y")),
    ]


def _types_with(arguments: bytes, procedure: bytes) -> list[bytes]:
    return [_array(T_RCHAR, 16), arguments, procedure]


def test_the_parameters_come_from_the_procedure_type() -> None:
    # A trailing T_NOTYPE is `...`: `void f(int, ...)` has one parameter record,
    # so `i` (ESP0+8) is homed in n's word.
    varargs = _types_with(_arglist([T_INT4, 0]), _procedure(0x1001, 2))
    objects = _extents([("n", 4, T_INT4), ("i", 8, T_INT4)], varargs)
    assert [(item.pin(), item.names) for item in objects.objects] == [([4, 4], ("i", "n"))]
    with pytest.raises(ByteIdentityError, match=r"has `...` before its last entry"):
        _extents([("n", 4, T_INT4)], _types_with(_arglist([0, T_INT4]), _procedure(0x1001, 2)))
    with pytest.raises(ByteIdentityError, match=r"has 1 entries in 12 bytes, but the procedure"):
        _extents([("n", 4, T_INT4)], _types_with(_arglist([T_INT4]), _procedure(0x1001, 2)))
    with pytest.raises(ByteIdentityError, match=r"is leaf 0x1009, not LF_PROCEDURE"):
        _extents(
            [("n", 4, T_INT4)],
            _types_with(_arglist([T_INT4]), _procedure(0x1001, 1, leaf=0x1009)),
        )
    with pytest.raises(ByteIdentityError, match=r"is not an LF_ARGLIST"):
        _extents([("n", 4, T_INT4)], _types_with(_array(T_RCHAR, 4), _procedure(0x1001, 1)))
    with pytest.raises(ByteIdentityError, match=r"1 parameters are not its first location"):
        _extents([("{", 0, 0), ("n", 4, T_INT4), ("}", 0, 0)])
    with pytest.raises(ByteIdentityError, match=r"CodeView 4's, whose parameter records"):
        _extents([("n", 4, T_INT4)], codeview4=True)
    with pytest.raises(
        ByteIdentityError,
        match=r"a record at a positive offset is a parameter or a local homed in a parameter's "
        r"word, which only the procedure's type tells apart, and the types are unknown: .* not "
        r"supplied",
    ):
        _extents([("n", 4, T_INT4)], None)
    # Without a record at a positive offset no type is read.
    assert [item.pin() for item in _extents([("t", -4, T_INT4)], None).objects] == [[-4, 4]]


FIXTURES = Path(__file__).parent / "fixtures" / "frame_objects"


def test_a_real_compile_s_local_homed_in_a_dead_parameter_s_word() -> None:
    # tests/fixtures/frame_objects/homed.c compiled by MSVC 5.0 (cl /nologo /TC
    # /ML /Zi /O2 /Ob1 /FAs /Fahomed.asm /Fohomed.obj /Fdhomed.obj.pdb), the
    # record shape of lrr's tooltip_draw.  After `down`'s last read the loop
    # keeps `i` in down's word, ESP0+12: homed.asm has `_down$ = 16` and
    # `_i$ = 16`, and `mov DWORD PTR _i$[esp+32], ecx` (`mov [esp+0x30], ecx`
    # at 0x2f, ESP at ESP0-36) stores ESP0+12.  The S_BPREL32 records say
    # down 12 and i 16.
    data = (FIXTURES / "homed.obj").read_bytes()
    server = (FIXTURES / "homed.obj.pdb").read_bytes()
    donor = CoffObject(data)
    primary = donor.function_section("_homed_draw")
    body = bytes(coff_body(donor, primary))
    stream = bytes(coff_body(donor, _comdat_child(donor, primary, ".debug$S")))
    recorded = {
        item["name"]: struct.unpack_from("<i", stream, item["offset"] + 4)[0]
        for item in parse_codeview_symbol_stream(stream, "x")
        if item["type"] == 0x1006
    }
    assert recorded == {"row": 4, "across": 8, "down": 12, "pos": -24, "i": 16}
    assert body[0x2F:0x33] == bytes.fromhex("894c2430")
    fpo = parse_fpo_data(
        bytes(coff_body(donor, _comdat_child(donor, primary, ".debug$F"))),
        expected_proc_size=primary["raw_size"],
        body=body,
    )
    base, params_end = -4 * fpo["cdwLocals"], 4 + 4 * fpo["cdwParams"]
    assert (base, params_end, fpo["cbFrame"]) == (-24, 16, 0)
    local_records, _used = frame_locals(
        donor, primary, server, base=base, params_end=params_end, context="x"
    )
    assert {item.name: (item.start, item.size) for item in local_records} == {
        "row": (4, 4),
        "across": (8, 4),
        "down": (12, 4),
        "pos": (-24, 8),
        "i": (12, 4),
    }
    objects = donor_frame_objects(
        donor, primary, server, base=base, params_end=params_end, context="x"
    )
    assert [(item.pin(), item.names) for item in objects.objects] == [
        ([-24, 8], ("pos",)),
        ([4, 4], ("row",)),
        ([8, 4], ("across",)),
        ([12, 4], ("down", "i")),
    ]
    with pytest.raises(ByteIdentityError, match=r"types are unknown: .* not supplied"):
        donor_frame_objects(donor, primary, None, base=base, params_end=params_end, context="x")


def test_a_user_type_without_its_type_server_has_no_size() -> None:
    with pytest.raises(ByteIdentityError, match=r"'buf' .* whose size is unknown: .* not supplied"):
        _extents([("buf", -16, 0x1000)], None)


# --- 2. proofs ---------------------------------------------------------------------------

OBJECTS = ObjectModel({}, 8)


def _objects(*local_records: tuple[str, int, int]) -> FrameObjects:
    return merge_frame_objects(
        tuple(FrameLocal(name, at, size, 0) for name, at, size in local_records)
    )


def _prove(
    donor: bytes,
    image: bytes,
    relocations: dict[int, Any],
    image_relocations: dict[int, Any],
    frame: FrameFacts,
    frame_objects: FrameObjects | None,
) -> Any:
    return prove_function(
        donor,
        relocations,
        image,
        image_relocations,
        {},
        "fixture",
        private_frame=frame,
        objects=OBJECTS,
        frame_objects=frame_objects,
    )


# 0: sub esp,0x1c / 3: push edi / 4: mov ecx,[esp+0x24] / 8: mov [esp+8],ecx
# 12: lea edi,[esp+0x10] / 16: xor eax,eax / 18: rep stosb / 20: mov eax,[esp+8]
# 24: pop edi / 25: add esp,0x1c / 28: ret: memset(buf, 0, n) of a char buf[16] at
# ESP0-16 with n kept in the slot ESP0-24.
REP_D = _code("83ec1c 57 8b4c2424 894c2408 8d7c2410 33c0 f3aa 8b442408 5f 83c41c c3")
# ... with n kept in the slot ESP0-28 instead: 8: mov [esp+4],ecx / 20: mov eax,[esp+4]
REP_P = _code("83ec1c 57 8b4c2424 894c2404 8d7c2410 33c0 f3aa 8b442404 5f 83c41c c3")
REP_FRAME = FrameFacts(True, base=-28, params_end=8)
# buf is char[16] (type 0x1000 in the type server); n the int parameter.  The
# slots that hold n's copy are the compiler's, with no record.
REP_LOCALS = [("n", 4, T_INT4), ("buf", -16, 0x1000)]


def test_a_slot_swap_beside_an_escaping_array_is_proved_under_a14() -> None:
    # The block move's pointer is a stack address, so the earlier passes use
    # the shared frame, where the block event names the store log and the two
    # versions' logs differ (n's copy at ESP0-24 and at ESP0-28).
    with pytest.raises(ByteIdentityError, match=r"block string moves"):
        _prove(REP_D, REP_P, {}, {}, REP_FRAME, None)
    proof = _prove(REP_D, REP_P, {}, {}, REP_FRAME, _objects(("buf", -16, 16), ("n", 4, 4)))
    summary = proof_summary(proof)
    assert summary["frame"] == "private"
    assert summary["frame_objects"] == [[-16, 16]]  # only the object whose address escapes
    assert summary["assumptions"] == ["a14"]


# 0: sub esp,0x10 / 3: mov ecx,[esp+0x14] / 7: mov [esp+8],ecx / 11: mov dword [esp+0xc],0
# 19: mov [esp+4],ecx / 23: lea eax,[esp+8] / 27: push eax / 28: call _g / 33: add esp,4
# 36: mov eax,[esp+4] / 40: add esp,0x10 / 43: ret: s = {p, 0}; g(&s); return p, with
# struct { int a, b; } s at ESP0-8 and p's copy in the slot ESP0-12.
STRUCT_D = _code(
    "83ec10 8b4c2414 894c2408 c744240c00000000 894c2404 8d442408 50 e800000000 83c404 "
    "8b442404 83c410 c3"
)
# The fields stored in the other order and p's copy in ESP0-16: 7: mov dword [esp+0xc],0
# 15: mov [esp+8],ecx / 19: mov [esp],ecx / 22: lea eax,[esp+8] / 26: push eax
# 27: call _g / 32: add esp,4 / 35: mov eax,[esp] / 38: add esp,0x10 / 41: ret
STRUCT_P = _code(
    "83ec10 8b4c2414 c744240c00000000 894c2408 890c24 8d442408 50 e800000000 83c404 "
    "8b0424 83c410 c3"
)
# 19: mov [esp+6],ecx / 36: mov eax,[esp+6]: p's copy in [ESP0-10, ESP0-6), two bytes of
# which the donor's s holds: the replacement's object is not the donor's extent.
STRUCT_P_STRADDLE = _code(
    "83ec10 8b4c2414 c744240c00000000 894c2408 894c2406 8d442408 50 e800000000 83c404 "
    "8b442406 83c410 c3"
)
STRUCT_FRAME = FrameFacts(True, base=-16, params_end=8)
STRUCT_OBJECTS = (("s", -8, 8), ("p", 4, 4))


def test_a_slot_swap_beside_an_escaping_structure_is_proved_under_a14() -> None:
    with pytest.raises(ByteIdentityError, match=r"make different calls"):
        _prove(STRUCT_D, STRUCT_P, {29: ("rel32", "_g")}, {28: ("rel32", "_g")}, STRUCT_FRAME, None)
    proof = _prove(
        STRUCT_D,
        STRUCT_P,
        {29: ("rel32", "_g")},
        {28: ("rel32", "_g")},
        STRUCT_FRAME,
        _objects(*STRUCT_OBJECTS),
    )
    assert proof_summary(proof)["frame_objects"] == [[-8, 8]]


def test_an_extent_the_replacement_does_not_keep_is_refused() -> None:
    # The replacement's write of p's copy straddles s's start: its two bytes
    # inside s are memory (the access is split into its runs), so s holds
    # other bytes than the donor's when g reads it.
    with pytest.raises(ByteIdentityError, match=r"make different calls"):
        _prove(
            STRUCT_D,
            STRUCT_P_STRADDLE,
            {29: ("rel32", "_g")},
            {29: ("rel32", "_g")},
            STRUCT_FRAME,
            _objects(*STRUCT_OBJECTS),
        )


def test_a_neighbour_one_past_whose_end_a_pointer_may_lie_escapes_too() -> None:
    # Declared, p's copy at ESP0-12 ends where s starts: &s may be one past
    # its end, so it is memory as well, and the versions write it differently.
    with pytest.raises(ByteIdentityError, match=r"leave different memory|make different calls"):
        _prove(
            STRUCT_D,
            STRUCT_P,
            {29: ("rel32", "_g")},
            {28: ("rel32", "_g")},
            STRUCT_FRAME,
            _objects(*STRUCT_OBJECTS, ("copy", -12, 4)),
        )


# 23: lea eax,[esp+8] / 27: mov dword [eax+8],0 / 34: push eax / 35: call _g ...: a store
# eight bytes into the eight-byte s.
OUTSIDE = _code(
    "83ec10 8b4c2414 894c2408 c744240c00000000 894c2404 8d442408 c7400800000000 50 "
    "e800000000 83c404 8b442404 83c410 c3"
)
# 0: sub esp,0x10 / 3: lea eax,[esp+0x18] / 7: push eax / 8: call _g / 13: add esp,4
# 16: add esp,0x10 / 19: ret: a pointer just past the last parameter (va_start's).
VA_START = _code("83ec10 8d442418 50 e800000000 83c404 83c410 c3")
# 3: lea eax,[esp+4]: the address of the compiler's slot ESP0-12, no local's.
UNDECLARED = _code("83ec10 8d442404 50 e800000000 83c404 83c410 c3")
# 3: mov ecx,[esp+0x14] / 7: mov eax,[esp+ecx*4+8] / 11: add esp,0x10 / 14: ret
INDEXED = _code("83ec10 8b4c2414 8b448c08 83c410 c3")


def test_an_access_outside_its_object_is_refused() -> None:
    relocations = {36: ("rel32", "_g")}
    with pytest.raises(ByteIdentityError, match=r"access at offset 8 .* leaves it"):
        _prove(OUTSIDE, OUTSIDE, relocations, relocations, STRUCT_FRAME, _objects(*STRUCT_OBJECTS))


def test_a_pointer_past_the_last_parameter_is_refused() -> None:
    relocations = {9: ("rel32", "_g")}
    with pytest.raises(
        ByteIdentityError, match=r"pointer at offset 4 of the frame object .* stored"
    ):
        _prove(
            VA_START, VA_START, relocations, relocations, STRUCT_FRAME, _objects(*STRUCT_OBJECTS)
        )


def test_a_stack_address_in_no_declared_local_is_refused() -> None:
    relocations = {9: ("rel32", "_g")}
    with pytest.raises(ByteIdentityError, match=r"ESP0-12 lies in no local"):
        _prove(
            UNDECLARED,
            UNDECLARED,
            relocations,
            relocations,
            STRUCT_FRAME,
            _objects(*STRUCT_OBJECTS),
        )


def test_a_stack_access_at_a_variable_offset_is_refused() -> None:
    with pytest.raises(ByteIdentityError, match=r"variable offset from ESP, which a14"):
        _prove(INDEXED, INDEXED, {}, {}, STRUCT_FRAME, _objects(*STRUCT_OBJECTS))


# 0: sub esp,0x10 / 3: mov eax,[esp+0x14] / 7: mov [esp+4],eax / 11: sub esp,8
# 14: mov ecx,esp / 16: mov [ecx],eax / 18: mov [ecx+4],eax / 21: call _g / 26: add esp,8
# 29: mov eax,[esp+4] / 33: add esp,0x10 / 36: ret: g(s) of a structure argument {p, p}
# built through a copy of ESP, as MSVC 5.0 passes tooltip_draw_box its colours, with p's
# copy in the slot ESP0-12.  ECX holds ESP0-24, in the outgoing argument block, which no
# local declares.
ARGUMENT_D = _code(
    "83ec10 8b442414 89442404 83ec08 8bcc 8901 894104 e800000000 83c408 8b442404 83c410 c3"
)
# ... built through EDX, with p's copy in ESP0-16: 7: mov [esp+0],eax / 14: mov edx,esp
# 16: mov [edx],eax / 18: mov [edx+4],eax / 29: mov eax,[esp+0]
ARGUMENT_P = _code(
    "83ec10 8b442414 89442400 83ec08 8bd4 8902 894204 e800000000 83c408 8b442400 83c410 c3"
)
# 0: sub esp,0x10 / 3: mov eax,[esp+0x14] / 7: sub esp,8 / 10: mov ecx,esp
# 12: mov [ecx],eax / 14: mov [ecx+4],eax / 17: push ecx / 18: call _g / 23: add esp,0x1c
# 26: ret: the pointer itself pushed as a further argument.
ARGUMENT_STORED = _code("83ec10 8b442414 83ec08 8bcc 8901 894104 51 e800000000 83c41c c3")


def test_a_structure_argument_built_through_a_copy_of_esp_is_related() -> None:
    # In the shared frame the call reads p's copies, which differ.  The
    # frame-objects pass keeps ECX and EDX as ESP0-24: every access through
    # them is a private slot of the argument window, and no callee receives
    # them (a call's event names no register, and _g takes none).
    relocations = {22: ("rel32", "_g")}
    with pytest.raises(ByteIdentityError, match=r"make different calls"):
        _prove(ARGUMENT_D, ARGUMENT_P, relocations, relocations, STRUCT_FRAME, None)
    proof = _prove(
        ARGUMENT_D, ARGUMENT_P, relocations, relocations, STRUCT_FRAME, _objects(*STRUCT_OBJECTS)
    )
    summary = proof_summary(proof)
    assert summary["frame"] == "private" and summary["frame_objects"] == []


def test_a_stored_stack_address_in_no_declared_local_is_refused() -> None:
    # Held in a register it is admitted; pushed, a callee could reach past it.
    relocations = {19: ("rel32", "_g")}
    with pytest.raises(ByteIdentityError, match=r"ESP0-24 lies in no local"):
        _prove(
            ARGUMENT_STORED,
            ARGUMENT_STORED,
            relocations,
            relocations,
            STRUCT_FRAME,
            _objects(*STRUCT_OBJECTS),
        )


# --- 3. the record -----------------------------------------------------------------------


def _rep_coff(body: bytes) -> bytes:
    return _coff(body, REP_LOCALS, types=_type_server_stream(), locals_words=7, params=1)


def _author(type_server: bytes | None) -> Any:
    seed = _rep_coff(REP_D)
    return seed, build_function_validation_rewriting(
        donor=_extern_donor(),
        target_id="program",
        translation_unit_id="tu.fixture",
        build_target="program",
        symbol=TARGET_SYMBOL,
        seed_object=seed,
        donor_object=seed,
        reference_object=_rep_coff(REP_P),
        donor_type_server=type_server,
    )


def test_a_frame_objects_record_pins_a14_and_dispatches_with_the_type_server() -> None:
    server = _pdb(REP_TYPES)
    seed, authored = _author(server)
    proof = authored.function.receipt.expected_values["function_validation.expected_proof"]
    assert proof["assumptions"] == ["a14"] and proof["frame_objects"] == [[-16, 16]]
    assert proof["equivalences"] is True
    composed = CoffObject(authored.candidate_object)
    assert bytes(coff_body(composed, composed.function_section(TARGET_SYMBOL))) == REP_P
    constraints = merge_candidate_constraints(
        authored.function.intervention, authored.function.receipt
    ).materialize()

    def dispatch(type_server: bytes | None) -> Any:
        return ClassicFamilyDispatcher().dispatch(
            authored.function.intervention,
            ClassicDispatchMaterials(
                seed_object=seed,
                donor_object=seed,
                candidate_constraints=constraints,
                donor_type_server=type_server,
            ),
        )

    candidate = dispatch(server)
    assert candidate.output == authored.candidate_object
    names = [item["name"] for item in candidate.semantic_input_statement["binary_inputs"]]
    assert f"dependency_types:{authored.function.intervention.dependencies[0]}" in names
    with pytest.raises((ByteIdentityError, ClassicProjectError), match=r"not supplied"):
        dispatch(None)


def test_without_the_type_server_the_frame_objects_pass_cannot_run() -> None:
    with pytest.raises(
        DiscoveryAuthoringError,
        match=r"block string moves; the frame-objects pass \(a14\) cannot run: .* not supplied",
    ):
        _author(None)


# --- 4. grind and the build: the type server the donor's own compile wrote ----------------


def _grind_rewriting(
    monkeypatch: pytest.MonkeyPatch, type_server: bytes | None, debug_sibling: Any = None
) -> Any:
    """Grind's donor rewriting of the fixture, with the probe's type server or debug sibling."""
    import reprobit.discovery_grind as grind
    from reprobit.discovery_contracts import DeclarationFamily

    def refuse(**_kwargs: object) -> object:
        raise DiscoveryAuthoringError("block string moves")

    monkeypatch.setattr(grind, "_extern_run", lambda _state: SimpleNamespace(**_RUN))
    monkeypatch.setattr(grind, "_header_placement", lambda _context: "after-includes")
    monkeypatch.setattr(grind, "build_extern_run_donor", lambda **_kwargs: _extern_donor())
    monkeypatch.setattr(grind, "build_donor_schedule_rewriting", refuse)
    monkeypatch.setattr(grind, "build_region_resize_rewriting", refuse)
    seed = _rep_coff(REP_D)
    context = SimpleNamespace(
        unit=SimpleNamespace(target_id="program", id="tu.fixture", build_target="program"),
        symbol=TARGET_SYMBOL,
    )
    return seed, grind._state_rewriting(
        cast(Any, SimpleNamespace(family=DeclarationFamily.EXTERN_RUN_PAIR)),
        cast(Any, context),
        seed_object=seed,
        donor_object=seed,
        reference_object=_rep_coff(REP_P),
        donor_type_server=type_server,
        donor_debug_sibling=debug_sibling,
    )


_RUN = {
    "header_prefix": "ReproBitPad",
    "header_count": 1,
    "seat_prefix": "ReproBitPadSeat",
    "seat_count": 0,
    "width": 3,
}


def _donor_material(
    donor: Any, donor_object: bytes, type_server: bytes | None, debug_sibling: Any = None
) -> Any:
    """The build's fresh donor material: the object and the PDB its compile wrote
    (or, without /Zi, its debug sibling)."""
    from reprobit.classic.semantic_contracts import (
        _CLASSIC_SEMANTIC_ISSUER,
        _ClassicDonorSemanticMaterial,
    )

    return _ClassicDonorSemanticMaterial(
        intervention=donor.intervention,
        donor_object=donor_object,
        source_inputs={},
        compiler_statement={"schema": 1},
        _issuer=_CLASSIC_SEMANTIC_ISSUER,
        donor_type_server=type_server,
        donor_debug_sibling=debug_sibling,
    )


def _compose(
    seed: bytes, authored: Any, type_server: bytes | None, debug_sibling: Any = None
) -> Any:
    """Compose the unit as the build does, from the donor compile's own outputs."""
    from reprobit.classic_orchestration import (
        ClassicPreparedDonor,
        ClassicPreparedUnit,
        compose_classic_unit,
    )
    from reprobit.schema import ClassicTranslationUnitPlan

    function = authored.function.intervention
    unit = ClassicPreparedUnit(
        ClassicTranslationUnitPlan(
            id="tu.fixture",
            target_id="program",
            build_target="program",
            source="src/unit.c",
            source_digest=Digest.from_bytes(b"source"),
        ),
        (
            ClassicPreparedDonor(
                authored.donor.intervention,
                cast(Any, SimpleNamespace(logical_outputs={}, carrier_identifiers=frozenset())),
            ),
        ),
        (function,),
        (),
        (function,),
        (authored.function.receipt,),
    )
    return compose_classic_unit(
        unit,
        seed_object=seed,
        donor_materials={
            authored.donor.intervention.id: _donor_material(
                authored.donor, seed, type_server, debug_sibling
            )
        },
        seed_source=b"source",
    )


def test_grind_authors_an_a14_record_from_its_donor_compile_s_pdb_and_the_build_composes_it(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    server = _pdb(REP_TYPES)
    seed, authored = _grind_rewriting(monkeypatch, server)
    proof = authored.function.receipt.expected_values["function_validation.expected_proof"]
    assert proof["assumptions"] == ["a14"] and proof["frame_objects"] == [[-16, 16]]

    composed = _compose(seed, authored, server)
    assert not composed.incomplete
    assert composed.output == authored.candidate_object
    output = CoffObject(composed.output)
    assert bytes(coff_body(output, output.function_section(TARGET_SYMBOL))) == REP_P
    # The consumer names the PDB the donor's compile wrote, by digest: the
    # evidence binds it to that compile's produced type-server artifact.
    (witness,) = composed.witnesses
    inputs = {
        item["name"]: item["digest"]
        for item in witness.semantic_proof.input_statement["binary_inputs"]
    }
    assert inputs[f"dependency_types:{authored.donor.intervention.id}"] == (
        Digest.from_bytes(server).model_dump(mode="json")
    )


def test_grind_without_its_donor_compile_s_pdb_cannot_run_a14(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    with pytest.raises(
        DiscoveryAuthoringError,
        match=r"function validation: .* the frame-objects pass \(a14\) cannot run: .* "
        r"not supplied",
    ):
        _grind_rewriting(monkeypatch, None)


def test_grind_refuses_a_pdb_another_compile_wrote(monkeypatch: pytest.MonkeyPatch) -> None:
    other = _pdb(REP_TYPES, signature=SIGNATURE + 1)
    with pytest.raises(
        DiscoveryAuthoringError,
        match=r"supplied type server has signature 0x6afe5731 and age 42, but the object "
        r"names 0x6afe5730 and age 42",
    ):
        _grind_rewriting(monkeypatch, other)


def test_the_build_refuses_an_a14_record_without_its_pdb_or_with_another_compile_s(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    server = _pdb(REP_TYPES)
    seed, authored = _grind_rewriting(monkeypatch, server)
    with pytest.raises((ByteIdentityError, ClassicProjectError), match=r"not supplied"):
        _compose(seed, authored, None)
    older = _pdb(REP_TYPES, age=AGE - 1)
    with pytest.raises(
        (ByteIdentityError, ClassicProjectError),
        match=r"supplied type server has signature 0x6afe5730 and age 41",
    ):
        _compose(seed, authored, older)
