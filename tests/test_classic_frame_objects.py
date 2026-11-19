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
   overlapping locals merged.
2. Proofs: swapped slots beside an escaping array or structure; refusals for
   an extent the replacement does not keep, an unknown size, an access or a
   stored pointer outside its object, a stack address in no local, and a
   stack access at a variable offset.
3. The record: authored and dispatched with the donor's type server, pinning
   a14 and its escaping objects.
4. Grind and the build: grind authors the record with the PDB its donor
   compile wrote, and the build composes it from its own donor compile's PDB;
   a missing PDB, or one another compile wrote, refuses.
"""

from __future__ import annotations

import re
import struct
from types import SimpleNamespace
from typing import Any, cast

import pytest
from test_classic_function_validation import _extern_donor
from test_classic_register_bijection_reencoding_full import TARGET_SYMBOL, make_coff

from reprobit.binary import ByteIdentityError
from reprobit.classic.frame_objects import (
    FrameLocal,
    FrameObjects,
    TypeSizes,
    donor_frame_objects,
    merge_frame_objects,
    object_type_records,
    primitive_size,
    read_type_server,
)
from reprobit.classic.function_validation import FrameFacts, proof_summary, prove_function
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


def _debug_s(body_length: int, local_records: list[tuple[str, int, int]]) -> bytes:
    """S_GPROC32, one S_BPREL32_ST per (name, offset, type), S_END."""
    records = bytearray()

    def record(kind: int, payload: bytes) -> None:
        records.extend(struct.pack("<HH", len(payload) + 2, kind))
        records.extend(payload)

    proc = bytearray(33)
    struct.pack_into("<III", proc, 12, body_length, 0, body_length - 1)
    record(0x0205, bytes(proc) + _name("_fixture"))
    for name, offset, type_index in local_records:
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
) -> bytes:
    """A donor (or reference) object with an FPO record of the given frame."""
    data = bytearray(
        make_coff(
            body=body,
            relocations=(),
            lines=((0, 10),),
            debug_stream=_debug_s(len(body), local_records),
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
    records, source = object_type_records(donor, _pdb([_array(T_RCHAR, 16)]), "x")
    assert source == "type server" and records is not None and len(records) == 1
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
        _coff(
            REP_D, REP_LOCALS, types=_object_types([_array(T_RCHAR, 16)]), locals_words=7, params=1
        )
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


def test_a_local_outside_the_fpo_frame_is_refused() -> None:
    donor = CoffObject(
        _coff(REP_D, [("bx", 12, T_INT4)], types=_type_server_stream(), locals_words=7, params=1)
    )
    with pytest.raises(ByteIdentityError, match=r"'bx' .* lies outside the locals block"):
        donor_frame_objects(
            donor, donor.function_section(TARGET_SYMBOL), None, base=-28, params_end=8, context="x"
        )


def test_a_user_type_without_its_type_server_has_no_size() -> None:
    donor = CoffObject(
        _coff(REP_D, REP_LOCALS, types=_type_server_stream(), locals_words=7, params=1)
    )
    with pytest.raises(ByteIdentityError, match=r"'buf' .* whose size is unknown: .* not supplied"):
        donor_frame_objects(
            donor, donor.function_section(TARGET_SYMBOL), None, base=-28, params_end=8, context="x"
        )


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
REP_LOCALS = [("buf", -16, 0x1000), ("n", 4, T_INT4)]


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
    with pytest.raises(ByteIdentityError, match=r"straddles the escaping frame object"):
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
    server = _pdb([_array(T_RCHAR, 16)])
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


def _grind_rewriting(monkeypatch: pytest.MonkeyPatch, type_server: bytes | None) -> Any:
    """Grind's donor rewriting of the fixture, with the probe's type server."""
    import reprobit.discovery_grind as grind
    from reprobit.discovery_contracts import DeclarationFamily

    def refuse(**_kwargs: object) -> object:
        raise DiscoveryAuthoringError("block string moves")

    monkeypatch.setattr(grind, "_extern_run", lambda _state: SimpleNamespace(**_RUN))
    monkeypatch.setattr(grind, "_header_placement", lambda _context: "after-includes")
    monkeypatch.setattr(grind, "build_extern_run_donor", lambda **_kwargs: _extern_donor())
    monkeypatch.setattr(grind, "build_donor_schedule_rewriting", refuse)
    monkeypatch.setattr(grind, "build_region_resize_rewriting", refuse)

    def validation(**kwargs: Any) -> object:
        # Grind reports the reorder's reason; keep the proof's own refusal.
        try:
            return build_function_validation_rewriting(**kwargs)
        except DiscoveryAuthoringError as error:
            _REFUSALS.append(str(error))
            raise

    _REFUSALS.clear()
    monkeypatch.setattr(grind, "build_function_validation_rewriting", validation)
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
    )


_REFUSALS: list[str] = []
_RUN = {
    "header_prefix": "ReproBitPad",
    "header_count": 1,
    "seat_prefix": "ReproBitPadSeat",
    "seat_count": 0,
    "width": 3,
}


def _donor_material(donor: Any, donor_object: bytes, type_server: bytes | None) -> Any:
    """The build's fresh donor material: the object and the PDB its compile wrote."""
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
    )


def _compose(seed: bytes, authored: Any, type_server: bytes | None) -> Any:
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
            authored.donor.intervention.id: _donor_material(authored.donor, seed, type_server)
        },
        seed_source=b"source",
    )


def test_grind_authors_an_a14_record_from_its_donor_compile_s_pdb_and_the_build_composes_it(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    server = _pdb([_array(T_RCHAR, 16)])
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
    with pytest.raises(DiscoveryAuthoringError, match=r"block string moves"):
        _grind_rewriting(monkeypatch, None)
    assert len(_REFUSALS) == 1
    assert re.search(r"the frame-objects pass \(a14\) cannot run: .* not supplied", _REFUSALS[0])


def test_grind_refuses_a_pdb_another_compile_wrote(monkeypatch: pytest.MonkeyPatch) -> None:
    other = _pdb([_array(T_RCHAR, 16)], signature=SIGNATURE + 1)
    with pytest.raises(DiscoveryAuthoringError, match=r"block string moves"):
        _grind_rewriting(monkeypatch, other)
    assert len(_REFUSALS) == 1
    assert (
        "supplied type server has signature 0x6afe5731 and age 42, but the object "
        "names 0x6afe5730 and age 42" in _REFUSALS[0]
    )


def test_the_build_refuses_an_a14_record_without_its_pdb_or_with_another_compile_s(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    server = _pdb([_array(T_RCHAR, 16)])
    seed, authored = _grind_rewriting(monkeypatch, server)
    with pytest.raises((ByteIdentityError, ClassicProjectError), match=r"not supplied"):
        _compose(seed, authored, None)
    older = _pdb([_array(T_RCHAR, 16)], age=AGE - 1)
    with pytest.raises(
        (ByteIdentityError, ClassicProjectError),
        match=r"supplied type server has signature 0x6afe5730 and age 41",
    ):
        _compose(seed, authored, older)
