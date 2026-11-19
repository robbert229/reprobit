"""Compiler helpers simulated from an authenticated library, and COM vtable calls as events.

Every helper body here is written for these tests (hand-encoded IA-32, each
listing in the comment above it) and packed into a synthetic COFF archive
that a test-only authority authenticates; no toolchain bytes are used.  The
proofs run through `prove_function` and the region simulator; the pins of a
record through grind's authoring, the producer and the build dispatcher.
"""

from __future__ import annotations

import hashlib
import json
import struct

import pytest
from test_classic_register_bijection_reencoding_full import (
    NIL_SYMBOL,
    TARGET_SYMBOL,
    codeview_stream,
    make_coff,
)

from reprobit.binary import ByteIdentityError
from reprobit.classic.function_validation import FrameFacts, prove_function
from reprobit.classic.region_simulation import (
    HelperCode,
    PathState,
    _Undefined,
    entry_state,
    lin,
    run_helper,
    simulate_region,
)
from reprobit.classic.rewriting_region_resize import region_helper_callees
from reprobit.classic.toolchain_helpers import (
    HELPER_LIBRARY,
    HelperLibraryError,
    authenticate_helper_library,
    compiler_helper,
)
from reprobit.classic_donors import merge_candidate_constraints
from reprobit.classic_project import ClassicDispatchMaterials, ClassicFamilyDispatcher
from reprobit.coff_format import CoffObject, coff_body
from reprobit.discovery_authoring import DiscoveryAuthoringError, build_extern_run_donor
from reprobit.discovery_function_validation import build_function_validation_rewriting
from reprobit.msvc50_authorities import Msvc50FileAuthority
from reprobit.toolchain_helper_library import reviewed_helper_library

UNIT = "tu.fixture"
PROFILE = "test_profile"


def _code(text: str) -> bytes:
    return bytes.fromhex(text.replace(" ", ""))


# --- synthetic helpers (written for these tests) ----------------------------------------

# A truncating float-to-int64 conversion without a frame pointer:
# 0: sub esp,12 / 3: fnstcw [esp+8] / 7: mov ax,[esp+8] / 12: or ah,0x0c
# 15: mov [esp+10],ax / 20: fldcw [esp+10] / 24: fistp qword [esp]
# 27: fldcw [esp+8] / 31: mov eax,[esp] / 34: mov edx,[esp+4] / 38: add esp,12 / 41: ret
TRUNCATE = _code(
    "83ec0c d97c2408 668b442408 80cc0c 668944240a d96c240a df3c24 d96c2408 8b0424 8b542404 "
    "83c40c c3"
)
# The same with a nop before the return (another body, another digest).
TRUNCATE_NOP = TRUNCATE[:-1] + _code("90 c3")
# A page-probing allocator: EAX bytes off the caller's stack.
# 0: push ecx / 1: lea ecx,[esp+8] / 5: cmp eax,0x1000 / 10: jb 27 / 12: sub ecx,0x1000
# 18: sub eax,0x1000 / 23: test [ecx],eax / 25: jmp 5 / 27: sub ecx,eax / 29: test [ecx],eax
# 31: mov eax,esp / 33: mov esp,ecx / 35: mov ecx,[eax] / 37: mov eax,[eax+4] / 40: push eax
# 41: ret
PROBE = _code(
    "51 8d4c2408 3d00100000 720f 81e900100000 2d00100000 8501 ebea 2bc8 8501 8bc4 8be1 8b08 "
    "8b4004 50 c3"
)
# 0: fsin / 2: ret (an x87 instruction outside the closed set)
SINE = _code("d9fe c3")
# 0: sub esp,4 / 3: fnstcw [esp] / 6: mov ax,[esp] / 10: or al,1 / 12: mov [esp+2],ax
# 17: fldcw [esp+2] / 21: fldcw [esp] / 24: add esp,4 / 27: ret (changes a mask bit)
UNMASK = _code("83ec04 d93c24 668b0424 0c01 6689442402 d96c2402 d92c24 83c404 c3")
# 0: sub esp,4 / 3: fnstcw [esp] / 6: mov ax,[esp] / 10: or ah,0x0c / 13: mov [esp+2],ax
# 18: fldcw [esp+2] / 22: add esp,4 / 25: ret (leaves the rounding mode changed)
LEAVE_ROUNDING = _code("83ec04 d93c24 668b0424 80cc0c 6689442402 d96c2402 83c404 c3")
# 0: call rel32 / 5: ret (calls out, through a relocation)
CALLER = _code("e800000000 c3")


def _helper_object(symbol: str, code: bytes, *, calls: str | None = None) -> bytes:
    """One COFF object whose .text defines ``symbol`` at 0 (and relocates a call to ``calls``)."""
    relocations = [(1, 3, 0x14)] if calls is not None else []
    raw_offset = 20 + 40
    relocation_offset = raw_offset + len(code)
    table = b"".join(struct.pack("<IIH", *row) for row in relocations)
    symbol_offset = relocation_offset + len(table)
    strings = bytearray(b"\0\0\0\0")

    def name(text: str) -> bytes:
        raw = text.encode("ascii")
        if len(raw) <= 8:
            return raw.ljust(8, b"\0")
        offset = len(strings)
        strings.extend(raw + b"\0")
        return b"\0\0\0\0" + struct.pack("<I", offset)

    records = [
        name(".text") + struct.pack("<IhHBB", 0, 1, 0, 3, 1),
        struct.pack("<IHHIHBxxx", len(code), len(relocations), 0, 0, 0, 0),
        name(symbol) + struct.pack("<IhHBB", 0, 1, 0x20, 2, 0),
    ]
    if calls is not None:
        records.append(name(calls) + struct.pack("<IhHBB", 0, 0, 0x20, 2, 0))
    struct.pack_into("<I", strings, 0, len(strings))
    header = struct.pack("<HHIIIHH", 0x14C, 1, 0, symbol_offset, len(records), 0, 0)
    section = b".text\0\0\0" + struct.pack(
        "<IIIIIIHHI",
        0,
        0,
        len(code),
        raw_offset,
        relocation_offset if relocations else 0,
        0,
        len(relocations),
        0,
        0x60500020,
    )
    return header + section + code + table + b"".join(records) + bytes(strings)


def _archive(members: list[tuple[str, str, bytes]]) -> bytes:
    """A COFF archive: a first linker member indexing each (symbol, member name, object)."""

    def member(name: str, body: bytes) -> bytes:
        head = (
            name.encode("ascii").ljust(16)
            + b"0".ljust(12)
            + b"0".ljust(6)
            + b"0".ljust(6)
            + b"644".ljust(8)
            + str(len(body)).encode("ascii").ljust(10)
            + b"`\n"
        )
        return head + body + (b"\n" if len(body) & 1 else b"")

    names = b"".join(symbol.encode("ascii") + b"\0" for symbol, _name, _data in members)
    linker_size = 4 + 4 * len(members) + len(names)
    offset = 8 + 60 + linker_size + (linker_size & 1)
    offsets = []
    for _symbol, _name, data in members:
        offsets.append(offset)
        offset += 60 + len(data) + (len(data) & 1)
    linker = struct.pack(">I", len(members)) + b"".join(struct.pack(">I", at) for at in offsets)
    payload = b"!<arch>\n" + member("/", linker + names)
    for _symbol, name, data in members:
        payload += member(name + "/", data)
    return payload


def _library(*, truncate: bytes = TRUNCATE):
    data = _archive(
        [
            ("__ftol", "ftol.obj", _helper_object("__ftol", truncate)),
            ("__chkstk", "chkstk.obj", _helper_object("__chkstk", PROBE)),
            ("__sine", "sine.obj", _helper_object("__sine", SINE)),
            ("__unmask", "unmask.obj", _helper_object("__unmask", UNMASK)),
            ("__round", "round.obj", _helper_object("__round", LEAVE_ROUNDING)),
            ("__caller", "caller.obj", _helper_object("__caller", CALLER, calls="_g")),
        ]
    )
    authority = Msvc50FileAuthority(len(data), hashlib.sha256(data).hexdigest())
    return authenticate_helper_library(PROFILE, data, {PROFILE: {HELPER_LIBRARY: authority}})


def _helpers(*symbols: str, truncate: bytes = TRUNCATE) -> dict[str, HelperCode]:
    library = _library(truncate=truncate)
    return {symbol: library.helper(symbol).code for symbol in symbols}


def _prove(donor, image, donor_relocations, image_relocations, *, helpers=None, frame=None):
    return prove_function(
        donor,
        donor_relocations,
        image,
        image_relocations,
        {},
        "fixture",
        private_frame=frame,
        helpers=helpers,
    )


# --- the library -------------------------------------------------------------------------


def test_the_library_resolves_a_helper_through_its_index_and_pins_both_digests() -> None:
    library = _library()
    body = library.helper("__ftol")
    assert body.code.code == TRUNCATE
    assert body.pin() == {
        "symbol": "__ftol",
        "library": HELPER_LIBRARY,
        "library_sha256": library.sha256,
        "member": "ftol.obj",
        "body_sha256": hashlib.sha256(TRUNCATE).hexdigest(),
        "body_length": len(TRUNCATE),
    }


def test_bytes_that_are_not_the_reviewed_library_are_refused() -> None:
    data = _library().data
    with pytest.raises(HelperLibraryError, match="not the reviewed one"):
        reviewed_helper_library("msvc_5_0_rtm", data)
    with pytest.raises(HelperLibraryError, match="no reviewed authority"):
        reviewed_helper_library("msvc_4_2", data)


def test_a_helper_that_calls_out_is_refused() -> None:
    with pytest.raises(HelperLibraryError, match="calls out or touches the environment"):
        _library().helper("__caller")


def test_a_symbol_the_index_does_not_name_is_refused() -> None:
    with pytest.raises(HelperLibraryError, match="names 0 members"):
        _library().helper("__absent")


def test_only_undecorated_double_underscore_callees_are_helpers() -> None:
    assert compiler_helper("__ftol") and compiler_helper("__chkstk")
    assert not compiler_helper("_printf") and not compiler_helper("__imp__Sleep@4")
    assert not compiler_helper("_Sleep@4")


# --- the helper run ----------------------------------------------------------------------


def test_the_probe_allocates_exactly_its_constant_argument() -> None:
    state = entry_state()
    state.regs["eax"] = lin(0x2000)
    run_helper(state, _helpers("__chkstk")["__chkstk"], _Undefined("D"), "fixture")
    assert state.regs["esp"] == lin(-0x2000, [(("reg0", "esp"), 1)])
    assert state.regs["ecx"] == entry_state().regs["ecx"]


def test_a_helper_whose_control_flow_depends_on_an_unknown_value_is_refused() -> None:
    state = entry_state()
    with pytest.raises(ByteIdentityError, match="branches on a value that is not constant"):
        run_helper(state, _helpers("__chkstk")["__chkstk"], _Undefined("D"), "fixture")


def test_the_truncating_conversion_restores_the_control_word() -> None:
    state: PathState = entry_state()
    state.fpu.slots[-1] = ("fld", 32, "x")
    state.fpu.push = 1
    run_helper(state, _helpers("__ftol")["__ftol"], _Undefined("D"), "fixture")
    assert state.fpu.cw is None and state.fpu.push == 0
    assert state.regs["esp"] == entry_state().regs["esp"]


@pytest.mark.parametrize(
    ("symbol", "why"),
    [
        ("__sine", "outside the simulator's closed set"),
        ("__unmask", "may change the exception masks"),
        ("__round", "returns with the x87 control word changed"),
    ],
)
def test_a_helper_outside_the_model_is_refused(symbol: str, why: str) -> None:
    state = entry_state()
    state.fpu.slots[-1] = ("fld", 32, "x")
    state.fpu.push = 1
    with pytest.raises(ByteIdentityError, match=why):
        run_helper(state, _helpers(symbol)[symbol], _Undefined("D"), "fixture")


# --- helpers in a whole-function proof ---------------------------------------------------

# 0: fld dword [esp+4] / 4: call __ftol / 9: mov ecx,eax / 11: ret
FTOL_D = _code("d9442404 e800000000 8bc8 c3")
# 0: fld dword [esp+4] / 4: call __ftol / 9: ret
FTOL_P = _code("d9442404 e800000000 c3")
# ... returning EDX:EAX's high word instead.
FTOL_P_HIGH = _code("d9442404 e800000000 8bc2 c3")
FTOL_RELOCATIONS = {5: ("rel32", "__ftol")}
# 0: mov eax,0x2000 / 5: call __chkstk / 10: mov dword [esp],7 / 17: mov eax,[esp]
# 20: add esp,0x2000 / 26: ret
PROBE_D = _code("b800200000 e800000000 c7042407000000 8b0424 81c400200000 c3")
# ... returning the constant instead of reloading the local.
PROBE_P = _code("b800200000 e800000000 c7042407000000 b807000000 81c400200000 c3")
PROBE_RELOCATIONS = {6: ("rel32", "__chkstk")}
PROBE_FRAME = FrameFacts(True, base=-0x2000, params_end=4)


@pytest.mark.parametrize("frame", [None, FrameFacts(True, base=0, params_end=8)])
def test_a_function_calling_the_conversion_is_proved_with_its_body_simulated(frame) -> None:
    proof = _prove(
        FTOL_D,
        FTOL_P,
        FTOL_RELOCATIONS,
        FTOL_RELOCATIONS,
        helpers=_helpers("__ftol"),
        frame=frame,
    )
    assert proof.returns == 1
    assert proof.frame.private is (frame is not None)


def test_a_different_use_of_the_conversion_is_refused() -> None:
    with pytest.raises(ByteIdentityError, match="eax differs at the return"):
        _prove(FTOL_D, FTOL_P_HIGH, FTOL_RELOCATIONS, FTOL_RELOCATIONS, helpers=_helpers("__ftol"))


def test_without_its_body_a_helper_call_stays_outside_the_closed_set() -> None:
    with pytest.raises(ByteIdentityError, match="does not fix a register-free convention"):
        _prove(FTOL_D, FTOL_P, FTOL_RELOCATIONS, FTOL_RELOCATIONS)


def test_a_large_frame_allocated_by_the_probe_is_a_private_frame() -> None:
    proof = _prove(
        PROBE_D,
        PROBE_P,
        PROBE_RELOCATIONS,
        PROBE_RELOCATIONS,
        helpers=_helpers("__chkstk"),
        frame=PROBE_FRAME,
    )
    assert proof.frame.private and proof.frame.base == -0x2000


def test_a_helper_with_an_unmodelled_instruction_refuses_the_proof() -> None:
    sine = _code("d9442404 e800000000 dd d8 c3")  # fld / call __sine / fstp st0 / ret
    relocations = {5: ("rel32", "__sine")}
    with pytest.raises(ByteIdentityError, match="outside the simulator's closed set"):
        _prove(sine, sine, relocations, relocations, helpers=_helpers("__sine"))


def test_the_region_simulator_runs_a_helper_inline_too() -> None:
    paths = simulate_region(
        FTOL_P, 0, 9, FTOL_RELOCATIONS, "donor", "fixture", helpers=_helpers("__ftol")
    )
    assert len(paths) == 1 and paths[0].x87.push == 0 and not paths[0].events


# --- COM vtable calls --------------------------------------------------------------------

# 0: mov eax,[esp+4] / 4: mov ecx,[eax] / 6: push 5 / 8: push eax / 9: call [ecx+0x10] / 12: ret
VTABLE_D = _code("8b442404 8b08 6a05 50 ff5110 c3")
# The vtable read after the pushes, which a shared frame cannot keep apart from them:
# 0: mov eax,[esp+4] / 4: push 5 / 6: push eax / 7: mov ecx,[eax] / 9: call [ecx+0x10] / 12: ret
VTABLE_D_LATE = _code("8b442404 6a05 50 8b08 ff5110 c3")
# 0: mov edx,[esp+4] / 4: mov eax,[edx] / 6: push 5 / 8: push edx / 9: call [eax+0x10] / 12: ret
VTABLE_P = _code("8b542404 8b02 6a05 52 ff5010 c3")
# ... through the next slot.
VTABLE_P_SLOT = _code("8b542404 8b02 6a05 52 ff5014 c3")
# ... without the second argument (7: push edx / 8: call [eax+0x10] / 11: ret).
VTABLE_P_ARGS = _code("8b542404 8b02 52 ff5010 c3")
# Two calls in a row: only the sum of their pops is fixed by the return.
# 0: mov eax,[esp+4] / 4: push eax / 5: mov ecx,[eax] / 7: call [ecx+0x10]
# 10: mov eax,[esp+4] / 14: push eax / 15: mov ecx,[eax] / 17: call [ecx+0x14] / 20: ret
VTABLE_TWO = _code("8b442404 50 8b08 ff5110 8b442404 50 8b08 ff5114 c3")
# 0: push 5 / 2: call [esp+8] / 6: ret (a function pointer argument, not a vtable slot)
POINTER_CALL = _code("6a05 ff542408 c3")


def test_an_indirect_call_through_the_same_vtable_slot_is_proved() -> None:
    proof = _prove(VTABLE_D, VTABLE_P, {}, {})
    assert proof.returns == 1


def test_in_a_private_frame_the_pushes_do_not_alias_the_vtable_read() -> None:
    frame = FrameFacts(True, base=0, params_end=8)
    proof = _prove(VTABLE_D_LATE, VTABLE_P, {}, {}, frame=frame)
    assert proof.frame.private
    with pytest.raises(ByteIdentityError, match="make different calls"):
        _prove(VTABLE_D_LATE, VTABLE_P, {}, {})


@pytest.mark.parametrize(
    "image", [VTABLE_P_SLOT, VTABLE_P_ARGS], ids=["another slot", "another argument count"]
)
def test_an_indirect_call_that_differs_is_refused(image: bytes) -> None:
    with pytest.raises(ByteIdentityError, match="make different calls"):
        _prove(VTABLE_D, image, {}, {})


def test_an_argument_pop_the_stack_relation_does_not_fix_is_refused() -> None:
    with pytest.raises(ByteIdentityError, match="does not determine the argument pop"):
        _prove(VTABLE_TWO, VTABLE_TWO, {}, {})


def test_an_indirect_call_that_is_not_through_a_vtable_is_refused() -> None:
    with pytest.raises(ByteIdentityError, match="not a slot of a vtable"):
        _prove(POINTER_CALL, POINTER_CALL, {}, {})


def test_the_region_simulator_still_refuses_an_indirect_call() -> None:
    with pytest.raises(ByteIdentityError, match="indirect call or jump"):
        simulate_region(VTABLE_D, 0, 12, {}, "donor", "fixture")


def _region(start: int, end: int) -> dict[str, object]:
    return {
        "region_start": start,
        "region_end": end,
        "replacement_instructions": ["90"],
        "replacement_relocations": [],
    }


def test_a_region_pins_only_the_helpers_it_calls() -> None:
    rows = [
        {"offset": 5, "type": 0x0014, "target": "__ftol"},
        {"offset": 40, "type": 0x0014, "target": "__chkstk"},
        {"offset": 60, "type": 0x0014, "target": "_printf"},
    ]
    library = _library()
    helpers, pins = region_helper_callees([_region(0, 12)], rows, library, "fixture")
    assert set(helpers) == {"__ftol"} and pins == [library.helper("__ftol").pin()]
    assert region_helper_callees([_region(20, 30)], rows, library, "fixture") == ({}, [])
    with pytest.raises(ByteIdentityError, match="no authenticated toolchain library"):
        region_helper_callees([_region(36, 64)], rows, None, "fixture")


# --- the record's pins -------------------------------------------------------------------


def _call_coff(body: bytes, call_at: int) -> bytes:
    """The re-encoding fixture's object with one REL32 call to ``__ftol`` at ``call_at``."""
    data = bytearray(
        make_coff(
            body=body,
            relocations=(call_at,),
            lines=((0, 10), (4, 11)),
            debug_stream=codeview_stream(len(body), 0, len(body) - 1),
        )
    )
    coff = CoffObject(bytes(data))
    section = coff.function_section(TARGET_SYMBOL)
    row = int(section["relocation_offset"])
    assert struct.unpack_from("<IIH", data, row)[2] == 0x0006
    struct.pack_into("<H", data, row + 8, 0x0014)
    name = NIL_SYMBOL.encode("ascii")
    at = data.index(name + b"\0")
    data[at : at + len(name)] = b"__ftol".ljust(len(name), b"\0")
    return bytes(data)


def _extern_donor():
    return build_extern_run_donor(
        target_id="program",
        translation_unit_id=UNIT,
        build_target="program",
        header_prefix="ReproBitPad",
        header_count=1,
        seat_prefix="ReproBitPadSeat",
        seat_count=0,
        width=3,
        beneficiary_symbols=(TARGET_SYMBOL,),
    )


def _author(library):
    seed = _call_coff(FTOL_D, 5)
    return build_function_validation_rewriting(
        donor=_extern_donor(),
        target_id="program",
        translation_unit_id=UNIT,
        build_target="program",
        symbol=TARGET_SYMBOL,
        seed_object=seed,
        donor_object=seed,
        reference_object=_call_coff(FTOL_P, 5),
        helper_library=library,
    )


def _dispatch(authored, library):
    seed = _call_coff(FTOL_D, 5)
    constraints = merge_candidate_constraints(
        authored.function.intervention, authored.function.receipt
    ).materialize()
    return ClassicFamilyDispatcher().dispatch(
        authored.function.intervention,
        ClassicDispatchMaterials(
            seed_object=seed,
            donor_object=seed,
            candidate_constraints=json.loads(json.dumps(constraints)),
            helper_library=library,
        ),
    )


def test_the_record_pins_the_helper_and_composes_the_reference_body() -> None:
    library = _library()
    authored = _author(library)
    values = authored.function.receipt.expected_values
    assert values["function_validation.expected_helper_callees"] == [library.helper("__ftol").pin()]
    composed = CoffObject(authored.candidate_object)
    assert bytes(coff_body(composed, composed.function_section(TARGET_SYMBOL))) == FTOL_P
    assert _dispatch(authored, library).output == authored.candidate_object


def test_a_changed_helper_body_refuses_the_record() -> None:
    authored = _author(_library())
    with pytest.raises(ByteIdentityError, match="helper_callees differs from its declaration"):
        _dispatch(authored, _library(truncate=TRUNCATE_NOP))


def test_a_build_without_the_library_refuses_the_record() -> None:
    authored = _author(_library())
    with pytest.raises(ByteIdentityError, match="no authenticated toolchain library"):
        _dispatch(authored, None)


def test_authoring_without_the_library_authors_nothing() -> None:
    with pytest.raises(DiscoveryAuthoringError, match="no authenticated toolchain library"):
        _author(None)


# --- grind: the library reaches both proofs, and its records build -----------------------


def _grind_rewriting(monkeypatch, library, *, region_resize=True):
    """Grind's donor rewriting for the ``__ftol`` fixture; the refusals each proof raised."""
    from types import SimpleNamespace

    import reprobit.discovery_grind as grind
    from reprobit.discovery_contracts import DeclarationFamily

    refusals: list[str] = []

    def recording(builder):
        def build(**kwargs):
            try:
                return builder(**kwargs)
            except DiscoveryAuthoringError as exc:
                refusals.append(str(exc))
                raise

        return build

    def no_region_resize(**_kwargs):
        raise DiscoveryAuthoringError("region resize refused")

    monkeypatch.setattr(
        grind,
        "build_region_resize_rewriting",
        recording(grind.build_region_resize_rewriting if region_resize else no_region_resize),
    )
    monkeypatch.setattr(
        grind,
        "build_function_validation_rewriting",
        recording(grind.build_function_validation_rewriting),
    )
    monkeypatch.setattr(grind, "_require_grind_family", lambda _state: None)
    monkeypatch.setattr(
        grind,
        "_extern_run",
        lambda _state: SimpleNamespace(
            header_prefix="ReproBitPad",
            header_count=1,
            seat_prefix="ReproBitPadSeat",
            seat_count=0,
            width=3,
        ),
    )
    monkeypatch.setattr(grind, "_header_placement", lambda _context: "after_includes")
    context = SimpleNamespace(
        unit=SimpleNamespace(target_id="program", id=UNIT, build_target="program"),
        symbol=TARGET_SYMBOL,
    )
    seed = _call_coff(FTOL_D, 5)

    def author():
        return grind._state_rewriting(
            SimpleNamespace(family=DeclarationFamily.EXTERN_RUN_PAIR),
            context,
            seed_object=seed,
            donor_object=seed,
            reference_object=_call_coff(FTOL_P, 5),
            helper_library=library,
        )

    return author, refusals


def test_grind_authors_a_function_validation_record_pinning_the_helper(monkeypatch) -> None:
    library = _library()
    author, refusals = _grind_rewriting(monkeypatch, library, region_resize=False)
    authored = author()
    assert refusals == ["region resize refused"]
    values = authored.function.receipt.expected_values
    assert values["function_validation.expected_helper_callees"] == [library.helper("__ftol").pin()]
    composed = CoffObject(authored.candidate_object)
    assert bytes(coff_body(composed, composed.function_section(TARGET_SYMBOL))) == FTOL_P
    assert _dispatch(authored, library).output == authored.candidate_object


def test_grind_without_the_library_refuses_the_helper_call(monkeypatch) -> None:
    author, refusals = _grind_rewriting(monkeypatch, None, region_resize=False)
    with pytest.raises(DiscoveryAuthoringError):
        author()
    assert len(refusals) == 2
    assert "the donor calls the compiler helpers ['__ftol']" in refusals[1]
    assert "no authenticated toolchain library is supplied" in refusals[1]


def test_grind_s_region_resize_record_builds_with_the_library(monkeypatch) -> None:
    library = _library()
    author, refusals = _grind_rewriting(monkeypatch, library)
    authored = author()
    assert refusals == []
    assert _dispatch(authored, library).output == authored.candidate_object


def test_grind_loads_the_library_the_producer_reads(monkeypatch, tmp_path) -> None:
    import reprobit.toolchain_helper_library as toolchain_library
    from reprobit.backends import NativeWindowsBackend
    from reprobit.discovery_grind_cli import _helper_library_loader
    from reprobit.project_execution import ProjectExecutionOptions

    profile = "msvc_5_0_rtm"
    data = _library().data
    authority = Msvc50FileAuthority(len(data), hashlib.sha256(data).hexdigest())
    monkeypatch.setattr(
        toolchain_library, "MSVC50_LIBRARY_AUTHORITIES", {profile: {HELPER_LIBRARY: authority}}
    )
    root = tmp_path / "toolchain"
    (root / "lib").mkdir(parents=True)
    options = ProjectExecutionOptions(jobs=1, backend=NativeWindowsBackend(), toolchain_root=root)
    assert _helper_library_loader(options)(profile) is None
    (root / "lib" / "libc.lib").write_bytes(data)
    load = _helper_library_loader(options)
    library = load(profile)
    assert library is not None and load(profile) is library
    assert library.sha256 == authority.sha256
    produced = toolchain_library.load_helper_library(root, profile)
    assert produced is not None
    authored = _author(library)
    assert _dispatch(authored, produced).output == authored.candidate_object
