"""Argument pops of consecutive calls, calls through pointers, helpers that name globals or
other helpers, and stack slots read before any write.

Every body here is hand-encoded IA-32 written for these tests (each listing
in the comment above it); the helpers are packed into a synthetic COFF
archive that a test-only authority authenticates, as in
`test_classic_helper_and_vtable_calls`.  No toolchain bytes are used.
"""

from __future__ import annotations

import hashlib
import struct

import pytest
from test_classic_helper_and_vtable_calls import _archive

from reprobit.binary import ByteIdentityError
from reprobit.classic import toolchain_helpers
from reprobit.classic.function_validation import (
    FrameFacts,
    Program,
    prove_function,
    results_dead,
)
from reprobit.classic.region_simulation import (
    ObjectModel,
    _Undefined,
    entry_state,
    interval_truth,
    lin,
    lin_atom,
    run_helper,
    simulate_region,
    term_range,
)
from reprobit.classic.toolchain_helpers import (
    HELPER_LIBRARY,
    HelperLibraryError,
    authenticate_helper_library,
)
from reprobit.msvc50_authorities import Msvc50FileAuthority

PROFILE = "test_profile"
NO_OBJECTS = ObjectModel({}, 4, frozenset())


def _code(text: str) -> bytes:
    return bytes.fromhex(text.replace(" ", ""))


def _prove(
    donor,
    image,
    donor_relocations=None,
    image_relocations=None,
    *,
    helpers=None,
    frame=None,
    objects=None,
    entry_values=False,
):
    return prove_function(
        donor,
        donor_relocations or {},
        image,
        image_relocations if image_relocations is not None else donor_relocations or {},
        {},
        "fixture",
        private_frame=frame,
        helpers=helpers,
        objects=objects,
        entry_values=entry_values,
    )


# --- 1. argument pops of consecutive calls (a11) ----------------------------------------

# A cdecl call and its cleanup, then two COM calls; the second's object comes
# through a branch on an argument:
# 0: push 1 / 2: call _f / 7: add esp,4 / 10: mov eax,[esp+4] / 14: push eax
# 15: mov ecx,[eax] / 17: call [ecx+0x10] / 20: mov eax,[esp+8] / 24: test eax,eax
# 26: jne 32 / 28: mov eax,[esp+4] / 32: push eax / 33: mov ecx,[eax] / 35: call [ecx+0x14]
# 38: ret
PUSHES_D = _code(
    "6a01 e800000000 83c404 8b442404 50 8b08 ff5110 8b442408 85c0 7504 8b442404 50 8b08 ff5114 c3"
)
# The first object in EDX, its vtable in EAX.
PUSHES_P = _code(
    "6a01 e800000000 83c404 8b542404 52 8b02 ff5010 8b442408 85c0 7504 8b442404 50 8b08 ff5114 c3"
)
# ... and an extra argument for the second call (32: push 0 / 34: push eax / ... / 37: call).
PUSHES_P_EXTRA = _code(
    "6a01 e800000000 83c404 8b542404 52 8b02 ff5010 8b442408 85c0 7504 8b442404 6a00 50 "
    "8b08 ff5114 c3"
)
PUSHES_RELOCATIONS = {3: ("rel32", "_f")}
# A register saved lazily between two calls, counted as an argument by the pushes:
# 0: mov eax,[esp+4] / 4: push eax / 5: mov ecx,[eax] / 7: call [ecx+0x10] / 10: push esi
# 11: mov eax,[esp+8] / 15: push eax / 16: mov ecx,[eax] / 18: call [ecx+0x14] / 21: pop esi
# 22: ret
LAZY_SAVE = _code("8b442404 50 8b08 ff5110 56 8b442408 50 8b08 ff5114 5e c3")
# The same after a direct call, so the pushes fix both pops, against the return:
# 0: call _f / 5: mov eax,[esp+4] / 9: push eax / 10: mov ecx,[eax] / 12: call [ecx+0x10]
# 15: push esi / 16: mov eax,[esp+8] / 20: push eax / 21: mov ecx,[eax] / 23: call [ecx+0x14]
# 26: pop esi / 27: ret
LAZY_SAVE_ANCHORED = _code("e800000000 8b442404 50 8b08 ff5110 56 8b442408 50 8b08 ff5114 5e c3")
# A frame allocation between the calls: 7: call [ecx+0x10] / 10: sub esp,4 / 13: mov eax,[esp+8]
# 17: push eax / 18: mov ecx,[eax] / 20: call [ecx+0x14] / 23: add esp,4 / 26: ret
ALLOCATED = _code("8b442404 50 8b08 ff5110 83ec04 8b442408 50 8b08 ff5114 83c404 c3")
# The first call's result decides the second's argument: 7: call [ecx+0x10] / 10: test eax,eax
# 12: mov eax,[esp+4] / 16: jne 20 / 18: xor eax,eax / 20: push eax / 21: mov ecx,[eax]
# 23: call [ecx+0x14] / 26: ret
TESTED = _code("8b442404 50 8b08 ff5110 85c0 8b442404 7502 33c0 50 8b08 ff5114 c3")
# The code after a call loops before the next: 7: call [ecx+0x10] / 10: mov edx,3 / 15: dec edx
# 16: jne 15 / 18: mov eax,[esp+4] / 22: push eax / 23: mov ecx,[eax] / 25: call [ecx+0x14]
# 28: ret
LOOPING = _code("8b442404 50 8b08 ff5110 ba03000000 4a 75fd 8b442404 50 8b08 ff5114 c3")


def test_the_words_pushed_since_the_previous_call_fix_each_pop() -> None:
    program = Program(PUSHES_D, PUSHES_RELOCATIONS, "D", "fixture")
    assert program.indirect_pops == {17: 4, 35: 4}
    assert program.pushed_pops == frozenset({17, 35})
    proof = _prove(PUSHES_D, PUSHES_P, PUSHES_RELOCATIONS)
    assert proof.returns == 2


def test_a_different_argument_count_makes_a_different_call() -> None:
    assert Program(PUSHES_P_EXTRA, PUSHES_RELOCATIONS, "P", "fixture").indirect_pops == {
        17: 4,
        37: 8,
    }
    with pytest.raises(ByteIdentityError, match="make different calls"):
        _prove(PUSHES_D, PUSHES_P_EXTRA, PUSHES_RELOCATIONS)


def test_a_saved_register_counted_as_an_argument_is_refused() -> None:
    assert Program(LAZY_SAVE, {}, "D", "fixture").indirect_pops == {7: 0, 18: 8}
    with pytest.raises(ByteIdentityError, match="saved register's entry value"):
        _prove(LAZY_SAVE, LAZY_SAVE)


def test_pushes_that_contradict_the_stack_relation_are_refused() -> None:
    with pytest.raises(ByteIdentityError, match=r"\(a11\) contradict the stack relation"):
        Program(LAZY_SAVE_ANCHORED, {1: ("rel32", "_f")}, "D", "fixture")


@pytest.mark.parametrize(
    ("code", "why"),
    [
        (ALLOCATED, "changes ESP other than by a push"),
        (TESTED, "decide the branch"),
        (LOOPING, "loops"),
    ],
    ids=["a frame allocation", "a tested result", "a loop"],
)
def test_where_the_pushes_cannot_be_trusted_the_sum_stays_undetermined(code, why) -> None:
    with pytest.raises(ByteIdentityError, match=f"does not determine the argument pop.*{why}"):
        Program(code, {}, "D", "fixture")


# A return between two calls on one path (their pops are fixed without a11):
# 0: mov eax,[esp+4] / 4: push eax / 5: mov ecx,[eax] / 7: call [ecx+0x10] / 10: test eax,eax
# 12: je 25 / 14: mov eax,[esp+4] / 18: push eax / 19: mov ecx,[eax] / 21: call [ecx+0x14]
# 24: ret / 25: ret
SEPARATED = _code("8b442404 50 8b08 ff5110 85c0 740b 8b442404 50 8b08 ff5114 c3 c3")


def test_a_call_whose_results_are_overwritten_leaves_them_dead() -> None:
    program = Program(PUSHES_D, PUSHES_RELOCATIONS, "D", "fixture")
    assert results_dead(program, 17) is None
    assert results_dead(program, 2) is None
    assert "decide the branch at 12" in str(results_dead(Program(SEPARATED, {}, "D", "f"), 7))


# --- 4. calls through a pointer (a12) ------------------------------------------------------

# 0: mov eax,[esp+4] / 4: push 5 / 6: call eax / 8: add esp,4 / 11: ret
POINTER_D = _code("8b442404 6a05 ffd0 83c404 c3")
# 0: mov ecx,[esp+4] / 4: push 5 / 6: call ecx / 8: pop ecx / 9: ret
POINTER_P = _code("8b4c2404 6a05 ffd1 59 c3")
# ... through the second argument.
POINTER_P_OTHER = _code("8b4c2408 6a05 ffd1 59 c3")
# A structure field: 0: mov eax,[esp+4] / 4: mov eax,[eax+0x18] / 7: push 5 / 9: call eax
# 11: add esp,4 / 14: ret
FIELD_D = _code("8b442404 8b4018 6a05 ffd0 83c404 c3")
# 0: mov edx,[esp+4] / 4: push 5 / 6: call [edx+0x18] / 9: add esp,4 / 12: ret
FIELD_P = _code("8b542404 6a05 ff5218 83c404 c3")
# ... the next field.
FIELD_P_OTHER = _code("8b542404 6a05 ff521c 83c404 c3")
# A helper that returns its own return address: 0: mov eax,[esp] / 3: ret
RETURN_ADDRESS = _code("8b0424 c3")
# 0: call __retaddr / 5: call eax / 7: ret
CODE_POINTER = _code("e800000000 ffd0 c3")


def test_a_call_through_a_register_is_an_event_named_by_its_pointer() -> None:
    assert Program(POINTER_D, {}, "D", "fixture").indirect_pops == {6: 0}
    assert _prove(POINTER_D, POINTER_P).returns == 1
    with pytest.raises(ByteIdentityError, match="make different calls"):
        _prove(POINTER_D, POINTER_P_OTHER)


def test_a_call_through_a_structure_field_meets_the_register_form() -> None:
    frame = FrameFacts(True, base=0, params_end=8)
    assert _prove(FIELD_D, FIELD_P, frame=frame).frame.private
    with pytest.raises(ByteIdentityError, match="make different calls"):
        _prove(FIELD_D, FIELD_P_OTHER, frame=frame)


def test_a_call_to_a_code_address_of_the_function_is_refused() -> None:
    helpers = _library_codes("__retaddr")
    relocations = {1: ("rel32", "__retaddr")}
    with pytest.raises(ByteIdentityError, match="code address of this function"):
        _prove(CODE_POINTER, CODE_POINTER, relocations, helpers=helpers, objects=NO_OBJECTS)


def test_the_region_simulator_still_refuses_a_call_through_a_pointer() -> None:
    with pytest.raises(ByteIdentityError, match="indirect call or jump"):
        simulate_region(POINTER_D, 0, 11, {}, "donor", "fixture")


# --- 2. helpers that name globals and other helpers ------------------------------------------

# A table lookup with a slow path that calls out:
# 0: mov ecx,[esp+4] / 4: lea eax,[ecx+1] / 7: cmp eax,0x100 / 12: ja 25
# 14: mov edx,[_table] / 20: movzx eax,byte [edx+ecx] / 24: ret
# 25: push ecx / 26: call _env / 31: add esp,4 / 34: ret
CLASSIFY = _code("8b4c2404 8d4101 3d00010000 770b 8b1500000000 0fb6040a c3 51 e800000000 83c404 c3")
CLASSIFY_RELOCATIONS = [(16, "_table", 0x06), (27, "_env", 0x14)]
# 0: mov eax,[esp+4] / 4: shl eax,1 / 6: ret
INNER = _code("8b442404 d1e0 c3")
# 0: mov eax,[esp+4] / 4: push eax / 5: call __inner / 10: add esp,4 / 13: inc eax / 14: ret
OUTER = _code("8b442404 50 e800000000 83c404 40 c3")
# 0: jmp __inner
TAIL = _code("e900000000")
# A pop that depends on the argument: 0: mov eax,[esp+4] / 4: cmp eax,0x100 / 9: jb 12
# 11: ret / 12: ret 4
POPPER = _code("8b442404 3d00010000 7201 c3 c20400")
# A call naming its own section: 0: call .text / 5: ret
SELF_CALL = _code("e800000000 c3")


def _relocated_object(symbol: str, code: bytes, relocations, *, own_section: bool = False):
    """One COFF object defining ``symbol`` at 0 of its .text, with the given relocations.

    Each relocation is (offset, external symbol, type); ``own_section`` makes
    the first one name the section symbol itself.
    """
    externals = sorted({name for _offset, name, _type in relocations})
    index = {name: 3 + number for number, name in enumerate(externals)}
    table = b"".join(
        struct.pack("<IIH", offset, 0 if own_section else index[name], kind)
        for offset, name, kind in relocations
    )
    raw_offset = 20 + 40
    relocation_offset = raw_offset + len(code)
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
    for external in externals:
        records.append(name(external) + struct.pack("<IhHBB", 0, 0, 0x20, 2, 0))
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


def _library():
    data = _archive(
        [
            (
                "__classify",
                "classify.obj",
                _relocated_object("__classify", CLASSIFY, CLASSIFY_RELOCATIONS),
            ),
            ("__inner", "inner.obj", _relocated_object("__inner", INNER, [])),
            ("__outer", "outer.obj", _relocated_object("__outer", OUTER, [(6, "__inner", 0x14)])),
            ("__tail", "tail.obj", _relocated_object("__tail", TAIL, [(1, "__inner", 0x14)])),
            ("__popper", "popper.obj", _relocated_object("__popper", POPPER, [])),
            ("__retaddr", "retaddr.obj", _relocated_object("__retaddr", RETURN_ADDRESS, [])),
            (
                "__self",
                "self.obj",
                _relocated_object("__self", SELF_CALL, [(1, "__self", 0x14)], own_section=True),
            ),
        ]
    )
    authority = Msvc50FileAuthority(len(data), hashlib.sha256(data).hexdigest())
    return authenticate_helper_library(PROFILE, data, {PROFILE: {HELPER_LIBRARY: authority}})


def _library_codes(*symbols: str):
    library = _library()
    return {symbol: library.helper(symbol).code for symbol in symbols}


# 0: xor eax,eax / 2: mov al,[esp+4] / 6: push eax / 7: call __classify / 12: add esp,4 / 15: ret
CLASSIFY_D = _code("33c0 8a442404 50 e800000000 83c404 c3")
# 0: xor edx,edx / 2: mov dl,[esp+4] / 6: push edx / 7: call __classify / 12: pop ecx / 13: ret
CLASSIFY_P = _code("33d2 8a542404 52 e800000000 59 c3")
CLASSIFY_CALL = {8: ("rel32", "__classify")}
# The whole argument word, unbounded: 0: mov eax,[esp+4] / 4: push eax / 5: call __classify
# 10: add esp,4 / 13: ret
CLASSIFY_WIDE = _code("8b442404 50 e800000000 83c404 c3")
# A constant above the table: 0: push 0x200 / 5: call __classify / 10: add esp,4 / 13: ret
CLASSIFY_LARGE = _code("6800020000 e800000000 83c404 c3")
CLASSIFY_CALL_AT_6 = {6: ("rel32", "__classify")}
# 0: push 3 / 2: call __outer / 7: add esp,4 / 10: ret
OUTER_D = _code("6a03 e800000000 83c404 c3")
# 0: mov eax,7 / 5: ret
SEVEN = _code("b807000000 c3")
SIX = _code("b806000000 c3")
# 0: xor eax,eax / 2: mov al,[esp+4] / 6: push eax / 7: call __popper / 12: add esp,4 / 15: ret
POPPER_D = _code("33c0 8a442404 50 e800000000 83c404 c3")


def test_a_relocated_helper_is_resolved_with_its_fields_and_pins_them() -> None:
    library = _library()
    body = library.helper("__classify")
    assert body.code.relocations == {16: "_table", 27: ("rel32", "_env")}
    pin = body.pin()
    assert pin["relocations_sha256"] == toolchain_helpers.relocations_digest(body.code.relocations)
    assert pin["linked"] == []  # _env is a C function, not a helper: never resolved
    assert set(library.helper("__inner").pin()) == {
        "symbol",
        "library",
        "library_sha256",
        "member",
        "body_sha256",
        "body_length",
    }


def test_a_bounded_argument_takes_the_table_path_and_reads_the_global() -> None:
    helpers = _library_codes("__classify")
    proof = _prove(CLASSIFY_D, CLASSIFY_P, CLASSIFY_CALL, helpers=helpers, objects=NO_OBJECTS)
    assert proof.returns == 1
    program = Program(CLASSIFY_D, CLASSIFY_CALL, "D", "fixture", helpers)
    # Alone, the body's branch on its argument is not decided: the walk solves its ESP effect.
    assert program.helper_changes == {7: 0}


def test_an_unbounded_argument_leaves_the_helper_branch_undecided() -> None:
    helpers = _library_codes("__classify")
    with pytest.raises(ByteIdentityError, match="branches on a value that is not constant"):
        _prove(CLASSIFY_WIDE, CLASSIFY_WIDE, {6: ("rel32", "__classify")}, helpers=helpers)


def test_a_helper_path_that_calls_out_is_refused() -> None:
    helpers = _library_codes("__classify")
    with pytest.raises(ByteIdentityError, match="reaches the environment"):
        _prove(CLASSIFY_LARGE, CLASSIFY_LARGE, CLASSIFY_CALL_AT_6, helpers=helpers)


def test_a_region_proof_refuses_a_relocated_helper() -> None:
    state = entry_state()
    with pytest.raises(ByteIdentityError, match="only a whole-function proof simulates"):
        run_helper(state, _library_codes("__classify")["__classify"], _Undefined("D"), "fixture")


def test_a_helper_calling_another_helper_runs_both_bodies() -> None:
    library = _library()
    body = library.helper("__outer")
    assert set(body.code.linked) == {"__outer", "__inner"}
    assert [item["symbol"] for item in body.pin()["linked"]] == ["__inner"]
    helpers = {"__outer": body.code}
    relocations = {3: ("rel32", "__outer")}
    proof = _prove(OUTER_D, SEVEN, relocations, {}, helpers=helpers)
    assert proof.returns == 1
    with pytest.raises(ByteIdentityError, match="eax differs at the return"):
        _prove(OUTER_D, SIX, relocations, {}, helpers=helpers)


def test_a_tail_jump_continues_in_the_other_helper() -> None:
    helpers = _library_codes("__tail")
    assert _prove(OUTER_D, SIX, {3: ("rel32", "__tail")}, {}, helpers=helpers).returns == 1


def test_a_helper_beyond_the_closure_bound_is_not_run(monkeypatch) -> None:
    monkeypatch.setattr(toolchain_helpers, "MAX_HELPER_DEPTH", 0)
    helpers = _library_codes("__outer")
    with pytest.raises(ByteIdentityError, match="beyond the closure's bounds"):
        _prove(OUTER_D, SEVEN, {3: ("rel32", "__outer")}, {}, helpers=helpers)


def test_a_helper_whose_field_names_its_own_section_is_refused() -> None:
    with pytest.raises(HelperLibraryError, match="names its own section"):
        _library().helper("__self")


def test_a_run_that_changes_esp_otherwise_than_the_solved_change_is_refused() -> None:
    helpers = _library_codes("__popper")
    relocations = {8: ("rel32", "__popper")}
    assert Program(POPPER_D, relocations, "D", "fixture", helpers).helper_changes == {7: 0}
    with pytest.raises(ByteIdentityError, match="changes ESP otherwise than the stack relation"):
        _prove(POPPER_D, POPPER_D, relocations, helpers=helpers, objects=NO_OBJECTS)


def test_ranges_decide_only_compares_their_forms_bound() -> None:
    byte = ("b", 8, ("ld", "x", 1, ()))
    widened = lin(1, [(("zx", byte, 8), 1)])
    assert term_range(widened) == (1, 256)
    inserted = lin_atom(("ins", lin(0), 0, 8, byte))
    assert term_range(inserted) == (0, 255)
    masked = lin_atom(("op", "and", 32, (lin(0xFF), lin_atom("y"))))
    assert term_range(masked) == (0, 0xFF)
    assert term_range(lin(-1, [(("zx", byte, 8), 1)])) is None  # it may wrap below zero
    assert term_range(lin_atom("y")) is None
    assert interval_truth(("ltu", 32, lin(0x100), widened)) is False
    assert interval_truth(("ltu", 32, widened, lin(0x101))) is True
    assert interval_truth(("ltu", 32, lin(0x80), widened)) is None
    assert interval_truth(("eqz", 32, widened)) is False


# --- 3. stack slots read before any write (a13) ---------------------------------------------

# An uninitialised local: 0: sub esp,8 / 3: mov eax,[esp+4] / 7: add esp,8 / 10: ret
LOCAL_D = _code("83ec08 8b442404 83c408 c3")
# 0: sub esp,8 / 3: mov ecx,[esp+4] / 7: mov eax,ecx / 9: add esp,8 / 12: ret
LOCAL_P = _code("83ec08 8b4c2404 8bc1 83c408 c3")
# ... reading the other local (ESP0-8).
LOCAL_P_OTHER = _code("83ec08 8b0c24 90 8bc1 83c408 c3")
LOCAL_FRAME = FrameFacts(True, base=-8, params_end=4)
# Below the locals block: 0: sub esp,4 / 3: sub esp,4 / 6: mov eax,[esp] / 9: add esp,8 / 12: ret
BELOW = _code("83ec04 83ec04 8b0424 83c408 c3")
# A parameter written on one path and read on the other, then read after the join:
# 0: mov eax,[esp+4] / 4: test eax,eax / 6: je 15 / 8: inc eax / 9: mov [esp+4],eax / 13: jmp 19
# 15: mov eax,[esp+4] / 19: mov ecx,[esp+4] / 23: test ecx,ecx / 25: je 28 / 27: inc ecx
# 28: add eax,ecx / 30: ret
WRITTEN_D = _code("8b442404 85c0 7407 40 89442404 eb04 8b442404 8b4c2404 85c9 7401 41 03c1 c3")
# ... with EDX after the join.
WRITTEN_P = _code("8b442404 85c0 7407 40 89442404 eb04 8b442404 8b542404 85d2 7401 42 03c2 c3")
WRITTEN_FRAME = FrameFacts(True, base=0, params_end=8)


def test_an_untouched_local_reads_its_entry_value_in_the_equivalences_pass() -> None:
    with pytest.raises(ByteIdentityError, match="only in the equivalences pass"):
        _prove(LOCAL_D, LOCAL_P, frame=LOCAL_FRAME)
    proof = _prove(LOCAL_D, LOCAL_P, frame=LOCAL_FRAME, objects=NO_OBJECTS)
    assert proof.frame.private and proof.returns == 1


def test_another_uninitialised_local_holds_another_value() -> None:
    with pytest.raises(ByteIdentityError, match="eax differs at the return"):
        _prove(LOCAL_D, LOCAL_P_OTHER, frame=LOCAL_FRAME, objects=NO_OBJECTS)


def test_a_slot_below_the_locals_block_has_no_entry_value() -> None:
    frame = FrameFacts(True, base=-4, params_end=4)
    with pytest.raises(ByteIdentityError, match="below the locals block"):
        _prove(BELOW, BELOW, frame=frame, objects=NO_OBJECTS)


def test_an_entry_value_read_on_one_path_is_carried_as_the_slot() -> None:
    with pytest.raises(ByteIdentityError, match="wrote its bytes"):
        _prove(WRITTEN_D, WRITTEN_P, frame=WRITTEN_FRAME, objects=NO_OBJECTS)
    proof = _prove(WRITTEN_D, WRITTEN_P, frame=WRITTEN_FRAME, objects=NO_OBJECTS, entry_values=True)
    assert proof.frame.private and proof.returns == 2


# --- fixed in passing: a compare of constants under ``be``/``a`` and ``le``/``g`` ------------


@pytest.mark.parametrize(
    ("left", "right"), [(0x201, 0x100), (0x100, 0x201), (7, 7), (5, 0xFFFFFFF0)]
)
def test_a_compare_of_constants_decides_every_condition_as_the_processor_does(left, right) -> None:
    from reprobit.classic.region_simulation import _arith_flags, condition

    def signed(value: int) -> int:
        return value - (1 << 32) if value >> 31 else value

    state = entry_state()
    _arith_flags(state, "sub", 32, lin(left), lin(right))
    expected = {
        2: left < right,
        3: left >= right,
        4: left == right,
        5: left != right,
        6: left <= right,
        7: left > right,
        12: signed(left) < signed(right),
        13: signed(left) >= signed(right),
        14: signed(left) <= signed(right),
        15: signed(left) > signed(right),
    }
    assert {code: condition(code, state.flags) for code in expected} == expected
