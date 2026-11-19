"""Partial slot relations: a private slot related at a join only on the paths that wrote it.

The programs are hand-encoded IA-32 (each listing is in the comment above
it).  Each loop keeps a flag that is -1 until its first iteration, which
writes a slot; later iterations read that slot only while the flag is not
-1, as ``mesh_uview_mesh`` reads ``polyIndex`` only once ``polyVert`` has left
-1.  At the loop's head the slot is unwritten on the path from the entry and
written on the back edges: one relation cannot carry it, two variants of the
relation can (`function_validation.validate_function`).
"""

from __future__ import annotations

from typing import Any

import pytest
from test_classic_frame_objects import _coff
from test_classic_function_validation import SPILL_D, SPILL_FRAME, SPILL_P, _extern_donor
from test_classic_register_bijection_reencoding_full import TARGET_SYMBOL

from reprobit.binary import ByteIdentityError
from reprobit.classic import function_validation
from reprobit.classic.frame_objects import FrameLocal, merge_frame_objects
from reprobit.classic.function_validation import (
    FrameFacts,
    UncarriedSlot,
    proof_summary,
    prove_function,
)
from reprobit.classic.region_simulation import ObjectModel
from reprobit.classic_donors import merge_candidate_constraints
from reprobit.classic_project import ClassicDispatchMaterials, ClassicFamilyDispatcher
from reprobit.coff_format import CoffObject, coff_body
from reprobit.discovery_function_validation import build_function_validation_rewriting

NO_OBJECTS = ObjectModel({}, 4, frozenset())
FRAME = FrameFacts(True, base=-8, params_end=4)
X87_RETURNS = {"_next": 0, "_use": 0}


def _code(text: str) -> bytes:
    return bytes.fromhex(text.replace(" ", ""))


# 0: sub esp,8 / 3: mov dword [esp],-1 (the flag at ESP0-8)
# 10: call _next / 15: test eax,eax / 17: je 53 / 19: cmp dword [esp],-1 / 23: jne 38
# 25: mov [esp+4],eax (the slot at ESP0-4) / 29: mov dword [esp],0 / 36: jmp 10
# 38: mov ecx,[esp+4] / 42: push ecx / 43: call _use / 48: add esp,4 / 51: jmp 10
# 53: add esp,8 / 56: ret
FIRST_D = _code(
    "83ec08 c70424ffffffff e800000000 85c0 7422 833c24ff 750d 89442404 c7042400000000 ebe4 "
    "8b4c2404 51 e800000000 83c404 ebd5 83c408 c3"
)
FIRST_D_CALLS = {11: ("rel32", "_next"), 44: ("rel32", "_use")}
# The other allocation: the flag at ESP0-4, the slot at ESP0-8.
# 3: mov dword [esp+4],-1 / 11: call _next / 16: test eax,eax / 18: je 54
# 20: cmp dword [esp+4],-1 / 25: jne 40 / 27: mov [esp],eax / 30: mov dword [esp+4],0
# 38: jmp 11 / 40: mov ecx,[esp] / 43: push ecx / 44: call _use / 49: add esp,4
# 52: jmp 11 / 54: add esp,8 / 57: ret
FIRST_P = _code(
    "83ec08 c7442404ffffffff e800000000 85c0 7422 837c2404ff 750d 890424 c744240400000000 "
    "ebe3 8b0c24 51 e800000000 83c404 ebd5 83c408 c3"
)
FIRST_P_CALLS = {12: ("rel32", "_next"), 45: ("rel32", "_use")}
# ... without the first iteration's write (27: mov dword [esp+4],0 / 35: jmp 11): the
# replacement passes its slot's entry value where the donor passes the first value.
UNWRITTEN_P = _code(
    "83ec08 c7442404ffffffff e800000000 85c0 741f 837c2404ff 750a c744240400000000 ebe6 "
    "8b0c24 51 e800000000 83c404 ebd8 83c408 c3"
)
UNWRITTEN_P_CALLS = {12: ("rel32", "_next"), 42: ("rel32", "_use")}
# ... clearing its slot after each use (52: mov dword [esp],0 / 59: jmp 11): the third
# iteration passes 0 where the donor passes the first value again.
CLEARED_P = _code(
    "83ec08 c7442404ffffffff e800000000 85c0 7429 837c2404ff 750d 890424 c744240400000000 "
    "ebe3 8b0c24 51 e800000000 83c404 c7042400000000 ebce 83c408 c3"
)
# The donor's allocation, with the slot also cleared at the entry (10: mov dword
# [esp+4],0), a store no read sees: 18: call _next ... 46: mov ecx,[esp+4] ...
INIT_D = _code(
    "83ec08 c70424ffffffff c744240400000000 e800000000 85c0 7422 833c24ff 750d 89442404 "
    "c7042400000000 ebe4 8b4c2404 51 e800000000 83c404 ebd5 83c408 c3"
)
INIT_D_CALLS = {19: ("rel32", "_next"), 52: ("rel32", "_use")}
# ... passing the slot's address instead (46: lea ecx,[esp+4]), so the slot escapes.
INIT_D_ESCAPING = _code(
    "83ec08 c70424ffffffff c744240400000000 e800000000 85c0 7422 833c24ff 750d 89442404 "
    "c7042400000000 ebe4 8d4c2404 51 e800000000 83c404 ebd5 83c408 c3"
)
# FIRST_D with the address passed (38: lea ecx,[esp+4]): the replacement of INIT_D_ESCAPING,
# which leaves the slot unwritten until the first iteration.
FIRST_D_ESCAPING = _code(
    "83ec08 c70424ffffffff e800000000 85c0 7422 833c24ff 750d 89442404 c7042400000000 ebe4 "
    "8d4c2404 51 e800000000 83c404 ebd5 83c408 c3"
)


def _prove(
    donor: bytes,
    donor_calls: dict[int, Any],
    image: bytes,
    image_calls: dict[int, Any],
    *,
    partial_slots: bool = True,
    **options: Any,
) -> Any:
    return prove_function(
        donor,
        donor_calls,
        image,
        image_calls,
        X87_RETURNS,
        "fixture",
        private_frame=FRAME,
        objects=NO_OBJECTS,
        partial_slots=partial_slots,
        **options,
    )


def _bytes(side: str, start: int, width: int = 4) -> list[list[Any]]:
    return [[side, offset] for offset in range(start, start + width)]


# --- the rule ------------------------------------------------------------------------------


def test_a_slot_written_on_the_first_iteration_is_related_on_the_paths_that_wrote_it() -> None:
    # One relation at the loop's head loses the slot: the entry's path left it
    # unwritten, so the read in a later iteration is refused as before.
    with pytest.raises(UncarriedSlot, match=r"ESP0-4 whose value the relation does not carry"):
        _prove(FIRST_D, FIRST_D_CALLS, FIRST_P, FIRST_P_CALLS, partial_slots=False)
    proof = _prove(FIRST_D, FIRST_D_CALLS, FIRST_P, FIRST_P_CALLS)
    summary = proof_summary(proof)
    # Split on both versions' slots: the variant that wrote them relates them,
    # the variant that did not keeps the flag the constant -1, so its paths
    # never reach the read.
    assert summary["partial_slots"] == _bytes("D", -4) + _bytes("P", -8)
    assert summary["relation_variants"] == 2
    variants = [variant for key, variant in proof.variants if key == (10, 11)]
    assert sorted(variants, key=lambda item: sorted(item[0])) == [
        (frozenset(), frozenset()),
        (frozenset(range(-4, 0)), frozenset(range(-8, -4))),
    ]
    assert proof.returns == 2


def test_a_slot_one_version_also_writes_at_the_entry_splits_the_other_version_s_writes() -> None:
    # The donor's slot is written on every path (the entry's store is dead),
    # the replacement's only on the loop's: the class is lost because the
    # replacement's slot was unwritten, so its bytes split the joins.
    proof = _prove(INIT_D, INIT_D_CALLS, FIRST_D, FIRST_D_CALLS)
    assert proof_summary(proof)["partial_slots"] == _bytes("P", -4)


def test_a_proof_that_needs_no_split_pins_nothing_new() -> None:
    def summary(partial_slots: bool) -> dict[str, Any]:
        return proof_summary(
            prove_function(
                SPILL_D,
                {11: ("rel32", "_f")},
                SPILL_P,
                {15: ("rel32", "_f")},
                {},
                "fixture",
                private_frame=SPILL_FRAME,
                objects=NO_OBJECTS,
                partial_slots=partial_slots,
            )
        )

    assert summary(True) == summary(False)
    assert "partial_slots" not in summary(True)


# --- refusals ------------------------------------------------------------------------------


def test_a_slot_read_where_one_version_wrote_it_and_the_other_did_not_is_refused() -> None:
    with pytest.raises(
        ByteIdentityError,
        match=r"\[the variant where the donor has written ESP0-4..-1\] P: a read of the stack "
        r"slot ESP0-8 whose value the relation does not carry",
    ):
        _prove(FIRST_D, FIRST_D_CALLS, UNWRITTEN_P, UNWRITTEN_P_CALLS)


def test_a_slot_whose_written_paths_leave_different_values_is_refused() -> None:
    with pytest.raises(
        ByteIdentityError,
        match=r"ESP0-4 whose value the relation does not carry .*; partial slot relations do "
        r"not carry it: no path into a join that lost its class left one of the class's slots "
        r"unwritten",
    ):
        _prove(FIRST_D, FIRST_D_CALLS, CLEARED_P, FIRST_P_CALLS)


def test_an_escaping_object_is_never_split() -> None:
    # The same two loops as the entry-store test, with the slot's address
    # passed instead of its value: under a14 the slot is a frame object,
    # memory compared whole at every call, so the dead store at the entry
    # is a difference whatever later reads see.
    objects = merge_frame_objects((FrameLocal("flag", -8, 4, 0), FrameLocal("x", -4, 4, 0)))
    with pytest.raises(ByteIdentityError, match=r"leave different memory"):
        _prove(
            INIT_D_ESCAPING, INIT_D_CALLS, FIRST_D_ESCAPING, FIRST_D_CALLS, frame_objects=objects
        )
    proof = _prove(
        INIT_D_ESCAPING, INIT_D_CALLS, INIT_D_ESCAPING, INIT_D_CALLS, frame_objects=objects
    )
    summary = proof_summary(proof)
    assert summary["frame_objects"] == [[-8, 4], [-4, 4]] and "partial_slots" not in summary


def test_variants_beyond_the_bound_leave_the_writes_undecided(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(function_validation, "MAX_VARIANTS", 1)
    with pytest.raises(
        ByteIdentityError,
        match=r"splits into more than 1 variants, so which paths write its split slots is not "
        r"decided",
    ):
        _prove(FIRST_D, FIRST_D_CALLS, FIRST_P, FIRST_P_CALLS)


# 0: push dword [esp+4] / 4: call _free / 9: add esp,4 / 12: push dword [esp+8]
# 16: call _free / 21: add esp,4 / 24: ret: free(a); free(b) of two parameters no path
# writes, a at ESP0+4 and b at ESP0+8.
FREE_D = _code("ff742404 e800000000 83c404 ff742408 e800000000 83c404 c3")
# ... freeing b first.
FREE_P = _code("ff742408 e800000000 83c404 ff742404 e800000000 83c404 c3")


def test_entry_values_at_other_offsets_make_other_calls() -> None:
    # No split applies: nothing writes the slots, and their entry values are
    # equal only at equal offsets.
    calls = {5: ("rel32", "_free"), 17: ("rel32", "_free")}
    with pytest.raises(
        ByteIdentityError,
        match=r"make different calls; event 1 passes the entry values of stack slots never "
        r"written since the entry \(the donor's ESP0\+4, the replacement's ESP0\+8\)",
    ):
        prove_function(
            FREE_D,
            calls,
            FREE_P,
            calls,
            {"_free": 0},
            "fixture",
            private_frame=FrameFacts(True, base=0, params_end=12),
            objects=NO_OBJECTS,
            partial_slots=True,
        )


# --- the record ----------------------------------------------------------------------------

# A loop over its parameter n, with no call: 0: sub esp,8 / 3: mov dword [esp],-1
# 10: xor edx,edx / 12: mov eax,[esp+0xc] / 16: test eax,eax / 18: je 50 / 20: dec eax
# 21: mov [esp+0xc],eax / 25: cmp dword [esp],-1 / 29: jne 44 / 31: mov [esp+4],eax
# 35: mov dword [esp],0 / 42: jmp 12 / 44: add edx,[esp+4] / 48: jmp 12
# 50: mov eax,edx / 52: add esp,8 / 55: ret
LOOP_D = _code(
    "83ec08 c70424ffffffff 31d2 8b44240c 85c0 741e 48 8944240c 833c24ff 750d 89442404 "
    "c7042400000000 ebe0 03542404 ebda 89d0 83c408 c3"
)
# The flag and the slot in each other's places.
LOOP_P = _code(
    "83ec08 c7442404ffffffff 31d2 8b44240c 85c0 741e 48 8944240c 837c2404ff 750d 890424 "
    "c744240400000000 ebdf 031424 ebda 89d0 83c408 c3"
)


def _loop_coff(body: bytes) -> bytes:
    return _coff(body, [], types=None, locals_words=2, params=1)


def test_a_record_pins_its_split_bytes_only_when_every_pass_needed_them() -> None:
    seed = _loop_coff(LOOP_D)
    authored = build_function_validation_rewriting(
        donor=_extern_donor(),
        target_id="program",
        translation_unit_id="tu.fixture",
        build_target="program",
        symbol=TARGET_SYMBOL,
        seed_object=seed,
        donor_object=seed,
        reference_object=_loop_coff(LOOP_P),
    )
    proof = authored.function.receipt.expected_values["function_validation.expected_proof"]
    # Already the first pass, which takes no local's entry value, proves: it
    # splits on the slot and on the parameter n, written by every iteration,
    # whose class holds the first iteration's copy of n in the slot.  Both
    # were unwritten on the entry's path into the loop's head.
    assert proof["partial_slots"] == (
        _bytes("D", -4) + _bytes("D", 4) + _bytes("P", -8) + _bytes("P", 4)
    )
    assert proof["relation_variants"] == 2
    assert "equivalences" not in proof and "assumptions" not in proof
    assert "assumptions" not in proof
    composed = CoffObject(authored.candidate_object)
    assert bytes(coff_body(composed, composed.function_section(TARGET_SYMBOL))) == LOOP_P
    constraints = merge_candidate_constraints(
        authored.function.intervention, authored.function.receipt
    ).materialize()
    candidate = ClassicFamilyDispatcher().dispatch(
        authored.function.intervention,
        ClassicDispatchMaterials(
            seed_object=seed, donor_object=seed, candidate_constraints=constraints
        ),
    )
    assert candidate.output == authored.candidate_object
