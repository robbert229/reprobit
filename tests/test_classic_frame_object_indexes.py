"""The indexed frame-objects pass (a14 with proved index ranges, a16) and x87 intrinsics (a17).

Every function here is hand-encoded IA-32 written for these tests (each
listing in the comment above it).  The proofs run through `prove_function`
with the donor's frame objects given directly, as `test_classic_frame_objects`
does; the intrinsic dispatcher is a synthetic `HelperCode` of the
``__CI<name>`` form.
"""

from __future__ import annotations

from typing import Any

import pytest

from reprobit.binary import ByteIdentityError
from reprobit.classic.frame_objects import FrameLocal, FrameObjects, merge_frame_objects
from reprobit.classic.function_validation import (
    MAX_WIDENINGS,
    FrameFacts,
    Relation,
    SideFacts,
    ValueClass,
    condition_ranges,
    implies,
    linear_range,
    meet,
    pin_x87_intrinsics,
    proof_summary,
    prove_function,
    value_range,
)
from reprobit.classic.region_simulation import (
    HelperCode,
    ObjectModel,
    lin,
    lin_atom,
    x87_intrinsic_arity,
)


def _code(text: str) -> bytes:
    return bytes.fromhex(text.replace(" ", ""))


OBJECTS = ObjectModel({}, 8)


def _objects(*records: tuple[str, int, int]) -> FrameObjects:
    return merge_frame_objects(tuple(FrameLocal(name, at, size, 0) for name, at, size in records))


def _prove(
    donor: bytes,
    image: bytes,
    frame: FrameFacts,
    frame_objects: FrameObjects | None,
    *,
    indexed: bool,
    relocations: dict[int, Any] | None = None,
    image_relocations: dict[int, Any] | None = None,
) -> Any:
    return prove_function(
        donor,
        relocations or {},
        image,
        image_relocations if image_relocations is not None else relocations or {},
        {},
        "fixture",
        private_frame=frame,
        objects=OBJECTS,
        frame_objects=frame_objects,
        indexed=indexed,
    )


# --- 1. ranges ---------------------------------------------------------------------------

V = ("v",)
W = ("w",)


def test_conditions_bound_a_term_exactly() -> None:
    v = lin_atom(V)
    facts = condition_ranges(
        [
            (("ltu", 32, v, lin(10)), True),  # v < 10
            (("ltu", 32, lin(2), v), True),  # 2 < v
        ]
    )
    assert facts[v] == (3, 9)
    assert condition_ranges([(("ltu", 32, v, lin(4)), False)])[v] == (4, 0xFFFFFFFF)
    assert condition_ranges([(("eqz", 32, v), True)])[v] == (0, 0)
    # v != 0 (the canonical form of not (v <u 1)) puts v in [1, 2**32 - 1].
    assert condition_ranges([(("eqz", 32, v), False)])[v] == (1, 0xFFFFFFFF)


def test_an_atom_is_bounded_by_a_fact_on_itself_plus_a_constant() -> None:
    # v + 1 < 4 (a counter incremented, then compared): v + 1 in [0, 3].  That
    # does not bound v itself (v may be 2**32 - 1), but the term v + 1 is.
    facts = condition_ranges([(("ltu", 32, lin(1, [(V, 1)]), lin(4)), True)])
    assert value_range(lin(1, [(V, 1)]), facts) == (0, 3)
    assert linear_range([(V, 1)], facts) is None
    # v - 1 in [0, 3] puts v in [1, 4].
    facts = condition_ranges([(("ltu", 32, lin(-1, [(V, 1)]), lin(4)), True)])
    assert linear_range([(V, 4)], facts) == (4, 16)


def test_forms_bound_an_atom() -> None:
    masked = ("op", "and", 32, (lin_atom(V), lin(3)))
    assert linear_range([(masked, 32)], {}) == (0, 96)
    # xor eax,eax / sete al: a byte that is 0 or 1 inserted into a cleared word.
    setcc = ("ins", lin(0), 0, 8, ("b", 8, ("cc", ("eqz", 32, lin_atom(W)), True)))
    assert linear_range([(setcc, 2000)], {}) == (0, 2000)
    zero_extended = ("zx", ("b", 8, ("ld", lin_atom(W), 1, ())), 8)
    assert linear_range([(zero_extended, 1)], {}) == (0, 255)
    assert linear_range([(V, 1)], {}) is None


# --- 2. indexed stack addresses ----------------------------------------------------------

# int arr[4] at ESP0-16 and the slots ESP0-20 and ESP0-24 outside it; i the parameter.
# 0: sub esp,0x18 / 3: mov ecx,[esp+0x1c] / 7: mov [esp+4],ecx / 11: and ecx,3
# 14: mov eax,[esp+ecx*4+8] / 18: add eax,[esp+4] / 22: add esp,0x18 / 25: ret:
# return arr[i & 3] + i, i's copy in ESP0-20.
MASKED_D = _code("83ec18 8b4c241c 894c2404 83e103 8b448c08 03442404 83c418 c3")
# ... with i's copy in ESP0-24: 7: mov [esp],ecx / 17: add eax,[esp]
MASKED_P = _code("83ec18 8b4c241c 890c24 83e103 8b448c08 030424 83c418 c3")
# ... without the mask: 11: mov eax,[esp+ecx*4+8]
UNBOUNDED = _code("83ec18 8b4c241c 894c2404 8b448c08 03442404 83c418 c3")
# ... masked by 7: arr[0..7] leaves the 16-byte array.
WIDE = _code("83ec18 8b4c241c 894c2404 83e107 8b448c08 03442404 83c418 c3")
# 0: sub esp,0x18 / 3: mov ecx,[esp+0x1c] / 7: xor eax,eax / 9: cmp ecx,4 / 12: jae 18
# 14: mov eax,[esp+ecx*4+8] / 18: add esp,0x18 / 21: ret: i < 4 ? arr[i] : 0.
GUARDED = _code("83ec18 8b4c241c 33c0 83f904 7304 8b448c08 83c418 c3")
# ... guarded by i < 5: arr[4] is past the array on a feasible path.
GUARDED_WIDE = _code("83ec18 8b4c241c 33c0 83f905 7304 8b448c08 83c418 c3")
ARRAY_FRAME = FrameFacts(True, base=-24, params_end=8)
ARRAY_OBJECTS = (("arr", -16, 16), ("i", 4, 4))


def test_a_masked_index_into_a_local_array_is_proved() -> None:
    # a14 alone refuses any stack access at a variable offset.
    with pytest.raises(ByteIdentityError, match=r"variable offset from ESP, which a14"):
        _prove(MASKED_D, MASKED_P, ARRAY_FRAME, _objects(*ARRAY_OBJECTS), indexed=False)
    proof = _prove(MASKED_D, MASKED_P, ARRAY_FRAME, _objects(*ARRAY_OBJECTS), indexed=True)
    summary = proof_summary(proof)
    assert summary["frame_objects"] == [[-16, 16]]  # the indexed array escapes: memory
    assert summary["frame_object_indexes"] is True
    assert summary["assumptions"] == ["a14", "a16"]


def test_an_a14_proof_pins_no_index() -> None:
    # Without the indexed pass a14's pins are as before.
    proof = _prove(MASKED_D, MASKED_D, ARRAY_FRAME, _objects(*ARRAY_OBJECTS), indexed=True)
    assert proof_summary(proof)["frame_object_indexes"] is True
    rep_d = _code("83ec1c 57 8b4c2424 894c2408 8d7c2410 33c0 f3aa 8b442408 5f 83c41c c3")
    plain = proof_summary(
        _prove(
            rep_d,
            rep_d,
            FrameFacts(True, base=-28, params_end=8),
            _objects(("buf", -16, 16), ("n", 4, 4)),
            indexed=False,
        )
    )
    assert "frame_object_indexes" not in plain and plain["assumptions"] == ["a14"]


def test_an_index_with_no_bound_is_refused() -> None:
    with pytest.raises(ByteIdentityError, match=r"whose index no path condition"):
        _prove(UNBOUNDED, UNBOUNDED, ARRAY_FRAME, _objects(*ARRAY_OBJECTS), indexed=True)


def test_an_index_range_that_leaves_the_object_is_refused() -> None:
    with pytest.raises(ByteIdentityError, match=r"lies in no single frame object"):
        _prove(WIDE, WIDE, ARRAY_FRAME, _objects(*ARRAY_OBJECTS), indexed=True)


def test_a_path_condition_bounds_an_index() -> None:
    proof = _prove(GUARDED, GUARDED, ARRAY_FRAME, _objects(*ARRAY_OBJECTS), indexed=True)
    assert proof_summary(proof)["frame_objects"] == [[-16, 16]]
    with pytest.raises(ByteIdentityError, match=r"lies in no single frame object"):
        _prove(GUARDED_WIDE, GUARDED_WIDE, ARRAY_FRAME, _objects(*ARRAY_OBJECTS), indexed=True)


# int arr[4] at ESP0-16: 0: sub esp,0x10 / 3: xor eax,eax / 5: xor ecx,ecx
# 7: add eax,[esp+ecx*4] / 10: inc ecx / 11: cmp ecx,4 / 14: jb 7 / 16: add esp,0x10 / 19: ret
LOOP_D = _code("83ec10 33c0 33c9 03048c 41 83f904 72f7 83c410 c3")
# ... counting in EDX: 5: xor edx,edx / 7: add eax,[esp+edx*4] / 10: inc edx / 11: cmp edx,4
LOOP_P = _code("83ec10 33c0 33d2 030494 42 83fa04 72f7 83c410 c3")
# ... compared with 5: the counter reaches 4, and arr[4] is past the array.
LOOP_WIDE = _code("83ec10 33c0 33c9 03048c 41 83f905 72f7 83c410 c3")
LOOP_FRAME = FrameFacts(True, base=-16, params_end=4)


def test_a_loop_counter_s_range_is_carried_by_the_relation() -> None:
    # At the loop head the counter is a class of the relation, 0 from the
    # entry and v + 1 < 4 from the back edge: its range [0, 3] bounds the
    # index there.
    proof = _prove(LOOP_D, LOOP_P, LOOP_FRAME, _objects(("arr", -16, 16)), indexed=True)
    head = proof.relations[(7, 7)]
    counter = next(cls for cls in head.classes if ("D", ("r", "ecx")) in cls.members and cls.bounds)
    assert ("P", ("r", "edx")) in counter.members and counter.bounds == (0, 3)
    with pytest.raises(ByteIdentityError, match=r"lies in no single frame object"):
        _prove(LOOP_WIDE, LOOP_WIDE, LOOP_FRAME, _objects(("arr", -16, 16)), indexed=True)


def _relation(*classes: ValueClass) -> Relation:
    facts = SideFacts(0, ("depth", 0))
    return Relation(frozenset(classes), facts, facts)


MEMBERS = frozenset({("D", ("r", "ecx")), ("P", ("r", "edx"))})


def test_a_meet_takes_the_hull_and_widens_a_growing_range_away() -> None:
    zero = ValueClass(MEMBERS, lin(0), "lin")
    grown = meet(_relation(zero), _relation(ValueClass(MEMBERS, None, "lin", (1, 3))), "x")
    (cls,) = grown.classes
    assert cls.bounds == (0, 3) and cls.widened == 1
    relation = grown
    for high in range(4, 4 + MAX_WIDENINGS):
        relation = meet(relation, _relation(ValueClass(MEMBERS, None, "lin", (0, high))), "x")
    (cls,) = relation.classes
    assert cls.bounds is None  # widened away: the fixpoint settles
    # A class with no range on one side keeps none.
    unbounded = meet(_relation(zero), _relation(ValueClass(MEMBERS, None, "lin")), "x")
    assert next(iter(unbounded.classes)).bounds is None


def test_the_final_pass_checks_each_range() -> None:
    target = _relation(ValueClass(MEMBERS, None, "lin", (0, 3)))
    assert implies(_relation(ValueClass(MEMBERS, None, "lin", (1, 2))), target) is None
    assert implies(_relation(ValueClass(MEMBERS, lin(3), "lin")), target) is None
    assert "within its range" in str(
        implies(_relation(ValueClass(MEMBERS, None, "lin", (0, 4))), target)
    )
    assert "within its range" in str(implies(_relation(ValueClass(MEMBERS, None, "lin")), target))


# --- 3. locals whose address has not left (a16) ------------------------------------------

# int arr[4] at ESP0-16, p the parameter: arr[0] = 0; arr[1] = *p; g(arr).
# 0: sub esp,0x10 / 3: mov ecx,[esp+0x14] / 7: mov dword [esp],0 / 14: mov eax,[ecx]
# 16: mov [esp+4],eax / 20: lea edx,[esp] / 23: push edx / 24: call _g / 29: add esp,4
# 32: add esp,0x10 / 35: ret
FRESH_D = _code(
    "83ec10 8b4c2414 c7042400000000 8b01 89442404 8d1424 52 e800000000 83c404 83c410 c3"
)
# ... reading *p before the store to arr[0]: 7: mov eax,[ecx] / 9: mov dword [esp],0
FRESH_P = _code(
    "83ec10 8b4c2414 8b01 c7042400000000 89442404 8d1424 52 e800000000 83c404 83c410 c3"
)
FRESH_RELOCATIONS = {25: ("rel32", "_g")}
# g(arr) first, then arr[0] = 0 and return *p: arr's address has left, so p may
# point into it, and the load must come after the store.
# 0: sub esp,0x10 / 3: lea eax,[esp] / 6: push eax / 7: call _g / 12: add esp,4
# 15: mov ecx,[esp+0x14] / 19: mov dword [esp],0 / 26: mov eax,[ecx] / 28: add esp,0x10 / 31: ret
EXPOSED_D = _code("83ec10 8d0424 50 e800000000 83c404 8b4c2414 c7042400000000 8b01 83c410 c3")
# ... reading *p before the store: 19: mov eax,[ecx] / 21: mov dword [esp],0
EXPOSED_P = _code("83ec10 8d0424 50 e800000000 83c404 8b4c2414 8b01 c7042400000000 83c410 c3")
EXPOSED_RELOCATIONS = {8: ("rel32", "_g")}
FRESH_FRAME = FrameFacts(True, base=-16, params_end=8)
FRESH_OBJECTS = (("arr", -16, 16), ("p", 4, 4))


def test_a_load_through_a_pointer_does_not_depend_on_stores_to_a_fresh_local() -> None:
    # a14 alone keeps the store to arr[0] as a dependency of *p's load in the
    # donor, not in the replacement, so g sees different memory.
    with pytest.raises(ByteIdentityError, match=r"make different calls"):
        _prove(
            FRESH_D,
            FRESH_P,
            FRESH_FRAME,
            _objects(*FRESH_OBJECTS),
            indexed=False,
            relocations=FRESH_RELOCATIONS,
        )
    proof = _prove(
        FRESH_D,
        FRESH_P,
        FRESH_FRAME,
        _objects(*FRESH_OBJECTS),
        indexed=True,
        relocations=FRESH_RELOCATIONS,
    )
    assert proof_summary(proof)["frame_objects"] == [[-16, 16]]


def test_after_its_address_leaves_a_local_may_alias_a_pointer() -> None:
    with pytest.raises(ByteIdentityError, match=r"eax differs at the return"):
        _prove(
            EXPOSED_D,
            EXPOSED_P,
            FRESH_FRAME,
            _objects(*FRESH_OBJECTS),
            indexed=True,
            relocations=EXPOSED_RELOCATIONS,
        )


# --- 4. x87 intrinsic dispatchers (a17) --------------------------------------------------

# A dispatcher's body written for these tests: 0: mov edx,__OP_FMODjmptab
# 5: jmp __cintrindisp2 / 10: fxch st(1) / 12: fprem / 14: fnstsw ax / 16: sahf
# 17: jp 12 / 19: fstp st(1) / 21: ret (the tail the dispatcher calls back).
FMOD = _code("ba00000000 e900000000 d9c9 d9f8 dfe0 9e 7af9 ddd9 c3")
# The dispatcher it jumps to: it reads a global and branches on it.
DISPATCH = _code("833d0000000000 7401 c3 c3")
DISPATCH_BODY = HelperCode("__cintrindisp2", DISPATCH, "0" * 64, {2: "__matherr_flag"})


def _fmod(
    code: bytes = FMOD,
    relocations: dict[int, Any] | None = None,
    linked: dict[str, HelperCode] | None = None,
) -> HelperCode:
    return HelperCode(
        "__CIfmod",
        code,
        "1" * 64,
        relocations
        if relocations is not None
        else {1: "__OP_FMODjmptab", 6: ("rel32", "__cintrindisp2")},
        linked if linked is not None else {"__cintrindisp2": DISPATCH_BODY},
    )


def test_an_intrinsic_dispatcher_is_recognised_by_its_form() -> None:
    assert x87_intrinsic_arity(_fmod()) == 2
    unary = _fmod(
        relocations={1: "__OP_SINjmptab", 6: ("rel32", "__cintrindisp1")},
        linked={"__cintrindisp1": DISPATCH_BODY},
    )
    assert x87_intrinsic_arity(unary) == 1
    assert x87_intrinsic_arity(_fmod(linked={})) is None  # the dispatcher is not resolved
    other = {1: "__OP_FMODjmptab", 6: ("rel32", "__other")}
    assert x87_intrinsic_arity(_fmod(relocations=other, linked={"__other": DISPATCH_BODY})) is None
    assert x87_intrinsic_arity(_fmod(code=_code("90") + FMOD[1:])) is None
    assert x87_intrinsic_arity(_fmod(code=FMOD[:6] + _code("04") + FMOD[7:])) is None


def test_the_form_needs_an_op_table() -> None:
    assert (
        x87_intrinsic_arity(_fmod(relocations={1: "_table", 6: ("rel32", "__cintrindisp2")}))
        is None
    )


# 0: fld dword [esp+4] / 4: fld dword [esp+8] / 8: call __CIfmod / 13: ret:
# fmod(a, b) of two float parameters.
CALL_D = _code("d9442404 d9442408 e800000000 c3")
# ... loading b first and exchanging: 8: fxch st(1) / 10: call __CIfmod / 15: ret
CALL_P = _code("d9442408 d9442404 d9c9 e800000000 c3")
# ... with the operands the other way round: fmod(b, a).
CALL_SWAPPED = _code("d9442408 d9442404 e800000000 c3")
# ... with a third value on the stack: 0: fld [esp+4] / 4: fld [esp+4] / 8: fld [esp+8]
# 12: call __CIfmod / 17: fstp st(1) / 19: ret
CALL_DEEP = _code("d9442404 d9442404 d9442408 e800000000 ddd9 c3")


def _prove_call(
    donor: bytes, image: bytes, donor_call: int, image_call: int, helper: HelperCode
) -> Any:
    return prove_function(
        donor,
        {donor_call: ("rel32", "__CIfmod")},
        image,
        {image_call: ("rel32", "__CIfmod")},
        {},
        "fixture",
        helpers={"__CIfmod": helper},
    )


def test_a_call_to_an_intrinsic_dispatcher_is_an_event_of_its_operands() -> None:
    proof = _prove_call(CALL_D, CALL_P, 9, 11, _fmod())
    assert proof.returns == 1
    with pytest.raises(ByteIdentityError, match=r"make different calls"):
        _prove_call(CALL_D, CALL_SWAPPED, 9, 9, _fmod())


def test_without_the_dispatcher_form_its_body_runs_and_refuses() -> None:
    plain = _fmod(relocations={1: "_table", 6: ("rel32", "__cintrindisp2")})
    with pytest.raises(ByteIdentityError, match=r"branches on a value that is not constant"):
        _prove_call(CALL_D, CALL_D, 9, 9, plain)


def test_an_intrinsic_needs_exactly_its_operands_on_the_stack() -> None:
    with pytest.raises(ByteIdentityError, match=r"takes 2 x87 operands, and is called with 3"):
        _prove_call(CALL_DEEP, CALL_DEEP, 13, 13, _fmod())


def test_a_record_pins_the_intrinsics_and_a17() -> None:
    summary = {"frame": "shared", "assumptions": ["a14"]}
    pinned = pin_x87_intrinsics(summary, {"__CIfmod": _fmod(), "__ftol": DISPATCH_BODY})
    assert pinned["x87_intrinsics"] == ["__CIfmod"]
    assert pinned["assumptions"] == ["a14", "a17"]
    assert pin_x87_intrinsics(summary, {"__ftol": DISPATCH_BODY}) is summary
    assert pin_x87_intrinsics({}, {"__CIfmod": _fmod()})["assumptions"] == ["a17"]
