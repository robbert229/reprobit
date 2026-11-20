"""The x87 memory-operands run (a19) and the in-bounds run of the indexed pass (a20).

Every function here is hand-encoded IA-32 written for these tests (each
listing in the comment above it).  The proofs run through `prove_function`
with the donor's frame objects given directly, as
`test_classic_frame_object_indexes` does; one record is authored end to end
through `build_function_validation_rewriting`.
"""

from __future__ import annotations

from pathlib import Path
from typing import Any

import pytest
from test_classic_frame_objects import T_INT4, _array, _coff, _modifier, _structure
from test_classic_function_validation import _extern_donor
from test_classic_register_bijection_reencoding_full import TARGET_SYMBOL

from reprobit.binary import ByteIdentityError
from reprobit.classic.frame_objects import (
    FrameLocal,
    FrameObjects,
    TypeSizes,
    merge_frame_objects,
)
from reprobit.classic.function_validation import (
    FrameFacts,
    Program,
    proof_summary,
    prove_function,
    x87_memory_arithmetic,
)
from reprobit.classic.region_simulation import (
    ObjectModel,
    entry_state,
    x87_memory_operands_as_loads,
)
from reprobit.classic_donors import merge_candidate_constraints
from reprobit.classic_project import ClassicDispatchMaterials, ClassicFamilyDispatcher
from reprobit.coff_format import CoffObject, coff_body
from reprobit.discovery_authoring import DiscoveryAuthoringError
from reprobit.discovery_function_validation import build_function_validation_rewriting

PROBE = Path(__file__).parent / "fixtures" / "x87_probe" / "memory_commute.out"
OBJECTS = ObjectModel({}, 8)


def _code(text: str) -> bytes:
    return bytes.fromhex(text.replace(" ", ""))


# --- 1. the probe behind a19 -------------------------------------------------------------


def _probe_lines() -> list[tuple[str, str, str, str, dict[str, str]]]:
    lines = []
    for line in PROBE.read_text().splitlines():
        width, operation, left, right, *verdicts = line.split()
        lines.append(
            (
                width,
                operation,
                left,
                right,
                dict(verdict.split("=", 1) for verdict in verdicts),
            )
        )
    return lines


def test_the_probe_ran_every_width_operation_and_operand_pair() -> None:
    lines = _probe_lines()
    assert len(lines) == 2 * 2 * 17 * 17
    assert {(width, operation) for width, operation, *_rest in lines} == {
        ("m32", "fadd"),
        ("m32", "fmul"),
        ("m64", "fadd"),
        ("m64", "fmul"),
    }


def test_without_a_nan_memory_operands_commute_and_are_their_loads_on_the_probe() -> None:
    non_nan = [line for line in _probe_lines() if "nan" not in line[2] + line[3]]
    assert len(non_nan) == 2 * 2 * 15 * 15
    for *_operands, verdicts in non_nan:
        # Under every one of the twelve control words: the 80-bit result,
        # the exception flags, SF, ES and C1.
        assert verdicts == {
            "commute-memory": "same",
            "memory-as-register": "same",
            "commute-register": "same",
        }


def test_with_a_nan_the_order_shows_on_the_probe() -> None:
    # Why a19 is an assumption: with a NaN operand the payload chosen, or DE,
    # depends on which operand was in memory.  Registers still commute.
    nan = [line for line in _probe_lines() if "nan" in line[2] + line[3]]
    assert any(verdicts["commute-memory"] != "same" for *_rest, verdicts in nan)
    assert all(verdicts["commute-register"] == "same" for *_rest, verdicts in nan)
    differing = [line for line in _probe_lines() if "DIFF" in " ".join(line[4].values())]
    assert differing and all("nan" in left + right for _w, _o, left, right, _v in differing)


# --- 2. the x87 memory-operands run ------------------------------------------------------

# float f(float a, float b): 0: fld dword [esp+4] / 4: fadd dword [esp+8] / 8: ret.
ADD_D = _code("d9442404 d8442408 c3")
# ... 0: fld dword [esp+8] / 4: fadd dword [esp+4] / 8: ret: b + a.
ADD_P = _code("d9442408 d8442404 c3")
# ... 0: fld dword [esp+8] / 4: fld dword [esp+4] / 8: faddp st(1),st / 10: ret.
ADD_REGISTERS = _code("d9442408 d9442404 dec1 c3")
# a * b and b * a: fmul dword (D8 /1).
MUL_D = _code("d9442404 d84c2408 c3")
MUL_P = _code("d9442408 d84c2404 c3")
# double f(double a, double b): fld qword [esp+4] / fadd qword [esp+0xc] / ret, and b + a.
ADD64_D = _code("dd442404 dc44240c c3")
ADD64_P = _code("dd44240c dc442404 c3")
# a - b and b - a: fsub dword (D8 /4), which a19 leaves as it is.
SUB_D = _code("d9442404 d8642408 c3")
SUB_P = _code("d9442408 d8642404 c3")
# a + b, then a branch on C0 and C3 (test ah,0x41) that the fadd left undefined:
# 8: fnstsw ax / 10: test ah,0x41 / 13: jne 19 / 15: xor eax,eax / 17: jmp 24
# 19: mov eax,1 / 24: ret.
BRANCH_D = _code("d9442404 d8442408 dfe0 f6c441 7504 33c0 eb05 b801000000 c3")
BRANCH_P = _code("d9442408 d8442404 dfe0 f6c441 7504 33c0 eb05 b801000000 c3")
FLOAT_FRAME = FrameFacts(True, base=0, params_end=12)
DOUBLE_FRAME = FrameFacts(True, base=0, params_end=20)


def _prove_x87(donor: bytes, image: bytes, *, a19: bool, frame: FrameFacts = FLOAT_FRAME) -> Any:
    return prove_function(
        donor,
        {},
        image,
        {},
        {},
        "fixture",
        private_frame=frame,
        objects=OBJECTS,
        x87_memory_operands=a19,
    )


@pytest.mark.parametrize(
    ("donor", "image", "frame"),
    [
        (ADD_D, ADD_P, FLOAT_FRAME),
        (MUL_D, MUL_P, FLOAT_FRAME),
        (ADD64_D, ADD64_P, DOUBLE_FRAME),
        (ADD_D, ADD_REGISTERS, FLOAT_FRAME),
    ],
)
def test_commuted_memory_operands_prove_only_under_a19(
    donor: bytes, image: bytes, frame: FrameFacts
) -> None:
    with pytest.raises(ByteIdentityError, match=r"differ"):
        _prove_x87(donor, image, a19=False, frame=frame)
    proof = _prove_x87(donor, image, a19=True, frame=frame)
    summary = proof_summary(proof)
    assert summary["x87_memory_operands"] is True
    assert summary["assumptions"] == ["a19"]


def test_a_proof_without_a19_pins_neither() -> None:
    summary = proof_summary(_prove_x87(ADD_D, ADD_D, a19=False))
    assert "x87_memory_operands" not in summary and "assumptions" not in summary


def test_a19_does_not_commute_a_subtraction() -> None:
    with pytest.raises(ByteIdentityError, match=r"differ"):
        _prove_x87(SUB_D, SUB_P, a19=True)
    _prove_x87(SUB_D, SUB_D, a19=True)


def test_a_condition_bit_the_commuted_operation_left_is_still_refused() -> None:
    # C0 and C3 after the fadd are a8 terms of the x87 state it ran from, and
    # ST(0) held a in one version and b in the other: the branch is refused.
    with pytest.raises(ByteIdentityError, match=r"undefined"):
        _prove_x87(BRANCH_D, BRANCH_P, a19=True)
    # The same order on both sides reads the same bit.
    _prove_x87(BRANCH_D, BRANCH_D, a19=True)


def test_a_region_proof_never_runs_a19() -> None:
    assert x87_memory_operands_as_loads(entry_state()) is False


def test_the_run_is_offered_only_where_an_add_or_multiply_has_a_memory_operand() -> None:
    assert x87_memory_arithmetic(Program(ADD_D, {}, "D", "fixture"))
    assert x87_memory_arithmetic(Program(MUL_P, {}, "P", "fixture"))
    assert x87_memory_arithmetic(Program(ADD64_D, {}, "D", "fixture"))
    assert not x87_memory_arithmetic(Program(SUB_D, {}, "D", "fixture"))
    # fld; fld; faddp: a register form only.
    assert not x87_memory_arithmetic(Program(_code("d9442404 d9442408 dec1 c3"), {}, "D", "x"))


def _float_coff(body: bytes) -> bytes:
    return _coff(body, [], types=None, locals_words=0, params=2)


def _author(donor: bytes, reference: bytes) -> Any:
    seed = _float_coff(donor)
    return build_function_validation_rewriting(
        donor=_extern_donor(),
        target_id="program",
        translation_unit_id="tu.fixture",
        build_target="program",
        symbol=TARGET_SYMBOL,
        seed_object=seed,
        donor_object=seed,
        reference_object=_float_coff(reference),
    )


def test_a_record_pins_a19_only_when_every_pass_needed_it() -> None:
    authored = _author(ADD_D, ADD_P)
    proof = authored.function.receipt.expected_values["function_validation.expected_proof"]
    assert proof["x87_memory_operands"] is True
    assert proof["assumptions"] == ["a19"]
    composed = CoffObject(authored.candidate_object)
    assert bytes(coff_body(composed, composed.function_section(TARGET_SYMBOL))) == ADD_P
    # The build re-runs the measurement from the donor and reaches the same pins.
    seed = _float_coff(ADD_D)
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


# (a + b) - a against (b + a) - b: a19 runs, and the differences still differ.
# 0: fld dword [esp+4] / 4: fadd dword [esp+8] / 8: fsub dword [esp+4] / 12: ret.
SUM_LESS_D = _code("d9442404 d8442408 d8642404 c3")
SUM_LESS_P = _code("d9442408 d8442404 d8642408 c3")


def test_a19_runs_only_where_an_add_or_multiply_has_a_memory_operand() -> None:
    with pytest.raises(DiscoveryAuthoringError) as refused:
        _author(SUB_D, SUB_P)
    assert "a19" not in str(refused.value)
    with pytest.raises(DiscoveryAuthoringError, match=r"x87 memory operands, a19"):
        _author(SUM_LESS_D, SUM_LESS_P)


# --- 3. array extents --------------------------------------------------------------------


def test_the_element_size_of_an_array_comes_from_its_element_type() -> None:
    records = (
        _array(T_INT4, 16),  # 0x1000: int[4]
        _structure(8, "P"),  # 0x1001: struct P (8 bytes)
        _array(0x1001, 32),  # 0x1002: struct P[4]
        _modifier(0x1002),  # 0x1003: const struct P[4]
        _array(0x1000, 32),  # 0x1004: int[2][4]
    )
    sizes = TypeSizes(records, "x")
    assert sizes.element_size(0x1000) == 4
    assert sizes.element_size(0x1002) == 8
    assert sizes.element_size(0x1003) == 8
    assert sizes.element_size(0x1004) == 16  # a row
    assert sizes.element_size(0x1001) == 0  # a structure is no array
    assert sizes.element_size(T_INT4) == 0
    with pytest.raises(ByteIdentityError, match=r"has elements of"):
        TypeSizes((_array(T_INT4, 6),), "x").element_size(0x1000)


def _local(name: str, start: int, size: int, element: int = 0) -> FrameLocal:
    return FrameLocal(name, start, size, 0, element)


def test_arrays_laid_over_one_another_stay_one_array_only_when_alike() -> None:
    alike = merge_frame_objects((_local("offsets", -32, 32, 8), _local("dirs", -32, 32, 8)))
    assert [(item.start, item.size, item.element) for item in alike.objects] == [(-32, 32, 8)]
    other_element = merge_frame_objects((_local("a", -32, 32, 8), _local("b", -32, 32, 4)))
    assert other_element.objects[0].element == 0
    with_scalar = merge_frame_objects((_local("a", -32, 32, 8), _local("x", -32, 4)))
    assert with_scalar.objects[0].element == 0
    longer = merge_frame_objects((_local("a", -32, 32, 8), _local("b", -32, 40, 8)))
    assert longer.objects[0].element == 0


# --- 4. the in-bounds run ----------------------------------------------------------------

# int arr[4] at ESP0-16, the slots ESP0-20 and ESP0-24 outside it; i the parameter.
# 0: sub esp,0x18 / 3: mov ecx,[esp+0x1c] / 7: mov [esp+4],ecx / 11: mov eax,[esp+ecx*4+8]
# 15: add eax,[esp+4] / 19: add esp,0x18 / 22: ret: return arr[i] + i, i unbounded.
UNBOUNDED_D = _code("83ec18 8b4c241c 894c2404 8b448c08 03442404 83c418 c3")
# ... with i's copy in ESP0-24: 7: mov [esp],ecx / 14: add eax,[esp]
UNBOUNDED_P = _code("83ec18 8b4c241c 890c24 8b448c08 030424 83c418 c3")
# ... through a pointer: 7: lea eax,[esp+ecx*4+8] / 11: mov edx,[eax] / 13: mov eax,edx
# 15: add esp,0x18 / 18: ret: int *p = &arr[i]; return *p.
POINTER_D = _code("83ec18 8b4c241c 8d448c08 8b10 8bc2 83c418 c3")
# ... read straight through the index: 7: mov eax,[esp+ecx*4+8] / 11: add esp,0x18 / 14: ret
POINTER_P = _code("83ec18 8b4c241c 8b448c08 83c418 c3")
# ... arr[i + 1] read as [esp+ecx*4+0xc]: the constant part is past the first element.
SECOND_ELEMENT = _code("83ec18 8b4c241c 894c2404 8b448c0c 03442404 83c418 c3")
# 0: sub esp,0x18 / 3: mov ecx,[esp+0x1c] / 7: lea eax,[esp+ecx*4+8] / 11: push eax
# 12: call _g / 17: add esp,4 / 20: add esp,0x18 / 23: ret: g(&arr[i]).
PASSED = _code("83ec18 8b4c241c 8d448c08 50 e800000000 83c404 83c418 c3")
# 0: sub esp,0x18 / 3: mov ecx,[esp+0x1c] / 7: lea eax,[esp+ecx*4+8]
# 11: mov edx,[esp+0x20] / 15: mov [edx],eax / 17: add esp,0x18 / 20: ret: *q = &arr[i].
STORED = _code("83ec18 8b4c241c 8d448c08 8b542420 8902 83c418 c3")
ARRAY_FRAME = FrameFacts(True, base=-24, params_end=12)


def _array_objects(element: int = 4) -> FrameObjects:
    return merge_frame_objects(
        (_local("arr", -16, 16, element), _local("i", 4, 4), _local("q", 8, 4))
    )


def _prove_indexed(
    donor: bytes,
    image: bytes,
    *,
    in_bounds: bool,
    objects: FrameObjects | None = None,
    relocations: dict[int, Any] | None = None,
) -> Any:
    return prove_function(
        donor,
        relocations or {},
        image,
        relocations or {},
        {},
        "fixture",
        private_frame=ARRAY_FRAME,
        objects=OBJECTS,
        frame_objects=objects if objects is not None else _array_objects(),
        indexed=True,
        in_bounds=in_bounds,
    )


def test_an_unbounded_index_into_an_array_proves_only_under_a20() -> None:
    with pytest.raises(ByteIdentityError, match=r"no path condition, relation range or form"):
        _prove_indexed(UNBOUNDED_D, UNBOUNDED_P, in_bounds=False)
    summary = proof_summary(_prove_indexed(UNBOUNDED_D, UNBOUNDED_P, in_bounds=True))
    assert summary["frame_objects"] == [[-16, 16]]
    assert summary["frame_object_in_bounds"] == [[-16, 16, 4]]
    assert summary["assumptions"] == ["a14", "a16", "a20"]


def test_a_pointer_to_an_element_and_the_element_read_through_the_index_meet() -> None:
    summary = proof_summary(_prove_indexed(POINTER_D, POINTER_P, in_bounds=True))
    assert summary["frame_object_in_bounds"] == [[-16, 16, 4]]


def test_a20_places_an_index_only_in_an_array() -> None:
    with pytest.raises(ByteIdentityError, match=r"not one local of array type"):
        _prove_indexed(UNBOUNDED_D, UNBOUNDED_P, in_bounds=True, objects=_array_objects(0))


def test_a20_places_an_index_only_from_the_first_element() -> None:
    with pytest.raises(ByteIdentityError, match=r"outside the first 4-byte element"):
        _prove_indexed(SECOND_ELEMENT, SECOND_ELEMENT, in_bounds=True)


def test_a20_places_an_index_only_at_a_multiple_of_the_element() -> None:
    with pytest.raises(ByteIdentityError, match=r"other than a multiple"):
        _prove_indexed(UNBOUNDED_D, UNBOUNDED_D, in_bounds=True, objects=_array_objects(8))


def test_an_address_a20_placed_never_reaches_a_callee() -> None:
    with pytest.raises(ByteIdentityError, match=r"leaves the function"):
        _prove_indexed(PASSED, PASSED, in_bounds=True, relocations={13: ("rel32", "_g")})


def test_an_address_a20_placed_is_never_stored_to_memory() -> None:
    with pytest.raises(ByteIdentityError, match=r"leaves the function"):
        _prove_indexed(STORED, STORED, in_bounds=True)
