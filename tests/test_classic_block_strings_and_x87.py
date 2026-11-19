"""Block string moves, x87 transcendentals, undefined x87 condition bits and vtable pops.

Whole-function proofs (`prove_function`) over hand-encoded IA-32 (each listing
in the comment above it):

1. ``rep movs``/``rep stos`` of a count that is not a small constant is one
   event of its count, pointers, value and the memory before it.
2. ``fsin``, ``fcos``, ``fpatan`` and the other D9 forms are uninterpreted
   functions of their operands; ``fptan``/``fsincos`` are refused.
3. A condition bit an x87 instruction leaves undefined is related only to the
   bit the same instruction leaves from the same x87 state (a8).
4. A vtable call's pop is determined only where the stack relation fixes it;
   otherwise the refusal names the calls whose pops are fixed only together.
"""

from __future__ import annotations

import pytest

from reprobit.binary import ByteIdentityError
from reprobit.classic.function_validation import FrameFacts, prove_function


def _code(text: str) -> bytes:
    return bytes.fromhex(text.replace(" ", ""))


def _prove(donor, image, *, donor_relocations=None, image_relocations=None, frame=None):
    return prove_function(
        donor,
        donor_relocations or {},
        image,
        image_relocations or {},
        {},
        "fixture",
        private_frame=frame,
    )


# --- 1. block string moves ---------------------------------------------------------------

# strcpy(buffer, source) into a stack buffer, then f(buffer):
# 0: sub esp,0x40 / 3: push esi / 4: push edi / 5: mov edi,[esp+0x4c] / 9: or ecx,-1
# 12: xor eax,eax / 14: repne scasb / 16: not ecx / 18: sub edi,ecx / 20: lea edx,[esp+8]
# 24: mov eax,ecx / 26: mov esi,edi / 28: mov edi,edx / 30: shr ecx,2 / 33: rep movsd
# 35: mov ecx,eax / 37: and ecx,3 / 40: rep movsb / 42: lea eax,[esp+8] / 46: push eax
# 47: call _f / 52: add esp,4 / 55: pop edi / 56: pop esi / 57: add esp,0x40 / 60: ret
STRCPY_D = _code(
    "83ec40 56 57 8b7c244c 83c9ff 33c0 f2ae f7d1 2bf9 8d542408 8bc1 8bf7 8bfa c1e902 f3a5 "
    "8bc8 83e103 f3a4 8d442408 50 e800000000 83c404 5f 5e 83c440 c3"
)
# The same with 20: mov esi,edi / 22: mov eax,ecx / 24: lea edx,[esp+8] (rescheduled).
STRCPY_P = _code(
    "83ec40 56 57 8b7c244c 83c9ff 33c0 f2ae f7d1 2bf9 8bf7 8bc1 8d542408 8bfa c1e902 f3a5 "
    "8bc8 83e103 f3a4 8d442408 50 e800000000 83c404 5f 5e 83c440 c3"
)
# ... copying one dword fewer (30: shr ecx,2 / 33: dec ecx / 34: rep movsd ...).
STRCPY_SHORT = _code(
    "83ec40 56 57 8b7c244c 83c9ff 33c0 f2ae f7d1 2bf9 8bf7 8bc1 8d542408 8bfa c1e902 49 f3a5 "
    "8bc8 83e103 f3a4 8d442408 50 e800000000 83c404 5f 5e 83c440 c3"
)
STRCPY_CALLS = {48: ("rel32", "_f")}
# 0: mov edi,[esp+4] / 4: mov ecx,[esp+8] / 8: xor eax,eax / 10: rep stosd / 12: ret
MEMSET_D = _code("8b7c2404 8b4c2408 33c0 f3ab c3")
# The pointer and the count loaded in the other order.
MEMSET_P = _code("8b4c2408 8b7c2404 33c0 f3ab c3")
# 0: mov edx,[esp+12] / 4: mov dword [edx],1 / 10: mov edi,[esp+4] / 14: mov ecx,[esp+8]
# 18: xor eax,eax / 20: rep stosd / 22: ret
STORE_THEN_BLOCK = _code("8b54240c c70201000000 8b7c2404 8b4c2408 33c0 f3ab c3")
# ... the store after the block: 0: mov edi,[esp+4] / 4: mov ecx,[esp+8] / 8: xor eax,eax
# 10: rep stosd / 12: mov edx,[esp+12] / 16: mov dword [edx],1 / 22: ret
BLOCK_THEN_STORE = _code("8b7c2404 8b4c2408 33c0 f3ab 8b54240c c70201000000 c3")
# 0: lea edi,[esp-8] / 4: mov ecx,[esp+4] / 8: xor eax,eax / 10: rep stosd / 12: ret
BELOW_ESP = _code("8d7c24f8 8b4c2404 33c0 f3ab c3")
# 0: mov ecx,[esp+4] / 4: lea edi,[esp+ecx*4+8] / 8: xor eax,eax / 10: rep stosd / 12: ret
VARIABLE_START = _code("8b4c2404 8d7c8c08 33c0 f3ab c3")


def test_an_inline_strcpy_into_a_stack_buffer_is_proved() -> None:
    proof = _prove(
        STRCPY_D, STRCPY_P, donor_relocations=STRCPY_CALLS, image_relocations=STRCPY_CALLS
    )
    assert not proof.frame.private
    assert proof.returns == 1


def test_a_block_from_a_stack_address_takes_the_shared_frame() -> None:
    proof = _prove(
        STRCPY_D,
        STRCPY_P,
        donor_relocations=STRCPY_CALLS,
        image_relocations=STRCPY_CALLS,
        frame=FrameFacts(True, base=-0x40, params_end=8),
    )
    assert not proof.frame.private


def test_a_block_store_of_unknown_count_under_another_schedule_is_proved() -> None:
    assert _prove(MEMSET_D, MEMSET_P).returns == 1


def test_a_block_of_another_count_is_refused() -> None:
    with pytest.raises(ByteIdentityError, match="different calls or block string moves"):
        _prove(
            STRCPY_D,
            STRCPY_SHORT,
            donor_relocations=STRCPY_CALLS,
            image_relocations={49: ("rel32", "_f")},
        )


def test_a_store_moved_across_a_block_is_refused() -> None:
    with pytest.raises(ByteIdentityError, match="different calls or block string moves"):
        _prove(STORE_THEN_BLOCK, BLOCK_THEN_STORE)


def test_a_block_starting_below_esp_is_refused() -> None:
    with pytest.raises(ByteIdentityError, match="lies below ESP"):
        _prove(BELOW_ESP, BELOW_ESP)


def test_a_block_at_a_variable_stack_offset_is_refused() -> None:
    with pytest.raises(ByteIdentityError, match="variable offset"):
        _prove(VARIABLE_START, VARIABLE_START)


@pytest.mark.parametrize(
    ("code", "why"),
    [
        (_code("f3a6 c3"), "prefixed instruction"),  # repe cmpsb
        (_code("f2ab c3"), "repne stos or movs"),  # repne stosd
        (_code("fd c3"), "outside"),  # std: the direction flag stays clear
    ],
    ids=["repe cmps", "repne stos", "std"],
)
def test_string_forms_outside_the_model_are_refused(code: bytes, why: str) -> None:
    with pytest.raises(ByteIdentityError, match=why):
        _prove(code, code)


def test_the_region_simulator_still_refuses_a_block_of_unknown_count() -> None:
    from reprobit.classic.region_simulation import simulate_region

    with pytest.raises(ByteIdentityError, match="prefixed instruction"):
        simulate_region(MEMSET_D, 0, 12, {}, "donor", "fixture")


# --- 2. transcendentals --------------------------------------------------------------------

# 0: fld dword [esp+4] / 4: fsin / 6: fld dword [esp+8] / 10: fcos / 12: faddp st(1) / 14: ret
SIN_PLUS_COS = _code("d9442404 d9fe d9442408 d9ff dec1 c3")
# The cosine first: the same sum (addition is commutative).
COS_PLUS_SIN = _code("d9442408 d9ff d9442404 d9fe dec1 c3")
# ... the sine of the second parameter and the cosine of the first instead.
SIN_OF_OTHER = _code("d9442404 d9ff d9442408 d9fe dec1 c3")
# 0: fld dword [esp+4] / 4: fld dword [esp+8] / 8: fpatan / 10: ret
ATAN_D = _code("d9442404 d9442408 d9f3 c3")
# 0: fld dword [esp+8] / 4: fld dword [esp+4] / 8: fxch / 10: fpatan / 12: ret
ATAN_P = _code("d9442408 d9442404 d9c9 d9f3 c3")
# 0: fld dword [esp+4] / 4: fsin / 6: fnstsw ax / 8: test ah,4 (C2: out of range)
# 11: jne 19 / 13: mov eax,1 / 18: ret / 19: xor eax,eax / 21: ret
SIN_RANGE_D = _code("d9442404 d9fe dfe0 f6c404 7506 b801000000 c3 33c0 c3")
# The branch inverted: 11: je 16 / 13: xor eax,eax / 15: ret / 16: mov eax,1 / 21: ret
SIN_RANGE_P = _code("d9442404 d9fe dfe0 f6c404 7403 33c0 c3 b801000000 c3")


def test_sine_and_cosine_are_functions_of_their_operands() -> None:
    assert _prove(SIN_PLUS_COS, COS_PLUS_SIN).returns == 1


def test_a_partial_arctangent_is_a_function_of_its_ordered_operands() -> None:
    assert _prove(ATAN_D, ATAN_P).returns == 1


def test_the_out_of_range_bit_of_a_sine_is_one_term_on_both_sides() -> None:
    assert _prove(SIN_RANGE_D, SIN_RANGE_P).returns == 2


def test_a_sine_of_another_operand_is_refused() -> None:
    # Each transcendental is an exception event of its operand in the footprint.
    with pytest.raises(ByteIdentityError, match="access different memory"):
        _prove(SIN_PLUS_COS, SIN_OF_OTHER)


@pytest.mark.parametrize("encoding", ["d9f2", "d9fb"], ids=["fptan", "fsincos"])
def test_a_push_that_depends_on_the_operand_is_refused(encoding: str) -> None:
    code = _code(f"d9442404 {encoding} c3")
    with pytest.raises(ByteIdentityError, match="pushes a second value only when"):
        _prove(code, code)


def test_a_stack_rotation_stays_outside_the_closed_set() -> None:
    code = _code("d9442404 d9f7 c3")  # fincstp
    with pytest.raises(ByteIdentityError, match="d9f7 is outside"):
        _prove(code, code)


# --- 3. condition bits an instruction leaves undefined ------------------------------------

# 0: mov ecx,[esp+4] / 4: fld dword [ecx] / 6: fcomp dword [ecx+4] / 9: fld dword [ecx+8]
# 12: fstp dword [ecx+12] / 15: fnstsw ax / 17: test ah,0x41 / 20: jne 28
# 22: mov eax,1 / 27: ret / 28: xor eax,eax / 30: ret
# The compare's bits are read after an fld and an fstp, which Intel leaves them undefined after.
LATE_READ_D = _code("8b4c2404 d901 d85904 d94108 d9590c dfe0 f6c441 7506 b801000000 c3 33c0 c3")
# The same with the pointer in EDX.
LATE_READ_P = _code("8b542404 d902 d85a04 d94208 d95a0c dfe0 f6c441 7506 b801000000 c3 33c0 c3")
# The fld/fstp before the compare: the bits are read straight from the compare.
# 4: fld dword [edx+8] / 7: fstp dword [edx+12] / 10: fld dword [edx] / 12: fcomp dword [edx+4]
EARLY_READ_P = _code("8b542404 d94208 d95a0c d902 d85a04 dfe0 f6c441 7506 b801000000 c3 33c0 c3")
# The same store by another instruction: 9: fld dword [edx+8] / 12: fst dword [edx+12]
# 15: fstp st(0) / 17: fnstsw ax / 19: test ah,0x41 / 22: jne 30 / 24: mov eax,1 / 29: ret
# 30: xor eax,eax / 32: ret
OTHER_UNDEFINER_P = _code(
    "8b542404 d902 d85a04 d94208 d9520c ddd8 dfe0 f6c441 7506 b801000000 c3 33c0 c3"
)


def test_bits_left_undefined_by_the_same_instructions_from_the_same_state_are_related() -> None:
    assert _prove(LATE_READ_D, LATE_READ_P).returns == 2


def test_an_undefined_bit_is_never_a_compare_bit() -> None:
    with pytest.raises(ByteIdentityError, match="the donor branches on C0") as refused:
        _prove(LATE_READ_D, EARLY_READ_P)
    assert "never to a compare's" in str(refused.value)


def test_bits_another_instruction_leaves_undefined_are_refused() -> None:
    with pytest.raises(ByteIdentityError, match="the replacement branches on C0"):
        _prove(LATE_READ_D, OTHER_UNDEFINER_P)


def test_the_region_simulator_still_refuses_an_undefined_bit() -> None:
    from reprobit.classic.region_simulation import simulate_region

    with pytest.raises(ByteIdentityError, match="undefined"):
        simulate_region(LATE_READ_D, 0, 22, {}, "donor", "fixture", leave=True)


# --- 4. vtable pops -----------------------------------------------------------------------

# Two vtable calls, with a return between them on one path:
# 0: mov eax,[esp+4] / 4: push eax / 5: mov ecx,[eax] / 7: call [ecx+0x10] / 10: test eax,eax
# 12: je 25 / 14: mov eax,[esp+4] / 18: push eax / 19: mov ecx,[eax] / 21: call [ecx+0x14]
# 24: ret / 25: ret
SEPARATED_D = _code("8b442404 50 8b08 ff5110 85c0 740b 8b442404 50 8b08 ff5114 c3 c3")
# The object pointer in EDX.
SEPARATED_P = _code("8b542404 52 8b0a ff5110 85c0 740b 8b542404 52 8b0a ff5114 c3 c3")
# Two calls in a row on every path: 0: mov eax,[esp+4] / 4: push eax / 5: mov ecx,[eax]
# 7: call [ecx+0x10] / 10: mov eax,[esp+4] / 14: push eax / 15: mov ecx,[eax]
# 17: call [ecx+0x14] / 20: ret
TOGETHER = _code("8b442404 50 8b08 ff5110 8b442404 50 8b08 ff5114 c3")


def test_a_return_between_two_vtable_calls_determines_both_pops() -> None:
    from reprobit.classic.function_validation import Program

    assert Program(SEPARATED_D, {}, "D", "fixture").indirect_pops == {7: 4, 21: 4}
    assert _prove(SEPARATED_D, SEPARATED_P).returns == 2


def test_pops_fixed_only_together_are_refused_with_their_sum() -> None:
    with pytest.raises(ByteIdentityError, match=r"pop\(7\) \+ pop\(17\) = 8 bytes"):
        _prove(TOGETHER, TOGETHER)
