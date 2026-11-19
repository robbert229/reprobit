"""Instructions whole-function proofs admit beyond PR #32's closed set.

Whole-function proofs (`prove_function`) over hand-encoded IA-32 (each listing
in the comment above it, assembled with GNU as and checked with objdump):

1. ``fiadd fimul ficom ficomp fisub fisubr fidiv fidivr`` m32int and m16int:
   the integer converts exactly, so the operand is the term ``fild`` of the
   same load gives.
2. ``shl``/``shr``/``sar`` by CL (and the 8- and 16-bit shifts): the flags are
   functions of the value, the masked count and the flag before, so a count
   of zero is never assumed away; CF of a narrow shift by CL and OF are
   undefined.
3. ``adc``/``sbb``: the carry is the canonical CF bit, so ``sbb r, r`` is
   ``-CF``, exactly as ``setb; movzx; neg``.
4. Byte-wide ``not``, ``neg``, ``mul``, ``imul``, ``div`` and ``idiv``, and
   ``movzx``/``movsx`` into a 16-bit register.
5. An x87 instruction after a call whose x87 return count the donor's
   discipline leaves open: one proof per consistent case
   (`region_x87.x87_return_cases`), and an import slot's count.

Region proofs still refuse every one of these forms.
"""

from __future__ import annotations

from typing import Any

import pytest

from reprobit.binary import ByteIdentityError
from reprobit.classic.function_validation import FrameFacts, ValidationProof, prove_function
from reprobit.classic.region_simulation import simulate_region
from reprobit.classic.region_x87 import x87_return_cases, x87_stack_solution
from reprobit.classic.relational import ia32_relational_flow_walk


def _code(text: str) -> bytes:
    return bytes.fromhex(text.replace(" ", ""))


def _prove(
    donor: bytes,
    image: bytes,
    *,
    relocations: dict[int, Any] | None = None,
    image_relocations: dict[int, Any] | None = None,
    x87: dict[str, int] | None = None,
    frame: FrameFacts | None = None,
) -> ValidationProof:
    return prove_function(
        donor,
        relocations or {},
        image,
        image_relocations if image_relocations is not None else relocations or {},
        x87 or {},
        "fixture",
        private_frame=frame,
    )


# --- 1. x87 arithmetic on an integer in memory -----------------------------------------

# 0: fild dword [esp+4] / 4: fiadd dword [esp+8] / 8: ret
FIADD_D = _code("db442404 da442408 c3")
# 0: fild dword [esp+8] / 4: fild dword [esp+4] / 8: faddp st(1),st / 10: ret
FIADD_P = _code("db442408 db442404 dec1 c3")
# 0: fild dword [esp+4] / 4: fiadd word [esp+8] / 8: ret
FIADD_M16 = _code("db442404 de442408 c3")
# 0: fld dword [esp+4] / 4: fidiv dword [esp+8] / 8: ret
FIDIV_D = _code("d9442404 da742408 c3")
# 0: fld dword [esp+4] / 4: fild dword [esp+8] / 8: fdivp st(1),st / 10: ret
FIDIV_P = _code("d9442404 db442408 def9 c3")
# 0: fld dword [esp+4] / 4: fidivr dword [esp+8] / 8: ret
FIDIVR = _code("d9442404 da7c2408 c3")
# 0: fld dword [esp+4] / 4: ficomp dword [esp+8] / 8: fnstsw ax / 10: test ah,0x41
# 13: jne 21 / 15: mov eax,1 / 20: ret / 21: xor eax,eax / 23: ret
FICOM_D = _code("d9442404 da5c2408 dfe0 f6c441 7506 b801000000 c3 31c0 c3")
# 0: fild dword [esp+8] / 4: fld dword [esp+4] / 8: fcompp / 10: fnstsw ax
# 12: test ah,0x41 / 15: jne 23 / 17: mov eax,1 / 22: ret / 23: xor eax,eax / 25: ret
FICOM_P = _code("db442408 d9442404 ded9 dfe0 f6c441 7506 b801000000 c3 31c0 c3")


def test_fiadd_m32_is_fild_then_faddp() -> None:
    assert _prove(FIADD_D, FIADD_P).returns == 1


def test_fidiv_m32_divides_st0_by_the_converted_integer() -> None:
    assert _prove(FIDIV_D, FIDIV_P).returns == 1


def test_ficomp_m32_compares_with_the_converted_integer() -> None:
    assert _prove(FICOM_D, FICOM_P).returns == 2


def test_an_integer_operand_of_another_width_is_refused() -> None:
    # The arithmetic is an exception event in the footprint, over its operands.
    with pytest.raises(ByteIdentityError, match="access different memory"):
        _prove(FIADD_D, FIADD_M16)


def test_the_reversed_integer_division_is_refused() -> None:
    with pytest.raises(ByteIdentityError, match="access different memory"):
        _prove(FIDIV_D, FIDIVR)


def test_an_integer_operand_at_another_address_is_refused() -> None:
    other = _code("db442404 da44240c c3")  # fiadd dword [esp+12]
    with pytest.raises(ByteIdentityError, match="access different memory"):
        _prove(FIADD_D, other)


# --- 2. shifts by CL ---------------------------------------------------------------------

# 0: mov ecx,[esp+8] / 4: mov eax,[esp+4] / 8: shl eax,cl / 10: ret
SHL_CL_D = _code("8b4c2408 8b442404 d3e0 c3")
# 0: mov eax,[esp+4] / 4: mov ecx,[esp+8] / 8: shl eax,cl / 10: ret
SHL_CL_P = _code("8b442404 8b4c2408 d3e0 c3")
# 0: mov ecx,[esp+8] / 4: mov eax,[esp+4] / 8: shl eax,cl / 10: je 17 / 12: mov eax,1 / 17: ret
ZF_FLAG = _code("8b4c2408 8b442404 d3e0 7405 b801000000 c3")
# ... with 10: test eax,eax before the je (ZF of the result even when CL is 0).
ZF_TEST = _code("8b4c2408 8b442404 d3e0 85c0 7405 b801000000 c3")
# 0: mov ecx,3 / 5: mov eax,[esp+4] / 9: shl eax,cl / 11: je 18 / 13: mov eax,1 / 18: ret
CONST_CL = _code("b903000000 8b442404 d3e0 7405 b801000000 c3")
# ... with 9: shl eax,3 (12: je 19).
CONST_IMM = _code("b903000000 8b442404 c1e003 7405 b801000000 c3")
# 0: mov ecx,[esp+8] / 4: mov eax,[esp+4] / 8: shr al,cl / 10: jb 17 / 12: mov eax,1 / 17: ret
BYTE_CF = _code("8b4c2408 8b442404 d2e8 7205 b801000000 c3")
# 0: mov ecx,[esp+8] / 4: mov eax,[esp+4] / 8: shl eax,cl / 10: jo 17 / 12: mov eax,1 / 17: ret
OF_CL = _code("8b4c2408 8b442404 d3e0 7005 b801000000 c3")
# 0: mov ecx,[esp+8] / 4: mov eax,[esp+4] / 8: shr al,cl / 10: movzx eax,al / 13: ret
SHR8_D = _code("8b4c2408 8b442404 d2e8 0fb6c0 c3")
# The loads in the other order.
SHR8_P = _code("8b442404 8b4c2408 d2e8 0fb6c0 c3")
# 0: mov edx,[esp+4] / 4: shr dx,1 / 7: mov eax,edx / 9: ret
SHR16_D = _code("8b542404 66d1ea 89d0 c3")
# 0: mov eax,[esp+4] / 4: shr ax,1 / 7: ret
SHR16_P = _code("8b442404 66d1e8 c3")


def test_a_shift_by_cl_under_another_schedule_is_proved() -> None:
    assert _prove(SHL_CL_D, SHL_CL_P).returns == 1


def test_zf_after_a_shift_by_cl_is_one_function_of_value_count_and_prior_flag() -> None:
    assert _prove(ZF_FLAG, ZF_FLAG).returns == 2


def test_zf_after_a_shift_by_a_possibly_zero_count_is_not_the_result_test() -> None:
    # With CL = 0 the shift leaves ZF as it was, so the je of one version and
    # the test-then-je of the other can disagree.
    with pytest.raises(ByteIdentityError, match="differs at the return"):
        _prove(ZF_FLAG, ZF_TEST)


def test_a_constant_cl_is_the_constant_count_shift() -> None:
    assert _prove(CONST_CL, CONST_IMM).returns == 2


def test_cf_of_a_byte_shift_by_cl_is_undefined() -> None:
    # A masked count of 8 to 31 leaves CF undefined at 8 bits: even the same
    # code twice is refused when it branches on it.
    with pytest.raises(ByteIdentityError, match="differs at the return"):
        _prove(BYTE_CF, BYTE_CF)


def test_of_after_a_shift_by_cl_is_undefined() -> None:
    with pytest.raises(ByteIdentityError, match="differs at the return"):
        _prove(OF_CL, OF_CL)


def test_a_byte_shift_by_cl_is_proved() -> None:
    assert _prove(SHR8_D, SHR8_P).returns == 1


def test_a_16_bit_shift_keeps_the_upper_half() -> None:
    assert _prove(SHR16_D, SHR16_P).returns == 1


# --- 3. adc and sbb ----------------------------------------------------------------------

# 0: mov eax,[esp+4] / 4: cmp eax,[esp+8] / 8: sbb eax,eax (1B C0, MSVC's form) / 10: ret
SBB_D = _code("8b442404 3b442408 1bc0 c3")
# 0: mov eax,[esp+4] / 4: cmp eax,[esp+8] / 8: setb al / 11: movzx eax,al / 14: neg eax / 16: ret
SBB_P = _code("8b442404 3b442408 0f92c0 0fb6c0 f7d8 c3")
# ... with 8: setae al.
SBB_NOT = _code("8b442404 3b442408 0f93c0 0fb6c0 f7d8 c3")
# 0: mov eax,[esp+4] / 4: cmp eax,[esp+8] / 8: sbb eax,eax / 10: sbb eax,-1 / 13: ret
STRCMP_D = _code("8b442404 3b442408 19c0 83d8ff c3")
# 0: mov eax,[esp+4] / 4: cmp eax,[esp+8] / 8: setb al / 11: movzx eax,al / 14: add eax,eax
# 16: neg eax / 18: inc eax / 19: ret  (1 - 2 CF)
STRCMP_P = _code("8b442404 3b442408 0f92c0 0fb6c0 01c0 f7d8 40 c3")
# 0: mov eax,[esp+4] / 4: cmp eax,[esp+8] / 8: sbb eax,eax / 10: je 17 / 12: mov eax,5 / 17: ret
SBB_ZF_D = _code("8b442404 3b442408 19c0 7405 b805000000 c3")
# ... with 10: test eax,eax before the je.
SBB_ZF_P = _code("8b442404 3b442408 19c0 85c0 7405 b805000000 c3")
# 0: mov ecx,[esp+4] / 4: neg ecx / 6: sbb ecx,ecx / 8: and ecx,-9 / 11: add ecx,0x24
# 14: mov eax,ecx / 16: ret
NEG_SBB_D = _code("8b4c2404 f7d9 19c9 83e1f7 83c124 89c8 c3")
# 0: mov eax,[esp+4] / 4: neg eax / 6: sbb eax,eax / 8: and eax,-9 / 11: add eax,0x24 / 14: ret
NEG_SBB_P = _code("8b442404 f7d8 19c0 83e0f7 83c024 c3")
# 0: mov ecx,[esp+8] / 4: mov eax,[esp+4] / 8: shr al,cl / 10: sbb eax,eax / 12: ret
SBB_UNDEF = _code("8b4c2408 8b442404 d2e8 19c0 c3")
# 0: mov eax,[esp+4] / 4: add eax,[esp+8] / 8: adc eax,0 / 11: ret
ADC_D = _code("8b442404 03442408 83d000 c3")
# The sum's operands loaded the other way round.
ADC_P = _code("8b442408 03442404 83d000 c3")


def test_sbb_of_a_register_with_itself_is_minus_cf() -> None:
    assert _prove(SBB_D, SBB_P).returns == 1


def test_sbb_of_a_register_with_itself_is_not_minus_not_cf() -> None:
    with pytest.raises(ByteIdentityError, match="eax differs at the return"):
        _prove(SBB_D, SBB_NOT)


def test_sbb_of_a_register_with_itself_keeps_cf() -> None:
    # The inline strcmp tail: sbb eax,eax; sbb eax,-1 is 1 - 2 CF.
    assert _prove(STRCMP_D, STRCMP_P).returns == 1


def test_zf_after_sbb_follows_its_result() -> None:
    assert _prove(SBB_ZF_D, SBB_ZF_P).returns == 2


def test_the_neg_sbb_idiom_under_another_register_is_proved() -> None:
    assert _prove(NEG_SBB_D, NEG_SBB_P).returns == 1


def test_sbb_of_an_undefined_carry_is_refused() -> None:
    with pytest.raises(ByteIdentityError, match="eax differs at the return"):
        _prove(SBB_UNDEF, SBB_UNDEF)


def test_adc_after_a_commuted_add_is_proved() -> None:
    # An add names its operands sorted, so both carries are one term.
    assert _prove(ADC_D, ADC_P).returns == 1


# --- 4. byte-wide not, neg, multiply and divide; movzx into 16 bits ---------------------

# 0: mov ecx,[esp+4] / 4: and cl,3 / 7: neg cl / 9: sbb ecx,ecx / 11: and ecx,4
# 14: mov eax,ecx / 16: ret
NEGCL_D = _code("8b4c2404 80e103 f6d9 19c9 83e104 89c8 c3")
# 0: mov eax,[esp+4] / 4: and al,3 / 6: neg al / 8: sbb eax,eax / 10: and eax,4 / 13: ret
NEGCL_P = _code("8b442404 2403 f6d8 19c0 83e004 c3")
# 0: mov eax,[esp+4] / 4: not al / 6: movzx eax,al / 9: ret
NOT8_D = _code("8b442404 f6d0 0fb6c0 c3")
# 0: mov eax,[esp+4] / 4: xor al,0xff / 6: movzx eax,al / 9: ret
NOT8_P = _code("8b442404 34ff 0fb6c0 c3")
# 0: mov al,[esp+4] / 4: mul byte [esp+8] / 8: movzx eax,ax / 11: ret
MUL8_D = _code("8a442404 f6642408 0fb7c0 c3")
# 0: mov al,[esp+8] / 4: mul byte [esp+4] / 8: movzx eax,ax / 11: ret
MUL8_P = _code("8a442408 f6642404 0fb7c0 c3")
# 0: mov al,[esp+8] / 4: imul byte [esp+4] / 8: movzx eax,ax / 11: ret
IMUL8_P = _code("8a442408 f66c2404 0fb7c0 c3")
# 0: movzx eax,word [esp+4] / 5: div byte [esp+8] / 9: movzx eax,al / 12: ret
DIV8_D = _code("0fb7442404 f6742408 0fb6c0 c3")
# 0: movzx eax,word [esp+4] / 5: mov cl,[esp+8] / 9: div cl / 11: movzx eax,al / 14: ret
DIV8_P = _code("0fb7442404 8a4c2408 f6f1 0fb6c0 c3")
# 0: movzx eax,word [esp+4] / 5: idiv byte [esp+8] / 9: movzx eax,al / 12: ret
IDIV8 = _code("0fb7442404 f67c2408 0fb6c0 c3")
# 0: mov eax,[esp+4] / 4: movzx ax,al / 8: ret
MOVZX16_D = _code("8b442404 660fb6c0 c3")
# 0: mov ecx,[esp+4] / 4: mov eax,ecx / 6: movzx ax,cl / 10: ret
MOVZX16_P = _code("8b4c2404 89c8 660fb6c1 c3")
# 0: mov eax,[esp+4] / 4: movsx ax,al / 8: ret
MOVSX16 = _code("8b442404 660fbec0 c3")


def test_neg_of_a_byte_sets_cf_for_sbb() -> None:
    assert _prove(NEGCL_D, NEGCL_P).returns == 1


def test_not_of_a_byte_is_xor_with_ff() -> None:
    assert _prove(NOT8_D, NOT8_P).returns == 1


def test_a_byte_multiply_commutes() -> None:
    assert _prove(MUL8_D, MUL8_P).returns == 1


def test_the_signed_and_unsigned_byte_products_differ() -> None:
    with pytest.raises(ByteIdentityError, match="eax differs at the return"):
        _prove(MUL8_D, IMUL8_P)


def test_a_byte_divide_by_a_register_or_memory_is_one_division() -> None:
    assert _prove(DIV8_D, DIV8_P).returns == 1


def test_the_signed_and_unsigned_byte_divisions_differ() -> None:
    with pytest.raises(ByteIdentityError, match="access different memory"):
        _prove(DIV8_D, IDIV8)


def test_movzx_into_a_16_bit_register_keeps_the_upper_half() -> None:
    assert _prove(MOVZX16_D, MOVZX16_P).returns == 1


def test_movsx_and_movzx_into_16_bits_differ() -> None:
    with pytest.raises(ByteIdentityError, match="eax differs at the return"):
        _prove(MOVZX16_D, MOVSX16)


# --- 5. x87 after a call whose return count is open ------------------------------------

# 0: push 0 / 2: call _g / 7: add esp,4 / 10: mov eax,[esp+4] / 14: fld dword [eax]
# 16: fmul st,st(0) (D8 C8) / 18: fstp dword [eax] / 20: ret
CASE_D = _code("6a00 e800000000 83c404 8b442404 d900 d8c8 d918 c3")
# ... with 16: fmul st(0),st (DC C8).
CASE_P = _code("6a00 e800000000 83c404 8b442404 d900 dcc8 d918 c3")
CASE_CALLS = {3: ("rel32", "_g")}
# 0: cmp dword [esp+4],0 / 5: je 14 / 7: call _f / 12: jmp 19 / 14: call _g / 19: ret
JOIN = _code("837c240400 7407 e800000000 eb05 e800000000 c3")
# 0: call [__imp__g@0] / 6: mov eax,[esp+4] / 10: fld dword [eax] / 12: fmul st,st(0)
# 14: fstp dword [eax] / 16: ret
IMPORT_D = _code("ff1500000000 8b442404 d900 d8c8 d918 c3")
# ... with 12: fmul st(0),st.
IMPORT_P = _code("ff1500000000 8b442404 d900 dcc8 d918 c3")
IMPORT_SLOT = {2: "__imp__g@0"}


Walk = tuple[list[dict[str, Any]], list[list[int]], list[int], bytes, dict[int, Any]]


def _walk(code: bytes, calls: dict[int, str]) -> Walk:
    view = {at + 1: {"width": 4, "target": symbol} for at, symbol in calls.items()}
    items, successors, entries = ia32_relational_flow_walk(code, view, "walk")
    return items, successors, entries, code, view


def test_an_open_return_count_gives_one_case_per_value() -> None:
    walk = _walk(CASE_D, {2: "_g"})
    solution = x87_stack_solution(*walk)
    assert solution is not None and "_g" not in solution[1]
    assert x87_return_cases(*walk) == [{"_g": 0}, {"_g": 1}]


def test_a_case_no_consistent_assignment_has_is_dropped() -> None:
    # The join needs _f and _g to leave the same count.
    walk = _walk(JOIN, {7: "_f", 14: "_g"})
    assert x87_return_cases(*walk) == [{"_f": 0, "_g": 0}, {"_f": 1, "_g": 1}]


def test_no_case_split_above_the_limit() -> None:
    walk = _walk(JOIN, {7: "_f", 14: "_g"})
    assert x87_return_cases(*walk, limit=1) == [{}]


def test_x87_code_after_the_call_is_proved_in_every_case() -> None:
    for case in x87_return_cases(*_walk(CASE_D, {2: "_g"})) or []:
        assert _prove(CASE_D, CASE_P, relocations=CASE_CALLS, x87=case).returns == 1


def test_without_a_count_x87_code_after_the_call_is_refused() -> None:
    with pytest.raises(ByteIdentityError, match="x87 instruction after a call"):
        _prove(CASE_D, CASE_P, relocations=CASE_CALLS)


def test_a_case_that_underflows_is_refused() -> None:
    # 20: fstp st(1) / 22: ret after the store: the stack holds the callee's
    # result only in the case where it leaves one.
    donor = CASE_D[:-1] + _code("ddd9 c3")
    with pytest.raises(ByteIdentityError, match="underflow"):
        _prove(donor, donor, relocations=CASE_CALLS, x87={"_g": 0})


def test_an_import_slot_takes_its_count_in_a_function_proof() -> None:
    proof = _prove(IMPORT_D, IMPORT_P, relocations=IMPORT_SLOT, x87={"__imp__g@0": 0})
    assert proof.returns == 1
    with pytest.raises(ByteIdentityError, match="x87 instruction after a call"):
        _prove(IMPORT_D, IMPORT_P, relocations=IMPORT_SLOT)


def test_a_private_frame_proof_keeps_the_count() -> None:
    proof = _prove(
        CASE_D,
        CASE_P,
        relocations=CASE_CALLS,
        x87={"_g": 1},
        frame=FrameFacts(True, base=0, params_end=8),
    )
    assert proof.returns == 1


# --- the region simulator still refuses every new form ----------------------------------


@pytest.mark.parametrize(
    ("code", "why"),
    [
        (_code("da442408"), "x87 instruction da442408 is outside"),  # fiadd m32
        (_code("de442408"), "x87 instruction de442408 is outside"),  # fiadd m16
        (_code("d3e0"), "d3e0 is outside"),  # shl eax,cl
        (_code("d2e8"), "d2e8 is outside"),  # shr al,cl
        (_code("66d1ea"), "operand-size-prefixed"),  # shr dx,1
        (_code("1bc0"), "1bc0 is outside"),  # sbb eax,eax
        (_code("83d8ff"), "adc/sbb are outside"),  # sbb eax,-1
        (_code("f6d9"), "byte-wide not or neg"),  # neg cl
        (_code("f6642408"), "byte-wide multiply or divide"),  # mul byte [esp+8]
        (_code("660fb6c0"), "operand-size-prefixed"),  # movzx ax,al
    ],
    ids=[
        "fiadd m32",
        "fiadd m16",
        "shl cl",
        "shr r8 cl",
        "shr r16",
        "sbb r r",
        "sbb imm",
        "neg r8",
        "mul r8",
        "movzx r16",
    ],
)
def test_the_region_simulator_still_refuses(code: bytes, why: str) -> None:
    with pytest.raises(ByteIdentityError, match=why):
        simulate_region(code, 0, len(code), {}, "donor", "fixture")


def test_the_region_simulator_still_treats_an_import_count_as_unknown() -> None:
    code = IMPORT_D[:-1]
    with pytest.raises(ByteIdentityError, match="x87 instruction after a call"):
        simulate_region(
            code,
            0,
            len(code),
            IMPORT_SLOT,
            "donor",
            "fixture",
            x87_returns={"__imp__g@0": 0},
        )


def _case_summary(donor: bytes, image: bytes, calls: dict[int, str]) -> dict[str, Any]:
    from reprobit.classic.function_validation import _x87_case_proofs

    relocations = {at + 1: ("rel32", symbol) for at, symbol in calls.items()}
    return _x87_case_proofs(
        *_walk(donor, calls),
        lambda counts, note: prove_function(
            donor, relocations, image, relocations, counts, f"fixture{note}"
        ),
    )


def test_a_proof_that_needs_no_count_pins_no_cases() -> None:
    # The proof made before the case split stands, so its pins are unchanged.
    assert "x87_return_cases" not in _case_summary(SHL_CL_D, SHL_CL_P, {})


def test_a_proof_that_needs_the_open_count_pins_each_case() -> None:
    summary = _case_summary(CASE_D, CASE_P, {2: "_g"})
    cases = summary["x87_return_cases"]
    assert [case["x87_returns"] for case in cases] == [[["_g", 0]], [["_g", 1]]]
    assert all(case["proof"]["returning_pairs"] == 1 for case in cases)


def test_a_case_split_refusal_names_its_case() -> None:
    # The replacement drops the callee's value with fstp st(0): it underflows
    # when _g leaves nothing.
    image = CASE_P[:-1] + _code("ddd8 c3")
    with pytest.raises(ByteIdentityError, match="the case where _g returns 0 x87 values"):
        _case_summary(CASE_D, image, {2: "_g"})


@pytest.mark.parametrize("code", [_code("f7c801000000 c3"), _code("f6c801 c3")], ids=["F7", "F6"])
def test_the_undocumented_test_alias_is_refused(code: bytes) -> None:
    # F7 /1 is TEST r/m32, imm32 on the processor, never NEG.
    with pytest.raises(ByteIdentityError, match="test alias"):
        _prove(code, code)
    with pytest.raises(ByteIdentityError, match="test alias"):
        simulate_region(code[:-1], 0, len(code) - 1, {}, "donor", "fixture")
