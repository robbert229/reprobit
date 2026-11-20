"""Unsigned compares against small constants, and the 0/1 values they give.

MSVC 5.0 computes one unsigned 0/1 value several ways.  ``big = count > 1``
is ``mov ecx,1; cmp ecx,eax; sbb ecx,ecx; neg ecx`` (``[1 <u x]``) in one
compile and ``cmp eax,2; sbb eax,eax; inc eax`` (``1 - [x <u 2]``) in
another; ``!x`` is ``cmp eax,1; sbb eax,eax; neg eax``, ``neg eax; sbb
eax,eax; inc eax`` or ``test eax,eax; sete al; movzx eax,al``.  Whole-function
proofs (`prove_function`, hand-encoded IA-32 in the comment above each
listing, checked with objdump) read every such compare as one canonical atom
with a polarity (`region_simulation._ltu`), write the zero-extended
``setcc`` byte of polarity False as ``1 - bit`` (`zero_extend`), and give
``neg`` the flags of ``sub 0, x``.  Each identity is exact for every operand
value; the tests check the 8-bit form of every compare against every constant
exhaustively and the 32-bit form at its boundaries.
"""

from __future__ import annotations

from typing import Any

import pytest

from reprobit.binary import ByteIdentityError
from reprobit.classic.function_validation import ValidationProof, prove_function
from reprobit.classic.region_simulation import (
    condition,
    extract,
    lin,
    zero_extend,
)


def _code(text: str) -> bytes:
    return bytes.fromhex(text.replace(" ", ""))


def _prove(donor: bytes, image: bytes) -> ValidationProof:
    return prove_function(donor, {}, image, {}, {}, "fixture")


# 0x431780's two compiles of ``count > 1`` (count unsigned):
# 0: mov eax,[esp+4] / 4: mov ecx,1 / 9: cmp ecx,eax / 11: sbb ecx,ecx / 13: neg ecx
# 15: mov eax,ecx / 17: ret  ([1 <u x])
ABOVE_1_SBB_NEG = _code("8b442404 b901000000 3bc8 1bc9 f7d9 8bc1 c3")
# 0: mov eax,[esp+4] / 4: cmp eax,2 / 7: sbb eax,eax / 9: inc eax / 10: ret  (1 - [x <u 2])
BELOW_2_SBB_INC = _code("8b442404 83f802 1bc0 40 c3")
# 0: mov eax,[esp+4] / 4: cmp eax,1 / 7: seta al / 10: movzx eax,al / 13: ret  (not [x <=u 1])
ABOVE_1_SETA = _code("8b442404 83f801 0f97c0 0fb6c0 c3")
# 0: mov eax,[esp+4] / 4: cmp eax,2 / 7: setb al / 10: movzx eax,al / 13: ret  ([x <u 2])
BELOW_2_SETB = _code("8b442404 83f802 0f92c0 0fb6c0 c3")
# 0: mov eax,[esp+4] / 4: mov ecx,1 / 9: cmp ecx,eax / 11: sbb ecx,ecx / 13: inc ecx
# 14: mov eax,ecx / 16: ret  (1 - [1 <u x])
ABOVE_1_SBB_INC = _code("8b442404 b901000000 3bc8 1bc9 41 8bc1 c3")
# ``!x``: 0: mov eax,[esp+4] / 4: cmp eax,1 / 7: sbb eax,eax / 9: neg eax / 11: ret
NOT_CMP_1 = _code("8b442404 83f801 1bc0 f7d8 c3")
# 0: mov eax,[esp+4] / 4: test eax,eax / 6: sete al / 9: movzx eax,al / 12: ret
NOT_SETE = _code("8b442404 85c0 0f94c0 0fb6c0 c3")
# 0: mov eax,[esp+4] / 4: neg eax / 6: sbb eax,eax / 8: inc eax / 9: ret  (1 - [x != 0])
NOT_NEG = _code("8b442404 f7d8 1bc0 40 c3")
# A byte: 0: mov al,[esp+4] / 4: cmp al,1 / 6: seta al / 9: movzx eax,al / 12: ret
BYTE_ABOVE_1_SETA = _code("8a442404 3c01 0f97c0 0fb6c0 c3")
# 0: mov al,[esp+4] / 4: cmp al,2 / 6: sbb eax,eax / 8: inc eax / 9: ret
BYTE_BELOW_2_SBB_INC = _code("8a442404 3c02 1bc0 40 c3")
# A branch: 0: mov eax,[esp+4] / 4: cmp eax,1 / 7: ja 12 / 9: xor eax,eax / 11: ret
# 12: mov eax,1 / 17: ret
BRANCH_JA_1 = _code("8b442404 83f801 7703 33c0 c3 b801000000 c3")
# ... with 4: cmp eax,2 / 7: jae 12.
BRANCH_JAE_2 = _code("8b442404 83f802 7303 33c0 c3 b801000000 c3")
# Two non-constant operands: 0: mov eax,[esp+4] / 4: mov ecx,[esp+8] / 8: cmp eax,ecx
# 10: sbb eax,eax / 12: neg eax / 14: ret  ([a <u b])
BELOW_VAR = _code("8b442404 8b4c2408 3bc1 1bc0 f7d8 c3")
# 0: mov ecx,[esp+4] / 4: inc ecx / 5: mov eax,[esp+8] / 9: cmp eax,ecx / 11: sbb eax,eax
# 13: inc eax / 14: ret  (1 - [b <u a + 1], which differs from [a <u b] at a = 2**32 - 1)
NOT_BELOW_VAR_PLUS_1 = _code("8b4c2404 41 8b442408 3bc1 1bc0 40 c3")


@pytest.mark.parametrize(
    ("donor", "image"),
    [
        pytest.param(ABOVE_1_SBB_NEG, BELOW_2_SBB_INC, id="0x431780"),
        pytest.param(ABOVE_1_SETA, BELOW_2_SBB_INC, id="seta-sbb-inc"),
        pytest.param(ABOVE_1_SBB_NEG, ABOVE_1_SETA, id="sbb-neg-seta"),
        pytest.param(BELOW_2_SETB, ABOVE_1_SBB_INC, id="setb-sbb-inc"),
        pytest.param(NOT_CMP_1, NOT_SETE, id="not-cmp1-sete"),
        pytest.param(NOT_CMP_1, NOT_NEG, id="not-cmp1-neg"),
        pytest.param(NOT_SETE, NOT_NEG, id="not-sete-neg"),
        pytest.param(BYTE_ABOVE_1_SETA, BYTE_BELOW_2_SBB_INC, id="byte"),
    ],
)
def test_one_unsigned_flag_value_under_two_encodings_is_proved(donor: bytes, image: bytes) -> None:
    assert _prove(donor, image).returns == 1
    assert _prove(image, donor).returns == 1


def test_a_branch_on_above_1_meets_a_branch_on_not_below_2() -> None:
    assert _prove(BRANCH_JA_1, BRANCH_JAE_2).returns == 2


@pytest.mark.parametrize(
    ("donor", "image"),
    [
        # [x <u 2] is the negation of [1 <u x], not the same value.
        pytest.param(ABOVE_1_SBB_NEG, BELOW_2_SETB, id="above-vs-below"),
        pytest.param(ABOVE_1_SBB_NEG, ABOVE_1_SBB_INC, id="above-vs-not-above"),
        # !x is not x != 0.
        pytest.param(NOT_CMP_1, _code("8b442404 f7d8 1bc0 f7d8 c3"), id="zero-vs-nonzero"),
        # No identity relates two non-constant operands.
        pytest.param(BELOW_VAR, NOT_BELOW_VAR_PLUS_1, id="two-variables"),
    ],
)
def test_a_different_unsigned_flag_value_is_refused(donor: bytes, image: bytes) -> None:
    with pytest.raises(ByteIdentityError, match="eax differs at the return"):
        _prove(donor, image)


# --- the canonical atom, by evaluation -------------------------------------------------

X: Any = ("b", 8, ("free", "x"))
X32: Any = ("lin", 0, ((("free", "x"), 1),))


def _evaluate(atom: Any, x: int, width: int) -> bool:
    """The truth of a canonical compare atom over the one free value ``x``."""
    kind = atom[0]
    assert atom[1] == width
    if kind == "eqz":
        assert atom[2] in (X, X32)
        return x == 0
    assert kind == "ltu"
    left, right = atom[2], atom[3]
    if width == 8:
        assert left == X and right[2][0] == "k"
        return x < int(right[2][1])
    assert left == X32 and right[0] == "lin" and not right[2]
    return x < int(right[1])


def _flags(width: int, left: Any, right: Any) -> dict[str, Any]:
    names = ("cf", "pf", "af", "zf", "sf", "of")
    return {name: ("flag", name, "sub", width, left, right) for name in names}


def _compare_holds(code: int, flags: dict[str, Any], x: int, width: int) -> bool:
    decided = condition(code, flags)
    if isinstance(decided, bool):
        return decided
    atom, value = decided
    return _evaluate(atom, x, width) == value


def _truth(code: int, a: int, b: int) -> bool:
    """``jb``, ``jae``, ``jbe`` or ``ja`` after ``cmp a, b``, on the integers."""
    return {2: a < b, 3: a >= b, 6: a <= b, 7: a > b}[code]


@pytest.mark.parametrize("code", [2, 3, 6, 7])
def test_every_byte_compare_against_every_constant_keeps_its_truth(code: int) -> None:
    # jb, jae, jbe, ja after cmp x,k and cmp k,x, for all 256 x 256 pairs.
    for k in range(256):
        constant = ("b", 8, ("k", k))
        right_k, left_k = _flags(8, X, constant), _flags(8, constant, X)
        for x in range(256):
            assert _compare_holds(code, right_k, x, 8) == _truth(code, x, k), (code, "x,k", k, x)
            assert _compare_holds(code, left_k, x, 8) == _truth(code, k, x), (code, "k,x", k, x)


@pytest.mark.parametrize("code", [2, 3, 6, 7])
def test_a_32_bit_compare_against_a_constant_keeps_its_truth_at_its_boundaries(
    code: int,
) -> None:
    top = (1 << 32) - 1
    edges = sorted({e + d for e in (0, 1, 2, 3, 1 << 31, top - 1, top) for d in (-1, 0, 1)})
    values = [v for v in edges if 0 <= v <= top]
    for k in values:
        right_k, left_k = _flags(32, X32, lin(k)), _flags(32, lin(k), X32)
        for x in values:
            assert _compare_holds(code, right_k, x, 32) == _truth(code, x, k), (code, "x,k", k, x)
            assert _compare_holds(code, left_k, x, 32) == _truth(code, k, x), (code, "k,x", k, x)


def test_the_two_orders_read_one_atom() -> None:
    # jb after cmp 1,x and jae after cmp x,2: one atom, one polarity.
    assert condition(2, _flags(32, lin(1), X32)) == condition(3, _flags(32, X32, lin(2)))
    # jb after cmp x,1 is the zero test test x,x; je reads.
    zero = condition(4, {"zf": ("flag", "zf", "logic", 32, "result", X32)})
    assert condition(2, _flags(32, X32, lin(1))) == zero


def test_a_byte_of_polarity_false_is_one_minus_the_byte_and_reads_back() -> None:
    atom: Any = ("ltu", 32, X32, lin(2))
    true_byte: Any = ("b", 8, ("cc", atom, True))
    false_byte: Any = ("b", 8, ("cc", atom, False))
    widened = zero_extend(false_byte, 8)
    assert widened == lin(1, ((("zx", true_byte, 8), -1),))
    assert extract(widened, 0, 8) == false_byte
    assert extract(widened, 8, 8) == ("b", 8, ("k", 0))
    assert extract(zero_extend(true_byte, 8), 0, 8) == true_byte
