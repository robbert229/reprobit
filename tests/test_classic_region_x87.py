"""The region simulator's x87 model and the region-resize proof's x87 checks.

Every semantic claim the model rests on that Intel's manual leaves open to
misreading is backed by the hardware probe in ``tests/fixtures/x87_probe``
(MSVC 5.0 inline assembly with raw ``_emit`` encodings, run under Wine on
the host's x87 unit; see its README).  The tests below parse that probe's
recorded output and check the simulator against it:

- the D8/DC/DE register arithmetic forms: digit 4 computes ST(0) - ST(i),
  5 ST(i) - ST(0), 6 ST(0) / ST(i) and 7 ST(i) / ST(0), with the result in
  ST(0) for D8 and in ST(i) for DC and DE (DE then pops);
- the compares: C3 C2 C0 = 000 (greater), 001 (less), 100 (equal), 111
  (unordered), and C1 cleared, whatever C0-C3 held before;
- subtract and divide are one function of (minuend, subtrahend) and
  (dividend, divisor) whichever register holds which, NaN payloads and
  exception flags included -- the reason ``fsubr`` and ``fsub`` that compute
  the same difference meet;
- the register copies and sign operations (``fld st(i)``, ``fxch``,
  ``fst st(i)``, ``fchs``, ``fabs``, ``fld1``, ``fldz``) copy all 80 bits and
  raise no exception, even on an SNaN or a denormal, so they are no events;
- a store and reload through m32 or m64 is not the identity under any
  precision control (24, 53 or 64 bits): the register keeps a 15-bit
  exponent, so 1e30 * 1e30 is finite in a register and infinite as a float.
"""

from __future__ import annotations

import math
import re
from pathlib import Path

import pytest

from reprobit.binary import ByteIdentityError
from reprobit.classic.region_simulation import (
    FCMP_BITS,
    contradictory,
    fcc_atom,
    simulate_region,
)
from reprobit.classic.region_x87 import (
    x87_condition_liveness,
    x87_environment_exposures,
    x87_stack_depths,
)
from reprobit.classic.relational import ia32_relational_flow_walk
from reprobit.classic.rewriting_region_resize import apply_region_resize

PROBE = Path(__file__).parent / "fixtures" / "x87_probe"

PRE = "8b4c2404"  # mov ecx, [esp+4]
POST = "33c0c3"  # xor eax, eax ; ret
X = "dd01"  # fld qword [ecx]
Y = "d94108"  # fld dword [ecx+8]
FNSTSW = "dfe0"
STORE_ONE = "c7412801000000"  # mov dword [ecx+40], 1


def _prove(donor, replacement, pre=PRE, post=POST):
    donor_hex = "".join(donor)
    body = bytes.fromhex(pre + donor_hex + post)
    start = len(pre) // 2
    region = {
        "region_start": start,
        "region_end": start + len(donor_hex) // 2,
        "replacement_instructions": list(replacement),
        "replacement_relocations": [],
    }
    return apply_region_resize(body, [region], [], 1, "x87")


def _run(hex_code, relocations=None):
    code = bytes.fromhex(hex_code)
    return simulate_region(code, 0, len(code), relocations or {}, "t", "x87")


def _drain(depth):
    return [f"d959{20 + 4 * k:02x}" for k in range(depth)]


# --- the hardware probe ----------------------------------------------------------


def _probe_lines(prefix):
    return [line.split() for line in (PROBE / "probe.out").read_text().splitlines() if line.startswith(prefix)]


def _fields(parts):
    return dict(part.split("=", 1) for part in parts if "=" in part)


def _evaluate(term, memory):
    """A term's value over the probe's inputs (loads named by their [ecx+offset])."""
    tag = term[0]
    if tag in ("fld", "fmem"):
        load = term[2][2] if term[2][0] == "b" else term[2][2][0][0]
        return memory[load[1][1]]
    if tag == "fop":
        left, right = _evaluate(term[2], memory), _evaluate(term[3], memory)
        return {
            "add": left + right,
            "mul": left * right,
            "sub": left - right,
            "div": left / right,
        }[term[1]]
    raise AssertionError(term)


def test_the_probe_ran_the_encodings_the_model_names() -> None:
    encodings = (PROBE / "encodings.txt").read_text()
    for base in ("d8", "dc", "de"):
        for modrm in ("c1", "c9", "e1", "e9", "f1", "f9"):
            assert re.search(rf"\b{base} {modrm}\b", encodings), (base, modrm)
    for compare in ("d8 d1", "d8 d9", "de d9", "dd e1", "dd e9", "da e9", "d8 15", "dc 1d"):
        assert compare in encodings


def test_register_arithmetic_matches_the_probe() -> None:
    """Simulate each probed encoding from the probe's stack and evaluate the exit stack."""
    rows = _probe_lines("ARITH")
    assert len(rows) == 4 * 40
    for row in rows:
        encoding = row[1].lower()
        fields = _fields(row[2:])
        a, b, c = float(fields["A"]), float(fields["B"]), float(fields["C"])
        # The probe loads C, then A, then B: ST(0) = B, ST(1) = A, ST(2) = C.
        [path] = _run("dd4110" + "dd01" + "dd4108" + encoding)
        view = path.x87
        pops = (int(fields["top1"]) - int(fields["top0"])) % 8
        assert view.push == 3 - pops, encoding
        memory = {0: a, 8: b, 16: c}
        measured = [float(fields[f"R{k}"]) for k in range(3 - pops)]
        for k, expected in enumerate(measured):
            value = _evaluate(view.term(k - view.push), memory)
            assert math.isclose(value, expected, rel_tol=1e-15), (encoding, k, value, expected)


def _outcome(a, b):
    if math.isnan(a) or math.isnan(b):
        return "un"
    return "gt" if a > b else "lt" if a < b else "eq"


def test_compare_condition_bits_match_the_probe() -> None:
    rows = _probe_lines("CMP")
    pops = {"fcom_m32": 0, "fcomp_m32": 1, "fcom_m64": 0, "fcomp_m64": 1, "D8D1": 0,
            "D8D9": 1, "DED9": 2, "DDE1": 0, "DDE9": 1, "DAE9": 2}
    seen = set()
    for row in rows:
        fields = _fields(row[2:])
        a = float("nan") if "NAN" in fields["A"] else float(fields["A"])
        b = float(fields["B"])
        after = int(fields["swafter"], 16)
        bits = {"c0": after >> 8 & 1, "c1": after >> 9 & 1, "c2": after >> 10 & 1, "c3": after >> 14 & 1}
        assert bits == FCMP_BITS[_outcome(a, b)], row
        assert (int(fields["top1"]) - int(fields["top0"])) % 8 == pops[row[1]]
        seen.add((row[1], fields["preset"]))
    assert len(seen) == 20  # every form, with C0-C3 preset to 0 and to 1


def test_subtract_and_divide_are_functions_of_their_operand_roles_on_the_probe() -> None:
    groups = {"X-Y": [1, 2, 4], "Y-X": [0, 3, 5], "X/Y": [7, 8], "Y/X": [6, 9]}
    rows = (PROBE / "roles.out").read_text().splitlines()
    assert len(rows) == 14 * 14
    for line in rows:
        parts = line.split()
        results = {int(item.split(":")[0]): item.split(":")[1] for item in parts[2:]}
        for cases in groups.values():
            assert len({results[case] for case in cases}) == 1, line


def test_no_precision_control_makes_a_spill_the_identity_on_the_probe() -> None:
    differs = set()
    for row in _probe_lines("SPILL"):
        fields = _fields(row[1:])
        if fields["c3c2c0"] != "100":
            differs.add((row[0], fields["cw"]))
    assert differs == {(width, cw) for width in ("SPILL32", "SPILL64") for cw in ("007f", "027f", "037f")}


def test_register_copies_and_sign_operations_raise_nothing_and_copy_exactly_on_the_probe() -> None:
    """Why the simulator records no exception event for them: their results are exact."""
    rows = [line.split() for line in (PROBE / "moves.out").read_text().splitlines()]
    assert len(rows) == 8 * 25
    for row in rows:
        case = int(row[1])
        fields = _fields(row[4:])
        assert row[4] == "exc=00", row
        v0, v1, s0, s1 = fields["V0"], fields["V1"], fields["S0"], fields["S1"]
        flipped = f"{int(v0[:4], 16) ^ 0x8000:04x}" + v0[4:]
        cleared = f"{int(v0[:4], 16) & 0x7FFF:04x}" + v0[4:]
        expected = {0: (v1, v0), 1: (v1, v0), 2: (v0, v0), 3: (flipped, v1), 4: (cleared, v1), 5: (v0, v0)}
        if case in expected:
            assert (s0, s1) == expected[case], row
    encodings = (PROBE / "encodings.txt").read_text()
    for encoding in ("d9 c0", "d9 c1", "d9 c9", "dd d1", "d9 e0", "d9 e1", "d9 e8", "d9 ee"):
        assert encoding in encodings


# --- the simulator ---------------------------------------------------------------


def test_a_store_then_reload_is_a_rounding_term_not_the_value() -> None:
    [path] = _run("dd01" + "d95910" + "d94110")  # fld m64; fstp m32; fld m32
    reloaded = path.x87.term(-1)
    assert reloaded[0] == "fld" and reloaded[2][2][0][0][0] == "fstm"
    [kept] = _run("dd01")
    assert kept.x87.term(-1) != reloaded


def test_an_undefined_condition_bit_read_is_refused() -> None:
    # fadd leaves C0, C2 and C3 undefined; test ah, 41h reads C0 and C3.
    with pytest.raises(ByteIdentityError, match="undefined"):
        _run(X + "d84104" + FNSTSW + "f6c441" + "7500")
    # C1 after a compare is defined (cleared): reading it alone decides nothing.
    [path] = _run(X + Y + "ded9" + FNSTSW + "f6c402" + "7500")
    assert path.conditions == ()


def test_a_status_word_that_reaches_memory_with_undefined_bits_is_refused() -> None:
    with pytest.raises(ByteIdentityError, match="undefined"):
        _run(X + "d95910" + FNSTSW + "668901")  # fstp; fnstsw ax; mov [ecx], ax


def test_a_status_word_byte_combined_other_than_by_a_mask_is_refused() -> None:
    with pytest.raises(ByteIdentityError, match="status-word"):
        _run(X + Y + "ded9" + FNSTSW + "80cc41")  # or ah, 41h


def test_an_x87_instruction_after_a_call_is_refused() -> None:
    with pytest.raises(ByteIdentityError, match="after a call"):
        _run("e800000000" + X, {1: ("rel32", "_f")})


@pytest.mark.parametrize("encoding", ["d9fe", "d9ff", "df1e", "db1e", "d9e4", "d93c24", "9b"])
def test_x87_instructions_outside_the_closed_set_are_refused(encoding: str) -> None:
    # fsin, fcos, fistp m16, fistp m32, ftst, fnstcw, fwait
    with pytest.raises(ByteIdentityError, match="closed set"):
        _run(X + encoding)


def test_compare_atoms_meet_across_operand_order_and_equivalent_masks() -> None:
    a, b = ("fld", 32, "a"), ("fld", 32, "b")
    assert fcc_atom(("fcmp", a, b), {"gt", "lt"}) == fcc_atom(("fcmp", b, a), {"lt", "gt"})
    assert fcc_atom(("fcmp", a, b), {"gt"}) == fcc_atom(("fcmp", b, a), {"lt"})
    assert fcc_atom(("fcmp", a, b), {"gt"}) != fcc_atom(("fcmp", b, a), {"gt"})
    atom = fcc_atom(("fcmp", a, b), {"gt"})
    wider = fcc_atom(("fcmp", a, b), {"gt", "eq"})
    # outcome gt and outcome not in {gt, eq} cannot both hold
    assert contradictory([(atom, True)], [(wider, False)])
    assert not contradictory([(atom, False)], [(wider, True)])


def test_a_path_that_pins_a_compare_decides_a_later_test_of_it() -> None:
    # test ah, 41h; jne over; test ah, 01h; jne over: on the fall-through
    # path the outcome is gt, so the second test is decided.
    code = X + Y + "ded9" + FNSTSW + "f6c441" + "7505" + "f6c401" + "7500"
    paths = _run(code)
    assert len(paths) == 2


# --- the proof: each instruction family ----------------------------------------------

_FAMILIES = [
    # (encoding, net stack change, is a compare)
    *[(f"d8{m}", 0, False) for m in ("c1", "c9", "e1", "e9", "f1", "f9")],
    *[(f"dc{m}", 0, False) for m in ("c1", "c9", "e1", "e9", "f1", "f9")],
    *[(f"de{m}", -1, False) for m in ("c1", "c9", "e1", "e9", "f1", "f9")],
    *[(f"d8{m}0c", 0, False) for m in ("41", "49", "61", "69", "71", "79")],
    *[(f"dc{m}10", 0, False) for m in ("41", "49", "61", "69", "71", "79")],
    ("d9e0", 0, False), ("d9e1", 0, False), ("d9fa", 0, False),
    ("d9e8", 1, False), ("d9ee", 1, False), ("d9c1", 1, False),
    ("d9410c", 1, False), ("dd4110", 1, False),
    ("df410c", 1, False), ("db410c", 1, False), ("df6910", 1, False),
    ("d9c9", 0, False), ("ddd1", 0, False), ("ddd9", -1, False), ("ddd8", -1, False),
    ("d9510c", 0, False), ("d9590c", -1, False), ("dd5110", 0, False), ("dd5910", -1, False),
    ("d8d1", 0, True), ("d8d9", -1, True), ("ded9", -2, True),
    ("dde1", 0, True), ("dde9", -1, True), ("dae9", -2, True),
    ("d8510c", 0, True), ("d8590c", -1, True), ("dc5110", 0, True), ("dc5910", -1, True),
]


def _family_region(loads, encoding, change, compare):
    depth = 2 + change
    if compare:
        return [*loads, encoding, FNSTSW, *_drain(depth), "f6c441", "7507", STORE_ONE]
    return [*loads, encoding, *_drain(depth)]


@pytest.mark.parametrize(("encoding", "change", "compare"), _FAMILIES)
def test_each_family_proves_under_an_fxch_schedule_and_refuses_swapped_operands(
    encoding: str, change: int, compare: bool
) -> None:
    donor = _family_region([Y, X], encoding, change, compare)
    # The same stack reached by loading in the other order and exchanging.
    _image, proof = _prove(donor, _family_region([X, Y, "d9c9"], encoding, change, compare))
    [region] = proof["regions"]
    assert region["x87"]["entry_depths"] == [[0, 0]]
    assert region["x87"]["peak"] >= 2
    # Without the exchange the operands are swapped: a different term.
    with pytest.raises(ByteIdentityError, match="different (memory|x87)"):
        _prove(donor, _family_region([X, Y], encoding, change, compare))


def test_fsub_and_fsubr_computing_one_difference_meet() -> None:
    donor = [X, Y, "dee9", "d95914"]  # st1 = st1 - st0 = X - Y
    _prove(donor, [Y, X, "dee1", "d95914"])  # st1 = st0 - st1 = X - Y
    _prove(donor, [Y, X, "d8e1", "ddd9", "d95914"])  # st0 = st0 - st1; fstp st(1)
    with pytest.raises(ByteIdentityError, match="different memory"):
        _prove(donor, [Y, X, "dee9", "d95914"])  # Y - X


def test_a_different_association_is_refused() -> None:
    z = "d9410c"
    donor = [X, Y, "dec1", z, "dec1", "d95914"]  # (X + Y) + Z
    with pytest.raises(ByteIdentityError, match="different memory"):
        _prove(donor, [X, Y, z, "dec1", "dec1", "d95914"])  # X + (Y + Z)


def test_a_spill_whose_rounding_differs_is_refused() -> None:
    donor = [X, "d84904", "d95110", "d84108", "d95914"]  # keep X*m in the register
    with pytest.raises(ByteIdentityError, match="different memory"):
        # spill it through m32 and reload the rounded value
        _prove(donor, [X, "d84904", "d95910", "d94110", "d84108", "d95914"])


def test_a_stack_depth_mismatch_at_the_exit_is_refused() -> None:
    with pytest.raises(ByteIdentityError, match="x87 stacks"):
        _prove([X, "d95914"], [X, "d95114"])  # fstp versus fst: one more value left


def test_a_value_left_on_the_stack_must_be_equal() -> None:
    pre, post = PRE + X, "d95918" + POST  # the region's entry holds X; fstp after it
    donor = [Y, "dec9"]  # X * Y, popped into the entry's register
    _image, proof = _prove(donor, [Y, "d9c9", "d8c9", "ddd9"], pre=pre, post=post)
    assert proof["regions"][0]["x87"] == {
        "entry_depths": [[1, 1]],
        "need": 1,
        "peak": 1,
        "compared_condition_bits": [],
    }
    with pytest.raises(ByteIdentityError, match="different x87 stacks"):
        _prove(donor, [Y, "d8c9", "ddd9"], pre=pre, post=post)  # Y * X


def test_overflow_is_refused() -> None:
    loads = [f"d941{4 * k:02x}" for k in range(9)]
    stores = [f"d959{0x40 + 4 * k:02x}" for k in range(9)]
    donor = [item for pair in zip(loads, stores, strict=True) for item in pair]
    # nine loads first, stored in reverse: a peak of nine registers
    replacement = [*loads, *reversed(stores)]
    with pytest.raises(ByteIdentityError, match="overflow"):
        _prove(donor, replacement)


def test_overflow_over_a_nonzero_entry_depth_is_refused() -> None:
    loads = [f"d941{4 * k:02x}" for k in range(8)]
    stores = [f"d959{0x40 + 4 * k:02x}" for k in range(8)]
    donor = [item for pair in zip(loads, stores, strict=True) for item in pair]
    replacement = [*loads, *reversed(stores)]
    _prove(donor, replacement)  # eight over an empty stack fit
    with pytest.raises(ByteIdentityError, match="overflow"):
        _prove(donor, replacement, pre=PRE + X, post="ddd8" + POST)


def test_underflow_is_refused() -> None:
    pre, post = PRE + X, POST
    donor = [Y, "d9c9", "d95914", "d95918"]  # depth 1 at the entry, 0 at the exit
    # the replacement reaches the entry's ST(1), which is empty
    replacement = ["d9c9", "d9c9", Y, "d9c9", "d95914", "d95918"]
    _prove(donor, [Y, "d95918", "d95914"], pre=pre, post=post)
    with pytest.raises(ByteIdentityError, match="underflow"):
        _prove(donor, replacement, pre=pre, post=post)


def test_an_undefined_bit_read_is_refused_by_the_proof() -> None:
    donor = [X, "d84104", FNSTSW, "d95914", "f6c441", "7507", STORE_ONE]
    with pytest.raises(ByteIdentityError, match="undefined"):
        _prove(donor, [X, "d84104", "d95914", FNSTSW, "f6c441", "7507", STORE_ONE])


# --- the proof: compares through fnstsw / test ah / jcc ------------------------------


def test_a_compare_branch_proves_with_mirrored_operands_and_an_equivalent_mask() -> None:
    donor = [Y, X, "ded9", FNSTSW, "f6c440", "7507", STORE_ONE]  # X vs Y; C3 zero: not eq, not un
    replacement = [X, Y, "ded9", FNSTSW, "f6c444", "7507", STORE_ONE]  # Y vs X; C3|C2 zero
    _image, proof = _prove(donor, replacement)
    [region] = proof["regions"]
    assert (region["donor_paths"], region["replacement_paths"], region["path_pairs"]) == (2, 2, 2)


def test_a_compare_branch_on_another_outcome_set_is_refused() -> None:
    donor = [Y, X, "ded9", FNSTSW, "f6c440", "7507", STORE_ONE]
    with pytest.raises(ByteIdentityError, match="different memory"):
        _prove(donor, [X, Y, "ded9", FNSTSW, "f6c441", "7507", STORE_ONE])


def test_condition_bits_live_at_the_exit_must_be_equal() -> None:
    post = FNSTSW + "f6c441" + "7507" + "c7410c02000000" + POST
    donor = [Y, X, "ded9"]
    _image, proof = _prove(donor, [X, Y, "d9c9", "ded9"], post=post)
    assert proof["regions"][0]["x87"]["compared_condition_bits"] == ["c0", "c1", "c2", "c3"]
    with pytest.raises(ByteIdentityError, match="condition bit C0 is live"):
        _prove(donor, [X, Y, "ded9"], post=post)  # the mirrored compare: other raw bits


def test_condition_bits_dead_at_the_exit_may_differ() -> None:
    post = X + "d8590c" + FNSTSW + "f6c441" + "7507" + "c7410c02000000" + POST
    donor = [Y, X, "ded9"]
    # A compare after the region defines C0-C3 again before fnstsw reads them.
    _prove(donor, [X, Y, "ded9"], post=post)


def test_the_environment_stored_anywhere_in_the_body_is_refused() -> None:
    with pytest.raises(ByteIdentityError, match="environment"):
        _prove([Y, X, "d9c9", "d95914", "d95918"], [X, Y, "d95914", "d95918"], post="d93424" + POST)


def test_a_region_without_x87_is_unaffected_by_x87_around_it() -> None:
    pre = PRE + X
    post = "d95914" + POST
    _image, proof = _prove(["8b4104", "8bd0", "895108"], ["8b4104", "894108"], pre=pre, post=post)
    assert "x87" not in proof["regions"][0]


# --- the donor-wide analyses ---------------------------------------------------------


def _walk(hex_code, relocations=None):
    code = bytes.fromhex(hex_code)
    items, successors, entries = ia32_relational_flow_walk(code, relocations or {}, "walk")
    return code, items, successors, entries


def _depths(hex_code, relocations=None):
    code, items, successors, entries = _walk(hex_code, relocations)
    depths = x87_stack_depths(items, successors, entries, code, relocations or {})
    return None if depths is None else {item["offset"]: d for item, d in zip(items, depths, strict=True)}


def _call(at, symbol):
    return {at + 1: {"width": 4, "target": symbol}}


def test_a_callee_that_returns_a_value_is_inferred_from_its_consumer() -> None:
    depths = _depths("e800000000" + "d95908" + "c3", _call(0, "_f"))
    assert depths[5] == (1, 1)


def test_a_callee_that_returns_nothing_is_inferred_from_the_next_call() -> None:
    code = "e800000000" + "d901" + "d95904" + "e800000000" + "c3"
    relocations = {**_call(0, "_g"), **_call(10, "_g")}
    depths = _depths(code, relocations)
    assert depths[5] == (0, 0) and depths[7] == (1, 1)


def test_a_helper_that_pops_is_inferred() -> None:
    code = "d901" + "e800000000" + "e800000000" + "c3"
    depths = _depths(code, {**_call(2, "__ftol"), **_call(7, "_h")})
    assert depths[7] == (0, 0)


def test_an_undetermined_callee_leaves_an_interval() -> None:
    assert _depths("e800000000" + "c3", _call(0, "_f"))[5] == (0, 1)


def test_an_inconsistent_donor_has_no_depths() -> None:
    assert _depths("d95904" + "c3") is None  # a pop of an empty stack at the entry


def test_unequal_depths_at_a_join_are_inconsistent() -> None:
    # je over a push: the two paths meet with depths 0 and 1
    assert _depths("85c0" + "7402" + "d901" + "c3") is None


def test_condition_bits_are_live_up_to_fnstsw_and_killed_by_a_compare() -> None:
    hex_code = X + "d9c0" + "ded9" + FNSTSW + "d95904" + FNSTSW + "c3"
    code, items, successors, _entries = _walk(hex_code)
    live = x87_condition_liveness(items, successors, code, "cc")
    by_offset = {item["offset"]: bits for item, bits in zip(items, live, strict=True)}
    assert by_offset[0] == frozenset()  # killed by the compare at 4
    assert by_offset[6] == {"c0", "c1", "c2", "c3"}  # read by the first fnstsw
    assert by_offset[8] == {"c0", "c1", "c2", "c3"}  # fstp does not kill: undefined may keep


def test_environment_stores_are_found() -> None:
    code, items, _successors, _entries = _walk("d93424" + "dd3424" + "d93c24" + "c3")
    assert x87_environment_exposures(items, code) == [0, 3]
