"""Classic compiler algorithms: the x87 facts a region proof needs from the whole body.

The region simulator (:mod:`reprobit.classic.region_simulation`) runs an x87
region relative to its entry: it does not know how many registers are full
when the region starts.  A region is sound only if, on every execution, the
entry depth D is at least the deepest entry register the region touches
(no stack underflow) and D plus the region's highest push is at most eight
(no overflow).  :func:`x87_stack_depths` bounds D at every instruction of
the donor body; :func:`x87_condition_liveness` says which of C0-C3 a later
instruction can still read, so a region may leave dead condition bits
different; :func:`x87_environment_exposures` finds the instructions that
would read the parts of the x87 state the proof does not compare.

Depth model.  The depth at an instruction is an affine form ``k + sum(c *
v)`` over unknowns ``v``, one per callee symbol (the number of values that
callee leaves on the stack), one per indirect call site, and one per
instruction whose stack effect is not tabulated.  The forms come from one
forward walk of the donor's control-flow graph from the function's entry
(depth 0) and every other external entry the walk does not reach (depth 0).
The walk writes these constraints:

- every instruction: ``0 <= depth <= 8``, depth at least the registers it
  reads or pops (``need``), and depth plus its pushes at most eight;
- a call to a C or C++ function (any callee but a compiler helper) or an
  indirect call: depth 0 before it, and the callee's unknown in {0, 1};
- a call to a compiler helper (``__name``, e.g. ``__ftol``): its unknown in
  {-2, -1, 0, 1} and the depth after it in [0, 8];
- a return: depth 0 or 1;
- a point two edges reach: the two forms are equal.

Bounds propagation narrows each unknown's domain to the values some
assignment of the others allows; every remaining value is kept, so the
true assignment survives.  The depth set at an instruction is then the
interval of its form over the narrowed domains, an over-approximation.  The
analysis fails (returns None) when a domain empties.  A C callee whose
domain narrows to one value has that return count
(:func:`x87_stack_solution`); the region simulator uses it to run x87 code
after a direct call to that callee inside a region.

Assumption (MSVC 5.0's x87 discipline).  The donor is compiled code: its
depth at a point is one number on every path that reaches it (the
compiler's static stack model), it holds no x87 value across a call to a C
function (the callee may use all eight registers) and returns with 0 or 1
values; each callee leaves a fixed number of values (its prototype's), the
same at every call of that symbol.  These are code-generator and calling-
convention invariants, not facts measured here; the constraints only check
that the donor is consistent with them.
"""

from __future__ import annotations

from collections.abc import Mapping
from typing import Any

from reprobit.binary import require

from .register_semantics import _ia32_backward_liveness

X87_CC = frozenset({"c0", "c1", "c2", "c3"})
MAX_DEPTH = 8

# (need, delta) for every x87 register form whose stack effect is fixed, by
# (opcode, ModR/M byte); memory forms by (opcode, digit).
_RESET = "reset"


def _register_effect(op: int, modrm: int) -> tuple[int, int] | str | None:
    digit, index = modrm >> 3 & 7, modrm & 7
    reach = index + 1
    if op == 0xD8:
        return (reach, -1) if digit == 3 else (reach, 0)
    if op == 0xD9:
        if digit == 0:
            return (reach, 1)
        if digit == 1:
            return (reach, 0)
        fixed = {
            0xD0: (0, 0),
            0xE0: (1, 0),
            0xE1: (1, 0),
            0xE4: (1, 0),
            0xE5: (0, 0),
            0xF0: (1, 0),
            0xF1: (2, -1),
            0xF2: (1, 1),
            0xF3: (2, -1),
            0xF4: (1, 1),
            0xF5: (2, 0),
            0xF8: (2, 0),
            0xF9: (2, -1),
            0xFA: (1, 0),
            0xFB: (1, 1),
            0xFC: (1, 0),
            0xFD: (2, 0),
            0xFE: (1, 0),
            0xFF: (1, 0),
        }
        if 0xE8 <= modrm <= 0xEE:
            return (0, 1)
        return fixed.get(modrm)
    if op == 0xDA:
        return (2, -2) if modrm == 0xE9 else None
    if op == 0xDB:
        if modrm in (0xE2,):
            return (0, 0)
        if modrm == 0xE3:
            return _RESET
        return None
    if op == 0xDC:
        return None if digit in (2, 3) else (reach, 0)
    if op == 0xDD:
        if digit == 2:
            return (reach, 0)
        if digit == 3:
            return (reach, -1)
        if digit == 4:
            return (reach, 0)
        if digit == 5:
            return (reach, -1)
        return None
    if op == 0xDE:
        if modrm == 0xD9:
            return (2, -2)
        return None if digit in (2, 3) else (max(reach, 1), -1)
    if op == 0xDF:
        return (0, 0) if modrm == 0xE0 else None
    return None


def _memory_effect(op: int, digit: int) -> tuple[int, int] | str | None:
    if op in (0xD8, 0xDC, 0xDA, 0xDE):
        return (1, -1) if digit == 3 else (1, 0)
    if op == 0xD9:
        return {0: (0, 1), 2: (1, 0), 3: (1, -1), 5: (0, 0), 7: (0, 0), 6: (0, 0)}.get(digit)
    if op == 0xDB:
        return {0: (0, 1), 2: (1, 0), 3: (1, -1), 5: (0, 1), 7: (1, -1)}.get(digit)
    if op == 0xDD:
        if digit == 6:
            return _RESET  # fnsave re-initialises the unit after storing it
        return {0: (0, 1), 2: (1, 0), 3: (1, -1), 7: (0, 0)}.get(digit)
    if op == 0xDF:
        return {0: (0, 1), 2: (1, 0), 3: (1, -1), 4: (0, 1), 5: (0, 1), 6: (1, -1), 7: (1, -1)}.get(
            digit
        )
    return None


def x87_stack_effect(code: bytes, item: Mapping[str, Any]) -> tuple[int, int] | str | None:
    """``(need, delta)`` of a flow item, ``"reset"`` for fninit/fnsave, None when not fixed.

    A non-x87 instruction is ``(0, 0)``; ``fwait`` too.
    """
    op = item["opcode"]
    if not 0xD8 <= op <= 0xDF:
        return (0, 0)
    modrm = code[item["opcode_at"] + 1]
    if modrm >> 6 == 3:
        return _register_effect(op, modrm)
    return _memory_effect(op, modrm >> 3 & 7)


def _call_symbol(
    code: bytes, item: Mapping[str, Any], relocations: Mapping[int, Any]
) -> str | None:
    at = item["opcode_at"]
    if code[at] == 0xE8:
        row = relocations.get(at + 1)
    elif code[at] == 0xFF and code[at + 1] == 0x15:
        row = relocations.get(at + 2)
    else:
        return None
    target = row.get("target") if isinstance(row, Mapping) else row
    return target if isinstance(target, str) else None


def _is_helper(symbol: str) -> bool:
    name = symbol[len("__imp_") :] if symbol.startswith("__imp_") else symbol
    return name.startswith("__")


# A form is (constant, ((variable, coefficient), ...)) with sorted variables.
Form = tuple[int, tuple[tuple[int, int], ...]]


def _form(constant: int, terms: Mapping[int, int] | None = None) -> Form:
    return (constant, tuple(sorted((v, c) for v, c in (terms or {}).items() if c)))


def _add(form: Form, constant: int = 0, variable: int | None = None) -> Form:
    terms = dict(form[1])
    if variable is not None:
        terms[variable] = terms.get(variable, 0) + 1
    return _form(form[0] + constant, terms)


def _sub(left: Form, right: Form) -> Form:
    terms = dict(left[1])
    for variable, coefficient in right[1]:
        terms[variable] = terms.get(variable, 0) - coefficient
    return _form(left[0] - right[0], terms)


def _bounds(form: Form, domains: list[set[int]]) -> tuple[int, int]:
    low = high = form[0]
    for variable, coefficient in form[1]:
        values = [coefficient * value for value in domains[variable]]
        low += min(values)
        high += max(values)
    return low, high


def x87_stack_depths(
    items: list[dict[str, Any]],
    successors: list[list[int]],
    entries: list[int],
    code: bytes,
    relocations: Mapping[int, Any],
) -> list[tuple[int, int] | None] | None:
    """The x87 depth interval at every flow item, or None when the donor is inconsistent.

    An item the walk does not reach is None.  See the module docstring for
    the model and its assumption.
    """
    solution = x87_stack_solution(items, successors, entries, code, relocations)
    return None if solution is None else solution[0]


def x87_stack_solution(
    items: list[dict[str, Any]],
    successors: list[list[int]],
    entries: list[int],
    code: bytes,
    relocations: Mapping[int, Any],
) -> tuple[list[tuple[int, int] | None], dict[str, int]] | None:
    """The depth intervals and the callees' determined return counts, or None.

    The second part maps each C function (any callee symbol but a compiler
    helper) whose number of returned x87 values the donor's discipline fixes
    to that number, 0 or 1.  A callee whose count stays undetermined
    (0 or 1 both consistent), a helper and an indirect call site are absent.
    Under assumption x1 (the module docstring) the number is the callee's:
    bounds propagation removes only values no consistent assignment has.
    """
    domains: list[set[int]] = []
    symbol_variable: dict[str, int] = {}
    forms: list[Form | None] = [None] * len(items)
    # Each constraint is (kind, form): kind "eq" (form == 0) or "ge" (form >= 0).
    constraints: list[tuple[str, Form]] = []
    written: set[tuple[str, Form]] = set()

    def constrain(kind: str, form: Form) -> None:
        if (kind, form) not in written:
            written.add((kind, form))
            constraints.append((kind, form))

    def variable(values: set[int]) -> int:
        domains.append(set(values))
        return len(domains) - 1

    def range_of(form: Form, low: int, high: int) -> None:
        constrain("ge", _add(form, -low))
        constrain("ge", _sub(_form(high), form))

    order = [0] + [index for index in entries if index != 0]
    for root in order:
        if forms[root] is not None:
            continue
        forms[root] = _form(0)
        pending = [root]
        while pending:
            index = pending.pop()
            item = items[index]
            depth = forms[index]
            assert depth is not None
            range_of(depth, 0, MAX_DEPTH)
            after: Form
            if item["flow"] == "call":
                symbol = _call_symbol(code, item, relocations)
                if symbol is not None and _is_helper(symbol):
                    if symbol not in symbol_variable:
                        symbol_variable[symbol] = variable({-2, -1, 0, 1})
                    after = _add(depth, 0, symbol_variable[symbol])
                    range_of(after, 0, MAX_DEPTH)
                else:
                    constrain("eq", depth)
                    if symbol is None:
                        returned = variable({0, 1})
                    else:
                        if symbol not in symbol_variable:
                            symbol_variable[symbol] = variable({0, 1})
                        returned = symbol_variable[symbol]
                    after = _add(depth, 0, returned)
            else:
                effect = x87_stack_effect(code, item)
                if effect == _RESET:
                    after = _form(0)
                elif effect is None:
                    after = _form(0, {variable(set(range(MAX_DEPTH + 1))): 1})
                elif effect == (0, 0):
                    after = depth
                elif isinstance(effect, tuple):
                    need, delta = effect
                    constrain("ge", _add(depth, -need))
                    constrain("ge", _sub(_form(MAX_DEPTH - max(delta, 0)), depth))
                    after = _add(depth, delta)
                if item["flow"] == "ret":
                    range_of(depth, 0, 1)
            for successor in successors[index]:
                known = forms[successor]
                if known is None:
                    forms[successor] = after
                    pending.append(successor)
                elif known != after:
                    constrain("eq", _sub(known, after))
    # Bounds propagation to a fixpoint.
    changed = True
    while changed:
        changed = False
        for kind, form in constraints:
            for variable_index, coefficient in form[1]:
                rest = (form[0], tuple(p for p in form[1] if p[0] != variable_index))
                low, high = _bounds(rest, domains)
                keep = {
                    value
                    for value in domains[variable_index]
                    if (
                        low <= -coefficient * value <= high
                        if kind == "eq"
                        else coefficient * value + high >= 0
                    )
                }
                if keep != domains[variable_index]:
                    if not keep:
                        return None
                    domains[variable_index] = keep
                    changed = True
            if not form[1] and ((kind == "eq" and form[0] != 0) or (kind == "ge" and form[0] < 0)):
                return None
    depths = [None if form is None else _bounds(form, domains) for form in forms]
    returns = {
        symbol: next(iter(domains[index]))
        for symbol, index in symbol_variable.items()
        if not _is_helper(symbol) and len(domains[index]) == 1
    }
    return depths, returns


def _condition_effect(
    code: bytes, item: Mapping[str, Any]
) -> tuple[frozenset[str], frozenset[str]]:
    """(read, defined) condition bits of one flow item.

    ``fnstsw`` (AX or m16), ``fnstenv`` and ``fnsave`` read C0-C3.  The
    compares, ``ftst``, ``fxam`` and ``fninit`` define all four; ``fnsave``
    re-initialises after reading.  Every other instruction -- calls
    included -- is treated as preserving them: an instruction Intel leaves
    them undefined after may in fact keep them, so it never kills liveness.
    """
    op = item["opcode"]
    if not 0xD8 <= op <= 0xDF:
        return frozenset(), frozenset()
    modrm = code[item["opcode_at"] + 1]
    digit = modrm >> 3 & 7
    none: frozenset[str] = frozenset()
    if modrm >> 6 != 3:
        if (op, digit) in ((0xDD, 7), (0xD9, 6)):
            return X87_CC, none
        if (op, digit) == (0xDD, 6):
            return X87_CC, X87_CC
        if op in (0xD8, 0xDC, 0xDA, 0xDE) and digit in (2, 3):
            return none, X87_CC
        return none, none
    if (op, modrm) == (0xDF, 0xE0):
        return X87_CC, none
    if (
        (op == 0xD8 and digit in (2, 3))
        or (op, modrm) in ((0xDE, 0xD9), (0xDA, 0xE9), (0xD9, 0xE4), (0xD9, 0xE5), (0xDB, 0xE3))
        or (op == 0xDD and digit in (4, 5))
    ):
        return none, X87_CC
    return none, none


def x87_condition_liveness(
    items: list[dict[str, Any]], successors: list[list[int]], code: bytes, context: str
) -> list[frozenset[str]]:
    """Backward liveness of C0-C3 at every flow item (live on entry to the item)."""
    shim = []
    for item in items:
        reads, defines = _condition_effect(code, item)
        shim.append({"read_atoms": reads, "write_atoms": defines})
    return _ia32_backward_liveness(shim, successors, context)


def x87_environment_exposures(items: list[dict[str, Any]], code: bytes) -> list[int]:
    """Offsets of instructions that store the x87 environment (fnstenv, fnsave, fxsave).

    They expose the contents of empty registers, the tag word and the last
    instruction and data pointers, none of which a region proof compares.
    """
    found = []
    for item in items:
        op = item["opcode"]
        at = item["opcode_at"]
        if op in (0xD9, 0xDD):
            modrm = code[at + 1]
            if modrm >> 6 != 3 and modrm >> 3 & 7 == 6:
                found.append(item["offset"])
        elif op == 0x0FAE:
            modrm = code[at + 2]
            if modrm >> 6 != 3 and modrm >> 3 & 7 == 0:
                found.append(item["offset"])
    return found


def require_x87_depth(depth: tuple[int, int] | None, need: int, peak: int, context: str) -> None:
    """Refuse unless every entry depth in ``depth`` covers ``need`` and leaves room for ``peak``."""
    require(
        depth is not None,
        f"{context}: the region uses the x87 stack but its depth at the region entry is not "
        "determined by the donor's stack discipline",
    )
    assert depth is not None
    low, high = depth
    require(
        need <= low,
        f"{context}: the region reads x87 entry register ST({need - 1}) but the entry depth may "
        f"be {low} (stack underflow)",
    )
    require(
        high + peak <= MAX_DEPTH,
        f"{context}: the region pushes {peak} x87 values over an entry depth that may be {high} "
        "(stack overflow)",
    )


__all__ = [
    "MAX_DEPTH",
    "X87_CC",
    "require_x87_depth",
    "x87_condition_liveness",
    "x87_environment_exposures",
    "x87_stack_depths",
    "x87_stack_effect",
    "x87_stack_solution",
]
