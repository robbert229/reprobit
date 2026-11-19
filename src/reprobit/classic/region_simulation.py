"""Classic compiler algorithms: a strict, path-sensitive IA-32 region simulator.

This is the simulator behind `simulated_region_resize_v1`
(:mod:`reprobit.classic.rewriting_region_resize`).  It symbolically executes
one single-entry, single-exit region of straight-line code and forward
branches, once per path, from a symbolic entry state, and returns every
path's end state for the caller to compare.  It is deliberately separate from
the permutation simulator of `simulated_region_rewrite_v1`, whose memory model
is built for a reordering of the same instructions: it resolves a load by an
exact-key lookup in a single-base map and treats the compiler's frame as
private, so a reload after a partially overlapping store, or after a store
through another pointer, reads as the pre-region value.  A length-changing
rewrite replaces a value held in a register by a reload from memory (or the
other way round), and that equivalence holds exactly when no store between
the two reads can reach the location -- the case such a model cannot see.

Term language (every term is a hashable tuple; equal terms denote equal
values on every execution that reaches them from the same entry state):

- A 32-bit value is a canonical linear form ``("lin", c, ((atom, k), ...))``
  denoting ``c + sum(k * atom)`` modulo 2**32, with the coefficients reduced
  modulo 2**32, zero coefficients dropped and the atoms sorted.  Linear forms
  are a normal form of the ring Z/2**32, so ``lea eax, [eax+eax*2]``,
  ``imul eax, eax, 3`` and ``shl``-then-``add`` sequences that compute the
  same polynomial of degree one compare equal.  An atom is an entry register
  ``("reg0", r)``, a relocated symbol ``("sym", name)``, a load, or an opaque
  operation (``and``/``or``/``xor`` of non-constant operands, ``shr``,
  ``sar``, a non-constant product, a zero or sign extension, a sub-register
  insertion) whose operands are themselves canonical terms.  Commutative
  opaque operations sort their operands.
- An 8- or 16-bit value is ``("b", width, inner)`` where ``inner`` is
  ``("k", value)`` for a constant or an opaque term.  Reading a sub-register
  of a value that was just inserted returns the inserted value; any other
  combination stays opaque.
- Memory is a store log in program order.  A load of ``width`` bytes at
  address ``A`` walks the log backwards: a store whose address differs from
  ``A`` by a constant that puts the two byte ranges apart is skipped (the
  ranges are disjoint on the 2**32 ring); the first store at exactly ``A``
  with the same width supplies the value when no possibly-overlapping store
  lies after it.  Otherwise the load is ``("ld", A, width, deps)`` where
  ``deps`` is the ordered tuple of every store the walk could not prove
  disjoint, up to and including the first exact one.  A load's value is a
  function of the entry memory and exactly those stores, so two equal load
  terms denote equal values.  Two addresses whose difference is not a
  constant are never assumed disjoint: there is no frame-privacy assumption.
- Flags are tracked one term per arithmetic flag (``cf pf af zf sf of``).
  A flag an instruction leaves undefined gets a fresh ``("undef", ...)`` term
  that never equals anything; a flag it preserves keeps its term.
- A conditional branch or ``setcc`` reads its condition as a canonical atom
  with a polarity: after ``cmp a, b`` (or ``sub``) ``je`` is
  ``eqz(a - b)`` with the sign of ``a - b`` normalised, ``jb`` is
  ``ltu(a, b)``, ``ja`` is ``ltu(b, a)``, ``jae``/``jbe`` their negations,
  and the signed forms likewise; after a logical operation (``test``,
  ``and``, ``or``, ``xor``) CF=OF=0 is used, so ``test r, r; je`` and
  ``cmp r, 0; je`` both read ``eqz(r)``.  Every other condition is a raw atom
  over the exact flag terms it reads.  An atom decided by constants does not
  fork the path.
- A region proved under a register bijection starts the replacement from a
  renamed entry state (:func:`entry_state`): its register ``x`` holds the
  donor's entry atom ``("reg0", sigma^-1(x))``, so the two versions' terms
  are written over one set of entry atoms.

x87 (see :class:`X87State`).  The register stack is modelled relative to
the region's entry, whose depth the simulator does not know: ST(i) is the
entry-relative position ``i - push``; an entry register is the atom
``("fst0", k)``; each path records ``need`` (one more than the deepest entry
register it touches) and ``peak`` (its highest net push), and the caller
must show from the whole body that every entry depth covers ``need`` and
leaves room for ``peak`` (:mod:`reprobit.classic.region_x87`): stack
underflow and overflow are refused, never modelled.  Values are
uninterpreted terms over their exact operands with no algebraic identity:
``("fld", w, m)`` a load of a w-bit float, ``("fild", w, m)`` of an
integer, ``("fmem", w, m)`` a memory operand of an arithmetic instruction
(not the same term as a loaded register), ``("fop", op, a, b)`` for add and
mul with (destination, source) order and for sub and div with (minuend,
subtrahend) and (dividend, divisor) order -- so ``fsub``, ``fsubr`` and the
popping forms that compute one difference meet, as the hardware probe
shows they are one function -- and ``("fun", op, a)`` for chs, abs and
sqrt.  A store to memory writes ``("fstm", w, x)``, the rounding of ``x`` to
the slot, so a spill and reload is ``("fld", w, ("fstm", w, x))`` and never
``x``: no precision-control setting makes it the identity, because a
register keeps a 15-bit exponent.  The terms are therefore exact under
whatever control word the two versions share (the region never changes
it), and no precision or rounding mode is pinned.  Every operation that can
raise a floating-point exception is an event in the footprint, so equal
footprints give equal sticky exception flags; register copies, ``fxch``,
``fchs``, ``fabs``, ``fild`` and the constants raise none.  A compare
defines C0, C2 and C3 as exact functions of its outcome (greater, less,
equal, unordered) and clears C1; every other instruction leaves C0-C3
undefined (fresh ``("x87undef", ...)`` terms).  ``fnstsw ax`` puts the
status word in AX; ``test``/``and`` of AH with an immediate reads exactly
the masked bits and refuses an undefined one, and a zero test over one
compare's bits is the canonical atom "the outcome lies in this set" with
the operand pair in a fixed order.  Any other use of the status word, and
any path whose conditions, stores or footprint mention an undefined bit, is
refused.  A call names the x87 stack and the event set in its event; no
x87 instruction may follow a call inside the region.

Every instruction outside the closed set below is refused, as is any
relocated field the simulator does not consume as a displacement or
immediate, any absolute address without a relocation, any prefix but the
operand-size prefix on the forms that admit it, and any branch that is not
strictly forward to an instruction boundary of the region or to its exit.

Closed set: ``mov`` (8/16/32-bit register, memory and immediate forms, and
the 8/32-bit accumulator ``moffs`` forms A0-A3),
``lea``, ``movzx``/``movsx``, ``add or and sub xor cmp`` in every ModR/M and
accumulator form (8/16/32-bit), ``test``, ``inc``/``dec``, ``neg``/``not``,
``shl shr sar`` by an immediate or by one, ``imul`` (one, two and three
operand), ``mul``, ``div`` and ``idiv`` (32-bit; a division is an event both
versions must perform on the same operands), ``setcc``, ``push`` (register,
immediate, memory), ``pop`` (register), ``nop``, ``jcc`` and ``jmp``
(rel8/rel32), and a direct call (``call rel32``, ``call [abs32]``) to a
callee whose MSVC C decoration fixes a register-free convention
(:func:`_call` states its exact model), and the x87 forms ``fld``/``fst``/
``fstp`` m32 and m64, ``fild`` m16/m32/m64, ``fadd fmul fsub fsubr fdiv
fdivr`` with m32, m64, ``st, st(i)``, ``st(i), st`` and popping operands,
``fcom fcomp`` (m32, m64, st(i)), ``fcompp``, ``fucom fucomp`` st(i),
``fucompp``, ``fld st(i)``, ``fst``/``fstp st(i)``, ``fxch``, ``fchs``,
``fabs``, ``fsqrt``, ``fld1``, ``fldz`` and ``fnstsw ax``.  No other call,
no return, string instruction, other x87 instruction (``fist``/``fistp``,
``fldcw``, the transcendentals, the environment instructions, ``fwait``)
or indirect transfer is admitted.
"""

from __future__ import annotations

from collections.abc import Iterable, Mapping
from dataclasses import dataclass, field
from typing import Any, TypeAlias, cast

from reprobit.binary import require
from reprobit.ia32_decode import supported_ia32_instruction_length

_MASK = 0xFFFFFFFF
_REGS = ("eax", "ecx", "edx", "ebx", "esp", "ebp", "esi", "edi")
FLAG_NAMES = ("cf", "pf", "af", "zf", "sf", "of")
_CONDITION_FLAGS: dict[int, tuple[str, ...]] = {
    0: ("of",),
    2: ("cf",),
    4: ("zf",),
    6: ("cf", "zf"),
    8: ("sf",),
    10: ("pf",),
    12: ("sf", "of"),
    14: ("zf", "sf", "of"),
}
MAX_PATHS = 64
MAX_STEPS = 4096

Term: TypeAlias = Any
# A relocated field's target: a symbol read as an absolute value (DIR32), or
# ``("rel32", symbol)`` for a call's PC-relative field.
RelocationTarget: TypeAlias = str | tuple[str, str]


def lin(const: int = 0, terms: Iterable[tuple[Term, int]] = ()) -> Term:
    """The canonical linear form of ``const + sum(coeff * atom)`` mod 2**32."""
    acc: dict[Term, int] = {}
    for atom, coeff in terms:
        acc[atom] = (acc.get(atom, 0) + coeff) & _MASK
    items = tuple(sorted(((a, c) for a, c in acc.items() if c), key=lambda p: repr(p[0])))
    return ("lin", const & _MASK, items)


def lin_atom(atom: Term) -> Term:
    return ("lin", 0, ((atom, 1),))


def lin_add(left: Term, right: Term) -> Term:
    return lin(left[1] + right[1], left[2] + right[2])


def lin_scale(value: Term, factor: int) -> Term:
    return lin(value[1] * factor, ((atom, coeff * factor) for atom, coeff in value[2]))


def lin_sub(left: Term, right: Term) -> Term:
    return lin_add(left, lin_scale(right, -1))


def const_of(value: Term) -> int | None:
    return value[1] if value[0] == "lin" and not value[2] else None


def _single_atom(value: Term) -> Term | None:
    if value[0] == "lin" and value[1] == 0 and len(value[2]) == 1 and value[2][0][1] == 1:
        return value[2][0][0]
    return None


def _small(width: int, value: int) -> Term:
    return ("b", width, ("k", value & ((1 << width) - 1)))


def _small_const(value: Term) -> int | None:
    return value[2][1] if value[0] == "b" and value[2][0] == "k" else None


def _signed(value: int, width: int) -> int:
    value &= (1 << width) - 1
    return value - (1 << width) if value >> (width - 1) else value


def extract(value: Term, low: int, width: int) -> Term:
    """Bits [low, low+width) of a 32-bit value, as a sub-width term."""
    constant = const_of(value)
    if constant is not None:
        return _small(width, constant >> low)
    atom = _single_atom(value)
    if atom is not None and atom[0] == "ins":
        _, old, ins_low, ins_width, inserted = atom
        if (ins_low, ins_width) == (low, width):
            return inserted
        if low + width <= ins_low or ins_low + ins_width <= low:
            return extract(old, low, width)
    if atom is not None and atom[0] == "ins" and (atom[2], atom[3]) == (0, 16):
        inserted = atom[4]
        if inserted[0] == "b" and inserted[2][0] == "fsw":
            # ``fnstsw ax``: AH holds C0 C1 C2 TOP C3 B, AL the exception bits.
            if (low, width) == (8, 8):
                return ("b", 8, ("fswh", *inserted[2][1:]))
            if (low, width) == (0, 8):
                return ("b", 8, ("fswl", inserted[2][6]))
    if atom is not None and atom[0] in ("zx", "sx") and low == 0 and width == atom[2]:
        return atom[1]
    if atom is not None and atom[0] == "zx" and low >= atom[2]:
        return _small(width, 0)
    return ("b", width, ("ext", value, low))


def insert(old: Term, low: int, width: int, part: Term) -> Term:
    """``old`` with bits [low, low+width) replaced by the sub-width term ``part``."""
    constant, small = const_of(old), _small_const(part)
    if constant is not None and small is not None:
        mask = ((1 << width) - 1) << low
        return lin((constant & ~mask) | (small << low))
    if extract(old, low, width) == part:
        return old
    atom = _single_atom(old)
    if atom is not None and atom[0] == "ins" and (atom[2], atom[3]) == (low, width):
        old = atom[1]
    return lin_atom(("ins", old, low, width, part))


def zero_extend(part: Term, width: int) -> Term:
    small = _small_const(part)
    return lin(small) if small is not None else lin_atom(("zx", part, width))


def sign_extend(part: Term, width: int) -> Term:
    small = _small_const(part)
    return lin(_signed(small, width)) if small is not None else lin_atom(("sx", part, width))


def _bitop(name: str, width: int, left: Term, right: Term) -> Term:
    """``and``/``or``/``xor`` with constant folding and idempotence."""
    if width == 8 and (_is_fswh(left) or _is_fswh(right)):
        return _fsw_mask(name, left, right)
    mask = (1 << width) - 1
    if width == 32:
        a, b = const_of(left), const_of(right)
    else:
        a, b = _small_const(left), _small_const(right)
    if a is not None and b is not None:
        value = {"and": a & b, "or": a | b, "xor": a ^ b}[name] & mask
        return lin(value) if width == 32 else _small(width, value)
    if left == right:
        if name == "xor":
            return lin(0) if width == 32 else _small(width, 0)
        return left
    for constant, other in ((a, right), (b, left)):
        if constant is None:
            continue
        if (name == "and" and constant == 0) or (name == "or" and constant == mask):
            return lin(constant) if width == 32 else _small(width, constant)
        if (name in ("or", "xor") and constant == 0) or (name == "and" and constant == mask):
            return other
    operands = tuple(sorted((left, right), key=repr))
    return (
        lin_atom(("op", name, width, operands))
        if width == 32
        else ("b", width, ("op", name, operands))
    )


def _opaque(name: str, width: int, *operands: Term) -> Term:
    return lin_atom((name, width, operands)) if width == 32 else ("b", width, (name, operands))


def address_relation(left: Term, left_width: int, right: Term, right_width: int) -> str:
    """``same``, ``disjoint`` or ``unknown`` for two byte ranges at symbolic addresses."""
    distance = const_of(lin_sub(right, left))
    if distance is None:
        return "unknown"
    if distance == 0 and left_width == right_width:
        return "same"
    if distance >= left_width and distance + right_width <= 1 << 32:
        return "disjoint"
    return "unknown"


# --- the x87 status word -------------------------------------------------------

# The four outcomes of an x87 compare of ST(0) with its source, and the
# condition bits each sets (C1 is cleared by every compare).  Measured with
# MSVC 5.0 inline assembly under Wine for fcom/fcomp m32 and m64, fcom/fcomp
# ST(1), fcompp, fucom/fucomp ST(1) and fucompp, with C0-C3 preset both to
# 0 and to 1 (tests/test_classic_region_x87.py records the probe).
FCMP_OUTCOMES = ("eq", "gt", "lt", "un")
FCMP_BITS: dict[str, dict[str, int]] = {
    "gt": {"c0": 0, "c1": 0, "c2": 0, "c3": 0},
    "lt": {"c0": 1, "c1": 0, "c2": 0, "c3": 0},
    "eq": {"c0": 0, "c1": 0, "c2": 0, "c3": 1},
    "un": {"c0": 1, "c1": 0, "c2": 1, "c3": 1},
}
_MIRROR = {"gt": "lt", "lt": "gt", "eq": "eq", "un": "un"}
# AH after ``fnstsw ax``: bit 0 C0, 1 C1, 2 C2, 3-5 TOP, 6 C3, 7 B.
_AH_BITS = ((0, "c0"), (1, "c1"), (2, "c2"), (6, "c3"))


def _is_fswh(value: Term) -> bool:
    return bool(value[0] == "b" and value[2][0] == "fswh")


def _fsw_mask(name: str, left: Term, right: Term) -> Term:
    """``and``/``test`` of AH (after ``fnstsw ax``) with an immediate.

    The result names exactly the bits the mask keeps.  A kept condition bit
    that the last x87 instruction left undefined is refused: Intel defines
    C0, C2 and C3 only after a compare, and the simulator never guesses what
    a processor leaves in an undefined bit.
    """
    status, other = (left, right) if _is_fswh(left) else (right, left)
    mask = _small_const(other)
    require(
        name == "and" and mask is not None,
        "an x87 status-word byte is combined other than by masking it with an immediate, which "
        "is outside the simulator's closed set",
    )
    c0, c1, c2, c3, top, exceptions = status[2][1:]
    terms = {"c0": c0, "c1": c1, "c2": c2, "c3": c3}
    kept: list[tuple[str, Term]] = []
    for bit, bit_name in _AH_BITS:
        if not cast(int, mask) >> bit & 1:
            continue
        term = terms[bit_name]
        require(
            term[0] != "x87undef",
            f"the x87 condition bit {bit_name.upper()} is read but the last x87 instruction left "
            "it "
            "undefined",
        )
        if term != ("fbit", 0):
            kept.append((bit_name, term))
    if cast(int, mask) & 0x38:
        kept.append(("top", (cast(int, mask) & 0x38, top)))
    if cast(int, mask) & 0x80:
        kept.append(("b", exceptions))
    if not kept:
        return _small(8, 0)
    return ("b", 8, ("fswand", mask, tuple(kept)))


def fcc_atom(compare: Term, outcomes: Iterable[str]) -> Term | bool:
    """The canonical atom "the compare's outcome lies in ``outcomes``", or a constant.

    A compare of ``a`` with ``b`` has outcome ``gt`` exactly when one of
    ``b`` with ``a`` has ``lt``; the atom names the operand pair in a fixed
    order and mirrors the outcome set to match, so both spellings meet.
    """
    chosen = frozenset(outcomes)
    if not chosen:
        return False
    if len(chosen) == len(FCMP_OUTCOMES):
        return True
    _tag, left, right = compare
    if repr(right) < repr(left):
        compare = ("fcmp", right, left)
        chosen = frozenset(_MIRROR[outcome] for outcome in chosen)
    return ("fcc", compare, tuple(sorted(chosen)))


def _fsw_zero(result: Term) -> Term | bool | None:
    """``(AH & mask) == 0`` as an outcome set of one compare, when the kept bits are its own."""
    kept = result[2][2]
    compares = set()
    for bit_name, term in kept:
        if bit_name not in ("c0", "c2", "c3") or term[0] != "fcbit":
            return None
        compares.add(term[2])
    if len(compares) != 1:
        return None
    names = {bit_name for bit_name, _term in kept}
    return fcc_atom(
        next(iter(compares)),
        (o for o in FCMP_OUTCOMES if all(FCMP_BITS[o][name] == 0 for name in names)),
    )


def _fcc_allowed(conditions: Iterable[tuple[Term, bool]]) -> dict[Term, frozenset[str]]:
    """The outcomes each compare can still have under a path condition."""
    allowed: dict[Term, frozenset[str]] = {}
    for atom, value in conditions:
        if isinstance(atom, tuple) and atom[0] == "fcc":
            outcomes = frozenset(atom[2])
            if not value:
                outcomes = frozenset(FCMP_OUTCOMES) - outcomes
            allowed[atom[1]] = allowed.get(atom[1], frozenset(FCMP_OUTCOMES)) & outcomes
    return allowed


# --- conditions ---------------------------------------------------------------


def _eqz(width: int, value: Term) -> Term | bool:
    if width == 32:
        constant = const_of(value)
        if constant is not None:
            return constant == 0
        return ("eqz", 32, min(value, lin_scale(value, -1), key=repr))
    small = _small_const(value)
    if small is not None:
        return small == 0
    if value[2][0] == "fswand":
        decided = _fsw_zero(value)
        if decided is not None:
            return decided
    return ("eqz", width, value)


def _eq(width: int, left: Term, right: Term) -> Term | bool:
    if width == 32:
        return _eqz(32, lin_sub(left, right))
    if left == right:
        return True
    a, b = _small_const(left), _small_const(right)
    if a is not None and b is not None:
        return a == b
    if a == 0:
        return _eqz(width, right)
    if b == 0:
        return _eqz(width, left)
    return ("eq", width, tuple(sorted((left, right), key=repr)))


def _constant(width: int, value: Term) -> int | None:
    return const_of(value) if width == 32 else _small_const(value)


def _ltu(width: int, left: Term, right: Term) -> Term | bool:
    if left == right:
        return False
    a, b = _constant(width, left), _constant(width, right)
    if a is not None and b is not None:
        return a < b
    return ("ltu", width, left, right)


def _lts(width: int, left: Term, right: Term) -> Term | bool:
    if left == right:
        return False
    a, b = _constant(width, left), _constant(width, right)
    if a is not None and b is not None:
        return _signed(a, width) < _signed(b, width)
    return ("lts", width, left, right)


def _sgn(width: int, value: Term) -> Term | bool:
    constant = _constant(width, value)
    if constant is not None:
        return bool(constant >> (width - 1))
    return ("sgn", width, value)


def condition(code: int, flags: Mapping[str, Term]) -> tuple[Term, bool] | bool:
    """The canonical (atom, value-when-satisfied) of condition ``code``, or a constant."""
    base, inverted = code & ~1, bool(code & 1)
    read = _CONDITION_FLAGS[base]
    terms = [flags[name] for name in read]
    producers = {term[2:] for term in terms if term[0] == "flag"}
    consts = {term[1]: term[2] for term in terms if term[0] == "fconst"}
    atom: Term | bool | None = None
    value = True
    if len(producers) == 1 and all(term[0] in ("flag", "fconst") for term in terms):
        producer = next(iter(producers))
        kind, width = producer[0], producer[1]
        if kind == "sub" and not consts:
            left, right = producer[2], producer[3]
            if base == 4:
                atom = _eq(width, left, right)
            elif base == 2:
                atom = _ltu(width, left, right)
            elif base == 6:
                atom, value = _ltu(width, right, left), False
            elif base == 12:
                atom = _lts(width, left, right)
            elif base == 14:
                atom, value = _lts(width, right, left), False
        elif kind == "logic" and all(consts.get(name, 0) == 0 for name in ("cf", "of")):
            result = producer[3]
            if base in (4, 6):
                atom = _eqz(width, result)
            elif base in (8, 12):
                atom = _sgn(width, result)
    elif consts and not producers and set(consts) == set(read):
        if base == 0:
            atom = bool(consts["of"])
        elif base == 2:
            atom = bool(consts["cf"])
    if atom is None:
        atom = ("raw", base, tuple(terms))
    if isinstance(atom, bool):
        return atom != inverted
    return (atom, value != inverted)


def canonical_flag(name: str, term: Term) -> Term:
    """A flag's value as a canonical term, for comparing two versions' exit flags.

    ZF is the only flag given a semantic normal form: after ``sub``/``cmp``
    of ``a`` and ``b`` it is ``a == b`` (an equality, symmetric in its
    operands), after a logical operation it is ``result == 0``, and the two
    meet (``cmp r, 0`` and ``test r, r``).  Both forms are exact functions of
    the operands, so equal canonical terms denote equal flags.  Every other
    flag, and ZF of any other producer, is its exact producer term.
    """
    if name == "zf" and term[0] == "flag" and term[1] == "zf":
        kind, width = term[2], term[3]
        if kind == "sub":
            return ("zf=", _eq(width, term[4], term[5]))
        if kind == "logic":
            return ("zf=", _eqz(width, term[5]))
    return term


# --- execution state ------------------------------------------------------------


X87_CONDITION_BITS = ("c0", "c1", "c2", "c3")


@dataclass
class X87State:
    """The x87 unit along one path, relative to the region's entry.

    ``push`` is the net number of pushes since the entry (negative after
    more pops than pushes), so ST(i) is the entry-relative *position*
    ``i - push``: position ``k >= 0`` is the entry's ST(k), a negative
    position a slot the region pushed.  ``slots`` holds every position the
    path has written; a position it has not written holds the entry term
    ``("fst0", k)`` (``("fst@", call, k)`` after a call).  ``need`` is one
    more than the deepest entry position the path touched (the entry depth
    must be at least ``need``) and ``peak`` the largest ``push`` (the entry
    depth plus ``peak`` must not exceed eight).  ``cc`` holds C0-C3; an
    undefined bit is a fresh ``("x87undef", ...)`` term.  ``events`` lists
    every operation that can raise a floating-point exception, so two paths
    with equal event sets leave equal sticky exception flags.
    """

    push: int = 0
    slots: dict[int, Term] = field(default_factory=dict)
    base: Term = None
    need: int = 0
    peak: int = 0
    cc: dict[str, Term] = field(
        default_factory=lambda: {name: ("fcc0", name) for name in X87_CONDITION_BITS}
    )
    events: list[Term] = field(default_factory=list)
    used: bool = False
    after_call: bool = False

    def fork(self) -> X87State:
        return X87State(
            self.push,
            dict(self.slots),
            self.base,
            self.need,
            self.peak,
            dict(self.cc),
            list(self.events),
            self.used,
            self.after_call,
        )

    def entry_term(self, position: int) -> Term:
        return ("fst0", position) if self.base is None else ("fst@", self.base, position)

    def view(self) -> X87View:
        live = tuple(
            sorted(
                (
                    (position, term)
                    for position, term in self.slots.items()
                    if position >= -self.push
                ),
                key=lambda item: item[0],
            )
        )
        return X87View(self.base, self.push, live, self.need, self.peak, self.used)


@dataclass(frozen=True)
class X87View:
    """A path's x87 stack at its exit: the registers from TOP down, and its bounds."""

    base: Term = None
    push: int = 0
    slots: tuple[tuple[int, Term], ...] = ()
    need: int = 0
    peak: int = 0
    used: bool = False

    def term(self, position: int) -> Term:
        for at, term in self.slots:
            if at == position:
                return term
        return ("fst0", position) if self.base is None else ("fst@", self.base, position)


def x87_stacks_equivalent(left: X87View, right: X87View) -> str | None:
    """None when two exits leave the same x87 stack (the same TOP and every register), else why.

    Both start from one entry stack of some depth D.  Equal net pushes give
    the same TOP and the same depth; every position from TOP down that
    either path wrote must hold equal terms, and a position neither wrote
    holds the same entry register in both.  Registers below the entry depth
    are empty in both.
    """
    if left.push != right.push:
        return (
            f"they leave the x87 stack at depths {left.push:+d} and {right.push:+d} from its entry"
        )
    if left.base != right.base:
        return "their x87 stacks descend from different calls"
    positions = {at for at, _term in left.slots} | {at for at, _term in right.slots}
    for position in sorted(positions):
        if left.term(position) != right.term(position):
            return f"they leave different values in ST({position + left.push})"
    return None


@dataclass
class PathState:
    """One path's machine state while it runs through the region."""

    regs: dict[str, Term]
    flags: dict[str, Term]
    stores: list[tuple[Term, int, Term]] = field(default_factory=list)
    footprint: set[Term] = field(default_factory=set)
    conditions: list[tuple[Term, bool]] = field(default_factory=list)
    relocations_read: set[int] = field(default_factory=set)
    epoch: Term = None
    events: list[Term] = field(default_factory=list)
    fpu: X87State = field(default_factory=X87State)

    def fork(self) -> PathState:
        return PathState(
            dict(self.regs),
            dict(self.flags),
            list(self.stores),
            set(self.footprint),
            list(self.conditions),
            set(self.relocations_read),
            self.epoch,
            list(self.events),
            self.fpu.fork(),
        )


@dataclass(frozen=True)
class PathResult:
    """A completed path: its conditions and its end state."""

    conditions: tuple[tuple[Term, bool], ...]
    regs: dict[str, Term]
    flags: dict[str, Term]
    stores: tuple[tuple[Term, int, Term], ...]
    footprint: frozenset[Term]
    relocations_read: frozenset[int]
    exit: int = 0
    events: tuple[Term, ...] = ()
    x87: X87View = field(default_factory=X87View)
    fcc: dict[str, Term] = field(default_factory=dict)


def entry_state(entry_names: Mapping[str, str] | None = None) -> PathState:
    """The symbolic entry state; ``entry_names`` renames which entry value a register holds.

    By default register ``r`` holds the atom ``("reg0", r)``.  Under a
    register bijection the replacement's register ``x`` holds the value the
    donor keeps in ``entry_names[x]``, so both versions start from one set of
    entry atoms named in the donor's registers.
    """
    names = dict(entry_names or {})
    require(
        set(names) <= set(_REGS)
        and set(names.values()) <= set(_REGS)
        and sorted(names) == sorted(names.values())
        and names.get("esp", "esp") == "esp",
        "a region entry renaming is not a permutation of the general registers fixing ESP",
    )
    return PathState(
        {name: lin_atom(("reg0", names.get(name, name))) for name in _REGS},
        {name: ("flag0", name) for name in FLAG_NAMES},
    )


def _load(state: PathState, address: Term, width: int) -> Term:
    state.footprint.add((address, width))
    deps: list[tuple[Term, int, Term]] = []
    for entry in reversed(state.stores):
        relation = address_relation(address, width, entry[0], entry[1])
        if relation == "disjoint":
            continue
        if relation == "same" and not deps:
            return entry[2]
        deps.append(entry)
        if relation == "same":
            break
    term: Term = ("ld", address, width, tuple(reversed(deps)))
    if state.epoch is not None:
        # Memory since the last call is that call's result: the load names it.
        term = (*term, state.epoch)
    return lin_atom(term) if width == 4 else ("b", width * 8, term)


def _store(state: PathState, address: Term, width: int, value: Term) -> None:
    state.footprint.add((address, width))
    state.stores.append((address, width, value))


class _Instruction:
    """One decoded instruction of the closed set: its operand layout."""

    def __init__(
        self,
        code: bytes,
        offset: int,
        relocations: Mapping[int, RelocationTarget],
        context: str,
    ) -> None:
        self.offset = offset
        self.context = f"{context} at {offset}"
        self.length = supported_ia32_instruction_length(code[offset:], self.context)
        self.raw = code[offset : offset + self.length]
        require(len(self.raw) == self.length, f"{self.context}: the instruction is truncated")
        self.relocations = relocations
        self.consumed: set[int] = set()
        cursor = 0
        self.operand16 = False
        while self.raw[cursor] in (0x66,):
            self.operand16 = True
            cursor += 1
        require(
            self.raw[cursor] not in (0x26, 0x2E, 0x36, 0x3E, 0x64, 0x65, 0xF0, 0xF2, 0xF3, 0x67),
            f"{self.context}: a prefixed instruction is outside the simulator's closed set",
        )
        self.opcode = self.raw[cursor]
        cursor += 1
        if self.opcode == 0x0F:
            self.opcode = 0x0F00 | self.raw[cursor]
            cursor += 1
        self.cursor = cursor
        self.modrm_at = cursor
        for at in range(offset, offset + self.length):
            if at in relocations:
                require(
                    at + 4 <= offset + self.length,
                    f"{self.context}: a relocated field straddles the instruction",
                )

    def reloc(self, local: int) -> Term | None:
        at = self.offset + local
        symbol = self.relocations.get(at)
        if symbol is None:
            return None
        require(
            isinstance(symbol, str),
            f"{self.context}: a PC-relative relocated field is read as an absolute value",
        )
        self.consumed.add(at)
        return lin_atom(("sym", symbol))

    def call_target(self, local: int) -> str:
        """The symbol of a ``call rel32``'s PC-relative relocated field."""
        at = self.offset + local
        symbol = self.relocations.get(at)
        require(
            isinstance(symbol, tuple) and symbol[0] == "rel32",
            f"{self.context}: a relative call without a PC-relative relocation is outside the "
            "simulator's closed set",
        )
        self.consumed.add(at)
        return cast(tuple[str, str], symbol)[1]

    def immediate(self, local: int, size: int, signed: bool = True) -> Term:
        raw = self.raw[local : local + size]
        require(len(raw) == size, f"{self.context}: the immediate is truncated")
        value = int.from_bytes(raw, "little", signed=signed)
        if size == 4:
            symbol = self.reloc(local)
            if symbol is not None:
                return lin_add(symbol, lin(value))
        return lin(value)

    def modrm(self) -> tuple[int, int, int]:
        byte = self.raw[self.modrm_at]
        return byte >> 6, (byte >> 3) & 7, byte & 7

    def operand_end(self) -> int:
        """The local offset just past the ModR/M, SIB and displacement bytes."""
        mod, _reg, rm = self.modrm()
        cursor = self.modrm_at + 1
        if mod == 3:
            return cursor
        if rm == 4:
            sib = self.raw[cursor]
            cursor += 1
            if mod == 0 and sib & 7 == 5:
                cursor += 4
        elif mod == 0 and rm == 5:
            cursor += 4
        if mod == 1:
            cursor += 1
        elif mod == 2:
            cursor += 4
        return cursor

    def address(self, regs: Mapping[str, Term]) -> Term:
        mod, _reg, rm = self.modrm()
        require(mod != 3, f"{self.context}: a register operand where memory was expected")
        cursor = self.modrm_at + 1
        total = lin(0)
        has_base = True
        if rm == 4:
            sib = self.raw[cursor]
            cursor += 1
            scale, index, base = 1 << (sib >> 6), (sib >> 3) & 7, sib & 7
            if index != 4:
                total = lin_add(total, lin_scale(regs[_REGS[index]], scale))
            if mod == 0 and base == 5:
                has_base = False
            else:
                total = lin_add(total, regs[_REGS[base]])
        elif mod == 0 and rm == 5:
            has_base = False
        else:
            total = lin_add(total, regs[_REGS[rm]])
        if not has_base or mod == 2:
            symbol = self.reloc(cursor)
            displacement = int.from_bytes(self.raw[cursor : cursor + 4], "little", signed=True)
            if not has_base:
                require(
                    symbol is not None,
                    f"{self.context}: an absolute address without a relocation is outside the "
                    "simulator's closed set",
                )
            if symbol is not None:
                total = lin_add(total, symbol)
            total = lin_add(total, lin(displacement))
        elif mod == 1:
            total = lin_add(
                total, lin(int.from_bytes(self.raw[cursor : cursor + 1], "little", signed=True))
            )
        return total


def _get(state: PathState, number: int, width: int) -> Term:
    if width == 32:
        return state.regs[_REGS[number]]
    if width == 16:
        return extract(state.regs[_REGS[number]], 0, 16)
    if number < 4:
        return extract(state.regs[_REGS[number]], 0, 8)
    return extract(state.regs[_REGS[number - 4]], 8, 8)


def _set(state: PathState, number: int, width: int, value: Term) -> None:
    if width == 32:
        state.regs[_REGS[number]] = value
    elif width == 16:
        state.regs[_REGS[number]] = insert(state.regs[_REGS[number]], 0, 16, value)
    elif number < 4:
        state.regs[_REGS[number]] = insert(state.regs[_REGS[number]], 0, 8, value)
    else:
        state.regs[_REGS[number - 4]] = insert(state.regs[_REGS[number - 4]], 8, 8, value)


def _read_rm(state: PathState, item: _Instruction, width: int) -> Term:
    mod, _reg, rm = item.modrm()
    if mod == 3:
        return _get(state, rm, width)
    return _load(state, item.address(state.regs), width // 8)


def _write_rm(state: PathState, item: _Instruction, width: int, value: Term) -> None:
    mod, _reg, rm = item.modrm()
    if mod == 3:
        _set(state, rm, width, value)
    else:
        _store(state, item.address(state.regs), width // 8, value)


class _Undefined:
    """Fresh, never-equal terms for flags an instruction leaves undefined."""

    def __init__(self, tag: str) -> None:
        self.tag = tag
        self.count = 0

    def __call__(self, name: str) -> Term:
        self.count += 1
        return ("undef", name, self.tag, self.count)


def _arith_flags(state: PathState, kind: str, width: int, left: Term, right: Term) -> None:
    if kind == "add":
        left, right = sorted((left, right), key=repr)
    for name in FLAG_NAMES:
        state.flags[name] = ("flag", name, kind, width, left, right)


def _logic_flags(state: PathState, width: int, result: Term, undefined: _Undefined) -> None:
    for name in ("zf", "sf", "pf"):
        state.flags[name] = ("flag", name, "logic", width, "result", result)
    state.flags["cf"] = ("fconst", "cf", 0)
    state.flags["of"] = ("fconst", "of", 0)
    state.flags["af"] = undefined("af")


def _alu(
    state: PathState, name: str, width: int, left: Term, right: Term, undefined: _Undefined
) -> Term | None:
    """Apply one of add/or/and/sub/xor/cmp; return the result (None for cmp)."""
    if name in ("add", "sub", "cmp"):
        kind = "add" if name == "add" else "sub"
        _arith_flags(state, kind, width, left, right)
        if name == "cmp":
            return None
        if width == 32:
            return lin_add(left, right) if name == "add" else lin_sub(left, right)
        a, b = _small_const(left), _small_const(right)
        if a is not None and b is not None:
            return _small(width, a + b if name == "add" else a - b)
        if name == "add":
            return ("b", width, ("op", "add", tuple(sorted((left, right), key=repr))))
        return ("b", width, ("op", "sub", (left, right)))
    result = _bitop(name, width, left, right)
    _logic_flags(state, width, result, undefined)
    return result


_ALU_NAMES = {0: "add", 1: "or", 4: "and", 5: "sub", 6: "xor", 7: "cmp"}
_SHIFT_NAMES = {4: "shl", 5: "shr", 7: "sar"}


def _shift(state: PathState, kind: str, value: Term, count: int, undefined: _Undefined) -> Term:
    count &= 31
    if count == 0:
        return value
    if kind == "shl":
        result = lin_scale(value, 1 << count)
    else:
        constant = const_of(value)
        if constant is not None:
            if kind == "shr":
                result = lin(constant >> count)
            else:
                result = lin(_signed(constant, 32) >> count)
        else:
            result = lin_atom((kind, 32, (value, count)))
    for name in ("cf", "sf", "zf", "pf"):
        state.flags[name] = ("flag", name, kind, 32, value, count)
    state.flags["of"] = ("flag", "of", kind, 32, value, 1) if count == 1 else undefined("of")
    state.flags["af"] = undefined("af")
    return result


def _multiply(state: PathState, left: Term, right: Term, undefined: _Undefined) -> Term:
    a, b = const_of(left), const_of(right)
    if a is not None:
        result = lin_scale(right, a)
    elif b is not None:
        result = lin_scale(left, b)
    else:
        result = lin_atom(("op", "mul", 32, tuple(sorted((left, right), key=repr))))
    for name in ("cf", "of"):
        state.flags[name] = ("flag", name, "imul", 32, left, right)
    for name in ("pf", "af", "zf", "sf"):
        state.flags[name] = undefined(name)
    return result


def _wide(state: PathState, digit: int, source: Term, undefined: _Undefined) -> None:
    """``mul``/``imul``/``div``/``idiv`` of EDX:EAX by a 32-bit source (F7 /4-/7).

    The low half of a product is the same ring product for the signed and
    unsigned forms; the high half and both division results are opaque terms
    of their exact operands.  A division is also recorded in the footprint
    as an event, so two versions are compared only when they divide the same
    operands -- and therefore raise #DE together.
    """
    signed = digit in (5, 7)
    eax, edx = state.regs["eax"], state.regs["edx"]
    if digit in (4, 5):
        low = _multiply(state, eax, source, undefined)
        pair = tuple(sorted((eax, source), key=repr))
        state.regs["eax"] = low
        state.regs["edx"] = lin_atom(("mulhi", "s" if signed else "u", pair))
        for name in ("cf", "of"):
            state.flags[name] = ("flag", name, "mulhi", 32, "s" if signed else "u", pair)
        return
    operands = (edx, eax, source)
    kind = "s" if signed else "u"
    state.footprint.add(("divide", kind, operands))
    state.regs["eax"] = lin_atom(("quotient", kind, operands))
    state.regs["edx"] = lin_atom(("remainder", kind, operands))
    for name in FLAG_NAMES:
        state.flags[name] = undefined(name)


_C_IDENTIFIER = frozenset("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_")


def callee_stack_pop(symbol: object) -> int | None:
    """The bytes a register-free callee pops on return, or None when the name does not say.

    MSVC decorates a C ``__cdecl`` function ``_name`` (the caller pops) and a
    ``__stdcall`` one ``_name@N`` (the callee pops N bytes); the import
    thunk's slot of either is ``__imp_`` before it.  Only ``__fastcall``
    (``@name@N``) and C++ member functions (``?...``) receive arguments in
    registers.  A name whose identifier itself starts with an underscore
    (``__chkstk``, ``__aullshr``, ``__ftol``) is a compiler or runtime helper
    with its own register convention and is not admitted.
    """
    if not isinstance(symbol, str):
        return None
    name = symbol[len("__imp_") :] if symbol.startswith("__imp_") else symbol
    if not name.startswith("_") or name.startswith("__"):
        return None
    core, pop = name[1:], 0
    if "@" in core:
        core, _at, size = core.rpartition("@")
        if not size.isdigit() or "@" in core or int(size) % 4:
            return None
        pop = int(size)
    if not core or core.startswith("_") or not set(core) <= _C_IDENTIFIER:
        return None
    return pop


def register_free_callee(symbol: object) -> bool:
    """Whether a callee's MSVC C decoration says it takes no argument in a register."""
    return callee_stack_pop(symbol) is not None


def store_normal_form(stores: Iterable[tuple[Term, int, Term]]) -> tuple[Any, ...]:
    """The canonical order of a store log up to swapping provably disjoint stores.

    Two logs leave the same memory under :func:`stores_equivalent` exactly
    when they are the same trace over the independence relation "the two
    byte ranges are disjoint" (symmetric and irreflexive), and the
    lexicographically least linearisation of a trace is unique: repeatedly
    take the least store (by its representation) that is disjoint from every
    store still before it.
    """
    remaining = list(stores)
    ordered = []
    while remaining:
        best = None
        for index, item in enumerate(remaining):
            if all(
                address_relation(item[0], item[1], other[0], other[1]) == "disjoint"
                for other in remaining[:index]
            ) and (best is None or repr(item) < repr(remaining[best])):
                best = index
        ordered.append(remaining.pop(cast(int, best)))
    return tuple(ordered)


def _call(
    state: PathState, callee: Term, symbol: object, undefined: _Undefined, context: str
) -> None:
    """A call to a register-free callee: one event named by everything it can read.

    Under the model every classic rewriting uses (callees honour the
    convention their decoration names), the callee reads memory and the
    stack pointer and no general register, may write any memory, returns in
    EDX:EAX, clobbers ECX and the flags, preserves EBX, ESI, EDI and EBP, and
    pops the bytes its decoration states.  The event's term is the callee,
    ESP, the canonical form of every store since the previous event, and
    that event, so two versions' events are equal terms exactly when they
    call the same function from the same state.  Memory after the call is
    unknown: the store log restarts and every later load names the event.
    The pushed return address is part of the call, as for every call the
    layout moves.
    """
    pop = callee_stack_pop(symbol)
    require(
        pop is not None,
        f"{context}: a call to {symbol!r}, whose decoration does not fix a register-free "
        "convention, is outside the simulator's closed set",
    )
    fpu = state.fpu
    identity: Term = (
        "call",
        callee,
        state.regs["esp"],
        store_normal_form(state.stores),
        state.epoch,
    )
    if fpu.used or fpu.base is not None:
        # The callee runs from this x87 state: the stack and the sticky
        # exception flags (the event set so far).  The calling convention
        # gives a callee no input in C0-C3.
        identity = (
            *identity,
            (fpu.base, fpu.push, fpu.view().slots),
            tuple(sorted(set(fpu.events), key=repr)),
        )
    state.events.append(identity)
    state.footprint.add(("event", identity))
    state.stores = []
    state.epoch = identity
    # The x87 state after the call is the callee's function of the state
    # before it (named by the event); how many values it leaves on the stack
    # is not modelled, so no x87 instruction may follow inside the region.
    fpu.base = identity
    fpu.push = 0
    fpu.slots = {}
    fpu.cc = {name: ("fcccall", identity, fpu.cc[name]) for name in X87_CONDITION_BITS}
    fpu.after_call = True
    for name in ("eax", "ecx", "edx"):
        state.regs[name] = lin_atom(("callret", name, identity))
    state.regs["esp"] = lin_add(state.regs["esp"], lin(cast(int, pop)))
    for name in FLAG_NAMES:
        state.flags[name] = undefined(name)


def _push(state: PathState, value: Term) -> None:
    state.regs["esp"] = lin_add(state.regs["esp"], lin(-4))
    _store(state, state.regs["esp"], 4, value)


# --- x87 ------------------------------------------------------------------------

# The value each arithmetic digit computes from ST(0) and the other operand
# (ST(i) or memory): digit 4 is ST(0) - other, 5 other - ST(0), 6 ST(0) /
# other and 7 other / ST(0), in D8 (result in ST(0)) and DC/DE (result in
# ST(i)) alike.  Measured with MSVC 5.0 inline assembly under Wine, raw
# encodings, for every D8/DC/DE register form with i = 1 and 2 (see
# tests/test_classic_region_x87.py).  Subtraction and division are named by
# their minuend and dividend, so ``fsub`` and ``fsubr`` that compute the same
# difference meet: the role probe found the result and the exception flags of
# every subtract (divide) encoding to be one function of (minuend,
# subtrahend) whichever register held which.  Addition and multiplication
# keep the order (destination, source); no commutativity is assumed.
_X87_ARITH = {0: "add", 1: "mul", 4: "sub", 5: "subr", 6: "div", 7: "divr"}


def _x87_arith(kind: str, st0: Term, other: Term, destination_is_st0: bool) -> Term:
    if kind == "sub":
        return ("fop", "sub", st0, other)
    if kind == "subr":
        return ("fop", "sub", other, st0)
    if kind == "div":
        return ("fop", "div", st0, other)
    if kind == "divr":
        return ("fop", "div", other, st0)
    pair = (st0, other) if destination_is_st0 else (other, st0)
    return ("fop", kind, *pair)


class _X87:
    """The x87 operations of one instruction on one path's state."""

    def __init__(self, state: PathState, undefined: _Undefined, context: str) -> None:
        self.state = state
        self.fpu = state.fpu
        self.undefined = undefined
        self.context = context

    def position(self, index: int) -> int:
        position = index - self.fpu.push
        if position >= 0:
            # The entry's ST(position) must be a full register.
            self.fpu.need = max(self.fpu.need, position + 1)
        return position

    def get(self, index: int) -> Term:
        position = self.position(index)
        return self.fpu.slots.get(position, self.fpu.entry_term(position))

    def put(self, index: int, value: Term) -> None:
        self.fpu.slots[self.position(index)] = value

    def push(self, value: Term) -> None:
        self.fpu.push += 1
        self.fpu.peak = max(self.fpu.peak, self.fpu.push)
        self.fpu.slots[-self.fpu.push] = value

    def pop(self) -> None:
        self.fpu.slots.pop(self.position(0), None)
        self.fpu.push -= 1

    def event(self, term: Term) -> None:
        """An operation that can raise a floating-point exception."""
        self.fpu.events.append(term)
        self.state.footprint.add(("fpe", term))

    def undefine(self) -> None:
        """Every condition bit after an instruction that is not a compare (Intel: undefined)."""
        for name in X87_CONDITION_BITS:
            self.undefined.count += 1
            self.fpu.cc[name] = ("x87undef", name, self.undefined.tag, self.undefined.count)

    def compare(self, kind: str, other: Term) -> None:
        compare = ("fcmp", self.get(0), other)
        self.event((kind, *sorted(compare[1:], key=repr)))
        for name in ("c0", "c2", "c3"):
            self.fpu.cc[name] = ("fcbit", name, compare)
        self.fpu.cc["c1"] = ("fbit", 0)

    def status_word(self) -> Term:
        fpu = self.fpu
        exceptions = ("fexc", fpu.base, tuple(sorted(set(fpu.events), key=repr)))
        top = ("ftop", fpu.base, fpu.push)
        return (
            "b",
            16,
            ("fsw", fpu.cc["c0"], fpu.cc["c1"], fpu.cc["c2"], fpu.cc["c3"], top, exceptions),
        )


def _x87_step(state: PathState, item: _Instruction, undefined: _Undefined) -> None:
    """Execute one x87 instruction of the closed set (see the module docstring)."""
    context = item.context
    require(
        not item.operand16,
        f"{context}: an operand-size-prefixed x87 instruction is outside the closed set",
    )
    require(
        not state.fpu.after_call,
        f"{context}: an x87 instruction after a call inside the region is outside the simulator's "
        "closed set (the callee's effect on the x87 stack is not modelled)",
    )
    x87 = _X87(state, undefined, context)
    state.fpu.used = True
    op = item.opcode
    mod, digit, index = item.modrm()
    refused = (
        f"{context}: the x87 instruction {item.raw.hex()} is outside the simulator's closed set"
    )
    if mod != 3:
        if op in (0xD8, 0xDC):
            width = 4 if op == 0xD8 else 8
            operand = ("fmem", width * 8, _load(state, item.address(state.regs), width))
            if digit in (2, 3):
                x87.compare("fcom", operand)
                if digit == 3:
                    x87.pop()
                return
            st0 = x87.get(0)
            result = _x87_arith(_X87_ARITH[digit], st0, operand, True)
            x87.event(result)
            x87.put(0, result)
            x87.undefine()
            return
        if op in (0xD9, 0xDD) and digit in (0, 2, 3):
            width = 4 if op == 0xD9 else 8
            address = item.address(state.regs)
            if digit == 0:
                value = ("fld", width * 8, _load(state, address, width))
                x87.event(value)
                x87.push(value)
            else:
                # A store rounds the register to the slot's format: the
                # memory holds the rounding of the value, never the value.
                stored = ("fstm", width * 8, x87.get(0))
                x87.event(stored)
                _store(state, address, width, lin_atom(stored) if width == 4 else ("b", 64, stored))
                if digit == 3:
                    x87.pop()
            x87.undefine()
            return
        integer = {(0xDF, 0): 2, (0xDB, 0): 4, (0xDF, 5): 8}.get((op, digit))
        require(integer is not None, refused)
        # fild: every 16-, 32- and 64-bit integer converts exactly.
        x87.push(
            (
                "fild",
                cast(int, integer) * 8,
                _load(state, item.address(state.regs), cast(int, integer)),
            )
        )
        x87.undefine()
        return
    if op in (0xD8, 0xDC, 0xDE) and digit in _X87_ARITH:
        st0, other = x87.get(0), x87.get(index)
        result = _x87_arith(_X87_ARITH[digit], st0, other, op == 0xD8)
        x87.event(result)
        if op == 0xD8:
            x87.put(0, result)
        else:
            x87.put(index, result)
            if op == 0xDE:
                x87.pop()
        x87.undefine()
        return
    if op == 0xD8 and digit in (2, 3):
        x87.compare("fcom", x87.get(index))
        if digit == 3:
            x87.pop()
        return
    if (op, digit, index) in ((0xDE, 3, 1), (0xDA, 5, 1)):
        # fcompp / fucompp: ST(0) with ST(1), then two pops.
        x87.compare("fcom" if op == 0xDE else "fucom", x87.get(1))
        x87.pop()
        x87.pop()
        return
    if op == 0xDD and digit in (4, 5):
        x87.compare("fucom", x87.get(index))
        if digit == 5:
            x87.pop()
        return
    if op == 0xDD and digit in (2, 3):
        # fst/fstp ST(i): an exact register copy.
        x87.put(index, x87.get(0))
        if digit == 3:
            x87.pop()
        x87.undefine()
        return
    if op == 0xD9 and digit == 0:
        x87.push(x87.get(index))
        x87.undefine()
        return
    if op == 0xD9 and digit == 1:
        first, other = x87.get(0), x87.get(index)
        x87.put(0, other)
        x87.put(index, first)
        x87.undefine()
        return
    if op == 0xD9 and digit == 4 and index in (0, 1):
        x87.put(0, ("fun", "chs" if index == 0 else "abs", x87.get(0)))
        x87.undefine()
        return
    if op == 0xD9 and digit == 5 and index in (0, 6):
        x87.push(("fconst", 1 if index == 0 else 0))
        x87.undefine()
        return
    if op == 0xD9 and digit == 7 and index == 2:
        result = ("fun", "sqrt", x87.get(0))
        x87.event(result)
        x87.put(0, result)
        x87.undefine()
        return
    if op == 0xDF and digit == 4 and index == 0:
        # fnstsw ax: AX takes the whole status word; Intel leaves C0-C3 undefined after it.
        _set(state, 0, 16, x87.status_word())
        x87.undefine()
        return
    require(False, refused)


def _step(state: PathState, item: _Instruction, undefined: _Undefined) -> tuple[str, Any]:
    """Execute one instruction; return ("fall", None), ("jump", target) or ("branch", ...)."""
    op = item.opcode
    end = item.offset + item.length
    context = item.context
    if item.operand16:
        require(
            op in (0x89, 0x8B, 0xC7, 0x81, 0x83, 0x39, 0x3B, 0x85),
            f"{context}: an operand-size-prefixed instruction is outside the simulator's closed "
            "set",
        )
    width32 = 16 if item.operand16 else 32
    if 0xD8 <= op <= 0xDF:
        _x87_step(state, item, undefined)
        return ("fall", None)
    if op in (0x88, 0x89, 0x8A, 0x8B):
        width = 8 if op in (0x88, 0x8A) else width32
        _mod, reg, _rm = item.modrm()
        if op in (0x88, 0x89):
            _write_rm(state, item, width, _get(state, reg, width))
        else:
            _set(state, reg, width, _read_rm(state, item, width))
        return ("fall", None)
    if 0xA0 <= op <= 0xA3:
        # mov al/eax, [moffs32] and mov [moffs32], al/eax: an absolute address
        # that must carry a relocation, exactly as a mod-00 disp32 operand.
        require(not item.operand16, f"{context}: a 16-bit moffs move is outside the closed set")
        symbol = item.reloc(item.cursor)
        require(
            symbol is not None,
            f"{context}: an absolute address without a relocation is outside the simulator's "
            "closed set",
        )
        address = lin_add(
            cast(Term, symbol),
            lin(int.from_bytes(item.raw[item.cursor : item.cursor + 4], "little", signed=True)),
        )
        width = 8 if op in (0xA0, 0xA2) else 32
        if op in (0xA0, 0xA1):
            _set(state, 0, width, _load(state, address, width // 8))
        else:
            _store(state, address, width // 8, _get(state, 0, width))
        return ("fall", None)
    if op == 0x8D:
        _mod, reg, _rm = item.modrm()
        require(not item.operand16, f"{context}: a 16-bit lea is outside the closed set")
        _set(state, reg, 32, item.address(state.regs))
        return ("fall", None)
    if 0xB0 <= op <= 0xB7:
        _set(state, op - 0xB0, 8, _small(8, item.raw[item.cursor]))
        return ("fall", None)
    if 0xB8 <= op <= 0xBF:
        require(not item.operand16, f"{context}: a 16-bit immediate move is outside the closed set")
        _set(state, op - 0xB8, 32, item.immediate(item.cursor, 4))
        return ("fall", None)
    if op in (0xC6, 0xC7):
        mod, reg, _rm = item.modrm()
        require(reg == 0, f"{context}: an undefined C6/C7 form")
        at = item.operand_end()
        if op == 0xC6:
            value = _small(8, item.raw[at])
            width = 8
        elif item.operand16:
            value = _small(16, int.from_bytes(item.raw[at : at + 2], "little"))
            width = 16
        else:
            value = item.immediate(at, 4)
            width = 32
        _write_rm(state, item, width, value)
        return ("fall", None)
    if op < 0x40 and op & 7 <= 5 and (op >> 3) in _ALU_NAMES:
        name = _ALU_NAMES[op >> 3]
        form = op & 7
        if form in (4, 5):
            width = 8 if form == 4 else 32
            require(
                not item.operand16,
                f"{context}: a 16-bit accumulator form is outside the closed set",
            )
            right = (
                _small(8, item.raw[item.cursor]) if width == 8 else item.immediate(item.cursor, 4)
            )
            result = _alu(state, name, width, _get(state, 0, width), right, undefined)
            if result is not None:
                _set(state, 0, width, result)
            return ("fall", None)
        width = 8 if form in (0, 2) else width32
        mod, reg, rm = item.modrm()
        if mod == 3 and reg == rm and name in ("xor", "sub") and width == 32:
            # The zeroing idiom reads nothing.
            zero = lin(0)
            _arith_flags(state, "sub", 32, zero, zero) if name == "sub" else _logic_flags(
                state, 32, zero, undefined
            )
            _set(state, reg, 32, zero)
            return ("fall", None)
        if form in (0, 1):
            left = _read_rm(state, item, width)
            right = _get(state, reg, width)
            result = _alu(state, name, width, left, right, undefined)
            if result is not None:
                _write_rm(state, item, width, result)
        else:
            left = _get(state, reg, width)
            right = _read_rm(state, item, width)
            result = _alu(state, name, width, left, right, undefined)
            if result is not None:
                _set(state, reg, width, result)
        return ("fall", None)
    if op in (0x80, 0x81, 0x83):
        mod, digit, _rm = item.modrm()
        require(digit in _ALU_NAMES, f"{context}: adc/sbb are outside the simulator's closed set")
        name = _ALU_NAMES[digit]
        at = item.operand_end()
        if op == 0x80:
            width, right = 8, _small(8, item.raw[at])
        elif op == 0x83:
            width = width32
            raw = int.from_bytes(item.raw[at : at + 1], "little", signed=True)
            right = lin(raw) if width == 32 else _small(16, raw)
        elif item.operand16:
            width, right = 16, _small(16, int.from_bytes(item.raw[at : at + 2], "little"))
        else:
            width, right = 32, item.immediate(at, 4)
        left = _read_rm(state, item, width)
        result = _alu(state, name, width, left, right, undefined)
        if result is not None:
            _write_rm(state, item, width, result)
        return ("fall", None)
    if op in (0x84, 0x85):
        width = 8 if op == 0x84 else width32
        _mod, reg, _rm = item.modrm()
        left = _read_rm(state, item, width)
        _logic_flags(state, width, _bitop("and", width, left, _get(state, reg, width)), undefined)
        return ("fall", None)
    if op in (0xA8, 0xA9):
        width = 8 if op == 0xA8 else 32
        require(not item.operand16, f"{context}: a 16-bit test form is outside the closed set")
        right = _small(8, item.raw[item.cursor]) if width == 8 else item.immediate(item.cursor, 4)
        _logic_flags(state, width, _bitop("and", width, _get(state, 0, width), right), undefined)
        return ("fall", None)
    if op in (0xF6, 0xF7):
        mod, digit, _rm = item.modrm()
        width = 8 if op == 0xF6 else 32
        at = item.operand_end()
        if digit == 0:
            right = _small(8, item.raw[at]) if width == 8 else item.immediate(at, 4)
            left = _read_rm(state, item, width)
            _logic_flags(state, width, _bitop("and", width, left, right), undefined)
            return ("fall", None)
        require(width == 32, f"{context}: a byte-wide multiply or divide is outside the closed set")
        if digit in (4, 5, 6, 7):
            source = _read_rm(state, item, 32)
            _wide(state, digit, source, undefined)
            return ("fall", None)
        value = _read_rm(state, item, 32)
        if digit == 2:
            result = lin_sub(lin(_MASK), value)
        else:
            result = lin_scale(value, -1)
            for name in FLAG_NAMES:
                state.flags[name] = ("flag", name, "neg", 32, value, "")
        _write_rm(state, item, 32, result)
        return ("fall", None)
    if 0x40 <= op <= 0x4F:
        number = op & 7
        kind = "inc" if op < 0x48 else "dec"
        value = _get(state, number, 32)
        result = lin_add(value, lin(1 if kind == "inc" else -1))
        for name in FLAG_NAMES:
            if name != "cf":
                state.flags[name] = ("flag", name, kind, 32, value, "")
        _set(state, number, 32, result)
        return ("fall", None)
    if op in (0xFE, 0xFF):
        mod, digit, _rm = item.modrm()
        width = 8 if op == 0xFE else 32
        if digit in (0, 1):
            value = _read_rm(state, item, width)
            kind = "inc" if digit == 0 else "dec"
            if width == 32:
                result = lin_add(value, lin(1 if digit == 0 else -1))
            else:
                small = _small_const(value)
                result = (
                    _small(8, small + (1 if digit == 0 else -1))
                    if small is not None
                    else ("b", 8, ("op", kind, (value,)))
                )
            for name in FLAG_NAMES:
                if name != "cf":
                    state.flags[name] = ("flag", name, kind, width, value, "")
            _write_rm(state, item, width, result)
            return ("fall", None)
        if op == 0xFF and digit == 2 and mod == 0 and _rm == 5:
            # call [abs32]: an import thunk's slot, read like any operand.
            callee = _read_rm(state, item, 32)
            symbol = item.relocations.get(item.modrm_at + 1 + item.offset)
            _call(state, ("indirect", callee), symbol, undefined, context)
            return ("fall", None)
        require(
            op == 0xFF and digit == 6,
            f"{context}: an indirect call or jump is outside the simulator's closed set",
        )
        _push(state, _read_rm(state, item, 32))
        return ("fall", None)
    if op == 0xE8:
        symbol = item.call_target(item.cursor)
        addend = int.from_bytes(item.raw[item.cursor : item.cursor + 4], "little", signed=True)
        require(
            addend == 0, f"{context}: a call into the middle of a symbol is outside the closed set"
        )
        _call(state, ("direct", symbol), symbol, undefined, context)
        return ("fall", None)
    if op in (0xC1, 0xD1):
        mod, digit, _rm = item.modrm()
        require(digit in _SHIFT_NAMES, f"{context}: a rotate is outside the simulator's closed set")
        count = item.raw[item.operand_end()] if op == 0xC1 else 1
        value = _read_rm(state, item, 32)
        _write_rm(state, item, 32, _shift(state, _SHIFT_NAMES[digit], value, count, undefined))
        return ("fall", None)
    if op == 0x0FAF:
        _mod, reg, _rm = item.modrm()
        right = _read_rm(state, item, 32)
        _set(state, reg, 32, _multiply(state, _get(state, reg, 32), right, undefined))
        return ("fall", None)
    if op in (0x69, 0x6B):
        _mod, reg, _rm = item.modrm()
        at = item.operand_end()
        factor = (
            item.immediate(at, 4)
            if op == 0x69
            else lin(int.from_bytes(item.raw[at : at + 1], "little", signed=True))
        )
        left = _read_rm(state, item, 32)
        _set(state, reg, 32, _multiply(state, left, factor, undefined))
        return ("fall", None)
    if op in (0x0FB6, 0x0FB7, 0x0FBE, 0x0FBF):
        _mod, reg, _rm = item.modrm()
        width = 8 if op in (0x0FB6, 0x0FBE) else 16
        part = _read_rm(state, item, width)
        extend = zero_extend if op in (0x0FB6, 0x0FB7) else sign_extend
        _set(state, reg, 32, extend(part, width))
        return ("fall", None)
    if 0x0F90 <= op <= 0x0F9F:
        decided = condition(op & 15, state.flags)
        if isinstance(decided, bool):
            value = _small(8, int(decided))
        else:
            atom, polarity = decided
            value = ("b", 8, ("cc", atom, polarity))
        _write_rm(state, item, 8, value)
        return ("fall", None)
    if op == 0x99:
        state.regs["edx"] = lin_atom(("sxhi", 32, state.regs["eax"]))
        return ("fall", None)
    if op == 0x90:
        return ("fall", None)
    if 0x50 <= op <= 0x57:
        _push(state, state.regs[_REGS[op - 0x50]])
        return ("fall", None)
    if op == 0x6A:
        _push(
            state,
            lin(int.from_bytes(item.raw[item.cursor : item.cursor + 1], "little", signed=True)),
        )
        return ("fall", None)
    if op == 0x68:
        _push(state, item.immediate(item.cursor, 4))
        return ("fall", None)
    if 0x58 <= op <= 0x5F:
        require(op != 0x5C, f"{context}: pop esp is outside the simulator's closed set")
        value = _load(state, state.regs["esp"], 4)
        state.regs["esp"] = lin_add(state.regs["esp"], lin(4))
        state.regs[_REGS[op - 0x58]] = value
        return ("fall", None)
    if 0x70 <= op <= 0x7F or 0x0F80 <= op <= 0x0F8F:
        size = 1 if op <= 0x7F else 4
        displacement = int.from_bytes(
            item.raw[item.cursor : item.cursor + size], "little", signed=True
        )
        require(
            item.offset + item.cursor not in item.relocations,
            f"{context}: a relocated branch is outside the simulator's closed set",
        )
        return ("branch", (op & 15, end + displacement))
    if op in (0xEB, 0xE9):
        size = 1 if op == 0xEB else 4
        require(
            item.offset + item.cursor not in item.relocations,
            f"{context}: a relocated jump leaves the region",
        )
        displacement = int.from_bytes(
            item.raw[item.cursor : item.cursor + size], "little", signed=True
        )
        return ("jump", end + displacement)
    require(
        False, f"{context}: the instruction {item.raw.hex()} is outside the simulator's closed set"
    )
    raise AssertionError("unreachable")


def region_boundaries(code: bytes, start: int, end: int, context: str) -> list[int]:
    """The instruction starts of [start, end), refusing a straddle."""
    starts = []
    offset = start
    while offset < end:
        starts.append(offset)
        offset += supported_ia32_instruction_length(code[offset:end], f"{context} at {offset}")
    require(offset == end, f"{context}: an instruction straddles the region end")
    return starts


def simulate_region(
    code: bytes,
    start: int,
    end: int,
    relocations: Mapping[int, RelocationTarget],
    tag: str,
    context: str,
    entry_names: Mapping[str, str] | None = None,
    *,
    begin: int | None = None,
    leave: bool = False,
) -> list[PathResult]:
    """Every path of [start, end) from the symbolic entry state.

    ``relocations`` maps the offset of each relocated 32-bit field (in
    ``code``'s own coordinates) to its target symbol.  A path starts at
    ``begin`` (an instruction start of the region; ``start`` by default) and
    ends when it reaches ``end``; every branch inside the region must go
    strictly forward to an instruction start of the region or to ``end``.
    With ``leave`` a branch may also leave the region for any offset outside
    [start, end], which ends the path there; each result's ``exit`` names
    where it ended.  ``entry_names`` is passed to :func:`entry_state`.  Every
    relocated field of the region must be read on some path of the main
    entry; a run from a later ``begin`` is not asked to read the fields
    before it.
    """
    starts = region_boundaries(code, start, end, context)
    boundaries = set(starts) | {end}
    first = start if begin is None else begin
    require(
        first in starts or first == start == end,
        f"{context}: the entry {first} is not an instruction of the region",
    )
    instructions = {offset: _Instruction(code, offset, relocations, context) for offset in starts}
    undefined = _Undefined(tag)
    results: list[PathResult] = []
    pending: list[tuple[int, PathState]] = [(first, entry_state(entry_names))]
    steps = 0

    def inside(target: int) -> bool:
        return start <= target < end

    def admitted(offset: int, target: int, strict: bool) -> bool:
        if inside(target):
            return (target > offset if strict else target >= offset) and target in boundaries
        return target == end or (leave and not start < target < end)

    while pending:
        offset, state = pending.pop()
        while inside(offset):
            steps += 1
            require(steps <= MAX_STEPS, f"{context}: the region's paths exceed the step bound")
            item = instructions[offset]
            action, detail = _step(state, item, undefined)
            following = offset + item.length
            if action == "fall":
                offset = following
                continue
            if action == "jump":
                target = detail
                require(
                    admitted(following, target, strict=False),
                    f"{context}: the jump at {offset} does not go forward to an instruction of "
                    "the region or its exit",
                )
                offset = target
                continue
            code_value, target = detail
            require(
                admitted(following, target, strict=True),
                f"{context}: the branch at {offset} does not go forward to an instruction of the "
                "region or its exit",
            )
            decided = condition(code_value, state.flags)
            if isinstance(decided, bool):
                offset = target if decided else following
                continue
            atom, taken_value = decided
            known = dict(state.conditions)
            if atom in known:
                offset = target if known[atom] == taken_value else following
                continue
            if atom[0] == "fcc":
                # The path may already pin the compare's outcome to a set
                # inside (or outside) this atom's.
                allowed = _fcc_allowed(state.conditions).get(atom[1])
                if allowed is not None and (allowed <= set(atom[2]) or not allowed & set(atom[2])):
                    holds = allowed <= set(atom[2])
                    offset = target if holds == taken_value else following
                    continue
            other = state.fork()
            other.conditions.append((atom, not taken_value))
            state.conditions.append((atom, taken_value))
            pending.append((following, other))
            require(
                len(results) + len(pending) + 1 <= MAX_PATHS,
                f"{context}: the region has more than {MAX_PATHS} paths",
            )
            offset = target
        consumed = set()
        for item in instructions.values():
            consumed |= item.consumed
        state.relocations_read |= consumed
        require(
            not mentions_x87_undefined((state.conditions, state.stores, state.footprint)),
            f"{context}: a path reads an x87 condition bit the last x87 instruction left undefined",
        )
        results.append(
            PathResult(
                tuple(state.conditions),
                dict(state.regs),
                dict(state.flags),
                tuple(state.stores),
                frozenset(state.footprint),
                frozenset(state.relocations_read),
                offset,
                tuple(state.events),
                state.fpu.view(),
                dict(state.fpu.cc),
            )
        )
    if first == start:
        unread = sorted(
            at
            for at in relocations
            if start <= at < end and not any(at in r.relocations_read for r in results)
        )
        require(
            not unread,
            f"{context}: the relocated fields at {unread} are not read as an address or immediate",
        )
    return results


def contradictory(left: Iterable[tuple[Term, bool]], right: Iterable[tuple[Term, bool]]) -> bool:
    """Whether two path conditions assign one atom different values."""
    decided = dict(left)
    if any(atom in decided and decided[atom] != value for atom, value in right):
        return True
    return any(not outcomes for outcomes in _fcc_allowed([*left, *right]).values())


def mentions_x87_undefined(value: Term) -> bool:
    """Whether a term mentions a condition bit an x87 instruction left undefined."""
    stack = [value]
    seen: set[int] = set()
    while stack:
        current = stack.pop()
        if isinstance(current, (tuple, list, frozenset, set)):
            if id(current) in seen:
                continue
            seen.add(id(current))
            if isinstance(current, tuple) and current and current[0] == "x87undef":
                return True
            stack.extend(current)
    return False


def term_atoms(value: Term, found: set[Term] | None = None) -> set[Term]:
    """Every ``reg0``/``flag0``/``fcc0`` leaf a term mentions (entry registers, flags, C0-C3)."""
    found = set() if found is None else found
    stack = [value]
    while stack:
        current = stack.pop()
        if isinstance(current, tuple):
            if len(current) == 2 and current[0] in ("reg0", "flag0", "fcc0"):
                found.add(current)
                continue
            stack.extend(current)
        elif isinstance(current, (list, frozenset, set)):
            stack.extend(current)
    return found


def stores_equivalent(
    left: tuple[tuple[Term, int, Term], ...], right: tuple[tuple[Term, int, Term], ...]
) -> str | None:
    """None when the two store sequences leave the same memory, else why not.

    The sequences must be permutations of each other (address, width and
    value equal) in which every pair whose relative order differs is
    provably disjoint: such a permutation is a product of adjacent
    transpositions of disjoint stores, each of which leaves memory unchanged.
    """
    if len(left) != len(right):
        return f"they make {len(left)} and {len(right)} stores"
    used = [False] * len(left)
    position = []
    for store in right:
        match = next(
            (index for index, other in enumerate(left) if not used[index] and other == store), None
        )
        if match is None:
            return "a store of one has no equal store in the other"
        used[match] = True
        position.append(match)
    for earlier in range(len(right)):
        for later in range(earlier + 1, len(right)):
            if position[earlier] > position[later]:
                a, b = right[earlier], right[later]
                if address_relation(a[0], a[1], b[0], b[1]) != "disjoint":
                    return "two stores that may overlap are made in a different order"
    return None


__all__ = [
    "FCMP_BITS",
    "FCMP_OUTCOMES",
    "FLAG_NAMES",
    "MAX_PATHS",
    "X87_CONDITION_BITS",
    "PathResult",
    "RelocationTarget",
    "X87State",
    "X87View",
    "address_relation",
    "callee_stack_pop",
    "canonical_flag",
    "condition",
    "contradictory",
    "entry_state",
    "fcc_atom",
    "mentions_x87_undefined",
    "region_boundaries",
    "register_free_callee",
    "simulate_region",
    "store_normal_form",
    "stores_equivalent",
    "term_atoms",
    "x87_stacks_equivalent",
]
