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
(rel8/rel32).  No call, return, string
instruction, x87 instruction or indirect transfer is admitted: a call's
register inputs and its effect on memory cannot be bounded from the bytes.
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


@dataclass
class PathState:
    """One path's machine state while it runs through the region."""

    regs: dict[str, Term]
    flags: dict[str, Term]
    stores: list[tuple[Term, int, Term]] = field(default_factory=list)
    footprint: set[Term] = field(default_factory=set)
    conditions: list[tuple[Term, bool]] = field(default_factory=list)
    relocations_read: set[int] = field(default_factory=set)

    def fork(self) -> PathState:
        return PathState(
            dict(self.regs),
            dict(self.flags),
            list(self.stores),
            set(self.footprint),
            list(self.conditions),
            set(self.relocations_read),
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
    term = ("ld", address, width, tuple(reversed(deps)))
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
        relocations: Mapping[int, str],
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
        self.consumed.add(at)
        return lin_atom(("sym", symbol))

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


def _push(state: PathState, value: Term) -> None:
    state.regs["esp"] = lin_add(state.regs["esp"], lin(-4))
    _store(state, state.regs["esp"], 4, value)


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
        require(
            op == 0xFF and digit == 6,
            f"{context}: an indirect call or jump is outside the simulator's closed set",
        )
        _push(state, _read_rm(state, item, 32))
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
    relocations: Mapping[int, str],
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
    require(first in starts, f"{context}: the entry {first} is not an instruction of the region")
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
        results.append(
            PathResult(
                tuple(state.conditions),
                dict(state.regs),
                dict(state.flags),
                tuple(state.stores),
                frozenset(state.footprint),
                frozenset(state.relocations_read),
                offset,
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
    return any(atom in decided and decided[atom] != value for atom, value in right)


def term_atoms(value: Term, found: set[Term] | None = None) -> set[Term]:
    """Every ``reg0``/``flag0`` leaf a term mentions."""
    found = set() if found is None else found
    stack = [value]
    while stack:
        current = stack.pop()
        if isinstance(current, tuple):
            if len(current) == 2 and current[0] in ("reg0", "flag0"):
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
    "FLAG_NAMES",
    "MAX_PATHS",
    "PathResult",
    "address_relation",
    "canonical_flag",
    "condition",
    "contradictory",
    "entry_state",
    "region_boundaries",
    "simulate_region",
    "stores_equivalent",
    "term_atoms",
]
