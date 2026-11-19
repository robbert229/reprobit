"""Choose region-resize regions whose boundaries are points where both versions agree.

`discovery_region_resize` aligns a donor's instructions with the reference
object's and proposes, for each maximal run of differing instructions, a
region to replace by the reference's instructions.  The prover
(`rewriting_region_resize`) then compares the two versions at every region
exit: ESP, every live register and flag, and the x87 stack.  A region that
ends where one version still holds a value the other has not computed (or
holds elsewhere), or at another stack depth, always refuses, however often it
is tried; a larger region, ending where the versions agree again, may prove.

This module measures, without simulating anything, which candidate regions
can only refuse.  A candidate is a run (or several adjacent runs, merged)
plus ``back`` aligned equal instructions before it and ``ahead`` after it.
Its *core* is the differing part; its context is equal on both sides, so the
context executes the same instructions in both versions.  The candidate is
*disagreeing* when one of these holds:

* structure: its interior holds an instruction no region may hold (a return,
  an indirect transfer, a call to a callee whose decoration fixes no
  register-free convention, a backward branch inside it), an external entry,
  relocated target or protected offset lies strictly inside it, it starts in
  the FPO prologue or ends at the code end;
* ESP: the two cores change ESP by different known amounts;
* x87: the two cores leave the x87 stack at different known net depths;
* exit: an atom (register part or flag) live at the exit in either version
  is written by exactly one core and not rewritten by the trailing context,
  so one version leaves its entry value and the other a value computed
  inside the region;
* entry: an atom one version reads before writing it, in the leading
  context and its core, and the other does not, so one version computes
  from an entry value the other never consults -- typically a value the
  leading context loaded and one version keeps in a register while the
  other reloads it (growing the region back over that load makes both
  versions read the load's own inputs); or a register either version reads
  is not live at the entry, all of its atoms, in either version (the
  prover's check 8f: ``mov al, [x]`` keeps EAX's upper bytes, so a region
  after it may read AL but not start there).

The first three are certain refusals of the prover (checks 1-3 and 8a, 8g).
The last two are what a "register live at the exit differs" refusal almost
always is, but they are heuristics: a push/pop pair that restores a
register, or a reload of a value both versions already hold, is a write
that keeps the value.  So they only order the search and decide merges;
every region the search proposes still goes through the unchanged prover,
which alone decides.

The search (in `discovery_region_resize`) tries, per group of runs, the
agreeing shapes smallest first, then the old fixed ladder of context extents
minus its certain refusals; a group with no agreeing shape inside its
neighbouring equal blocks merges with its neighbour first, since only a run
that also differs can make the versions agree again (the context, being
equal, never changes an ESP or x87 difference, nor writes an atom on one
side only).
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from reprobit.classic.candidate_recipe import internal_relocation_targets, relocation_symbol_map
from reprobit.classic.region_simulation import callee_stack_pop
from reprobit.classic.region_x87 import x87_stack_effect
from reprobit.classic.register_semantics import (
    _register_bijection_live_sets,
    decode_ia32_bijection_body,
    ia32_register_atoms,
)
from reprobit.classic.relational import ia32_relational_flag_liveness, ia32_relational_flow_walk
from reprobit.classic.rewriting_region_resize import refine_call_reads
from reprobit.classic.stack_frontier_foundation import stack_change

FLAG_NAMES = frozenset({"cf", "pf", "af", "zf", "sf", "of", "df"})
_BYTE_REGISTERS = ("eax", "ecx", "edx", "ebx")
# Agreeing shapes tried per group before the old ladder, and the farthest a
# shape reaches into its neighbouring equal blocks.
MAX_AGREEING_SHAPES = 8
MAX_CONTEXT = 32


@dataclass(frozen=True)
class VersionProfile:
    """Static facts about one version's code, by instruction index.

    ``live[i]`` is the set of register atoms and flags (``flag.zf``) live
    before instruction i; index ``len(offsets)`` is the code end, where
    nothing is live.  ``esp`` and ``x87`` are each instruction's ESP change
    and x87 net push, or None when unknown.
    """

    offsets: tuple[int, ...]
    code_end: int
    reads: tuple[frozenset[str], ...]
    writes: tuple[frozenset[str], ...]
    live: tuple[frozenset[str], ...]
    esp: tuple[int | None, ...]
    x87: tuple[int | None, ...]
    barrier: tuple[str | None, ...]
    backward: tuple[int | None, ...]
    pinned: frozenset[int]

    def offset(self, index: int) -> int:
        return self.offsets[index] if index < len(self.offsets) else self.code_end


def _call_symbol(body: bytes, item: dict[str, Any], view: dict[int, Any]) -> object:
    at = item["offset"]
    while body[at] in (0x26, 0x2E, 0x36, 0x3E, 0x64, 0x65, 0x66, 0x67, 0xF2, 0xF3):
        at += 1
    if body[at] == 0xE8:
        row = view.get(at + 1)
    elif body[at] == 0xFF and body[at + 1] == 0x15:
        row = view.get(at + 2)
    else:
        return None
    return None if row is None else row.get("target")


def version_profile(
    body: bytes,
    rows: list[dict[str, Any]],
    code_end: int,
    context: str,
    *,
    section_number: int | None = None,
    external_entries: frozenset[int] = frozenset(),
    protected_offsets: frozenset[int] = frozenset(),
) -> VersionProfile:
    """Measure one version's liveness, stack effects and region barriers."""
    view = relocation_symbol_map(rows)
    limit = None if code_end == len(body) else code_end
    items = refine_call_reads(decode_ia32_bijection_body(body, context, view, limit), view)
    live_atoms, successors = _register_bijection_live_sets(items, f"{context} liveness")
    flow, flow_successors, entries = ia32_relational_flow_walk(
        body, view, f"{context} flow", limit, external_entries
    )
    flag_live = ia32_relational_flag_liveness(flow, flow_successors, f"{context} flags")
    by_offset = {item["offset"]: index for index, item in enumerate(flow)}
    reads: list[frozenset[str]] = []
    writes: list[frozenset[str]] = []
    live: list[frozenset[str]] = []
    esp: list[int | None] = []
    x87: list[int | None] = []
    barrier: list[str | None] = []
    backward: list[int | None] = []
    for index, item in enumerate(items):
        walked = flow[by_offset[item["offset"]]] if item["offset"] in by_offset else None
        read_flags = frozenset() if walked is None else frozenset(walked["reads_flags"])
        write_flags = frozenset() if walked is None else frozenset(walked["writes_flags"])
        flags_here = frozenset() if walked is None else flag_live[by_offset[item["offset"]]]
        why: str | None = None
        change: int | None
        if item["flow"] == "call":
            symbol = _call_symbol(body, item, view)
            pop = callee_stack_pop(symbol)
            change = pop
            if pop is None:
                why = f"a call at {item['offset']} to a callee no region may call"
            # A callee leaves every flag undefined.
            write_flags = FLAG_NAMES
        else:
            change = stack_change(body, item)
        if item["flow"] not in ("fall", "jcc", "jmp", "call") or item["indirect"]:
            why = f"a {item['flow']} at {item['offset']}"
        push: int | None = None
        if walked is not None and item["flow"] != "call":
            effect = x87_stack_effect(body, walked)
            if effect == (0, 0):
                push = 0
            elif isinstance(effect, tuple):
                push = effect[1]
        target = item["target"]
        reads.append(frozenset(item["read_atoms"]) | {f"flag.{name}" for name in read_flags})
        writes.append(frozenset(item["write_atoms"]) | {f"flag.{name}" for name in write_flags})
        live.append(frozenset(live_atoms[index]) | {f"flag.{name}" for name in flags_here})
        esp.append(change)
        x87.append(push)
        barrier.append(why)
        backward.append(target if item["flow"] in ("jcc", "jmp") and target is not None else None)
    live.append(frozenset())
    del successors
    pinned = set(protected_offsets)
    pinned |= {flow[index]["offset"] for index in entries[1:]}
    if section_number is not None:
        pinned |= set(internal_relocation_targets(rows, section_number))
    branch_targets = {target for target in backward if target is not None}
    # A branch target is a declared entry when the alignment pairs it, so it
    # is not pinned here: the prover decides.
    return VersionProfile(
        offsets=tuple(item["offset"] for item in items),
        code_end=code_end,
        reads=tuple(reads),
        writes=tuple(writes),
        live=tuple(live),
        esp=tuple(esp),
        x87=tuple(x87),
        barrier=tuple(barrier),
        backward=tuple(backward),
        pinned=frozenset(pinned - branch_targets),
    )


def rename_atoms(atoms: frozenset[str], sigma: dict[str, str]) -> frozenset[str]:
    """The atoms of the registers sigma's image names (flags and other registers kept)."""
    if not sigma:
        return atoms
    renamed: set[str] = set()
    for atom in atoms:
        register, _dot, part = atom.partition(".")
        image = sigma.get(register, register)
        if image == register:
            renamed.add(atom)
        elif (register in _BYTE_REGISTERS) == (image in _BYTE_REGISTERS):
            renamed.add(f"{image}.{part}")
        elif image in _BYTE_REGISTERS:
            renamed |= {f"{image}.h", f"{image}.l", f"{image}.u"}
        else:
            renamed.add(f"{image}.w")
    return frozenset(renamed)


def _sum(values: tuple[int | None, ...], first: int, last: int) -> int | None:
    total = 0
    for value in values[first:last]:
        if value is None:
            return None
        total += value
    return total


# The kinds of disagreement the prover always refuses; the others are heuristic.
CERTAIN = frozenset({"structure", "esp", "x87"})


@dataclass(frozen=True)
class Selection:
    """The two versions' profiles, for verdicts on candidate regions.

    ``sigma`` and ``scopes`` are a declared scope bijection: a region whose
    exit lies in a scope compares the donor's registers renamed by sigma.
    """

    donor: VersionProfile
    reference: VersionProfile
    prologue_length: int = 0
    sigma: tuple[tuple[str, str], ...] = ()
    scopes: tuple[tuple[int, int], ...] = ()

    def structure(self, i1: int, i2: int) -> str | None:
        """Why a donor region [i1, i2) breaks a check the prover makes on its shape."""
        donor = self.donor
        if i1 >= i2:
            return "the region is empty"
        if donor.offset(i1) < self.prologue_length:
            return "the region overlaps the FPO prologue"
        if i2 >= len(donor.offsets):
            return "the region reaches the code end"
        start = donor.offset(i1)
        for index in range(i1, i2):
            if donor.barrier[index] is not None:
                return f"the region holds {donor.barrier[index]}"
            target = donor.backward[index]
            if target is not None and start <= target <= donor.offsets[index]:
                return f"the branch at {donor.offsets[index]} goes backward inside the region"
            if index > i1 and donor.offsets[index] in donor.pinned:
                return f"an entry or protected offset at {donor.offsets[index]} lies inside it"
        return None

    def verdict(
        self, ranges: tuple[int, int, int, int], core: tuple[int, int, int, int]
    ) -> tuple[str, str] | None:
        """(kind, reason) when the candidate disagrees, or None when it may prove.

        ``ranges`` is the candidate (i1, i2, j1, j2) as donor and reference
        instruction index ranges; ``core`` is the differing part (c1, c2, d1,
        d2) inside it, the rest being aligned context, equal on both sides.
        """
        i1, i2, j1, j2 = ranges
        why = self.structure(i1, i2)
        if why is not None:
            return "structure", why
        donor, reference = self.donor, self.reference
        c1, c2, d1, d2 = core
        ours = _sum(donor.esp, c1, c2)
        theirs = _sum(reference.esp, d1, d2)
        if ours is not None and theirs is not None and ours != theirs:
            return "esp", f"the versions change ESP by {ours} and {theirs}"
        ours = _sum(donor.x87, c1, c2)
        theirs = _sum(reference.x87, d1, d2)
        if ours is not None and theirs is not None and ours != theirs:
            return "x87", f"the versions push {ours} and {theirs} x87 values"
        exit_offset = donor.offset(i2)
        sigma = (
            dict(self.sigma)
            if any(left <= exit_offset < right for left, right in self.scopes)
            else {}
        )

        def union(sets: tuple[frozenset[str], ...]) -> frozenset[str]:
            return rename_atoms(frozenset().union(*sets), sigma)

        donor_writes = union(donor.writes[c1:c2])
        reference_writes = frozenset().union(*reference.writes[d1:d2])
        trailing = union(donor.writes[c2:i2])
        live = rename_atoms(donor.live[i2], sigma) | reference.live[j2]
        one_sided = sorted(
            atom
            for atom in (donor_writes ^ reference_writes) & live
            if atom not in trailing and not atom.startswith("esp")
        )
        if one_sided:
            return "exit", f"{one_sided[0]} is live at the exit and written by one version only"
        # Trailing reads see what the cores computed, not entry values.
        donor_reads = rename_atoms(_exposed(donor, i1, c2), sigma)
        reference_reads = _exposed(reference, j1, d2)
        one_sided = sorted(
            atom for atom in donor_reads ^ reference_reads if not atom.startswith("esp")
        )
        if one_sided:
            return "entry", f"{one_sided[0]} is read on entry by one version only"
        # Check 8f: an entry register the region reads must be live at its
        # entry, all of its atoms, in one version or the other.
        entry_live = rename_atoms(donor.live[i1], sigma) | reference.live[j1]
        read = rename_atoms(_exposed(donor, i1, i2), sigma) | _exposed(reference, j1, j2)
        for register in sorted({atom.partition(".")[0] for atom in read} - {"flag", "esp"}):
            dead = sorted(ia32_register_atoms({register}) - entry_live)
            if dead:
                return "entry", f"{register} is read but {dead} is dead at the region entry"
        return None


def _exposed(profile: VersionProfile, first: int, last: int) -> frozenset[str]:
    """Atoms the instructions [first, last) read before writing them (in index order)."""
    written: set[str] = set()
    exposed: set[str] = set()
    for index in range(first, last):
        exposed |= profile.reads[index] - written
        written |= profile.writes[index]
    return frozenset(exposed)


__all__ = [
    "CERTAIN",
    "FLAG_NAMES",
    "MAX_AGREEING_SHAPES",
    "MAX_CONTEXT",
    "Selection",
    "VersionProfile",
    "rename_atoms",
    "version_profile",
]
