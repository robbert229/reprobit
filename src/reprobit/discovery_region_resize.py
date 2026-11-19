"""Author region-resize rewritings whose replacements reach a reference body.

When grind's donor compiles a function to a body of another length than the
reference object's -- the compiler kept a value in a register where the
reference reloads it, or allocated another register -- no reordering reaches
the reference.  `retail_exact_region_resize_rewriting` replaces whole regions
of the donor by instructions a path simulation proves equivalent, then lays
the function out at its new length.  This module aligns the donor's
instructions with the reference object's, takes each maximal run of
differing instructions, chooses the region around it whose boundaries are
points where the two versions agree (`discovery_region_selection`: the same
ESP and x87 changes, no live value left by one version only; merged with
neighbouring runs when only that agrees, and while the proof refuses),
offers the reference's instructions for that region as the replacement, measures
every pin the producer checks, and finally requires the ordinary producer to
accept the record and compose the reference body.  The reference object is
the project-owned COFF the grind plan names; nothing here reads a reference
image, and the producer re-proves every replacement against the donor.
"""

from __future__ import annotations

import difflib
import itertools
from dataclasses import dataclass
from typing import Any, cast

from pydantic import ValidationError

from reprobit.binary import ByteIdentityError
from reprobit.classic.candidate_recipe import relocation_symbol_map
from reprobit.classic.coff import (
    _comdat_child,
    _comdat_child_closure,
    comdat_primary_identity_multiset,
    function_multiset,
)
from reprobit.classic.composition_mosaic import instruction_mosaic_metadata_sha256
from reprobit.classic.debug import parse_fpo_data
from reprobit.classic.foundation import sha256_bytes
from reprobit.classic.register_reencoding import require_frame_pointer_free_frame
from reprobit.classic.register_semantics import (
    IA32_GENERAL_REGISTER_NAMES,
    _register_bijection_live_sets,
    decode_ia32_bijection_body,
    ia32_register_atoms,
)
from reprobit.classic.relational import relational_form_external_entries
from reprobit.classic.rewriting_region_resize import (
    REGION_RESIZE_KIND,
    ScopeBoundRefusal,
    _implicit_support,
    _padded_length,
    _register_level_live,
    _sigma_rewrite,
    apply_region_resize,
    protected_code_offsets,
    refine_call_reads,
    resized_donor_object,
)
from reprobit.classic.scheduling_certificates import measure_instruction_schedule_debug_envelope
from reprobit.classic_donors import DonorSourceError, merge_candidate_constraints
from reprobit.classic_project import (
    ClassicDispatchMaterials,
    ClassicFamilyDispatcher,
    ClassicProjectError,
)
from reprobit.coff_format import CoffObject, coff_body, detailed_relocations, section_definitions
from reprobit.discovery_authoring import (
    AuthoredClassicRecord,
    DeclarationShapeEqualBodyAuthoring,
    DiscoveryAuthoringError,
    _record_receipt,
    _stable_id,
)
from reprobit.discovery_region_selection import (
    CERTAIN,
    MAX_AGREEING_SHAPES,
    MAX_CONTEXT,
    Selection,
    VersionProfile,
    version_profile,
)
from reprobit.discovery_rewriting import msvc50_code_end
from reprobit.intervention_metadata import ClassicRecipeFamily, ClassicRecipeRole
from reprobit.model import Scope
from reprobit.schema import ClassicField, ClassicRecipeIntervention
from reprobit.strict_json import JsonValue

_REGION_RESIZE_RATIONALE = (
    "A freshly compiled private donor of the same translation unit whose differing "
    "regions are replaced by instructions a path simulation proves equivalent, "
    "laid out again at the new length."
)
_RELOCATION_FIELDS = (
    "offset",
    "type",
    "addend",
    "target",
    "target_section",
    "target_value",
    "target_type",
    "target_storage",
)
# The shapes a refused region is tried in, in order: how many equal
# instructions it takes from its neighbourhood (before, after).  A region whose
# replacement reads a value the equal code before it loaded must hold that
# load; one whose exit liveness differs must hold the code that kills it.
# When every shape refuses, the region absorbs the next differing run.
CONTEXT_EXTENTS = (
    (0, 0),
    (1, 0),
    (2, 0),
    (3, 0),
    (4, 0),
    (6, 0),
    (8, 0),
    (0, 1),
    (0, 2),
    (0, 4),
    (0, 8),
    (1, 1),
    (2, 2),
    (4, 4),
    (8, 8),
    (0, 16),
    (16, 0),
    (16, 16),
)
MAX_ATTEMPTS = 400
# A region never grows past this many donor instructions by absorbing runs.
MAX_REGION_INSTRUCTIONS = 64
# A group with no agreeing shape absorbs at most this many neighbouring
# groups on one side to find one.
MAX_MERGED_GROUPS = 4
# When no plain search reaches the reference, this many register bijections
# are tried, drawn from at most this many registers that differ in aligned
# fields.
MAX_BIJECTION_CANDIDATES = 6
MAX_BIJECTION_REGISTERS = 6
# A bijection's scopes are chosen again at most this many times after the
# producer refuses one of their bounds on the image's liveness.
MAX_SCOPE_ROUNDS = 8


def _procedure(coff: CoffObject, section: dict[str, Any], context: str) -> tuple[int, int, int]:
    """(procedure size, code end, fill alignment) of one function COMDAT."""
    envelope = measure_instruction_schedule_debug_envelope(coff, section, context)
    proc = envelope["procedure_range"][0]
    body = bytes(coff_body(coff, section))
    rows = detailed_relocations(coff, section)
    if ".debug$F" in _comdat_child_closure(coff, section)[1]:
        fpo = parse_fpo_data(
            bytes(coff_body(coff, _comdat_child(coff, section, ".debug$F"))),
            expected_proc_size=section["raw_size"],
            body=body,
        )
        if fpo["cbProcSize"] != proc:
            raise DiscoveryAuthoringError(f"{context}: the FPO and CodeView procedure sizes differ")
    code_end = msvc50_code_end(body, rows, section["number"], proc)
    return proc, code_end, 16 if section["raw_size"] != proc else 1


def _instruction_keys(
    body: bytes,
    rows: list[dict[str, Any]],
    code_end: int,
    context: str,
    *,
    mask_registers: bool = False,
    unique: frozenset[int] = frozenset(),
) -> list[tuple[int, int, tuple[Any, ...]]]:
    """(offset, length, comparison key) for each instruction of the code.

    A relocated field compares by its target symbol and addend; a relative
    branch by its opcode alone, since a layout change re-encodes it.  With
    ``mask_registers`` every rewritable register field is zeroed, so two
    instructions that differ only in their registers compare equal; an
    instruction at an offset in ``unique`` equals nothing.
    """
    view = relocation_symbol_map(rows)
    by_offset = {row["offset"]: row for row in rows}
    instructions = decode_ia32_bijection_body(
        body, context, view, None if code_end == len(body) else code_end
    )
    keys: list[tuple[int, int, tuple[Any, ...]]] = []
    for item in instructions:
        if item["offset"] in unique:
            keys.append((item["offset"], item["length"], ("unique", item["offset"])))
            continue
        raw = bytearray(body[item["offset"] : item["offset"] + item["length"]])
        if mask_registers:
            for at, shift in [*item["fields"], *item.get("byte_fields", ())]:
                raw[at - item["offset"]] &= ~(7 << shift) & 0xFF
        fields = []
        for at in range(item["offset"], item["offset"] + item["length"]):
            row = by_offset.get(at)
            if row is None:
                continue
            local = at - item["offset"]
            raw[local : local + row["width"]] = bytes(row["width"])
            fields.append((local, row["type"], _symbol_identity(row), row["addend"]))
        if item["flow"] in ("jcc", "jmp") and item["target"] is not None:
            width = 1 if raw[0] in (0xEB, *range(0x70, 0x80)) else 4
            raw[len(raw) - width :] = bytes(width)
        keys.append((item["offset"], item["length"], (bytes(raw), tuple(fields))))
    return keys


def _symbol_identity(row: dict[str, Any]) -> tuple[Any, ...]:
    """A relocation target's identity across two compiles of one unit."""
    base, separator, serial = str(row["target"]).rpartition("$S")
    if row["target_storage"] == 3 and separator and base and serial.isdigit():
        return ("static", base, row["target_type"])
    return ("named", row["target"], row["target_type"], row["target_storage"])


def _branch_targets(
    body: bytes, rows: list[dict[str, Any]], code_end: int, context: str
) -> dict[int, int]:
    """Each relative branch's offset and its target."""
    return {
        item["offset"]: item["target"]
        for item in decode_ia32_bijection_body(
            body, context, relocation_symbol_map(rows), None if code_end == len(body) else code_end
        )
        if item["flow"] in ("jcc", "jmp") and item["target"] is not None
    }


def _aligned_offsets(
    donor_keys: list[tuple[int, int, tuple[Any, ...]]],
    reference_keys: list[tuple[int, int, tuple[Any, ...]]],
) -> dict[int, int]:
    """Donor offset to reference offset of every instruction the alignment calls equal."""
    matcher = difflib.SequenceMatcher(
        a=[key for _o, _l, key in donor_keys],
        b=[key for _o, _l, key in reference_keys],
        autojunk=False,
    )
    return {
        donor_keys[block.a + k][0]: reference_keys[block.b + k][0]
        for block in matcher.get_matching_blocks()
        for k in range(block.size)
    }


def derive_region_candidates(
    donor_keys: list[tuple[int, int, tuple[Any, ...]]],
    reference_keys: list[tuple[int, int, tuple[Any, ...]]],
) -> list[tuple[int, int, int, int]]:
    """Maximal differing runs as (donor i1, i2, reference j1, j2) instruction index ranges."""
    matcher = difflib.SequenceMatcher(
        a=[key for _o, _l, key in donor_keys],
        b=[key for _o, _l, key in reference_keys],
        autojunk=False,
    )
    return [(i1, i2, j1, j2) for tag, i1, i2, j1, j2 in matcher.get_opcodes() if tag != "equal"]


@dataclass
class _Group:
    """A region under search: the base runs it covers, its shapes and the one tried."""

    first: int
    last: int
    shape: int = 0
    shapes: tuple[tuple[int, int], ...] | None = None


def _shape_range(
    group: _Group,
    extent: tuple[int, int],
    runs: list[tuple[int, int, int, int]],
    donor_count: int,
    reference_count: int,
) -> tuple[int, int, int, int]:
    """A group's index ranges with ``extent`` (back, ahead) aligned instructions of context."""
    back, ahead = extent
    i1, j1 = runs[group.first][0], runs[group.first][2]
    i2, j2 = runs[group.last][1], runs[group.last][3]
    back = min(back, i1, j1)
    ahead = min(ahead, donor_count - i2, reference_count - j2)
    i1, i2, j1, j2 = i1 - back, i2 + ahead, j1 - back, j2 + ahead
    if i1 == i2:
        if i1 > 0 and j1 > 0:
            i1, j1 = i1 - 1, j1 - 1
        else:
            i2, j2 = i2 + 1, j2 + 1
    return i1, i2, j1, j2


def _group_ranges(
    groups: list[_Group],
    runs: list[tuple[int, int, int, int]],
    donor_count: int,
    reference_count: int,
) -> list[tuple[int, int, int, int]] | None:
    """Each group's index ranges with its context, or None when two collide."""
    ranges: list[tuple[int, int, int, int]] = []
    for group in groups:
        shapes = CONTEXT_EXTENTS if group.shapes is None else group.shapes
        i1, i2, j1, j2 = _shape_range(
            group, shapes[group.shape], runs, donor_count, reference_count
        )
        if ranges and (i1 < ranges[-1][1] or j1 < ranges[-1][3]):
            return None
        ranges.append((i1, i2, j1, j2))
    return ranges


def plan_group_shapes(
    groups: list[_Group],
    position: int,
    runs: list[tuple[int, int, int, int]],
    donor_count: int,
    reference_count: int,
    selection: Selection | None,
) -> tuple[tuple[tuple[int, int], ...], tuple[str, str] | None]:
    """The shapes a group is tried in, and why it has none that agrees.

    The agreeing shapes inside the group's neighbouring equal blocks come
    first, smallest first (at most `MAX_AGREEING_SHAPES`); then the fixed
    ladder of `CONTEXT_EXTENTS`, less the shapes the prover certainly
    refuses.  The second value is None when an agreeing shape exists, else
    the (kind, reason) the smallest shape disagrees for.
    """
    if selection is None:
        return CONTEXT_EXTENTS, None
    group = groups[position]
    core = (
        runs[group.first][0],
        runs[group.last][1],
        runs[group.first][2],
        runs[group.last][3],
    )
    previous_end = runs[groups[position - 1].last][1] if position > 0 else 0
    next_start = runs[groups[position + 1].first][0] if position + 1 < len(groups) else donor_count
    room_back = min(core[0] - previous_end, MAX_CONTEXT)
    room_ahead = min(next_start - core[1], MAX_CONTEXT)
    span = core[1] - core[0]
    if span:
        hopeless = selection.structure(core[0], core[1])
        if hopeless is not None:
            # Growing a region never removes what its differing core holds.
            return (), ("structure", hopeless)
    verdicts: dict[tuple[int, int], tuple[str, str] | None] = {}

    def verdict(extent: tuple[int, int]) -> tuple[str, str] | None:
        if extent not in verdicts:
            verdicts[extent] = selection.verdict(
                _shape_range(group, extent, runs, donor_count, reference_count), core
            )
        return verdicts[extent]

    agreeing: list[tuple[int, int]] = []
    for total in range(room_back + room_ahead + 1):
        if len(agreeing) >= MAX_AGREEING_SHAPES or span + total > MAX_REGION_INSTRUCTIONS:
            break
        for back in range(max(0, total - room_ahead), min(total, room_back) + 1):
            extent = (back, total - back)
            if verdict(extent) is None:
                agreeing.append(extent)
                if len(agreeing) >= MAX_AGREEING_SHAPES:
                    break
    ladder = []
    for extent in CONTEXT_EXTENTS:
        if extent in agreeing:
            continue
        back, ahead = extent
        # Past the room on a side with a neighbour, the shape meets that
        # neighbour and the search merges the two; elsewhere it is clamped.
        if (back <= room_back or position == 0) and (
            ahead <= room_ahead or position + 1 == len(groups)
        ):
            found = verdict(extent)
            if found is not None and found[0] in CERTAIN:
                continue
        ladder.append(extent)
    disagreement = None
    if not agreeing:
        disagreement = verdict((0, 0)) or ("bound", "no agreeing shape within the bounds")
    return tuple(agreeing) + tuple(ladder), disagreement


def _regions_for(
    runs: list[tuple[int, int, int, int]],
    donor_keys: list[tuple[int, int, tuple[Any, ...]]],
    reference_keys: list[tuple[int, int, tuple[Any, ...]]],
    donor_rows: list[dict[str, Any]],
    reference_rows: list[dict[str, Any]],
    donor_code_end: int,
    reference_code_end: int,
    reference_body: bytes,
    branches: tuple[dict[int, int], dict[int, int], dict[int, int]] | None = None,
) -> list[dict[str, Any]]:
    """The declared regions for index ranges of the two instruction lists.

    ``branches`` is (donor branch targets, reference branch targets, donor to
    reference offsets of the aligned equal instructions); with it, a donor
    branch from outside a region into its interior names a replacement entry
    wherever the aligned reference branch lands inside the reference's run.
    """

    def start_of(keys: list[tuple[int, int, Any]], index: int, end: int) -> int:
        return keys[index][0] if index < len(keys) else end

    regions = []
    for position, (i1, i2, j1, j2) in enumerate(runs):
        start = start_of(donor_keys, i1, donor_code_end)
        end = start_of(donor_keys, i2, donor_code_end)
        reference_start = start_of(reference_keys, j1, reference_code_end)
        reference_end = start_of(reference_keys, j2, reference_code_end)
        donor_fields = [row for row in donor_rows if start <= row["offset"] < end]
        reference_fields = [
            row for row in reference_rows if reference_start <= row["offset"] < reference_end
        ]
        # Each reference field takes the first unused donor record that names
        # the same symbol; the two regions must relocate the same multiset.
        unused = list(donor_fields)
        paired = []
        for reference_row in reference_fields:
            match = next(
                (
                    row
                    for row in unused
                    if _symbol_identity(row) == _symbol_identity(reference_row)
                    and row["type"] == reference_row["type"]
                ),
                None,
            )
            if match is None:
                break
            unused.remove(match)
            paired.append((match, reference_row))
        if unused or len(paired) != len(reference_fields):
            refusal = DiscoveryAuthoringError(
                f"the region at {start} relocates other symbols than the reference's at "
                f"{reference_start}"
            )
            refusal.region = position  # type: ignore[attr-defined]
            raise refusal
        region: dict[str, Any] = {
            "region_start": start,
            "region_end": end,
            "replacement_instructions": [
                reference_body[offset : offset + length].hex()
                for offset, length, _key in reference_keys[j1:j2]
            ],
            "replacement_relocations": [
                [reference_row["offset"] - reference_start, donor_row["offset"]]
                for donor_row, reference_row in paired
            ],
        }
        if branches is not None:
            donor_targets, reference_targets, aligned = branches
            replacement_starts = {
                offset - reference_start for offset, _l, _k in reference_keys[j1:j2]
            }
            entries: dict[int, int] = {}
            for source, target in donor_targets.items():
                if start <= source < end or not start < target < end:
                    continue
                partner = reference_targets.get(aligned.get(source, -1))
                if partner is None or not reference_start < partner < reference_end:
                    continue
                local = partner - reference_start
                if local in replacement_starts and entries.setdefault(target, local) == local:
                    continue
                entries.pop(target, None)
            if entries:
                region["replacement_entries"] = [
                    [target, local] for target, local in sorted(entries.items())
                ]
        regions.append(region)
    return regions


def _field_values(body: bytes, item: dict[str, Any]) -> list[tuple[str, bool]]:
    """Each register field's register, in encoding order, and whether it is a byte field."""
    names = IA32_GENERAL_REGISTER_NAMES
    fields = [(at, shift, False) for at, shift in item["fields"]]
    fields += [(at, shift, True) for at, shift in item.get("byte_fields", ())]
    fields.sort()
    return [(names[body[at] >> shift & (3 if byte else 7)], byte) for at, shift, byte in fields]


def _register_pairs(
    donor_body: bytes,
    donor_items: list[dict[str, Any]],
    reference_body: bytes,
    reference_items: list[dict[str, Any]],
    donor_masked: list[tuple[int, int, tuple[Any, ...]]],
    reference_masked: list[tuple[int, int, tuple[Any, ...]]],
) -> dict[int, list[tuple[str, str]]]:
    """For each donor instruction aligned with an equal-shaped reference instruction,
    the (donor register, reference register) pair of every field."""
    matcher = difflib.SequenceMatcher(
        a=[key for _o, _l, key in donor_masked],
        b=[key for _o, _l, key in reference_masked],
        autojunk=False,
    )
    pairs: dict[int, list[tuple[str, str]]] = {}
    for block in matcher.get_matching_blocks():
        for k in range(block.size):
            left, right = donor_items[block.a + k], reference_items[block.b + k]
            ours = _field_values(donor_body, left)
            theirs = _field_values(reference_body, right)
            if len(ours) == len(theirs):
                pairs[block.a + k] = [(x, y) for (x, _b), (y, _c) in zip(ours, theirs, strict=True)]
    return pairs


def _bijection_candidates(pairs: dict[int, list[tuple[str, str]]]) -> list[dict[str, str]]:
    """Register permutations the aligned fields suggest, best explained first.

    A candidate is a transposition, a 3-cycle or two disjoint transpositions
    over the registers that appear in a differing field pair; its score is the
    number of aligned instructions it turns from differing into equal.
    """
    involved = sorted(
        {name for fields in pairs.values() for x, y in fields if x != y for name in (x, y)}
        - {"esp"}
    )
    if len(involved) > MAX_BIJECTION_REGISTERS:
        return []
    candidates: list[dict[str, str]] = []
    for left, right in itertools.combinations(involved, 2):
        candidates.append({left: right, right: left})
    for a, b, c in itertools.permutations(involved, 3):
        if a == min(a, b, c):
            candidates.append({a: b, b: c, c: a})
    for (a, b), (c, d) in itertools.combinations(itertools.combinations(involved, 2), 2):
        if len({a, b, c, d}) == 4 and (a, b) < (c, d):
            candidates.append({a: b, b: a, c: d, d: c})
    scored = []
    for sigma in candidates:
        score = sum(
            1
            for fields in pairs.values()
            if any(x != y for x, y in fields) and all(sigma.get(x, x) == y for x, y in fields)
        )
        if score:
            scored.append((-score, sorted(sigma.items()), sigma))
    scored.sort()
    return [sigma for _score, _key, sigma in scored[:MAX_BIJECTION_CANDIDATES]]


def _bijection_scopes(
    sigma: dict[str, str],
    donor_body: bytes,
    items: list[dict[str, Any]],
    pairs: dict[int, list[tuple[str, str]]],
    code_end: int,
    context: str,
    forced_live: frozenset[int] = frozenset(),
) -> list[list[int]]:
    """Scopes that cover the instructions the bijection explains and none it breaks.

    The producer re-checks every bound against both versions.
    """
    support = set(sigma)
    atoms = ia32_register_atoms(support)
    live, successors = _register_bijection_live_sets(items, f"{context} liveness")
    registers = _register_level_live(items, successors, f"{context} register liveness")

    def dead(index: int) -> bool:
        if index == len(items):
            return True
        if items[index]["offset"] in forced_live:
            return False
        return not (live[index] & atoms) and not (registers[index] & support)

    prefer: list[str | None] = []
    for index, item in enumerate(items):
        if _implicit_support(donor_body, item, support):
            prefer.append("implicit")
            continue
        fields = pairs.get(index)
        if not fields or not any(x in support or y in support for x, y in fields):
            prefer.append(None)
            continue
        mapped = all(sigma.get(x, x) == y for x, y in fields)
        plain = all(x == y for x, y in fields)
        prefer.append(
            "mapped" if mapped and not plain else "plain" if plain and not mapped else None
        )
    # The correspondence can change only on an edge into a point where the
    # support is dead, so the instructions joined by edges into live points
    # share one mode.  Each such component takes the bijection when it
    # explains more of its instructions than it breaks; one holding an
    # instruction that touches a support register implicitly stays plain.
    parent = list(range(len(items)))

    def root(index: int) -> int:
        while parent[index] != index:
            parent[index] = parent[parent[index]]
            index = parent[index]
        return index

    for index in range(len(items)):
        for edge in successors[index]:
            if not dead(edge):
                parent[root(edge)] = root(index)
    members: dict[int, list[int]] = {}
    for index in range(len(items)):
        members.setdefault(root(index), []).append(index)
    chosen: set[int] = set()
    for group in members.values():
        votes = [prefer[index] for index in group]
        if "implicit" not in votes and votes.count("mapped") > votes.count("plain"):
            chosen |= set(group)
    scopes: list[list[int]] = []
    for index in sorted(chosen):
        bounds = [
            items[index]["offset"],
            items[index + 1]["offset"] if index + 1 < len(items) else code_end,
        ]
        if scopes and scopes[-1][1] == bounds[0]:
            scopes[-1][1] = bounds[1]
        else:
            scopes.append(bounds)
    return scopes


def build_region_resize_rewriting(
    *,
    donor: AuthoredClassicRecord,
    target_id: str,
    translation_unit_id: str,
    build_target: str,
    symbol: str,
    seed_object: bytes,
    donor_object: bytes,
    reference_object: bytes,
) -> DeclarationShapeEqualBodyAuthoring:
    """Author a region-resize consumer whose proved replacements reach the reference body."""

    for name, value in (
        ("seed_object", seed_object),
        ("donor_object", donor_object),
        ("reference_object", reference_object),
    ):
        if type(value) is not bytes or not value:
            raise DiscoveryAuthoringError(f"{name} must be non-empty immutable bytes")
    context = f"discovery region resize for {symbol}"
    try:
        seed = CoffObject(seed_object)
        donor_coff = CoffObject(donor_object)
        reference = CoffObject(reference_object)
        sp = seed.function_section(symbol)
        dp = donor_coff.function_section(symbol)
        rp = reference.function_section(symbol)
        donor_body = bytes(coff_body(donor_coff, dp))
        reference_body = bytes(coff_body(reference, rp))
        if donor_body == reference_body:
            raise DiscoveryAuthoringError("the donor body already equals the reference body")
        donor_rows = detailed_relocations(donor_coff, dp)
        reference_rows = detailed_relocations(reference, rp)
        proc, code_end, fill = _procedure(donor_coff, dp, f"{context} donor")
        reference_proc, reference_code_end, reference_fill = _procedure(
            reference, rp, f"{context} reference"
        )
        fill_alignment = max(fill, reference_fill)
        donor_keys = _instruction_keys(donor_body, donor_rows, code_end, f"{context} donor")
        reference_keys = _instruction_keys(
            reference_body, reference_rows, reference_code_end, f"{context} reference"
        )
        external_entries = sorted(
            relational_form_external_entries(donor_coff, dp, f"{context} external entries")
        )
        prologue = 0
        if ".debug$F" in _comdat_child_closure(donor_coff, dp)[1]:
            prologue = parse_fpo_data(
                bytes(coff_body(donor_coff, _comdat_child(donor_coff, dp, ".debug$F"))),
                expected_proc_size=dp["raw_size"],
                body=donor_body,
            )["cbProlog"]
        protected = protected_code_offsets(donor_coff, dp, context)
        # Without both profiles the search proposes the fixed ladder alone.
        profiles: tuple[VersionProfile, VersionProfile] | None
        try:
            profiles = (
                version_profile(
                    donor_body,
                    donor_rows,
                    code_end,
                    f"{context} donor profile",
                    section_number=dp["number"],
                    external_entries=frozenset(external_entries),
                    protected_offsets=protected,
                ),
                version_profile(
                    reference_body,
                    reference_rows,
                    reference_code_end,
                    f"{context} reference profile",
                    section_number=rp["number"],
                    external_entries=frozenset(
                        relational_form_external_entries(
                            reference, rp, f"{context} reference external entries"
                        )
                    ),
                ),
            )
        except ByteIdentityError:
            profiles = None
        donor_targets = _branch_targets(donor_body, donor_rows, code_end, f"{context} donor")
        reference_targets = _branch_targets(
            reference_body, reference_rows, reference_code_end, f"{context} reference"
        )

        def search(
            keys: list[tuple[int, int, tuple[Any, ...]]],
            bijection: dict[str, Any] | None,
        ) -> tuple[list[dict[str, Any]], bytes, dict[str, Any]]:
            runs = derive_region_candidates(keys, reference_keys)
            aligned = _aligned_offsets(keys, reference_keys)
            if not runs:
                raise DiscoveryAuthoringError("the donor and reference instructions do not differ")
            groups = [_Group(index, index) for index in range(len(runs))]
            first_refusals: dict[int, str] = {}
            last_refusals: dict[int, str] = {}
            varied: int | None = None
            scope_bound: int | None = None
            attempt: tuple[list[dict[str, Any]], bytes, dict[str, Any]] | None = None
            failure: str | None = None
            selection = (
                None
                if profiles is None
                else Selection(
                    *profiles,
                    prologue,
                    () if bijection is None else tuple(sorted(bijection["mapping"].items())),
                    ()
                    if bijection is None
                    else tuple((left, right) for left, right in bijection["scopes"]),
                )
            )
            disagreements: dict[int, str] = {}

            def span(first: int, last: int) -> int:
                return runs[last][1] - runs[first][0]

            def label_of(group: _Group) -> int:
                first_index = runs[group.first][0]
                return keys[first_index][0] if first_index < len(keys) else code_end

            def settle(position: int) -> int:
                """Plan a group's shapes; merge it with neighbours when that makes it agree.

                A group with no agreeing shape absorbs the fewest neighbouring
                groups (at most `MAX_MERGED_GROUPS` on one side, forward first)
                whose merged region has one.  A disagreement merging cannot
                cure (a barrier in the run itself) or one no bounded merge
                cures leaves the group as it is, with the ladder.  Returns the
                settled group's position.
                """
                shapes, disagreement = plan_group_shapes(
                    groups, position, runs, len(keys), len(reference_keys), selection
                )
                group = groups[position]
                group.shapes, group.shape = shapes, 0
                if disagreement is None:
                    return position
                disagreements.setdefault(label_of(group), disagreement[1])
                if disagreement[0] == "structure":
                    return position
                for reach in range(1, MAX_MERGED_GROUPS + 1):
                    for first, last in ((position, position + reach), (position - reach, position)):
                        if first < 0 or last >= len(groups):
                            continue
                        if span(groups[first].first, groups[last].last) > MAX_REGION_INSTRUCTIONS:
                            continue
                        merged = _Group(groups[first].first, groups[last].last)
                        trial = [*groups[:first], merged, *groups[last + 1 :]]
                        shapes, disagreement = plan_group_shapes(
                            trial, first, runs, len(keys), len(reference_keys), selection
                        )
                        if disagreement is None:
                            merged.shapes = shapes
                            groups[first : last + 1] = [merged]
                            return first
                return position

            position = 0
            while position < len(groups):
                position = settle(position) + 1
            for _ in range(MAX_ATTEMPTS):
                empty = next((group for group in groups if not group.shapes), None)
                if empty is not None:
                    label = label_of(empty)
                    failure = (
                        f"the region at {label} has no boundary where the versions agree: "
                        + disagreements.get(label, "every shape breaks the region's shape checks")
                    )
                    break
                ranges = _group_ranges(groups, runs, len(keys), len(reference_keys))
                refused: int | None = None
                message: str | None = None
                if ranges is None and varied is not None:
                    # The shape just taken runs into a neighbour: take the next one.
                    refused = varied
                elif ranges is None:
                    # Two regions' contexts meet: they are one region.
                    position = next(
                        position
                        for position in range(1, len(groups))
                        if _group_ranges(
                            groups[: position + 1], runs, len(keys), len(reference_keys)
                        )
                        is None
                    )
                    # The merged region is tried again from its own first shape.
                    groups[position - 1].last = groups[position].last
                    del groups[position]
                    varied = settle(position - 1)
                    continue
                else:
                    try:
                        regions = _regions_for(
                            ranges,
                            keys,
                            reference_keys,
                            donor_rows,
                            reference_rows,
                            code_end,
                            reference_code_end,
                            reference_body,
                            (donor_targets, reference_targets, aligned),
                        )
                        image, proof = apply_region_resize(
                            donor_body,
                            regions,
                            donor_rows,
                            dp["number"],
                            f"{context} image",
                            code_length=None if code_end == proc else code_end,
                            proc_size=proc,
                            external_entries=frozenset(external_entries),
                            protected_offsets=protected,
                            prologue_length=prologue,
                            bijection=bijection,
                            frame_pointer_free=frame_pointer_free,
                        )
                    except (ByteIdentityError, DiscoveryAuthoringError) as exc:
                        refused = getattr(exc, "region", None)
                        message = str(exc)
                        if refused is None:
                            failure = message
                            bound = getattr(exc, "offset", None)
                            if isinstance(exc, ScopeBoundRefusal):
                                scope_bound = bound
                            break
                    else:
                        image = image + b"\x90" * (
                            _padded_length(len(image), fill_alignment) - len(image)
                        )
                        if image != reference_body:
                            failure = "the proved layout differs from the reference body"
                            break
                        attempt = (regions, image, proof)
                        break
                group = groups[refused]
                varied = refused
                label = label_of(group)
                if message is not None:
                    first_refusals.setdefault(label, message)
                    last_refusals[label] = message
                group.shape += 1
                if group.shape == len(group.shapes or ()):
                    # Every shape refuses: the region absorbs a neighbouring run,
                    # while it stays a bounded region.
                    if (
                        refused + 1 < len(groups)
                        and span(group.first, groups[refused + 1].last) <= MAX_REGION_INSTRUCTIONS
                    ):
                        group.last = groups[refused + 1].last
                        del groups[refused + 1]
                        varied = settle(refused)
                    elif (
                        refused > 0
                        and span(groups[refused - 1].first, group.last) <= MAX_REGION_INSTRUCTIONS
                    ):
                        groups[refused - 1].last = group.last
                        del groups[refused]
                        varied = settle(refused - 1)
                    else:
                        failure = (
                            f"the region at {label} refuses in every shape it can take; "
                            "first refusal: "
                            + first_refusals.get(
                                label, disagreements.get(label, "every context meets a neighbour")
                            )
                            + (
                                f"; last refusal: {last_refusals[label]}"
                                if label in last_refusals
                                and last_refusals[label] != first_refusals.get(label)
                                else ""
                            )
                        )
                        break
            else:
                failure = "the region search exceeded its attempt bound"
            if attempt is None:
                detail = "; ".join(
                    f"at {key}: {value}" for key, value in sorted(first_refusals.items())
                )
                refusal = DiscoveryAuthoringError(
                    f"no region replacement reaches the reference: {failure}"
                    + (f" (first refusals: {detail})" if detail else "")
                )
                refusal.scope_bound = scope_bound  # type: ignore[attr-defined]
                raise refusal
            return attempt

        frame_pointer_free = False
        try:
            regions, image, proof = search(donor_keys, None)
            bijection: dict[str, Any] | None = None
        except DiscoveryAuthoringError as plain_refusal:
            found = None
            donor_items = refine_call_reads(
                decode_ia32_bijection_body(
                    donor_body,
                    f"{context} donor",
                    relocation_symbol_map(donor_rows),
                    None if code_end == len(donor_body) else code_end,
                ),
                relocation_symbol_map(donor_rows),
            )
            reference_items = decode_ia32_bijection_body(
                reference_body,
                f"{context} reference",
                relocation_symbol_map(reference_rows),
                None if reference_code_end == len(reference_body) else reference_code_end,
            )
            pairs = _register_pairs(
                donor_body,
                donor_items,
                reference_body,
                reference_items,
                _instruction_keys(
                    donor_body, donor_rows, code_end, f"{context} donor", mask_registers=True
                ),
                _instruction_keys(
                    reference_body,
                    reference_rows,
                    reference_code_end,
                    f"{context} reference",
                    mask_registers=True,
                ),
            )
            tried = []
            for sigma in _bijection_candidates(pairs):
                frame_pointer_free = False
                if "ebp" in sigma:
                    try:
                        require_frame_pointer_free_frame(
                            donor_coff, dp, donor_body, donor_items, f"{context} frame proof"
                        )
                    except ByteIdentityError:
                        continue
                    frame_pointer_free = True
                forced: set[int] = set()
                seen: list[list[list[int]]] = []
                for _round in range(MAX_SCOPE_ROUNDS):
                    scopes = _bijection_scopes(
                        sigma,
                        donor_body,
                        donor_items,
                        pairs,
                        code_end,
                        f"{context} bijection",
                        frozenset(forced),
                    )
                    if not scopes or scopes in seen:
                        break
                    seen.append(scopes)
                    declared = {"mapping": dict(sorted(sigma.items())), "scopes": scopes}
                    rewritten = bytearray(donor_body)
                    unique = set()
                    for item in donor_items:
                        if not any(left <= item["offset"] < right for left, right in scopes):
                            continue
                        saved = bytes(rewritten)
                        try:
                            _sigma_rewrite(
                                rewritten,
                                item,
                                sigma,
                                {
                                    row["offset"] + k
                                    for row in donor_rows
                                    for k in range(row["width"])
                                },
                                f"{context} bijection",
                            )
                        except ByteIdentityError:
                            rewritten[:] = saved
                            unique.add(item["offset"])
                    try:
                        mapped_keys = _instruction_keys(
                            bytes(rewritten),
                            donor_rows,
                            code_end,
                            f"{context} donor under the bijection",
                            unique=frozenset(unique),
                        )
                    except ByteIdentityError:
                        break
                    if [key[:2] for key in mapped_keys] != [key[:2] for key in donor_keys]:
                        break
                    try:
                        regions, image, proof = search(mapped_keys, declared)
                    except DiscoveryAuthoringError as exc:
                        bound = getattr(exc, "scope_bound", None)
                        if bound is not None and bound not in forced:
                            # A bound the image's liveness refuses: treat it as live
                            # and choose the scopes again.
                            forced.add(bound)
                            continue
                        tried.append(f"{declared['mapping']}: {exc}")
                        break
                    found = (regions, image, proof, declared)
                    break
                if found is not None:
                    break
            if found is None:
                if tried:
                    raise DiscoveryAuthoringError(
                        f"{plain_refusal}; under a register bijection: {tried[0]}"
                    ) from plain_refusal
                raise
            regions, image, proof, bijection = found
        if proof["image_proc_size"] != reference_proc:
            raise DiscoveryAuthoringError("the image's procedure size differs from the reference's")
        derived, derived_detail = resized_donor_object(
            donor_object, symbol, image, proof, f"{context} derived donor"
        )
        derived_coff = CoffObject(derived)
        installed = detailed_relocations(derived_coff, derived_coff.function_section(symbol))
        seed_functions = function_multiset(seed)
        donor_functions = function_multiset(donor_coff)
        extras = sorted(
            name
            for name in set(seed_functions) | set(donor_functions)
            if donor_functions.get(name, 0) != seed_functions.get(name, 0)
        )
        closure = _comdat_child_closure(seed, sp)[1]
        expected: dict[str, Any] = {
            "expected_section_number": sp["number"],
            "expected_section_count": len(seed.sections),
            "expected_function_count": sum(seed_functions.values()),
            "expected_comdat_count": sum(comdat_primary_identity_multiset(seed).values()),
            "expected_seed_length": sp["raw_size"],
            "expected_preimage_length": dp["raw_size"],
            "expected_donor_length": len(image),
            "expected_body_length": len(image),
            "expected_relocation_count": sp["relocation_count"],
            "expected_seed_line_count": sp["line_count"],
            "expected_donor_line_count": dp["line_count"],
            "expected_characteristics": sp["characteristics"],
            "expected_selection": section_definitions(seed)[sp["number"]]["selection"],
            "expected_closure": list(closure),
            "expected_seed_metadata_sha256": instruction_mosaic_metadata_sha256(seed, sp),
            "expected_donor_metadata_sha256": instruction_mosaic_metadata_sha256(donor_coff, dp),
            "expected_seed_body_sha256": sha256_bytes(coff_body(seed, sp)),
            "expected_donor_body_sha256": sha256_bytes(donor_body),
            "expected_body_sha256": sha256_bytes(image),
            "expected_linked_span": (len(image) + 15) // 16 * 16,
            "retail_oracle": {"length": len(image)},
            "retail_relocations": [
                {field: row[field] for field in _RELOCATION_FIELDS} for row in installed
            ],
            "region_resize.expected_external_entries": external_entries,
            "region_resize.expected_proc_size": proc,
            "region_resize.expected_fill_alignment": fill_alignment,
            "region_resize.expected_growth": proof["growth"],
            "region_resize.expected_region_proofs": proof["regions"],
            "region_resize.expected_branch_repairs": proof["branch_repairs"],
            "region_resize.expected_relocation_reseat": proof["relocation_reseat"],
            "region_resize.expected_addend_repairs": proof["addend_repairs"],
            "region_resize.expected_instruction_count": proof["instruction_count"],
            "region_resize.expected_procedure_range": derived_detail["procedure_range"],
            "region_resize.expected_carried_code_symbols": derived_detail["carried_code_symbols"],
            "region_resize.expected_collapsed_line_rows": derived_detail["collapsed_line_rows"],
        }
        if code_end != proc:
            expected["region_resize.expected_code_length"] = code_end
        if bijection is not None:
            expected["region_resize.expected_bijection_rewrites"] = proof["bijection_rewrites"]
            expected["region_resize.expected_bijection_mode_changes"] = proof[
                "bijection_mode_changes"
            ]
        if extras:
            expected["expected_donor_extra_functions"] = extras
        if dp["number"] != sp["number"]:
            expected["expected_donor_section_number"] = dp["number"]
        if len(donor_coff.sections) != len(seed.sections):
            expected["expected_donor_section_count"] = len(donor_coff.sections)
        scope = Scope(target=target_id, translation_unit=translation_unit_id, function=symbol)
        family = ClassicRecipeFamily.RETAIL_EXACT_REGION_RESIZE_REWRITING
        parameters = (
            ClassicField(
                name="region_resize",
                value=cast(
                    JsonValue,
                    {"kind": REGION_RESIZE_KIND, "regions": regions}
                    | ({} if bijection is None else {"bijection": bijection}),
                ),
            ),
        )
        intervention_id = _stable_id(
            "function",
            {
                "build_target": build_target,
                "dependency": donor.intervention.id,
                "expected_values": expected,
                "family": family.value,
                "parameters": [item.model_dump(mode="json") for item in parameters],
                "scope": scope.model_dump(mode="json"),
            },
        )
        intervention = ClassicRecipeIntervention(
            id=intervention_id,
            scope=scope,
            rationale=_REGION_RESIZE_RATIONALE,
            dependencies=(donor.intervention.id,),
            family=family,
            role=ClassicRecipeRole.FUNCTION,
            build_target=build_target,
            symbol=symbol,
            parameters=parameters,
        )
        receipt = _record_receipt(intervention, cast(dict[str, JsonValue], expected))
        constraints = merge_candidate_constraints(intervention, receipt).materialize()
        candidate = ClassicFamilyDispatcher().dispatch(
            intervention,
            ClassicDispatchMaterials(
                seed_object=seed_object,
                donor_object=donor_object,
                candidate_constraints=constraints,
            ),
        )
        composed = CoffObject(candidate.output)
        if bytes(coff_body(composed, composed.function_section(symbol))) != reference_body:
            raise DiscoveryAuthoringError("the rewritten body differs from the reference body")
        return DeclarationShapeEqualBodyAuthoring(
            donor=donor,
            function=AuthoredClassicRecord(intervention, receipt),
            candidate_object=candidate.output,
            composition_proof=None,
        )
    except DiscoveryAuthoringError:
        raise
    except (
        ByteIdentityError,
        ClassicProjectError,
        DonorSourceError,
        ValidationError,
        KeyError,
    ) as exc:
        raise DiscoveryAuthoringError(f"cannot author a region-resize rewriting: {exc}") from exc


__all__ = ["build_region_resize_rewriting", "derive_region_candidates"]
