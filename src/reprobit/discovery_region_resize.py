"""Author region-resize rewritings whose replacements reach a reference body.

When grind's donor compiles a function to a body of another length than the
reference object's -- the compiler kept a value in a register where the
reference reloads it, or allocated another register -- no reordering reaches
the reference.  `retail_exact_region_resize_rewriting` replaces whole regions
of the donor by instructions a path simulation proves equivalent, then lays
the function out at its new length.  This module aligns the donor's
instructions with the reference object's, takes each maximal run of
differing instructions (merged with its neighbours while the proof refuses),
offers the reference's instructions for that run as the replacement, measures
every pin the producer checks, and finally requires the ordinary producer to
accept the record and compose the reference body.  The reference object is
the project-owned COFF the grind plan names; nothing here reads a reference
image, and the producer re-proves every replacement against the donor.
"""

from __future__ import annotations

import difflib
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
from reprobit.classic.register_semantics import decode_ia32_bijection_body
from reprobit.classic.relational import relational_form_external_entries
from reprobit.classic.rewriting_region_resize import (
    REGION_RESIZE_KIND,
    _padded_length,
    apply_region_resize,
    protected_code_offsets,
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
) -> list[tuple[int, int, tuple[Any, ...]]]:
    """(offset, length, comparison key) for each instruction of the code.

    A relocated field compares by its target symbol and addend; a relative
    branch by its opcode alone, since a layout change re-encodes it.
    """
    view = relocation_symbol_map(rows)
    by_offset = {row["offset"]: row for row in rows}
    instructions = decode_ia32_bijection_body(
        body, context, view, None if code_end == len(body) else code_end
    )
    keys = []
    for item in instructions:
        raw = bytearray(body[item["offset"] : item["offset"] + item["length"]])
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
    """A region under search: the base runs it covers and its context shape."""

    first: int
    last: int
    shape: int = 0


def _group_ranges(
    groups: list[_Group],
    runs: list[tuple[int, int, int, int]],
    donor_count: int,
    reference_count: int,
) -> list[tuple[int, int, int, int]] | None:
    """Each group's index ranges with its context, or None when two collide."""
    ranges: list[tuple[int, int, int, int]] = []
    for group in groups:
        back, ahead = CONTEXT_EXTENTS[group.shape]
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
        if ranges and (i1 < ranges[-1][1] or j1 < ranges[-1][3]):
            return None
        ranges.append((i1, i2, j1, j2))
    return ranges


def _regions_for(
    runs: list[tuple[int, int, int, int]],
    donor_keys: list[tuple[int, int, tuple[Any, ...]]],
    reference_keys: list[tuple[int, int, tuple[Any, ...]]],
    donor_rows: list[dict[str, Any]],
    reference_rows: list[dict[str, Any]],
    donor_code_end: int,
    reference_code_end: int,
    reference_body: bytes,
) -> list[dict[str, Any]]:
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
        if [_symbol_identity(row) for row in donor_fields] != [
            _symbol_identity(row) for row in reference_fields
        ]:
            refusal = DiscoveryAuthoringError(
                f"the region at {start} relocates other symbols than the reference's at "
                f"{reference_start}"
            )
            refusal.region = position  # type: ignore[attr-defined]
            raise refusal
        regions.append(
            {
                "region_start": start,
                "region_end": end,
                "replacement_instructions": [
                    reference_body[offset : offset + length].hex()
                    for offset, length, _key in reference_keys[j1:j2]
                ],
                "replacement_relocations": [
                    [reference_row["offset"] - reference_start, donor_row["offset"]]
                    for donor_row, reference_row in zip(donor_fields, reference_fields, strict=True)
                ],
            }
        )
    return regions


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
        runs = derive_region_candidates(donor_keys, reference_keys)
        if not runs:
            raise DiscoveryAuthoringError("the donor and reference instructions do not differ")
        groups = [_Group(index, index) for index in range(len(runs))]
        first_refusals: dict[int, str] = {}
        attempt: tuple[list[dict[str, Any]], bytes, dict[str, Any]] | None = None
        failure: str | None = None
        for _ in range(MAX_ATTEMPTS):
            ranges = _group_ranges(groups, runs, len(donor_keys), len(reference_keys))
            refused: int | None = None
            if ranges is None:
                # Two regions' contexts meet: they are one region.
                position = next(
                    position
                    for position in range(1, len(groups))
                    if _group_ranges(
                        groups[: position + 1], runs, len(donor_keys), len(reference_keys)
                    )
                    is None
                )
                groups[position - 1].last = groups[position].last
                groups[position - 1].shape = max(groups[position - 1].shape, groups[position].shape)
                del groups[position]
                continue
            else:
                try:
                    regions = _regions_for(
                        ranges,
                        donor_keys,
                        reference_keys,
                        donor_rows,
                        reference_rows,
                        code_end,
                        reference_code_end,
                        reference_body,
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
                    )
                except (ByteIdentityError, DiscoveryAuthoringError) as exc:
                    refused = getattr(exc, "region", None)
                    message = str(exc)
                    if refused is None:
                        failure = message
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
            first_index = runs[group.first][0]
            label = donor_keys[first_index][0] if first_index < len(donor_keys) else code_end
            first_refusals.setdefault(label, message)
            group.shape += 1
            if group.shape == len(CONTEXT_EXTENTS):
                # Every shape refuses: the region absorbs a neighbouring run,
                # while it stays a bounded region.
                def span(first: int, last: int) -> int:
                    return runs[last][1] - runs[first][0]

                if (
                    refused + 1 < len(groups)
                    and span(group.first, groups[refused + 1].last) <= MAX_REGION_INSTRUCTIONS
                ):
                    group.last = groups[refused + 1].last
                    group.shape = 0
                    del groups[refused + 1]
                elif (
                    refused > 0
                    and span(groups[refused - 1].first, group.last) <= MAX_REGION_INSTRUCTIONS
                ):
                    groups[refused - 1].last = group.last
                    groups[refused - 1].shape = 0
                    del groups[refused]
                else:
                    failure = (
                        f"the region at {label} refuses in every shape it can take; "
                        f"first refusal: {first_refusals[label]}"
                    )
                    break
        else:
            failure = "the region search exceeded its attempt bound"
        if attempt is None:
            detail = "; ".join(
                f"at {key}: {value}" for key, value in sorted(first_refusals.items())
            )
            raise DiscoveryAuthoringError(
                f"no region replacement reaches the reference: {failure}"
                + (f" (first refusals: {detail})" if detail else "")
            )
        regions, image, proof = attempt
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
                value=cast(JsonValue, {"kind": REGION_RESIZE_KIND, "regions": regions}),
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
