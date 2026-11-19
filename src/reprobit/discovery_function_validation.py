"""Author whole-function translation validations whose replacement is the reference body.

When neither a reordering nor a region replacement reaches the reference
object's body -- the donor differs from it across the whole function, in
register allocation, spill slots and scheduling, with the same control flow
-- `retail_exact_function_translation_validation` replaces the donor's whole
code by the reference's instructions and proves the two equivalent join by
join (:mod:`reprobit.classic.function_validation`).  This module declares the
reference's instructions, pairs its relocated fields with the donor's
records, measures every pin the producer checks, and finally requires the
ordinary producer to accept the record and compose the reference body.  The
reference object is the project-owned COFF the grind plan names; nothing
here reads a reference image, and the producer re-proves the replacement
against the donor.
"""

from __future__ import annotations

from typing import Any, cast

from pydantic import ValidationError

from reprobit.binary import ByteIdentityError
from reprobit.classic.coff import (
    _comdat_child,
    _comdat_child_closure,
    comdat_primary_identity_multiset,
    function_multiset,
)
from reprobit.classic.composition_mosaic import instruction_mosaic_metadata_sha256
from reprobit.classic.foundation import sha256_bytes
from reprobit.classic.function_validation import (
    FUNCTION_VALIDATION_KIND,
    measure_function_validation,
)
from reprobit.classic.region_simulation import region_boundaries
from reprobit.classic.toolchain_helpers import HelperLibrary
from reprobit.classic_donors import DonorSourceError, merge_candidate_constraints
from reprobit.classic_project import (
    ClassicDispatchMaterials,
    ClassicFamilyDispatcher,
    ClassicProjectError,
)
from reprobit.coff_format import (
    CoffObject,
    coff_body,
    coff_unpack,
    detailed_relocations,
    section_definitions,
)
from reprobit.discovery_authoring import (
    AuthoredClassicRecord,
    DeclarationShapeEqualBodyAuthoring,
    DiscoveryAuthoringError,
    _record_receipt,
    _stable_id,
)
from reprobit.discovery_region_resize import _procedure, _symbol_identity
from reprobit.intervention_metadata import ClassicRecipeFamily, ClassicRecipeRole
from reprobit.model import Scope
from reprobit.schema import ClassicField, ClassicRecipeIntervention
from reprobit.strict_json import JsonValue

_RATIONALE = (
    "A freshly compiled private donor of the same translation unit whose whole code is "
    "replaced by instructions proved equivalent join by join under an inferred register "
    "and stack-slot correspondence."
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


def _pair_relocations(
    donor_rows: list[dict[str, Any]], reference_rows: list[dict[str, Any]]
) -> list[list[int]]:
    """Each reference field with the first unused donor record of the same symbol and type."""
    unused = list(donor_rows)
    pairs = []
    for row in sorted(reference_rows, key=lambda item: item["offset"]):
        match = next(
            (
                candidate
                for candidate in unused
                if _symbol_identity(candidate) == _symbol_identity(row)
                and candidate["type"] == row["type"]
            ),
            None,
        )
        if match is None:
            raise DiscoveryAuthoringError(
                f"the reference relocates {row['target']} at {row['offset']} more often than "
                "the donor"
            )
        unused.remove(match)
        pairs.append([row["offset"], match["offset"]])
    if unused:
        raise DiscoveryAuthoringError(
            f"the donor relocates {unused[0]['target']} more often than the reference"
        )
    return pairs


def build_function_validation_rewriting(
    *,
    donor: AuthoredClassicRecord,
    target_id: str,
    translation_unit_id: str,
    build_target: str,
    symbol: str,
    seed_object: bytes,
    donor_object: bytes,
    reference_object: bytes,
    helper_library: HelperLibrary | None = None,
) -> DeclarationShapeEqualBodyAuthoring:
    """Author a translation-validation consumer whose replacement is the reference body.

    ``helper_library`` is the authenticated toolchain library the bodies of
    compiler helpers are read from (`classic.toolchain_helpers`).
    """

    for name, value in (
        ("seed_object", seed_object),
        ("donor_object", donor_object),
        ("reference_object", reference_object),
    ):
        if type(value) is not bytes or not value:
            raise DiscoveryAuthoringError(f"{name} must be non-empty immutable bytes")
    context = f"discovery function validation for {symbol}"
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
        proc, code_end, fill = _procedure(donor_coff, dp, f"{context} donor")
        reference_proc, reference_code_end, reference_fill = _procedure(
            reference, rp, f"{context} reference"
        )
        if code_end != proc or reference_code_end != reference_proc:
            raise DiscoveryAuthoringError("a body has a data tail (a switch table)")
        fill_alignment = max(fill, reference_fill)
        code = reference_body[:reference_proc]
        reference_rows = detailed_relocations(reference, rp)
        donor_rows = detailed_relocations(donor_coff, dp)
        starts = region_boundaries(code, 0, len(code), f"{context} reference")
        instructions = [
            code[start:end].hex()
            for start, end in zip(starts, [*starts[1:], len(code)], strict=True)
        ]
        debug_raw = bytes(coff_body(reference, _comdat_child(reference, rp, ".debug$S")))
        _length, _start, debug_end = coff_unpack(
            "<III", debug_raw, 16, f"{context} reference debug range"
        )
        spec: dict[str, Any] = {
            "kind": FUNCTION_VALIDATION_KIND,
            "replacement_instructions": instructions,
            "replacement_relocations": _pair_relocations(donor_rows, reference_rows),
            "replacement_debug_end": debug_end,
        }
        image = reference_body
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
            "function_validation.expected_proc_size": proc,
            "function_validation.expected_fill_alignment": fill_alignment,
        }
        if extras:
            expected["expected_donor_extra_functions"] = extras
        if dp["number"] != sp["number"]:
            expected["expected_donor_section_number"] = dp["number"]
        if len(donor_coff.sections) != len(seed.sections):
            expected["expected_donor_section_count"] = len(donor_coff.sections)
        # The producer's own measurements are the pins.
        measured = measure_function_validation(
            donor_object,
            symbol,
            {
                **spec,
                "expected_proc_size": proc,
                "expected_fill_alignment": fill_alignment,
            },
            _comdat_child_closure(donor_coff, dp)[1],
            helper_library,
        )
        if measured.image != reference_body:
            raise DiscoveryAuthoringError("the proved image differs from the reference body")
        for key, value in measured.pins.items():
            expected[f"function_validation.{key}"] = value
        expected["retail_relocations"] = [
            {field: row[field] for field in _RELOCATION_FIELDS} for row in measured.rows
        ]
        scope = Scope(target=target_id, translation_unit=translation_unit_id, function=symbol)
        family = ClassicRecipeFamily.RETAIL_EXACT_FUNCTION_TRANSLATION_VALIDATION
        parameters = (ClassicField(name="function_validation", value=cast(JsonValue, spec)),)
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
            rationale=_RATIONALE,
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
                helper_library=helper_library,
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
        raise DiscoveryAuthoringError(
            f"cannot author a function translation validation: {exc}"
        ) from exc


__all__ = ["build_function_validation_rewriting"]
