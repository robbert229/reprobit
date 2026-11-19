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
from reprobit.classic.debug import MSVC50_FUNCTION_FILL_BYTE
from reprobit.classic.foundation import sha256_bytes
from reprobit.classic.function_validation import (
    FUNCTION_VALIDATION_KIND,
    measure_function_validation,
    section_label_values,
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


def _numbered_label(name: str) -> tuple[str, int] | None:
    """(kind, serial) of a label MSVC 5.0 numbers by compile order, else None.

    A ``$L<n>`` label (a switch table, a case) is of kind ``$L``; a C
    ``goto`` label ``$<name>$<n>`` of kind ``$<name>``.  Any declaration the
    grind donor's extern run adds before the function renumbers both.
    """
    if len(name) > 2 and name.startswith("$L") and name[2:].isdigit():
        return "$L", int(name[2:])
    base, separator, serial = name.rpartition("$")
    if separator and len(base) > 1 and base.startswith("$") and serial.isdigit():
        return base, int(serial)
    return None


def _label_renaming(
    donor: CoffObject,
    donor_section: dict[str, Any],
    reference: CoffObject,
    reference_section: dict[str, Any],
) -> dict[str, str]:
    """Each numbered label of the donor's section and the reference's label it is.

    Labels pair by kind, in serial order: the extern run before the function
    shifts every serial the function takes, never their order.  The renaming
    is a bijection by construction; a kind with another count of labels in
    the two sections is not renamed (its labels keep their names, as before
    any renaming).  It is only a proposal: the producer proves whatever
    pairing the record declares.
    """

    def kinds(coff: CoffObject, section: dict[str, Any]) -> dict[str, list[tuple[int, str]]]:
        found: dict[str, list[tuple[int, str]]] = {}
        for item in coff.symbols.values():
            if item["section"] != section["number"]:
                continue
            numbered = _numbered_label(str(item["name"]))
            if numbered is not None:
                found.setdefault(numbered[0], []).append((numbered[1], str(item["name"])))
        return {kind: sorted(set(names)) for kind, names in found.items()}

    mine, theirs = kinds(donor, donor_section), kinds(reference, reference_section)
    renaming: dict[str, str] = {}
    for kind in sorted(set(mine) | set(theirs)):
        left, right = mine.get(kind, []), theirs.get(kind, [])
        if len(left) != len(right):
            continue
        renaming.update((name, other) for (_s, name), (_t, other) in zip(left, right, strict=True))
    return renaming


def _require_bijection(pairs: list[tuple[str, str]], what: str) -> None:
    """Refuse a renaming that takes one name to two, or two names to one."""
    forward: dict[str, str] = {}
    backward: dict[str, str] = {}
    for mine, theirs in pairs:
        if forward.setdefault(mine, theirs) != theirs or backward.setdefault(theirs, mine) != mine:
            raise DiscoveryAuthoringError(f"the pairing renames the {what} inconsistently")


def _pair_relocations(
    donor_rows: list[dict[str, Any]],
    reference_rows: list[dict[str, Any]],
    donor_section: int | None = None,
    reference_section: int | None = None,
    *,
    renaming: dict[str, str] | None = None,
    code_ends: tuple[int, int] | None = None,
) -> list[list[int]]:
    """Each reference field with an unused donor record of the same symbol and type.

    Of those, the first whose addend is the field's own is taken, else the
    first.  The proof names a relocated value by its target alone (the
    addend is in the bytes), but the installed table's records are the
    donor's re-seated and must match the image's fields addend for addend:
    so when two fields of one symbol move past each other, each still takes
    the record of its own displacement.  A file static pairs by base name
    (`_symbol_identity`), and the statics' renaming must be one bijection.

    A record naming the function's own section (a switch table's base or
    entry, a recursive call) takes the donor record of the same symbol and
    type, occurrence by occurrence in offset order: the label's place
    differs between the two bodies, and the producer proves whatever pairing
    is declared.  A numbered label is the reference's label ``renaming``
    gives (`_label_renaming`), never the reference's label of the donor's
    own serial.  With ``code_ends`` (the donor's, the reference's), a field
    in a data tail (a table entry) pairs only with a field in a data tail,
    and a field naming a label in the tail (a table base) only with one
    naming a label in the tail.
    """
    names = renaming or {}
    own_donor = [row for row in donor_rows if row["target_section"] == donor_section]
    own_reference = [row for row in reference_rows if row["target_section"] == reference_section]
    pairs: list[list[int]] = []
    own_pairs: list[tuple[dict[str, Any], dict[str, Any]]] = []
    for name in sorted(
        {names.get(row["target"], row["target"]) for row in own_donor}
        | {row["target"] for row in own_reference}
    ):
        for kind in sorted({row["type"] for row in own_donor + own_reference}):
            mine = sorted(
                (
                    row
                    for row in own_donor
                    if (names.get(row["target"], row["target"]), row["type"]) == (name, kind)
                ),
                key=lambda row: row["offset"],
            )
            theirs = sorted(
                (row for row in own_reference if (row["target"], row["type"]) == (name, kind)),
                key=lambda row: row["offset"],
            )
            if len(mine) != len(theirs):
                donor_names = sorted({row["target"] for row in mine})
                raise DiscoveryAuthoringError(
                    f"the reference names its own {name} {len(theirs)} times, the donor "
                    f"{len(mine)} times"
                    + (f" (as {', '.join(donor_names)})" if donor_names != [name] and mine else "")
                )
            own_pairs.extend(zip(mine, theirs, strict=True))
    if code_ends is not None:
        donor_end, reference_end = code_ends
        for mine_row, their_row in own_pairs:
            if (mine_row["offset"] >= donor_end) != (their_row["offset"] >= reference_end) or (
                mine_row["target_value"] >= donor_end
            ) != (their_row["target_value"] >= reference_end):
                raise DiscoveryAuthoringError(
                    f"the donor's field at {mine_row['offset']} naming {mine_row['target']} "
                    f"and the reference's at {their_row['offset']} naming "
                    f"{their_row['target']} play different parts (code or table)"
                )
    pairs.extend([their_row["offset"], mine_row["offset"]] for mine_row, their_row in own_pairs)
    unused = [row for row in donor_rows if row["target_section"] != donor_section]
    statics: list[tuple[str, str]] = []
    for row in sorted(
        (row for row in reference_rows if row["target_section"] != reference_section),
        key=lambda item: item["offset"],
    ):
        candidates = [
            candidate
            for candidate in unused
            if _symbol_identity(candidate) == _symbol_identity(row)
            and candidate["type"] == row["type"]
        ]
        match = next(
            (candidate for candidate in candidates if candidate["addend"] == row["addend"]),
            candidates[0] if candidates else None,
        )
        if match is None:
            raise DiscoveryAuthoringError(
                f"the reference relocates {row['target']} at {row['offset']} more often than "
                "the donor"
            )
        unused.remove(match)
        if _symbol_identity(row)[0] == "static":
            statics.append((match["target"], row["target"]))
        pairs.append([row["offset"], match["offset"]])
    if unused:
        raise DiscoveryAuthoringError(
            f"the donor relocates {unused[0]['target']} more often than the reference"
        )
    _require_bijection(statics, "file statics")
    _require_bijection(
        [(mine_row["target"], their_row["target"]) for mine_row, their_row in own_pairs],
        "function's own labels",
    )
    return sorted(pairs)


def _labels(
    donor: CoffObject,
    donor_section: dict[str, Any],
    reference: CoffObject,
    reference_section: dict[str, Any],
    pairs: list[list[int]],
    donor_rows: list[dict[str, Any]],
    reference_rows: list[dict[str, Any]],
    renaming: dict[str, str] | None = None,
) -> list[list[int]]:
    """Where each label of the donor's section lies in the reference.

    A label a paired field names lies where the reference's paired record
    names its own label; every other label (a ``goto`` label) where the
    reference's symbol of the same name lies, a numbered label's name being
    the one ``renaming`` gives (`_label_renaming`).
    """
    names_of = renaming or {}
    places: dict[int, int] = {}
    by_donor = {row["offset"]: row for row in donor_rows}
    by_reference = {row["offset"]: row for row in reference_rows}
    for local, donor_offset in pairs:
        mine, theirs = by_donor[donor_offset], by_reference[local]
        if mine["target_section"] != donor_section["number"] or mine["target_value"] == 0:
            continue
        place = places.setdefault(mine["target_value"], theirs["target_value"])
        if place != theirs["target_value"]:
            raise DiscoveryAuthoringError(
                f"the donor's label at {mine['target_value']} is named at both "
                f"{place} and {theirs['target_value']} of the reference"
            )
    named = {
        item["name"]: item["value"]
        for item in reference.symbols.values()
        if item["section"] == reference_section["number"]
    }
    for value in sorted(section_label_values(donor, donor_section)):
        if value in places:
            continue
        names = sorted(
            item["name"]
            for item in donor.symbols.values()
            if item["section"] == donor_section["number"] and item["value"] == value
        )
        found = {
            named[names_of.get(name, name)] for name in names if names_of.get(name, name) in named
        }
        if len(found) != 1:
            raise DiscoveryAuthoringError(
                f"the donor's label {names} at {value} has no one place in the reference"
            )
        places[value] = found.pop()
    return [[donor_place, image_place] for donor_place, image_place in sorted(places.items())]


def _reference_procedure(
    reference: CoffObject,
    section: dict[str, Any],
    donor_body: bytes,
    donor_proc: int,
    donor_debug_end: int,
    context: str,
) -> tuple[int, int, int, int]:
    """(procedure size, code end, fill alignment, debug end) of the reference.

    A reference whose FPO or CodeView procedure size is stale (it is the
    seed's, and the original's code is longer or shorter) is measured from
    its body instead: its code is the body up to MSVC 5.0's fill, ending in
    a ``ret`` or ``jmp``.  Its debug end is then the donor's, carried back
    from the end by the donor's epilogue, which the reference must end with.
    Only the code bytes, never these sizes, reach the record's proof.
    """
    body = bytes(coff_body(reference, section))
    debug_raw = bytes(coff_body(reference, _comdat_child(reference, section, ".debug$S")))
    try:
        proc, code_end, fill = _procedure(reference, section, context)
    except (ByteIdentityError, DiscoveryAuthoringError):
        rows = detailed_relocations(reference, section)
        if any(row["target_section"] == section["number"] for row in rows):
            raise
        code_end = len(body)
        while code_end and body[code_end - 1] == MSVC50_FUNCTION_FILL_BYTE:
            code_end -= 1
        starts = region_boundaries(body, 0, code_end, f"{context} reference code")
        straddling = sorted(
            row["offset"]
            for row in rows
            if any(row["offset"] < start < row["offset"] + 4 for start in starts)
        )
        if straddling:
            raise DiscoveryAuthoringError(
                f"{context}: the reference is stale: its procedure size is the seed's and its "
                f"relocated fields at {straddling[:5]} straddle its own instructions (a "
                "synthetic reference that kept the seed's records for a longer or shorter "
                "original)"
            ) from None
        last = body[starts[-1] : code_end]
        if last[:1] not in (b"\xc3", b"\xc2", b"\xe9", b"\xeb"):
            raise DiscoveryAuthoringError(
                f"{context}: the reference's procedure size is stale and its code does not end "
                "in a ret or jmp before its fill"
            ) from None
        epilogue = donor_body[donor_debug_end:donor_proc]
        if not body[:code_end].endswith(epilogue):
            raise DiscoveryAuthoringError(
                f"{context}: the reference's procedure size is stale and it does not end with "
                "the donor's epilogue, so its debug range cannot be carried"
            ) from None
        fill = 16 if len(body) != code_end else 1
        return code_end, code_end, fill, code_end - len(epilogue)
    _length, _start, debug_end = coff_unpack("<III", debug_raw, 16, f"{context} debug range")
    return proc, code_end, fill, debug_end


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
        donor_debug = bytes(coff_body(donor_coff, _comdat_child(donor_coff, dp, ".debug$S")))
        _length, _start, donor_debug_end = coff_unpack(
            "<III", donor_debug, 16, f"{context} donor debug range"
        )
        reference_proc, reference_code_end, reference_fill, debug_end = _reference_procedure(
            reference, rp, donor_body, proc, donor_debug_end, f"{context} reference"
        )
        fill_alignment = max(fill, reference_fill)
        code = reference_body[:reference_code_end]
        tail = reference_body[reference_code_end:reference_proc]
        reference_rows = detailed_relocations(reference, rp)
        donor_rows = detailed_relocations(donor_coff, dp)
        starts = region_boundaries(code, 0, len(code), f"{context} reference")
        straddling = sorted(
            row["offset"]
            for row in reference_rows
            if any(row["offset"] < start < row["offset"] + 4 for start in starts)
        )
        if straddling:
            raise DiscoveryAuthoringError(
                f"{context} reference: the reference is stale: its relocated fields at "
                f"{straddling[:5]} straddle its own instructions (a synthetic reference that "
                "kept the seed's relocation offsets for a longer or shorter original)"
            )
        instructions = [
            code[start:end].hex()
            for start, end in zip(starts, [*starts[1:], len(code)], strict=True)
        ]
        renaming = _label_renaming(donor_coff, dp, reference, rp)
        pairs = _pair_relocations(
            donor_rows,
            reference_rows,
            dp["number"],
            rp["number"],
            renaming=renaming,
            code_ends=(code_end, reference_code_end),
        )
        labels = _labels(donor_coff, dp, reference, rp, pairs, donor_rows, reference_rows, renaming)
        spec: dict[str, Any] = {
            "kind": FUNCTION_VALIDATION_KIND,
            "replacement_instructions": instructions,
            "replacement_relocations": pairs,
            "replacement_debug_end": debug_end,
        }
        if code_end != proc:
            spec["donor_code_end"] = code_end
        if tail:
            spec["replacement_tail"] = tail.hex()
        if labels:
            spec["replacement_labels"] = labels
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
