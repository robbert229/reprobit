"""Author donor-rewriting records whose instruction schedule reaches a reference body.

A grind donor sometimes compiles a function to exactly the reference's
instructions in a slightly different order: the compiler's scheduler picked
another of several equivalent orders.  `retail_exact_donor_rewriting` proves
such a reordering sound (a dependence DAG per window, debug fidelity, the
same relocations) and installs the reordered body.  This module derives the
windows by comparing the donor body with the reference object's body,
measures every pin the producer checks from the two fresh objects, and then
requires the ordinary producer to accept the complete record and compose the
reference body.  Nothing here reads a reference image: the reference object
is the project-owned COFF the grind plan names.
"""

from __future__ import annotations

from typing import Any, cast

from pydantic import ValidationError

from reprobit.binary import ByteIdentityError
from reprobit.classic.address_forms import apply_sib_operand_swaps
from reprobit.classic.candidate_recipe import (
    internal_relocation_targets,
    relocated_byte_offsets,
    relocation_symbol_map,
)
from reprobit.classic.coff import (
    _coff_table_bytes,
    _comdat_child_closure,
    comdat_primary_identity_multiset,
    function_multiset,
)
from reprobit.classic.composition_mosaic import instruction_mosaic_metadata_sha256
from reprobit.classic.foundation import sha256_bytes
from reprobit.classic.register_bijection import apply_register_bijection
from reprobit.classic.register_semantics import (
    IA32_GENERAL_REGISTER_NAMES,
    decode_ia32_bijection_body,
    decode_ia32_bijection_instruction,
)
from reprobit.classic.relational import relational_form_external_entries
from reprobit.classic.rewriting_certificates import DONOR_REWRITING_KIND
from reprobit.classic.scheduling_apply import (
    ia32_schedule_body_walk,
    require_topological_instruction_order,
)
from reprobit.classic.scheduling_certificates import measure_instruction_schedule_debug_envelope
from reprobit.classic.scheduling_dependence import (
    ia32_schedule_dependence_edges,
    ia32_schedule_stack_adjustments,
)
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
from reprobit.intervention_metadata import ClassicRecipeFamily, ClassicRecipeRole
from reprobit.model import Scope
from reprobit.schema import ClassicField, ClassicRecipeIntervention
from reprobit.strict_json import JsonValue

_REWRITING_RATIONALE = (
    "A freshly compiled private donor of the same translation unit, reordered inside "
    "declared windows whose dependence DAGs, debug records and relocations are proved."
)
MAX_WINDOW_INSTRUCTIONS = 16
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


def _window_order(pieces: list[bytes], target: bytes) -> list[int] | None:
    """A permutation of ``pieces`` whose concatenation is ``target``, if any."""

    order: list[int] = []
    used: set[int] = set()
    cursor = 0
    while cursor < len(target):
        for index, piece in enumerate(pieces):
            if index not in used and target[cursor : cursor + len(piece)] == piece:
                order.append(index)
                used.add(index)
                cursor += len(piece)
                break
        else:
            return None
    return order if len(order) == len(pieces) else None


def derive_schedule_windows(
    donor_body: bytes,
    target_body: bytes,
    spans: list[tuple[int, int]],
    relocation_offsets: frozenset[int],
) -> list[dict[str, Any]]:
    """The smallest reorder windows that turn ``donor_body`` into ``target_body``.

    Each window spans whole donor instructions, holds no relocated byte, and
    the target bytes over it are a permutation of its instructions.  A window
    grows one instruction at a time, up to ``MAX_WINDOW_INSTRUCTIONS``, until
    that holds; overlapping windows merge.
    """

    if len(donor_body) != len(target_body):
        raise DiscoveryAuthoringError("donor and reference bodies differ in length")
    differing = [
        index
        for index, pair in enumerate(zip(donor_body, target_body, strict=True))
        if pair[0] != pair[1]
    ]
    if not differing:
        raise DiscoveryAuthoringError("donor and reference bodies are already identical")
    code_end = spans[-1][0] + spans[-1][1]
    if differing[-1] >= code_end:
        raise DiscoveryAuthoringError("the reference differs after the donor's code")
    position_of = {}
    for position, (start, length) in enumerate(spans):
        for offset in range(start, start + length):
            position_of[offset] = position

    windows: list[tuple[int, int, list[int]]] = []
    pending = sorted({position_of[offset] for offset in differing})
    while pending:
        first = last = pending[0]
        # Cover a contiguous cluster of differing instructions before growing.
        while last + 1 in pending:
            last += 1
        found: tuple[int, int, list[int]] | None = None
        while last - first + 1 <= MAX_WINDOW_INSTRUCTIONS:
            start = spans[first][0]
            end = spans[last][0] + spans[last][1]
            if not relocation_offsets.intersection(range(start, end)):
                pieces = [donor_body[s : s + n] for s, n in spans[first : last + 1]]
                order = _window_order(pieces, target_body[start:end])
                if order is not None and order != list(range(len(pieces))):
                    found = (first, last, order)
                    break
            grow_left = first > 0 and (last - first) % 2 == 0
            if grow_left:
                first -= 1
            elif last + 1 < len(spans):
                last += 1
            elif first > 0:
                first -= 1
            else:
                break
        if found is None:
            raise DiscoveryAuthoringError(
                f"no reorder window of at most {MAX_WINDOW_INSTRUCTIONS} instructions reaches "
                f"the reference at donor offset {spans[pending[0]][0]}"
            )
        if windows and found[0] <= windows[-1][1]:
            raise DiscoveryAuthoringError("derived reorder windows overlap")
        windows.append(found)
        pending = [position for position in pending if position > found[1]]
    return [
        {
            "start": spans[first][0],
            "end": spans[last][0] + spans[last][1],
            "source_instruction_lengths": [length for _start, length in spans[first : last + 1]],
            "target_order": order,
        }
        for first, last, order in windows
    ]


_PUSH_R32 = range(0x50, 0x58)
_POP_R32 = range(0x58, 0x60)


def _frame_edges(body: bytes, instructions: list[dict[str, Any]]) -> set[int]:
    """Indices of the prologue (``sub esp``/register pushes) and every epilogue.

    An epilogue is the run of register pops and ``add esp, imm`` that ends in
    a ``ret``; those instructions save and restore the caller's registers, so
    a callee-saved permutation must leave them alone.
    """

    def is_esp_adjust(item: dict[str, Any]) -> bool:
        raw = body[item["offset"] : item["offset"] + item["length"]]
        return raw[:2] in (b"\x83\xec", b"\x81\xec", b"\x83\xc4", b"\x81\xc4")

    frame: set[int] = set()
    for index, item in enumerate(instructions):
        if body[item["offset"]] in _PUSH_R32 or is_esp_adjust(item):
            frame.add(index)
            continue
        break
    for index, item in enumerate(instructions):
        if item["flow"] != "ret":
            continue
        frame.add(index)
        cursor = index - 1
        while cursor >= 0 and (
            body[instructions[cursor]["offset"]] in _POP_R32 or is_esp_adjust(instructions[cursor])
        ):
            frame.add(cursor)
            cursor -= 1
    return frame


def derive_register_bijection(
    donor_body: bytes,
    target_body: bytes,
    relocations: dict[int, Any],
    code_length: int | None,
) -> dict[str, Any]:
    """A callee-saved register permutation of the body proper, or refuse.

    Both bodies must decode to the same instruction grid.  The mapping is read
    from the register fields of every instruction outside the prologue and
    the epilogues, and must be one bijection of a register set; the regions
    are the maximal runs of those instructions.
    """

    donor = decode_ia32_bijection_body(donor_body, "rewriting donor", relocations, code_length)
    target = decode_ia32_bijection_body(
        target_body, "rewriting reference", relocations, code_length
    )
    if [(item["offset"], item["length"]) for item in donor] != [
        (item["offset"], item["length"]) for item in target
    ]:
        raise DiscoveryAuthoringError("donor and reference instruction grids differ")
    frame = _frame_edges(donor_body, donor)
    mapping: dict[str, str] = {}
    for index, (left, right) in enumerate(zip(donor, target, strict=True)):
        if index in frame:
            continue
        for (left_at, left_shift), (right_at, right_shift) in zip(
            left["fields"], right["fields"], strict=False
        ):
            source = IA32_GENERAL_REGISTER_NAMES[donor_body[left_at] >> left_shift & 7]
            image = IA32_GENERAL_REGISTER_NAMES[target_body[right_at] >> right_shift & 7]
            if mapping.setdefault(source, image) != image:
                raise DiscoveryAuthoringError(
                    f"register {source} maps to two registers at donor offset {left['offset']}"
                )
    mapping = {source: image for source, image in mapping.items() if source != image}
    if not mapping or set(mapping) != set(mapping.values()):
        raise DiscoveryAuthoringError("the register differences are not one register bijection")
    regions: list[list[int]] = []
    for index, item in enumerate(donor):
        if index in frame:
            continue
        end = item["offset"] + item["length"]
        if regions and regions[-1][1] == item["offset"]:
            regions[-1][1] = end
        else:
            regions.append([item["offset"], end])
    decision: dict[str, Any] = {
        "mapping": dict(sorted(mapping.items())),
        "region_start": regions[0][0],
        "region_end": regions[-1][1],
    }
    if len(regions) > 1:
        decision["regions"] = regions
    return decision


def derive_sib_operand_swaps(
    donor_body: bytes,
    target_body: bytes,
    relocations: dict[int, Any],
    code_length: int | None,
) -> list[dict[str, Any]]:
    """The instructions whose only difference is a swapped SIB base and index."""

    donor = decode_ia32_bijection_body(donor_body, "rewriting donor", relocations, code_length)
    sites = []
    for item in donor:
        start, end = item["offset"], item["offset"] + item["length"]
        if donor_body[start:end] == target_body[start:end]:
            continue
        encoding = item["encoding"]
        sib_at = encoding["sib_at"] if encoding is not None else None
        if sib_at is None:
            raise DiscoveryAuthoringError(
                f"the instruction at {start} differs beyond its operand order"
            )
        sib = donor_body[sib_at]
        swapped = bytearray(donor_body[start:end])
        swapped[sib_at - start] = (sib & 0xC0) | (sib & 7) << 3 | (sib >> 3 & 7)
        if bytes(swapped) != target_body[start:end]:
            raise DiscoveryAuthoringError(
                f"the instruction at {start} differs beyond its operand order"
            )
        sites.append({"instruction_offset": start})
    if not sites:
        raise DiscoveryAuthoringError("donor and reference bodies are already identical")
    if (
        target_body[donor[-1]["offset"] + donor[-1]["length"] :]
        != donor_body[donor[-1]["offset"] + donor[-1]["length"] :]
    ):
        raise DiscoveryAuthoringError("the reference differs after the donor's code")
    return sites


def _window_pins(
    body: bytes,
    window: dict[str, Any],
    relocations: dict[int, Any],
    line_rows: list[tuple[int, int]],
    image_index: dict[int, int],
    context: str,
) -> dict[str, Any]:
    """Measure one window's dependence DAG, stack adjustments and line attribution."""

    start, end, order = window["start"], window["end"], list(window["target_order"])
    inside = []
    cursor = start
    for length in window["source_instruction_lengths"]:
        inside.append(decode_ia32_bijection_instruction(body, cursor, context, relocations))
        cursor += length
    stack = ia32_schedule_stack_adjustments(body, inside, order, context)
    _facts, edges = ia32_schedule_dependence_edges(inside, context, body, bool(stack))
    require_topological_instruction_order(len(inside), edges, order, context)
    attribution = [
        [offset, line, order[image_index[offset] - image_index[start]]]
        for offset, line in line_rows
        if start <= offset < end
    ]
    pins: dict[str, Any] = {
        "expected_dependence_edges": [
            [left, right, list(reasons)] for left, right, reasons in edges
        ],
        "expected_line_rows": attribution,
    }
    if stack:
        pins["stack_adjustments"] = stack
    return pins


def _moved_line_rows(
    coff: CoffObject, section: dict[str, Any], windows: list[dict[str, Any]]
) -> list[tuple[int, int]]:
    """The donor's line rows after each window's instructions move with their lines."""

    moves: dict[int, int] = {}
    for window in windows:
        starts = []
        cursor = window["start"]
        for length in window["source_instruction_lengths"]:
            starts.append(cursor)
            cursor += length
        cursor = window["start"]
        for source in window["target_order"]:
            if starts[source] != cursor:
                moves[starts[source]] = cursor
            cursor += window["source_instruction_lengths"][source]
    line_bytes = _coff_table_bytes(coff, section, "lines")
    rows = []
    for position in range(1, section["line_count"]):
        offset, line = coff_unpack("<IH", line_bytes, position * 6, "donor line row")
        rows.append((moves.get(offset, offset), line))
    return sorted(rows)


def build_donor_schedule_rewriting(
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
    """Author a donor-rewriting consumer whose reorder windows reach the reference body."""

    for name, value in (
        ("seed_object", seed_object),
        ("donor_object", donor_object),
        ("reference_object", reference_object),
    ):
        if type(value) is not bytes or not value:
            raise DiscoveryAuthoringError(f"{name} must be non-empty immutable bytes")
    context = f"discovery rewriting for {symbol}"
    try:
        seed = CoffObject(seed_object)
        donor_coff = CoffObject(donor_object)
        reference = CoffObject(reference_object)
        sp = seed.function_section(symbol)
        dp = donor_coff.function_section(symbol)
        rp = reference.function_section(symbol)
        donor_body = bytes(coff_body(donor_coff, dp))
        target_body = bytes(coff_body(reference, rp))
        rows = detailed_relocations(donor_coff, dp)
        if [(row["offset"], row["width"]) for row in rows] != [
            (row["offset"], row["width"]) for row in detailed_relocations(reference, rp)
        ]:
            raise DiscoveryAuthoringError("donor and reference relocation layouts differ")
        relocations = relocation_symbol_map(rows)
        internal_targets = internal_relocation_targets(rows, dp["number"])
        envelope = measure_instruction_schedule_debug_envelope(donor_coff, dp, context)
        code_length = envelope["procedure_range"][0]
        view_length = code_length if code_length != len(donor_body) else None
        spans, _targets = ia32_schedule_body_walk(
            donor_body, relocations, context, view_length, internal_targets
        )
        bijection: dict[str, Any] | None = None
        swaps: list[dict[str, Any]] = []
        try:
            decisions = derive_schedule_windows(
                donor_body, target_body, spans, relocated_byte_offsets(rows)
            )
        except DiscoveryAuthoringError as window_error:
            decisions = []
            try:
                bijection = derive_register_bijection(
                    donor_body, target_body, relocations, view_length
                )
            except DiscoveryAuthoringError:
                try:
                    swaps = derive_sib_operand_swaps(
                        donor_body, target_body, relocations, view_length
                    )
                except DiscoveryAuthoringError:
                    raise window_error from None
        image_spans, _ = ia32_schedule_body_walk(
            target_body, relocations, f"{context} image", view_length, internal_targets
        )
        image_index = {start: position for position, (start, _length) in enumerate(image_spans)}
        line_rows = _moved_line_rows(donor_coff, dp, decisions)
        window_pins = [
            _window_pins(
                donor_body, window, relocations, line_rows, image_index, f"{context} window {index}"
            )
            for index, window in enumerate(decisions)
        ]
        # A measured stack adjustment is part of the reordering itself.
        for window, pins in zip(decisions, window_pins, strict=True):
            if "stack_adjustments" in pins:
                window["stack_adjustments"] = pins.pop("stack_adjustments")
        instructions = decode_ia32_bijection_body(
            donor_body, f"{context} pre-image", relocations, view_length
        )
        swap_pins: list[list[int]] = []
        if swaps:
            _image, swap_proof = apply_sib_operand_swaps(
                donor_body,
                [
                    {
                        "instruction_offset": site["instruction_offset"],
                        "expected_rewritten_offsets": [
                            next(
                                item["encoding"]["sib_at"]
                                for item in instructions
                                if item["offset"] == site["instruction_offset"]
                            )
                        ],
                    }
                    for site in swaps
                ],
                relocated_byte_offsets(rows),
                f"{context} SIB swaps",
                relocations,
                view_length,
            )
            swap_pins = [[site["sib_at"]] for site in swap_proof["sites"]]
        bijection_pins: dict[str, Any] = {}
        if bijection is not None:
            _image, proof = apply_register_bijection(
                donor_body,
                bijection["mapping"],
                [tuple(pair) for pair in bijection["regions"]]
                if "regions" in bijection
                else (bijection["region_start"], bijection["region_end"]),
                relocated_byte_offsets(rows),
                f"{context} bijection",
                relocations,
                view_length,
                internal_targets,
            )
            bijection_pins = {
                "expected_rewritten_offsets": proof["rewritten_offsets"],
                "expected_region_instruction_count": proof["region_instruction_count"],
            }
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
            "expected_donor_length": dp["raw_size"],
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
            "expected_body_sha256": sha256_bytes(target_body),
            "expected_linked_span": (dp["raw_size"] + 15) // 16 * 16,
            "retail_oracle": {"length": len(target_body)},
            "retail_relocations": [
                {field: row[field] for field in _RELOCATION_FIELDS} for row in rows
            ],
            "donor_rewriting.expected_changed_offsets": [
                index
                for index, pair in enumerate(zip(donor_body, target_body, strict=True))
                if pair[0] != pair[1]
            ],
            "donor_rewriting.expected_external_entries": sorted(
                relational_form_external_entries(donor_coff, dp, f"{context} external entries")
            ),
            "donor_rewriting.expected_instruction_count": len(instructions),
            "donor_rewriting.expected_procedure_range": envelope["procedure_range"],
            "donor_rewriting.expected_code_symbol_references": envelope["code_symbol_references"],
        }
        if extras:
            expected["expected_donor_extra_functions"] = extras
        if dp["number"] != sp["number"]:
            expected["expected_donor_section_number"] = dp["number"]
        if len(donor_coff.sections) != len(seed.sections):
            expected["expected_donor_section_count"] = len(donor_coff.sections)
        if view_length is not None:
            expected["donor_rewriting.expected_code_length"] = view_length
        for index, pins in enumerate(window_pins):
            for key, value in pins.items():
                expected[f"donor_rewriting.windows[{index}].{key}"] = value
        for key, value in bijection_pins.items():
            expected[f"donor_rewriting.register_bijections[0].{key}"] = value
        for position, rewritten_bytes in enumerate(swap_pins):
            pin = f"donor_rewriting.sib_operand_swaps[{position}].expected_rewritten_offsets"
            expected[pin] = rewritten_bytes

        scope = Scope(target=target_id, translation_unit=translation_unit_id, function=symbol)
        family = ClassicRecipeFamily.RETAIL_EXACT_DONOR_REWRITING
        parameters = (
            ClassicField(
                name="donor_rewriting",
                value=cast(
                    JsonValue,
                    {
                        "kind": DONOR_REWRITING_KIND,
                        "windows": decisions,
                        **({"register_bijections": [bijection]} if bijection else {}),
                        **({"sib_operand_swaps": swaps} if swaps else {}),
                    },
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
            rationale=_REWRITING_RATIONALE,
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
        if bytes(coff_body(composed, composed.function_section(symbol))) != target_body:
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
        raise DiscoveryAuthoringError(f"cannot author donor rewriting: {exc}") from exc


__all__ = ["build_donor_schedule_rewriting", "derive_schedule_windows"]
