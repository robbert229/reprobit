"""Tests for `retail_exact_region_resize_rewriting` and its path simulator.

The fixture is the re-encoding suite's complete classic-i386 COMDAT with an
FPO closure, carrying a body in which the donor keeps a loaded value in a
register while the reference reloads it from memory:

     0: 53 56 57 55        push ebx / esi / edi / ebp   <- FPO prologue
     4: 8b 1d <D32>        mov  ebx, [_Nil]
    10: 85 db              test ebx, ebx
    12: 74 0c              je   26              <- crosses the region; repaired
    14: 8b 43 04           mov  eax, [ebx+4]    <- region [14, 26)
    17: 8b c8              mov  ecx, eax
    19: 89 4b 08           mov  [ebx+8], ecx
    22: 8b d0              mov  edx, eax        <- the donor keeps the value
    24: 89 13              mov  [ebx], edx
    26: 8b 0d <D32>        mov  ecx, [_Nil]     <- its relocation is reseated
    32: 5d 5f 5e 5b        pop  ebp / edi / esi / ebx
    36: c3                 ret

The reference's region is one byte shorter:

    14: 8b 43 04           mov  eax, [ebx+4]
    17: 89 43 08           mov  [ebx+8], eax
    20: 8b 4b 04           mov  ecx, [ebx+4]    <- reloaded past a disjoint store
    23: 89 0b              mov  [ebx], ecx
"""

from __future__ import annotations

import json
import struct

import pytest
from test_classic_register_bijection_reencoding_full import (
    NIL_SYMBOL,
    TARGET_SYMBOL,
    codeview_stream,
    make_coff,
)

from reprobit.binary import ByteIdentityError
from reprobit.classic.region_simulation import (
    address_relation,
    condition,
    lin,
    lin_atom,
    simulate_region,
    stores_equivalent,
)
from reprobit.classic.rewriting_region_resize import (
    REGION_RESIZE_CLASS,
    apply_region_resize,
    produce_region_resize_rewriting_candidate,
)
from reprobit.classic_donors import merge_candidate_constraints
from reprobit.classic_project import ClassicDispatchMaterials, ClassicFamilyDispatcher
from reprobit.coff_format import CoffObject, coff_body, detailed_relocations
from reprobit.discovery_authoring import DiscoveryAuthoringError, build_extern_run_donor
from reprobit.discovery_region_resize import build_region_resize_rewriting
from reprobit.intervention_metadata import ClassicRecipeFamily
from reprobit.msvc_discovery_coff import qualify_msvc_reference_object
from reprobit.schema import ClassicRecipeIntervention

UNIT = "tu.fixture"
PROLOGUE = "535657558b1d0000000085db"
EPILOGUE = "8b0d000000005d5f5e5bc3"
DONOR_REGION = "8b43048bc8894b088bd08913"
REFERENCE_REGION = ["8b4304", "894308", "8b4b04", "890b"]
DONOR = bytes.fromhex(PROLOGUE + "740c" + DONOR_REGION + EPILOGUE)
REFERENCE = bytes.fromhex(PROLOGUE + "740b" + "".join(REFERENCE_REGION) + EPILOGUE)
DONOR_RELOCATIONS = (6, 28)
REFERENCE_RELOCATIONS = (6, 27)
DONOR_LINES = ((4, 11), (14, 12), (22, 13), (26, 14))
REFERENCE_LINES = ((4, 11), (14, 12), (14, 13), (25, 14))
REGION = {
    "region_start": 14,
    "region_end": 26,
    "replacement_instructions": list(REFERENCE_REGION),
    "replacement_relocations": [],
}


def _rows(offsets=DONOR_RELOCATIONS):
    return [
        {
            "offset": offset,
            "width": 4,
            "type": 6,
            "target": NIL_SYMBOL,
            "target_section": 0,
            "target_value": 0,
            "addend": 0,
        }
        for offset in offsets
    ]


def _apply(body=DONOR, regions=None, rows=None):
    return apply_region_resize(
        body,
        [dict(item) for item in (regions or [REGION])],
        _rows() if rows is None else rows,
        1,
        "fixture",
        prologue_length=4,
    )


def _region(**changes):
    return {**REGION, **changes}


def _donor_coff():
    return make_coff(
        body=DONOR,
        relocations=DONOR_RELOCATIONS,
        lines=DONOR_LINES,
        debug_stream=codeview_stream(len(DONOR), 4, 32),
    )


def _reference_coff(body=REFERENCE, relocations=REFERENCE_RELOCATIONS):
    return make_coff(
        body=body,
        relocations=relocations,
        lines=REFERENCE_LINES,
        debug_stream=codeview_stream(len(body), 4, 31),
    )


def _extern_donor():
    return build_extern_run_donor(
        target_id="program",
        translation_unit_id=UNIT,
        build_target="program",
        header_prefix="ReproBitPad",
        header_count=1,
        seat_prefix="ReproBitPadSeat",
        seat_count=0,
        width=3,
        beneficiary_symbols=(TARGET_SYMBOL,),
    )


def _author(reference=None):
    seed = _donor_coff()
    return build_region_resize_rewriting(
        donor=_extern_donor(),
        target_id="program",
        translation_unit_id=UNIT,
        build_target="program",
        symbol=TARGET_SYMBOL,
        seed_object=seed,
        donor_object=seed,
        reference_object=_reference_coff() if reference is None else reference,
    )


# --- the simulator's term model ---------------------------------------------------


def test_linear_forms_are_a_normal_form() -> None:
    x = lin_atom(("reg0", "eax"))
    assert lin(0, [(x[2][0][0], 3)]) == lin(0, [(x[2][0][0], 1), (x[2][0][0], 2)])
    assert lin(5, [(("reg0", "ecx"), 0)]) == lin(5)
    assert lin(-1) == lin(0xFFFFFFFF)


def test_address_relations_are_decided_on_the_ring() -> None:
    base = lin_atom(("reg0", "ebx"))
    other = lin_atom(("reg0", "esi"))

    def at(value, disp):
        return lin(value[1] + disp, value[2])

    assert address_relation(at(base, 4), 4, at(base, 4), 4) == "same"
    assert address_relation(at(base, 4), 4, at(base, 8), 4) == "disjoint"
    assert address_relation(at(base, 4), 4, at(base, 6), 4) == "unknown"
    assert address_relation(at(base, 4), 4, at(base, 4), 2) == "unknown"
    assert address_relation(at(base, 0), 4, at(other, 0), 4) == "unknown"


def test_compare_conditions_are_canonical_across_operand_order() -> None:
    a, b = lin_atom(("reg0", "ecx")), lin_atom(("reg0", "eax"))

    def flags(left, right):
        return {
            name: ("flag", name, "sub", 32, left, right)
            for name in ("cf", "pf", "af", "zf", "sf", "of")
        }

    # cmp ecx, eax; ja   ==   cmp eax, ecx; jb
    assert condition(7, flags(a, b)) == condition(2, flags(b, a))
    # cmp ecx, eax; jae  ==   cmp eax, ecx; jbe
    assert condition(3, flags(a, b)) == condition(6, flags(b, a))
    # je is symmetric
    assert condition(4, flags(a, b)) == condition(4, flags(b, a))


def test_test_and_compare_with_zero_read_the_same_condition() -> None:
    value = lin_atom(("reg0", "eax"))
    logic = {name: ("flag", name, "logic", 32, "result", value) for name in ("zf", "sf", "pf")}
    logic |= {"cf": ("fconst", "cf", 0), "of": ("fconst", "of", 0), "af": ("undef", "af", "t", 1)}
    compare = {
        name: ("flag", name, "sub", 32, value, lin(0))
        for name in ("cf", "pf", "af", "zf", "sf", "of")
    }
    assert condition(4, logic) == condition(4, compare)
    assert condition(2, logic) is False


def test_a_reload_past_a_disjoint_store_reads_the_first_load() -> None:
    code = bytes.fromhex("8b43048943088b4b04")
    (path,) = simulate_region(code, 0, len(code), {}, "t", "test")
    assert path.regs["eax"] == path.regs["ecx"]


@pytest.mark.parametrize(
    ("store", "why"),
    [("894306", "a partially overlapping store"), ("894608", "a store through another pointer")],
)
def test_a_reload_past_a_possibly_aliasing_store_is_a_new_value(store: str, why: str) -> None:
    code = bytes.fromhex("8b4304" + store + "8b4b04")
    (path,) = simulate_region(code, 0, len(code), {}, "t", why)
    assert path.regs["eax"] != path.regs["ecx"]


def test_a_store_swap_needs_provably_disjoint_stores() -> None:
    a = (lin(4, [(("reg0", "ebx"), 1)]), 4, lin(1))
    b = (lin(8, [(("reg0", "ebx"), 1)]), 4, lin(2))
    c = (lin(0, [(("reg0", "esi"), 1)]), 4, lin(3))
    assert stores_equivalent((a, b), (b, a)) is None
    assert stores_equivalent((a, c), (c, a)) is not None
    assert stores_equivalent((a,), (b,)) is not None


@pytest.mark.parametrize(
    "encoding",
    ["e800000000", "c3", "f6f1", "d9c0", "ff10", "f3a4", "648b00", "1bc0"],
)
def test_instructions_outside_the_closed_set_are_refused(encoding: str) -> None:
    code = bytes.fromhex(encoding)
    with pytest.raises(ByteIdentityError):
        simulate_region(code, 0, len(code), {}, "t", "closed set")


def test_a_backward_branch_is_refused() -> None:
    code = bytes.fromhex("85c075fc")
    with pytest.raises(ByteIdentityError, match="forward"):
        simulate_region(code, 0, len(code), {}, "t", "backward")


# --- the primitive ------------------------------------------------------------------


def test_a_reload_replacing_a_held_register_is_proved_and_relaid() -> None:
    image, proof = _apply()
    assert image == REFERENCE
    assert proof["growth"] == -1
    assert proof["branch_repairs"] == [12]
    assert proof["relocation_reseat"] == [[28, 27]]
    (region,) = proof["regions"]
    assert region["path_pairs"] == 1
    assert region["compared_registers"] == ["eax"]
    assert proof["offset_map"][26] == 25 and proof["offset_map"][14] == 14


def test_a_store_that_differs_is_refused() -> None:
    changed = _region(replacement_instructions=["8b4304", "89430c", "8b4b04", "890b"])
    with pytest.raises(ByteIdentityError, match="different memory"):
        _apply(regions=[changed])


def test_a_live_register_that_differs_is_refused() -> None:
    changed = _region(replacement_instructions=["8b4b04", "894b08", "890b"])
    with pytest.raises(ByteIdentityError, match="eax is live at the exit"):
        _apply(regions=[changed])


def test_a_callee_saved_register_clobbered_by_the_replacement_is_refused() -> None:
    # 0: push ebx; 1: mov ebx, [_Nil]; 7: mov eax, [ebx+4]; 10: mov ecx, eax;
    # 12: pop ebx; 13: ret -- the function never saves ESI, so ESI is live at
    # its return and a replacement that writes it is refused.
    body = bytes.fromhex("538b1d000000008b43048bc85bc3")
    region = _region(region_start=7, region_end=12, replacement_instructions=["8b4304", "8bf0"])
    with pytest.raises(ByteIdentityError, match="esi is live at the exit"):
        _apply(body=body, regions=[region], rows=_rows((3,)))
    popped = _region(region_start=7, region_end=12, replacement_instructions=["8b4304", "8bd8"])
    image, _proof = _apply(body=body, regions=[popped], rows=_rows((3,)))
    assert image[10:12] == bytes.fromhex("8bd8")


def test_a_branch_into_the_region_is_refused() -> None:
    body = bytearray(DONOR)
    body[13] = 19 - 14
    assert body[12] == 0x74
    with pytest.raises(ByteIdentityError, match="targets the region interior"):
        _apply(body=bytes(body))


def test_a_flag_live_at_the_exit_must_be_equal() -> None:
    body = bytes.fromhex(PROLOGUE + "740e" + "8b43048bc8894b0885c074028913" + EPILOGUE)
    region = _region(region_end=24, replacement_instructions=["8b4304", "894308", "85db"])
    with pytest.raises(ByteIdentityError, match="flag zf is live"):
        _apply(body=body, regions=[region], rows=_rows((6, 30)))


def test_an_entry_read_into_a_value_nothing_compares_is_admitted() -> None:
    changed = _region(replacement_instructions=["8bc2", *REFERENCE_REGION])
    image, _proof = _apply(regions=[changed])
    assert len(image) == len(REFERENCE) + 2


def test_an_entry_value_dead_in_both_liveness_sets_is_refused(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import reprobit.classic.rewriting_region_resize as module

    real = module._register_bijection_live_sets

    def blind(instructions, context):
        live, successors = real(instructions, context)
        return [frozenset(atoms - module._IA32_ATOMS_OF["ebx"]) for atoms in live], successors

    # A liveness that (wrongly) calls ebx dead must not let the symbolic
    # entry state stand for it: the region's results depend on ebx.
    monkeypatch.setattr(module, "_register_bijection_live_sets", blind)
    with pytest.raises(ByteIdentityError, match="entry value of ebx is read"):
        _apply()


def test_relocated_fields_pair_in_order_with_the_donor_and_keep_their_symbol() -> None:
    body = bytes.fromhex(PROLOGUE + "740b" + "8b43048bc88b0d00000000" + "5d5f5e5bc3")
    rows = _rows((6, 21))
    region = _region(
        region_end=25,
        replacement_instructions=["8b4304", "8b0d00000000"],
        replacement_relocations=[[5, 21]],
    )
    image, proof = _apply(body=body, regions=[region], rows=rows)
    assert proof["relocation_reseat"] == [[21, 19]]
    unpaired = {**region, "replacement_relocations": []}
    with pytest.raises(ByteIdentityError, match="not the region's"):
        _apply(body=body, regions=[unpaired], rows=rows)
    retargeted = {**region, "replacement_instructions": ["8b4304", "8b0d04000000"]}
    with pytest.raises(ByteIdentityError, match="access different memory"):
        _apply(body=body, regions=[retargeted], rows=rows)
    misplaced = {**region, "replacement_relocations": [[4, 21]]}
    with pytest.raises(ByteIdentityError):
        _apply(body=body, regions=[misplaced], rows=rows)
    assert image[19:23] == b"\0\0\0\0"


def test_a_short_branch_across_a_grown_region_that_no_longer_fits_is_refused() -> None:
    filler = "90" * 110
    body = bytes.fromhex(PROLOGUE + "747a" + DONOR_REGION + filler + EPILOGUE)
    rows = _rows((6, 26 + 110 + 2))
    grown = _region(
        replacement_instructions=[*REFERENCE_REGION, "90", "90", "90", "90", "90", "90"]
    )
    image, proof = _apply(body=body, regions=[grown], rows=rows)
    assert image[13] == 0x7A + 5 and proof["branch_repairs"] == [12]
    too_far = _region(replacement_instructions=[*REFERENCE_REGION, *["90"] * 8])
    with pytest.raises(ByteIdentityError, match="no longer reaches its target in 1"):
        _apply(body=body, regions=[too_far], rows=rows)


def test_a_backward_branch_across_the_region_is_repaired() -> None:
    # 26: dec eax; 27: jne 14 (back to the region start); 29: the epilogue
    body = bytes.fromhex(PROLOGUE + "740f" + DONOR_REGION + "4875f1" + EPILOGUE)
    rows = _rows((6, 31))
    image, proof = _apply(body=body, rows=rows)
    assert proof["branch_repairs"] == [12, 26]
    assert image[13] == 0x0E and image[27] == 0xF2


def test_a_diamond_with_mirrored_arms_is_proved_per_path() -> None:
    # donor:       cmp ecx, eax; ja L; mov edx, ecx; jmp E; L: mov edx, eax; E:
    # replacement: cmp eax, ecx; jb L'; mov edx, eax; jmp E'; L': mov edx, ecx; E':
    donor = bytes.fromhex("3bc877048bd1eb028bd0")
    replacement = bytes.fromhex("3bc172048bd1eb028bd0")
    left = simulate_region(donor, 0, len(donor), {}, "donor", "diamond")
    right = simulate_region(replacement, 0, len(replacement), {}, "replacement", "diamond")
    from reprobit.classic.region_simulation import contradictory

    pairs = [(a, b) for a in left for b in right if not contradictory(a.conditions, b.conditions)]
    assert len(left) == len(right) == 2 and len(pairs) == 2
    assert all(a.regs["edx"] == b.regs["edx"] for a, b in pairs)


# --- the candidate producer and discovery ----------------------------------------


def test_the_authored_record_composes_the_reference_body() -> None:
    authored = _author()
    intervention = authored.function.intervention
    assert intervention.family is ClassicRecipeFamily.RETAIL_EXACT_REGION_RESIZE_REWRITING
    assert intervention.dependencies == (authored.donor.intervention.id,)
    composed = CoffObject(authored.candidate_object)
    primary = composed.function_section(TARGET_SYMBOL)
    assert bytes(coff_body(composed, primary)) == REFERENCE
    assert [row["offset"] for row in detailed_relocations(composed, primary)] == [6, 27]
    values = authored.function.receipt.expected_values
    assert values["region_resize.expected_growth"] == -1
    assert values["region_resize.expected_collapsed_line_rows"] == 1
    assert values["expected_linked_span"] == 48


def test_the_record_round_trips_through_its_schema_and_the_build_dispatcher() -> None:
    authored = _author()
    seed = _donor_coff()
    intervention = ClassicRecipeIntervention.model_validate_json(
        authored.function.intervention.model_dump_json()
    )
    assert intervention == authored.function.intervention
    constraints = merge_candidate_constraints(intervention, authored.function.receipt).materialize()
    candidate = ClassicFamilyDispatcher().dispatch(
        intervention,
        ClassicDispatchMaterials(
            seed_object=seed, donor_object=seed, candidate_constraints=constraints
        ),
    )
    assert candidate.output == authored.candidate_object
    qualify_msvc_reference_object(
        reference_object=_reference_coff(),
        candidate_object=candidate.output,
        symbol=TARGET_SYMBOL,
    )


def test_a_tampered_replacement_is_refused_by_the_producer() -> None:
    authored = _author()
    seed = _donor_coff()
    constraints = merge_candidate_constraints(
        authored.function.intervention, authored.function.receipt
    ).materialize()
    function = json.loads(json.dumps(constraints))
    function.setdefault("splice_class", REGION_RESIZE_CLASS)
    function.setdefault("mangled", TARGET_SYMBOL)
    produce_region_resize_rewriting_candidate(seed, seed, json.loads(json.dumps(function)))
    region = function["region_resize"]["regions"][0]
    region["replacement_instructions"][1] = "89430c"
    with pytest.raises(ByteIdentityError, match="different memory"):
        produce_region_resize_rewriting_candidate(seed, seed, function)
    assert function["splice_class"] == REGION_RESIZE_CLASS


def test_a_reference_no_replacement_proves_authors_nothing() -> None:
    body = bytes.fromhex(PROLOGUE + "740b" + "8b430489430c8b4b04890b" + EPILOGUE)
    with pytest.raises(DiscoveryAuthoringError, match="no region replacement reaches"):
        _author(reference=_reference_coff(body=body))


def test_the_family_costs_at_least_a_donor_rewriting() -> None:
    from reprobit.intervention_metadata import CLASSIC_RECIPE_METADATA

    resize = CLASSIC_RECIPE_METADATA[ClassicRecipeFamily.RETAIL_EXACT_REGION_RESIZE_REWRITING]
    rewriting = CLASSIC_RECIPE_METADATA[ClassicRecipeFamily.RETAIL_EXACT_DONOR_REWRITING]
    from reprobit.costs import CostModel

    assert CostModel.weights[resize.cost_class] >= CostModel.weights[rewriting.cost_class]


def test_fixture_shapes_are_what_the_docstring_says() -> None:
    assert len(DONOR) == 37 and len(REFERENCE) == 36
    assert struct.unpack_from("<b", REFERENCE, 13)[0] == 25 - 14


def test_grind_falls_back_to_a_region_resize_when_no_reordering_reaches(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from types import SimpleNamespace

    import reprobit.discovery_grind as grind
    from reprobit.discovery_project import DeclarationFamily

    calls: list[str] = []

    def refuse(name: str):
        def builder(**_kwargs):
            calls.append(name)
            raise DiscoveryAuthoringError(f"{name} refused")

        return builder

    def resized(**kwargs):
        calls.append("region_resize")
        return kwargs["reference_object"]

    monkeypatch.setattr(grind, "build_donor_schedule_rewriting", refuse("reorder"))
    monkeypatch.setattr(grind, "build_region_resize_rewriting", resized)
    monkeypatch.setattr(grind, "_require_grind_family", lambda _state: None)
    monkeypatch.setattr(
        grind,
        "_extern_run",
        lambda _state: SimpleNamespace(
            header_prefix="ReproBitPad",
            header_count=3,
            seat_prefix="ReproBitPadSeat",
            seat_count=0,
            width=3,
        ),
    )
    monkeypatch.setattr(grind, "_header_placement", lambda _context: "after_includes")
    state = SimpleNamespace(family=DeclarationFamily.EXTERN_RUN_PAIR)
    context = SimpleNamespace(
        unit=SimpleNamespace(target_id="program", id=UNIT, build_target="program"),
        symbol=TARGET_SYMBOL,
    )
    authored = grind._state_rewriting(
        state, context, seed_object=b"s", donor_object=b"d", reference_object=b"r"
    )
    assert authored == b"r" and calls == ["reorder", "region_resize"]
    monkeypatch.setattr(grind, "build_region_resize_rewriting", refuse("region_resize"))
    with pytest.raises(DiscoveryAuthoringError, match="reorder refused"):
        grind._state_rewriting(
            state, context, seed_object=b"s", donor_object=b"d", reference_object=b"r"
        )


def test_an_unrelocated_relative_call_is_refused_before_any_layout() -> None:
    # 26: call 32 (a label of this body, no relocation) ... the shift would retarget it.
    body = bytes.fromhex(PROLOGUE + "7411" + DONOR_REGION + "e800000000" + EPILOGUE)
    with pytest.raises(ByteIdentityError, match="relative call at 26 has no relocation"):
        _apply(body=body, rows=_rows((6, 33)))


def test_a_run_past_the_last_donor_instruction_is_labelled_by_the_code_end() -> None:
    # The reference appends an instruction after the donor's last one; the
    # search must refuse cleanly rather than index past the donor's code.
    reference = _reference_coff(body=REFERENCE + bytes.fromhex("90"))
    with pytest.raises(DiscoveryAuthoringError):
        _author(reference=reference)
