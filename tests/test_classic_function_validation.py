"""Tests for `retail_exact_function_translation_validation` (whole-function translation validation).

The programs are hand-encoded IA-32 (each listing is in the comment above
it).  The proof engine is exercised directly through `prove_function`; the
record, its producer and grind's authoring through the re-encoding suite's
COFF fixture.
"""

from __future__ import annotations

import json

import pytest
from test_classic_register_bijection_reencoding_full import (
    TARGET_SYMBOL,
    codeview_stream,
    make_coff,
)

from reprobit.binary import ByteIdentityError
from reprobit.classic.function_validation import (
    FUNCTION_VALIDATION_CLASS,
    FrameFacts,
    Program,
    produce_function_validation_candidate,
    prove_function,
)
from reprobit.classic_donors import merge_candidate_constraints
from reprobit.classic_project import ClassicDispatchMaterials, ClassicFamilyDispatcher
from reprobit.coff_format import CoffObject, coff_body
from reprobit.discovery_authoring import DiscoveryAuthoringError, build_extern_run_donor
from reprobit.discovery_function_validation import build_function_validation_rewriting
from reprobit.intervention_metadata import CLASSIC_RECIPE_METADATA, ClassicRecipeFamily
from reprobit.schema import ClassicRecipeIntervention

UNIT = "tu.fixture"


def _code(text: str) -> bytes:
    return bytes.fromhex(text.replace(" ", ""))


# 0: mov ecx,[esp+4] / 4: xor eax,eax / 6: test ecx,ecx / 8: jle 15
# 10: add eax,ecx / 12: dec ecx / 13: jne 10 / 15: ret
SUM_D = _code("8b4c2404 33c0 85c9 7e05 03c1 49 75fb c3")
# The same loop with the counter in EDX instead of ECX.
SUM_P = _code("8b542404 33c0 85d2 7e05 03c2 4a 75fb c3")
# ... with jl in place of jle (a changed branch condition).
SUM_P_JL = _code("8b542404 33c0 85d2 7c05 03c2 4a 75fb c3")
# ... returning the counter (15: mov eax,edx / 17: ret).
SUM_P_EDX = _code("8b542404 33c0 85d2 7e05 03c2 4a 75fb 8bc2 c3")
# 0: xor eax,eax / 2: inc eax / 3: cmp eax,3 / 6: jl 2 / 8: ret
COUNT_D = _code("33c0 40 83f803 7cfa c3")
# 0: mov eax,3 / 5: ret (the same value, without the loop)
COUNT_P = _code("b803000000 c3")
# 0: mov ecx,[esp+4] / 4: mov edx,[esp+8] / 8: mov eax,[ecx] / 10: mov dword [edx],0 / 16: ret
ALIAS_D = _code("8b4c2404 8b542408 8b01 c70200000000 c3")
# The load after the store, which may alias it.
ALIAS_P = _code("8b4c2404 8b542408 c70200000000 8b01 c3")
# 0: sub esp,4 / 3: push esi / 4: mov esi,[esp+0xc] / 8: push 0 / 10: call _f
# 15: add esp,4 / 18: add eax,esi / 20: pop esi / 21: add esp,4 / 24: ret
SPILL_D = _code("83ec04 56 8b74240c 6a00 e800000000 83c404 03c6 5e 83c404 c3")
# The parameter spilled to the local slot ESP0-4 across the call instead:
# 4: mov eax,[esp+0xc] / 8: mov [esp+4],eax / 12: push 0 / 14: call _f
# 19: add esp,4 / 22: add eax,[esp+4] / 26: pop esi / 27: add esp,4 / 30: ret
SPILL_P = _code("83ec04 56 8b44240c 89442404 6a00 e800000000 83c404 03442404 5e 83c404 c3")
# ... with 26: lea ecx,[esp+4] (the slot's address taken, though never used).
SPILL_P_LEA = _code(
    "83ec04 56 8b44240c 89442404 6a00 e800000000 83c404 03442404 8d4c2404 5e 83c404 c3"
)
# ... passing 1 instead of 0.
SPILL_P_ARG = _code("83ec04 56 8b44240c 89442404 6a01 e800000000 83c404 03442404 5e 83c404 c3")
SPILL_FRAME = FrameFacts(True, base=-4, params_end=8)
# 0: mov ecx,[esp+4] / 4: mov edx,[esp+8] / 8: xor eax,eax / 10: test ecx,ecx / 12: jle 22
# 14: add eax,[edx] / 16: add edx,4 / 19: dec ecx / 20: jne 14 / 22: ret
ARRAY_D = _code("8b4c2404 8b542408 33c0 85c9 7e08 0302 83c204 49 75f8 c3")
# The body reordered: 14: add edx,4 / 17: add eax,[edx-4] / 20: dec ecx / 21: jne 14 / 23: ret
ARRAY_P = _code("8b4c2404 8b542408 33c0 85c9 7e09 83c204 0342fc 49 75f7 c3")
# 0: mov ecx,[esp+4] / 4: mov edx,[esp+8] / 8: fldz / 10: test ecx,ecx / 12: jle 22
# 14: fadd dword [edx] / 16: add edx,4 / 19: dec ecx / 20: jne 14 / 22: ret
FSUM_D = _code("8b4c2404 8b542408 d9ee 85c9 7e08 d802 83c204 49 75f8 c3")
# Counter and pointer in each other's registers.
FSUM_P = _code("8b542404 8b4c2408 d9ee 85d2 7e08 d801 83c104 4a 75f8 c3")


def _prove(donor, image, *, donor_relocations=None, image_relocations=None, frame=None):
    return prove_function(
        donor,
        donor_relocations or {},
        image,
        image_relocations or {},
        {},
        "fixture",
        private_frame=frame,
    )


def _spill(image, image_call=15):
    return _prove(
        SPILL_D,
        image,
        donor_relocations={11: ("rel32", "_f")},
        image_relocations={image_call: ("rel32", "_f")},
        frame=SPILL_FRAME,
    )


# --- the proof engine ------------------------------------------------------------------


def test_the_same_loop_under_another_register_allocation_is_proved() -> None:
    proof = _prove(SUM_D, SUM_P)
    assert proof.pairs == {0: 0, 10: 10}
    relation = proof.relations[(10, 10)]
    together = [cls.members for cls in relation.classes if ("D", ("r", "ecx")) in cls.members]
    assert together and ("P", ("r", "edx")) in together[0]
    assert proof.returns == 2


def test_a_value_spilled_on_one_side_and_kept_in_a_register_on_the_other_is_proved() -> None:
    proof = _spill(SPILL_P)
    assert proof.frame.private
    assert proof.returns == 1


def test_a_loop_with_a_reordered_body_is_proved() -> None:
    proof = _prove(ARRAY_D, ARRAY_P)
    assert proof.pairs == {0: 0, 14: 14}


def test_an_x87_loop_is_proved_with_its_stack_related() -> None:
    proof = _prove(FSUM_D, FSUM_P)
    relation = proof.relations[(14, 14)]
    assert relation.donor.x87 == relation.image.x87 == ("depth", 1)
    assert any({("D", ("st", 0)), ("P", ("st", 0))} <= cls.members for cls in relation.classes)


def test_different_control_flow_graphs_are_refused() -> None:
    with pytest.raises(ByteIdentityError, match="returns where the other reaches a join"):
        _prove(COUNT_D, COUNT_P)


def test_a_reload_past_a_possibly_aliasing_store_is_refused() -> None:
    with pytest.raises(ByteIdentityError, match="eax differs at the return"):
        _prove(ALIAS_D, ALIAS_P)


def test_a_changed_branch_condition_is_refused() -> None:
    with pytest.raises(ByteIdentityError):
        _prove(SUM_D, SUM_P_JL)


def test_a_live_out_difference_at_a_return_is_refused() -> None:
    with pytest.raises(ByteIdentityError, match="eax differs at the return"):
        _prove(SUM_D, SUM_P_EDX)


def test_an_address_taken_slot_takes_the_shared_frame_and_the_spill_is_refused() -> None:
    with pytest.raises(ByteIdentityError, match="shared frame"):
        _spill(SPILL_P_LEA)


def test_a_call_with_another_argument_is_refused() -> None:
    with pytest.raises(ByteIdentityError, match="different calls"):
        _spill(SPILL_P_ARG)


def test_without_a_private_frame_the_spill_is_refused() -> None:
    with pytest.raises(ByteIdentityError, match="shared frame"):
        _prove(
            SPILL_D,
            SPILL_P,
            donor_relocations={11: ("rel32", "_f")},
            image_relocations={15: ("rel32", "_f")},
        )


def test_an_unread_relocated_field_is_refused() -> None:
    with pytest.raises(ByteIdentityError, match="not read on any path"):
        _prove(SUM_D, SUM_P, image_relocations={0: "_g"})


def test_cut_points_are_joins_and_loop_headers_but_not_returning_tails() -> None:
    assert Program(SUM_D, {}, "D", "fixture").cuts == frozenset({0, 10})
    assert Program(COUNT_D, {}, "D", "fixture").cuts == frozenset({0, 2})


def test_an_indirect_jump_is_refused() -> None:
    with pytest.raises(ByteIdentityError, match="indirect jump"):
        Program(_code("ffe0"), {}, "D", "fixture")


# 0: mov edi,[esp+4] / 4: xor eax,eax / 6: mov ecx,3 / 11: rep stosd / 13: ret
MEMSET_D = _code("8b7c2404 33c0 b903000000 f3ab c3")
# The same three stores written out: 6: mov [edi],eax / 8: mov [edi+4],eax
# 11: mov [edi+8],eax / 14: add edi,12 / 17: xor ecx,ecx / 19: ret
MEMSET_P = _code("8b7c2404 33c0 8907 894704 894708 83c70c 33c9 c3")
# 0: mov edi,[esp+4] / 4: mov ecx,[esp+8] / 8: xor eax,eax / 10: rep stosd / 12: ret
MEMSET_VARIABLE = _code("8b7c2404 8b4c2408 33c0 f3ab c3")
# 0: mov edi,[esp+4] / 4: or ecx,-1 / 7: xor eax,eax / 9: repne scasb / 11: not ecx
# 13: dec ecx / 14: mov eax,ecx / 16: ret
STRLEN_D = _code("8b7c2404 83c9ff 33c0 f2ae f7d1 49 8bc1 c3")
# ... 13: lea eax,[ecx-1] / 16: ret
STRLEN_P = _code("8b7c2404 83c9ff 33c0 f2ae f7d1 8d41ff c3")


def test_a_constant_rep_stos_is_its_stores() -> None:
    assert _prove(MEMSET_D, MEMSET_P).returns == 1


def test_a_rep_stos_of_unknown_count_is_refused() -> None:
    with pytest.raises(ByteIdentityError, match="count is not a constant"):
        _prove(MEMSET_VARIABLE, MEMSET_VARIABLE)


def test_an_inline_strlen_is_one_scan_on_both_sides() -> None:
    assert _prove(STRLEN_D, STRLEN_P).returns == 1


def test_a_string_instruction_stays_outside_the_region_simulator() -> None:
    from reprobit.classic.region_simulation import simulate_region

    with pytest.raises(ByteIdentityError, match="prefixed instruction"):
        simulate_region(MEMSET_D, 0, 13, {}, "donor", "fixture")


# --- the record, its producer and grind ----------------------------------------------


def _coff(body):
    return make_coff(
        body=body,
        relocations=(),
        lines=((0, 10), (10, 11)),
        debug_stream=codeview_stream(len(body), 0, len(body) - 1),
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


def _author(reference_body=SUM_P):
    seed = _coff(SUM_D)
    return build_function_validation_rewriting(
        donor=_extern_donor(),
        target_id="program",
        translation_unit_id=UNIT,
        build_target="program",
        symbol=TARGET_SYMBOL,
        seed_object=seed,
        donor_object=seed,
        reference_object=_coff(reference_body),
    )


def test_the_authored_record_composes_the_reference_body() -> None:
    authored = _author()
    intervention = authored.function.intervention
    assert intervention.family is ClassicRecipeFamily.RETAIL_EXACT_FUNCTION_TRANSLATION_VALIDATION
    composed = CoffObject(authored.candidate_object)
    assert bytes(coff_body(composed, composed.function_section(TARGET_SYMBOL))) == SUM_P
    proof = authored.function.receipt.expected_values["function_validation.expected_proof"]
    assert proof["cut_pairs"] == [[0, 0], [10, 10]]


def test_the_record_round_trips_through_its_schema_and_the_build_dispatcher() -> None:
    authored = _author()
    seed = _coff(SUM_D)
    intervention = ClassicRecipeIntervention.model_validate_json(
        authored.function.intervention.model_dump_json()
    )
    constraints = merge_candidate_constraints(intervention, authored.function.receipt).materialize()
    candidate = ClassicFamilyDispatcher().dispatch(
        intervention,
        ClassicDispatchMaterials(
            seed_object=seed, donor_object=seed, candidate_constraints=constraints
        ),
    )
    assert candidate.output == authored.candidate_object


def test_a_tampered_replacement_is_refused_by_the_producer() -> None:
    authored = _author()
    seed = _coff(SUM_D)
    function = json.loads(
        json.dumps(
            merge_candidate_constraints(
                authored.function.intervention, authored.function.receipt
            ).materialize()
        )
    )
    function.setdefault("splice_class", FUNCTION_VALIDATION_CLASS)
    function.setdefault("mangled", TARGET_SYMBOL)
    produce_function_validation_candidate(seed, seed, json.loads(json.dumps(function)))
    function["function_validation"]["replacement_instructions"][2] = "85c9"
    with pytest.raises(ByteIdentityError):
        produce_function_validation_candidate(seed, seed, function)


def test_a_reference_that_is_not_equivalent_authors_nothing() -> None:
    with pytest.raises(DiscoveryAuthoringError, match="eax differs at the return"):
        _author(reference_body=SUM_P_EDX)


def test_the_family_costs_at_least_a_donor_rewriting() -> None:
    from reprobit.costs import CostModel

    validation = CLASSIC_RECIPE_METADATA[
        ClassicRecipeFamily.RETAIL_EXACT_FUNCTION_TRANSLATION_VALIDATION
    ]
    rewriting = CLASSIC_RECIPE_METADATA[ClassicRecipeFamily.RETAIL_EXACT_DONOR_REWRITING]
    assert CostModel.weights[validation.cost_class] >= CostModel.weights[rewriting.cost_class]


def test_grind_tries_translation_validation_after_a_region_resize_refuses(
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

    def validated(**kwargs):
        calls.append("function_validation")
        return kwargs["reference_object"]

    monkeypatch.setattr(grind, "build_donor_schedule_rewriting", refuse("reorder"))
    monkeypatch.setattr(grind, "build_region_resize_rewriting", refuse("region_resize"))
    monkeypatch.setattr(grind, "build_function_validation_rewriting", validated)
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
    assert authored == b"r"
    assert calls == ["reorder", "region_resize", "function_validation"]
    monkeypatch.setattr(grind, "build_function_validation_rewriting", refuse("validation"))
    with pytest.raises(DiscoveryAuthoringError, match="reorder refused"):
        grind._state_rewriting(
            state, context, seed_object=b"s", donor_object=b"d", reference_object=b"r"
        )
