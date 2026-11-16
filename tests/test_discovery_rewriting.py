"""Grind's donor-rewriting authoring: derived reorder windows and measured pins."""

from __future__ import annotations

import pytest
from test_classic_instruction_schedule_full import (
    BODY,
    IMAGE,
    LENGTHS,
    ORDER,
    TARGET_SYMBOL,
    WINDOW,
    make_coff,
)

from reprobit.classic.scheduling_apply import ia32_schedule_body_walk
from reprobit.coff_format import CoffObject, coff_body
from reprobit.discovery_authoring import DiscoveryAuthoringError, build_extern_run_donor
from reprobit.discovery_rewriting import build_donor_schedule_rewriting, derive_schedule_windows
from reprobit.intervention_metadata import ClassicRecipeFamily

UNIT = "tu.fixture"


def _spans(body: bytes) -> list[tuple[int, int]]:
    spans, _targets = ia32_schedule_body_walk(body, {}, "test")
    return spans


def test_the_window_covers_exactly_the_reordered_instructions() -> None:
    windows = derive_schedule_windows(BODY, IMAGE, _spans(BODY), frozenset())
    assert windows == [
        {
            "start": WINDOW[0],
            "end": WINDOW[1],
            "source_instruction_lengths": LENGTHS,
            "target_order": ORDER,
        }
    ]


def test_a_two_instruction_swap_is_its_own_window() -> None:
    body = bytes.fromhex("8d4c24088d542408c3")
    target = bytes.fromhex("8d5424088d4c2408c3")
    windows = derive_schedule_windows(body, target, _spans(body), frozenset())
    assert windows == [
        {"start": 0, "end": 8, "source_instruction_lengths": [4, 4], "target_order": [1, 0]}
    ]


def test_a_difference_no_reordering_explains_is_refused() -> None:
    body = bytes.fromhex("8d4c24088d542408c3")
    target = bytes.fromhex("8d4c24088d54240cc3")
    with pytest.raises(DiscoveryAuthoringError, match="no reorder window"):
        derive_schedule_windows(body, target, _spans(body), frozenset())


def test_a_window_never_holds_a_relocated_byte() -> None:
    body = bytes.fromhex("8d4c24088d542408c3")
    target = bytes.fromhex("8d5424088d4c2408c3")
    with pytest.raises(DiscoveryAuthoringError, match="no reorder window"):
        derive_schedule_windows(body, target, _spans(body), frozenset({5}))


def test_identical_and_unequal_bodies_are_refused() -> None:
    with pytest.raises(DiscoveryAuthoringError, match="already identical"):
        derive_schedule_windows(BODY, BODY, _spans(BODY), frozenset())
    with pytest.raises(DiscoveryAuthoringError, match="differ in length"):
        derive_schedule_windows(BODY, BODY[:-1], _spans(BODY), frozenset())


def _donor():
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


def test_the_authored_record_composes_the_reference_body() -> None:
    seed = make_coff()
    reference = make_coff(body=IMAGE)
    authored = build_donor_schedule_rewriting(
        donor=_donor(),
        target_id="program",
        translation_unit_id=UNIT,
        build_target="program",
        symbol=TARGET_SYMBOL,
        seed_object=seed,
        donor_object=seed,
        reference_object=reference,
    )
    intervention = authored.function.intervention
    assert intervention.family is ClassicRecipeFamily.RETAIL_EXACT_DONOR_REWRITING
    assert intervention.dependencies == (authored.donor.intervention.id,)
    composed = CoffObject(authored.candidate_object)
    assert bytes(coff_body(composed, composed.function_section(TARGET_SYMBOL))) == IMAGE
    values = authored.function.receipt.expected_values
    assert values["donor_rewriting.windows[0].expected_dependence_edges"] == []
    assert values["retail_oracle"] == {"length": len(IMAGE)}


def test_a_reference_no_window_reaches_authors_nothing() -> None:
    seed = make_coff()
    wrong = bytearray(IMAGE)
    wrong[WINDOW[0]] ^= 0x01
    with pytest.raises(DiscoveryAuthoringError):
        build_donor_schedule_rewriting(
            donor=_donor(),
            target_id="program",
            translation_unit_id=UNIT,
            build_target="program",
            symbol=TARGET_SYMBOL,
            seed_object=seed,
            donor_object=seed,
            reference_object=make_coff(body=bytes(wrong)),
        )


def _facts(body: bytes) -> list[dict]:
    from reprobit.classic.register_semantics import decode_ia32_bijection_instruction
    from reprobit.classic.scheduling_dependence import ia32_schedule_instruction_facts

    facts, offset = [], 0
    for length in [item[1] for item in _spans(body)]:
        item = decode_ia32_bijection_instruction(body, offset, "test")
        facts.append(ia32_schedule_instruction_facts(item, "test"))
        offset += length
    return facts


def test_x87_memory_forms_carry_their_direction_and_width() -> None:
    # fld dword [esp+8]; fstp qword [esp+16]; fild dword [esp+4]; fistp dword [esp]
    facts = _facts(bytes.fromhex("d9442408dd5c2410db442404db1c24"))
    memory = [
        (item["memory"]["read"], item["memory"]["write"], item["memory"]["width"]) for item in facts
    ]
    assert memory == [(True, False, 4), (False, True, 8), (True, False, 4), (False, True, 4)]
    assert all("x87" in item["reads"] and "x87" in item["writes"] for item in facts)


def test_x87_instructions_stay_ordered_and_integer_ones_cross_them() -> None:
    from reprobit.classic.register_semantics import decode_ia32_bijection_instruction
    from reprobit.classic.scheduling_dependence import ia32_schedule_dependence_edges

    # fld st(0); mov eax, ecx; fmulp st(1)
    body = bytes.fromhex("d9c08bc1dec9")
    items, offset = [], 0
    for length in [item[1] for item in _spans(body)]:
        items.append(decode_ia32_bijection_instruction(body, offset, "test"))
        offset += length
    _, edges = ia32_schedule_dependence_edges(items, "test", body)
    assert [edge[:2] for edge in edges] == [[0, 2]]


def test_fnstsw_ax_writes_eax_and_imul_writes_flags() -> None:
    fnstsw, imul = _facts(bytes.fromhex("dfe00fafc1"))
    assert "eax" in fnstsw["writes"]
    assert imul["writes_flags"] and not imul["reads_flags"]


def test_an_unlisted_x87_memory_form_is_refused() -> None:
    from reprobit.binary import ByteIdentityError

    with pytest.raises(ByteIdentityError, match="x87 form"):
        _facts(bytes.fromhex("d93424"))  # fnstenv [esp]


# push ebx; push esi; mov ebx, eax; test eax, eax; je +5; mov esi, ecx;
# add ebx, esi; mov eax, ebx; pop esi; pop ebx; ret  -- then a second exit:
# mov esi, edx; mov eax, esi; pop esi; pop ebx; ret
TWO_EXIT = bytes.fromhex("53568bd885c074098bf103de8bc35e5bc38bf28bc65e5bc3")
SWAPPED = bytes.fromhex("53568bf085c074098bd903f38bc65e5bc38bda8bc35e5bc3")


def test_a_callee_saved_permutation_spans_every_region_between_epilogues() -> None:
    from reprobit.classic.register_bijection import apply_register_bijection
    from reprobit.discovery_rewriting import derive_register_bijection

    decision = derive_register_bijection(TWO_EXIT, SWAPPED, {}, None)
    assert decision["mapping"] == {"ebx": "esi", "esi": "ebx"}
    assert decision["regions"] == [[2, 14], [17, 21]]
    image, proof = apply_register_bijection(
        TWO_EXIT,
        decision["mapping"],
        [tuple(pair) for pair in decision["regions"]],
        frozenset(),
        "t",
    )
    assert image == SWAPPED
    assert proof["region_instruction_count"] == 8


def test_a_single_region_cannot_hold_two_epilogues() -> None:
    from reprobit.binary import ByteIdentityError
    from reprobit.classic.register_bijection import apply_register_bijection

    with pytest.raises(ByteIdentityError, match="live"):
        apply_register_bijection(TWO_EXIT, {"ebx": "esi", "esi": "ebx"}, (2, 21), frozenset(), "t")


def test_a_register_mapped_two_ways_is_not_a_bijection() -> None:
    from reprobit.discovery_rewriting import derive_register_bijection

    partly = bytearray(SWAPPED)
    partly[17:19] = bytes.fromhex("8bf2")  # the second exit keeps mov esi, edx: esi maps two ways
    with pytest.raises(DiscoveryAuthoringError):
        derive_register_bijection(TWO_EXIT, bytes(partly), {}, None)


def test_grind_falls_back_to_a_same_slot_resize_when_the_splices_refuse(
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

    record = SimpleNamespace(intervention=SimpleNamespace(id="f"), receipt=None)

    def measured(**kwargs):
        calls.append(kwargs["family"].value)
        return record

    monkeypatch.setattr(grind, "build_donor_equal_body", refuse("strict"))
    monkeypatch.setattr(grind, "build_donor_reloc_layout_equal_body", refuse("reloc"))
    monkeypatch.setattr(grind, "build_measured_function_record", measured)
    monkeypatch.setattr(
        grind, "merge_candidate_constraints", lambda *_args: SimpleNamespace(materialize=dict)
    )
    monkeypatch.setattr(
        grind,
        "ClassicFamilyDispatcher",
        lambda: SimpleNamespace(dispatch=lambda *_args: SimpleNamespace(output=b"composed")),
    )
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
    authored = grind._state_equal_body(state, context, seed_object=b"s", donor_object=b"d")
    assert calls == ["strict", "reloc", "same_slot_resize"]
    assert authored.candidate_object == b"composed"
    assert authored.function is record
