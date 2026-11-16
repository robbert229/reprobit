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


def _swap(body: bytes, offset: int, sib_at: int, relocated: frozenset[int] = frozenset()):
    from reprobit.classic.address_forms import apply_sib_operand_swaps

    return apply_sib_operand_swaps(
        body,
        [{"instruction_offset": offset, "expected_rewritten_offsets": [sib_at]}],
        relocated,
        "t",
    )


def test_a_sib_base_and_index_exchange_names_the_same_address() -> None:
    # lea eax, [ecx+edx]; mov ecx, [eax+ebx+4]; ret
    body = bytes.fromhex("8d04118b4c1804c3")
    image, proof = _swap(body, 0, 2)
    assert image == bytes.fromhex("8d040a8b4c1804c3")
    assert proof["rewritten_offsets"] == [2]
    image, _ = _swap(body, 3, 5)
    assert image == bytes.fromhex("8d04118b4c0304c3")


@pytest.mark.parametrize(
    ("body", "message"),
    [
        (bytes.fromhex("8d0451c3"), "scaled"),  # lea eax, [ecx+edx*2]
        (bytes.fromhex("8d0414c3"), "ESP or EBP"),  # lea eax, [esp+edx]
        (bytes.fromhex("8d442900c3"), "ESP or EBP"),  # lea eax, [ecx+ebp+0]
        (bytes.fromhex("8d0409c3"), "same register"),  # lea eax, [ecx+ecx]
    ],
)
def test_a_sib_swap_outside_the_commutative_case_is_refused(body: bytes, message: str) -> None:
    from reprobit.binary import ByteIdentityError

    with pytest.raises(ByteIdentityError, match=message):
        _swap(body, 0, 2)


def test_a_relocated_or_misdeclared_sib_byte_is_refused() -> None:
    from reprobit.binary import ByteIdentityError

    body = bytes.fromhex("8d0411c3")
    with pytest.raises(ByteIdentityError, match="relocated"):
        _swap(body, 0, 2, frozenset({2}))
    with pytest.raises(ByteIdentityError, match="declaration"):
        _swap(body, 0, 1)


def test_sib_swaps_are_derived_only_when_they_explain_every_difference() -> None:
    from reprobit.discovery_rewriting import derive_sib_operand_swaps

    body = bytes.fromhex("8d04118b4c1804c3")
    assert derive_sib_operand_swaps(body, bytes.fromhex("8d040a8b4c1804c3"), {}, None) == [
        {"instruction_offset": 0}
    ]
    with pytest.raises(DiscoveryAuthoringError, match="operand order"):
        derive_sib_operand_swaps(body, bytes.fromhex("8d04128b4c1804c3"), {}, None)


def test_a_local_register_permutation_gets_its_own_region() -> None:
    from reprobit.discovery_rewriting import derive_regional_bijections

    # mov ecx, [esp+4]; mov edx, [esp+8]; add ecx, edx; mov eax, ecx; ret
    body = bytes.fromhex("8b4c24048b54240803ca8bc1c3")
    target = bytes.fromhex("8b5424048b4c240803d18bc2c3")
    items = derive_regional_bijections(body, target, {}, None, frozenset(), frozenset())
    assert items == [{"mapping": {"ecx": "edx", "edx": "ecx"}, "region_start": 0, "region_end": 12}]


def test_msvc50_code_end_stops_before_a_switch_table() -> None:
    from reprobit.discovery_rewriting import msvc50_code_end

    # ... ret, nop, mov edi,edi, then two table entries into this section.
    code = bytes.fromhex("33c0" "c3" "90" "8bff")
    body = code + bytes(8) + b"\x90" * 4
    rows = [
        {"offset": len(code), "width": 4, "target_section": 3},
        {"offset": len(code) + 4, "width": 4, "target_section": 3},
    ]
    assert msvc50_code_end(body, rows, 3, len(code) + 8) == 3
    # A table into another section is not this body's switch table.
    other = [dict(row, target_section=7) for row in rows]
    assert msvc50_code_end(body, other, 3, len(code) + 8) == len(code) + 8
    # Without a terminal instruction before the fill the extent stands.
    falls = bytes.fromhex("33c0" "40" "90" "8bff") + bytes(8)
    assert msvc50_code_end(falls, rows, 3, len(code) + 8) == len(code) + 8
    # No table: the procedure length stands.
    assert msvc50_code_end(body, [], 3, len(code) + 8) == len(code) + 8


def test_a_bijection_rewrites_byte_fields_within_eax_to_ebx() -> None:
    from reprobit.classic.register_bijection import apply_register_bijection
    from reprobit.classic.register_semantics import decode_ia32_bijection_body

    # mov edx, [0] ; or dh, 2 ; mov [0], edx ; ret
    body = bytes.fromhex("8b1500000000" "80ce02" "891500000000" "c3")
    decoded = decode_ia32_bijection_body(body, "t")
    assert decoded[1]["byte_fields"] == [(7, 0)]
    assert decoded[1]["byte_frozen"] == frozenset({"edx"})
    image, proof = apply_register_bijection(
        body, {"ecx": "edx", "edx": "ecx"}, (0, 15), frozenset(), "t", {}
    )
    assert image == bytes.fromhex("8b0d00000000" "80cd02" "890d00000000" "c3")
    assert proof["rewritten_offsets"] == [1, 7, 10]


def test_a_bijection_refuses_to_move_a_byte_field_off_eax_to_ebx() -> None:
    import pytest

    from reprobit.binary import ByteIdentityError
    from reprobit.classic.register_bijection import apply_register_bijection

    body = bytes.fromhex("8b1500000000" "80ce02" "891500000000" "c3")
    with pytest.raises(ByteIdentityError, match="off a byte register"):
        apply_register_bijection(body, {"esi": "edx", "edx": "esi"}, (0, 15), frozenset(), "t", {})


def test_the_regional_deriver_reads_byte_fields() -> None:
    from reprobit.discovery_rewriting import derive_regional_bijections

    donor = bytes.fromhex("8b1500000000" "80ce02" "891500000000" "c3")
    target = bytes.fromhex("8b0d00000000" "80cd02" "890d00000000" "c3")
    found = derive_regional_bijections(donor, target, {}, None, frozenset(), frozenset())
    assert found and found[0]["mapping"] == {"ecx": "edx", "edx": "ecx"}



def test_msvc50_code_end_stops_before_a_jump_table_and_its_index_table() -> None:
    from reprobit.discovery_rewriting import msvc50_code_end

    code = bytes.fromhex("33c0" "c3" "90")
    body = code + bytes(8) + bytes.fromhex("00010100") + b"\x90" * 4
    rows = [
        {"offset": len(code), "width": 4, "target_section": 3},
        {"offset": len(code) + 4, "width": 4, "target_section": 3},
    ]
    assert msvc50_code_end(body, rows, 3, len(code) + 12) == 3


def test_msvc50_code_end_stops_before_two_switch_tables() -> None:
    from reprobit.discovery_rewriting import msvc50_code_end

    code = bytes.fromhex("33c0" "c3" "90")
    first = len(code)
    second = first + 8 + 4
    body = code + bytes(8) + bytes.fromhex("00010000") + bytes(4) + bytes.fromhex("0001") + b"\x90" * 2
    rows = [
        {"offset": first, "width": 4, "target_section": 3},
        {"offset": first + 4, "width": 4, "target_section": 3},
        {"offset": second, "width": 4, "target_section": 3},
    ]
    assert msvc50_code_end(body, rows, 3, second + 6) == 3
    # A foreign relocation after the first table means it is not a table tail.
    foreign = rows + [{"offset": second + 4, "width": 2, "target_section": 9}]
    assert msvc50_code_end(body, foreign, 3, second + 6) == second + 6
