"""Tests for the scope bijection composed with `retail_exact_region_resize_rewriting`.

The donor keeps a loaded value in ESI and copies it to EDI for one store; the
reference allocated EDI for the value throughout and drops the copy.  A call
sits between the two uses, so no region can hold both and no plain
replacement proves:

     0: 53 56 57 55        push ebx / esi / edi / ebp   <- FPO prologue
     4: 8b 1d <D32>        mov  ebx, [_Nil]
    10: 8b 73 04           mov  esi, [ebx+4]    <- scope [10, 26) under esi<->edi
    13: 8b fe              mov  edi, esi        <- region [13, 18)
    15: 89 7b 08           mov  [ebx+8], edi
    18: ff 15 <D32>        call [_Nil]          <- touches neither ESI nor EDI
    24: 89 33              mov  [ebx], esi      <- rewritten to edi
    26: 33 c0              xor  eax, eax        <- outside the scope: ESI and EDI dead
    28: 5d 5f 5e 5b c3     pop ... / ret

The reference, two bytes shorter:

    10: 8b 7b 04           mov  edi, [ebx+4]
    13: 89 7b 08           mov  [ebx+8], edi
    16: ff 15 <D32>        call [_Nil]
    22: 89 3b              mov  [ebx], edi
    24: 33 c0              xor  eax, eax
"""

from __future__ import annotations

import json

import pytest
from test_classic_register_bijection_reencoding_full import (
    NIL_SYMBOL,
    TARGET_SYMBOL,
    codeview_stream,
    make_coff,
)

from reprobit.binary import ByteIdentityError
from reprobit.classic.region_simulation import canonical_flag, lin_atom, simulate_region
from reprobit.classic.register_semantics import decode_ia32_bijection_body
from reprobit.classic.rewriting_region_resize import (
    REGION_RESIZE_CLASS,
    ScopeBoundRefusal,
    apply_region_resize,
    produce_region_resize_rewriting_candidate,
    refine_call_reads,
    register_free_callee,
)
from reprobit.classic_donors import merge_candidate_constraints
from reprobit.classic_project import ClassicDispatchMaterials, ClassicFamilyDispatcher
from reprobit.discovery_authoring import build_extern_run_donor
from reprobit.discovery_region_resize import build_region_resize_rewriting
from reprobit.msvc_discovery_coff import qualify_msvc_reference_object
from reprobit.schema import ClassicRecipeIntervention

UNIT = "tu.fixture"
HEAD = "535657558b1d00000000"
TAIL = "33c05d5f5e5bc3"
CALL = "ff1500000000"
DONOR = bytes.fromhex(HEAD + "8b7304" + "8bfe897b08" + CALL + "8933" + TAIL)
REFERENCE = bytes.fromhex(HEAD + "8b7b04" + "897b08" + CALL + "893b" + TAIL)
SWAP = {"edi": "esi", "esi": "edi"}
REGION = {
    "region_start": 13,
    "region_end": 18,
    "replacement_instructions": ["897b08"],
    "replacement_relocations": [],
}
BIJECTION = {"mapping": SWAP, "scopes": [[10, 26]]}


def _rows(offsets=(6, 20)):
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


def _apply(body=DONOR, regions=None, bijection=BIJECTION, **kwargs):
    return apply_region_resize(
        body,
        [dict(item) for item in (regions or [REGION])],
        _rows(),
        1,
        "fixture",
        prologue_length=4,
        bijection=json.loads(json.dumps(bijection)) if bijection is not None else None,
        **kwargs,
    )


# --- the primitive ------------------------------------------------------------------


def test_a_region_proved_under_the_scope_bijection_reaches_the_reference() -> None:
    image, proof = _apply()
    assert image == REFERENCE
    assert proof["growth"] == -2
    # The two ModRM bytes the bijection rewrote, in image coordinates.
    assert proof["bijection_rewrites"] == [11, 23]
    assert proof["bijection_mode_changes"] == [10, 24]
    (region,) = proof["regions"]
    assert region["entry_mapped"] is True and region["exit_mapped"] is True
    # The donor's ESI is compared with the replacement's EDI; the call keeps
    # EAX, ECX and EDX live through the region.
    assert region["compared_registers"] == ["eax", "ebx", "ecx", "edx", "esi"]


@pytest.mark.parametrize(
    ("start", "end", "replacement"),
    [(13, 18, ["897b08"]), (10, 18, ["8b7b04", "897b08"]), (24, 26, ["893b"])],
)
def test_without_the_bijection_no_region_proves(
    start: int, end: int, replacement: list[str]
) -> None:
    region = {**REGION, "region_start": start, "region_end": end}
    region["replacement_instructions"] = replacement
    with pytest.raises(ByteIdentityError, match=r"is live at the exit|different memory"):
        _apply(bijection=None, regions=[region])


def test_a_region_may_carry_the_correspondence_across_a_scope_bound() -> None:
    # The scope ends inside the region: it is entered under the bijection and
    # left without it, so the replacement must hand ESI back.
    image, proof = _apply(
        regions=[{**REGION, "replacement_instructions": ["897b08", "8bf7"]}],
        bijection={"mapping": SWAP, "scopes": [[10, 15]]},
    )
    assert image == bytes.fromhex(HEAD + "8b7b04" + "897b08" + "8bf7" + CALL + "8933" + TAIL)
    (region,) = proof["regions"]
    assert region["entry_mapped"] is True and region["exit_mapped"] is False
    assert proof["bijection_mode_changes"] == [10]


def test_a_scope_bound_where_a_support_register_is_live_is_refused() -> None:
    # The unrewritten use at 24 keeps the image's ESI live back to the scope's
    # start, so the first bound checked already refuses.
    with pytest.raises(ScopeBoundRefusal, match=r"\['esi'\] is live at 10") as caught:
        _apply(bijection={"mapping": SWAP, "scopes": [[10, 24]]})
    assert caught.value.offset == 10


def test_a_scope_entered_where_a_support_register_is_live_is_refused() -> None:
    # Starting the scope at the region renames ESI after it was loaded.
    with pytest.raises(ScopeBoundRefusal, match="is live at 13"):
        _apply(bijection={"mapping": SWAP, "scopes": [[13, 26]]})


def test_a_return_inside_the_scope_is_refused() -> None:
    # `ret` reads ESI and EDI implicitly: swapping them breaks the caller's.
    with pytest.raises(ByteIdentityError, match="other than through a field"):
        _apply(bijection={"mapping": SWAP, "scopes": [[10, len(DONOR)]]})


def test_a_call_inside_the_scope_that_clobbers_a_support_register_is_refused() -> None:
    with pytest.raises(ByteIdentityError, match=r"18 touches \['eax', 'ecx'\] other than"):
        _apply(bijection={"mapping": {"eax": "ecx", "ecx": "eax"}, "scopes": [[10, 26]]})


@pytest.mark.parametrize(
    ("bijection", "why"),
    [
        ({"mapping": {"esi": "esp", "esp": "esi"}, "scopes": [[10, 26]]}, "ESP"),
        ({"mapping": {"esi": "ebp", "ebp": "esi"}, "scopes": [[10, 26]]}, "frame-pointer-free"),
        ({"mapping": {"esi": "edi"}, "scopes": [[10, 26]]}, "permutation"),
        ({"mapping": {"esi": "esi"}, "scopes": [[10, 26]]}, "permutation"),
        ({"mapping": SWAP, "scopes": [[11, 26]]}, "instruction boundaries"),
        ({"mapping": SWAP, "scopes": [[10, 15], [15, 26]]}, "adjacent"),
        ({"mapping": SWAP, "scopes": [[10, 40]]}, "instruction boundaries"),
        ({"mapping": SWAP, "scopes": []}, "list of ranges"),
        ({"mapping": SWAP}, "unknown or missing"),
    ],
)
def test_a_malformed_bijection_is_refused(bijection: dict, why: str) -> None:
    with pytest.raises(ByteIdentityError, match=why):
        _apply(bijection=bijection)


def test_a_replacement_that_ignores_the_correspondence_is_refused() -> None:
    # The replacement stores the image's ESI, which under the bijection holds
    # the donor's EDI -- dead at the scope's start in the donor, live in the image.
    with pytest.raises(ScopeBoundRefusal, match="is live at 10"):
        _apply(regions=[{**REGION, "replacement_instructions": ["897308"]}])


def test_the_replacement_starts_from_the_renamed_entry_state() -> None:
    code = bytes.fromhex("894b08")
    (path,) = simulate_region(
        code, 0, len(code), {}, "t", "renamed", entry_names={"ecx": "eax", "eax": "ecx"}
    )
    assert path.stores[0][2] == lin_atom(("reg0", "eax"))
    with pytest.raises(ByteIdentityError, match="permutation"):
        simulate_region(code, 0, len(code), {}, "t", "bad", entry_names={"ecx": "eax"})


def test_zero_flag_is_compared_by_its_meaning() -> None:
    a, b = lin_atom(("reg0", "eax")), lin_atom(("reg0", "ecx"))
    assert canonical_flag("zf", ("flag", "zf", "sub", 32, a, b)) == canonical_flag(
        "zf", ("flag", "zf", "sub", 32, b, a)
    )
    assert canonical_flag("cf", ("flag", "cf", "sub", 32, a, b)) != canonical_flag(
        "cf", ("flag", "cf", "sub", 32, b, a)
    )


def test_a_swapped_compare_feeding_only_je_is_proved() -> None:
    # cmp eax, ecx / cmp ecx, eax before a je that only reads ZF.
    body = bytes.fromhex(HEAD + "3bc1" + "7400" + TAIL)
    image, proof = apply_region_resize(
        body,
        [
            {
                "region_start": 10,
                "region_end": 12,
                "replacement_instructions": ["3bc8"],
                "replacement_relocations": [],
            }
        ],
        _rows(),
        1,
        "fixture",
        prologue_length=4,
    )
    assert image == bytes.fromhex(HEAD + "3bc8" + "7400" + TAIL)
    assert proof["regions"][0]["compared_flags"] == ["zf"]


# --- call arguments by decoration ---------------------------------------------------


@pytest.mark.parametrize(
    ("symbol", "free"),
    [
        ("_memcpy", True),
        ("_Sleep@4", True),
        ("__imp__Sleep@4", True),
        ("__imp__GetTickCount@0", True),
        ("@fast@8", False),
        ("__chkstk", False),
        ("__aullshr", False),
        ("?member@Class@@QAEXXZ", False),
        ("plain", False),
        ("_bad@x", False),
        ("_", False),
        (None, False),
    ],
)
def test_register_free_callees_follow_the_c_decoration(symbol: object, free: bool) -> None:
    assert register_free_callee(symbol) is free


def test_a_register_free_call_reads_only_the_stack() -> None:
    body = bytes.fromhex("e800000000c3")
    view = {1: {"width": 4, "target": "_callee"}}
    (call, _ret) = refine_call_reads(decode_ia32_bijection_body(body, "t", view), view)
    assert call["reads"] == frozenset({"esp"})
    assert {"eax", "ecx", "edx"} <= set(call["writes"])
    helper = {1: {"width": 4, "target": "__chkstk"}}
    (call, _ret) = refine_call_reads(decode_ia32_bijection_body(body, "t", helper), helper)
    assert {"eax", "ecx", "edx"} <= set(call["reads"])


# --- discovery and the producer -------------------------------------------------------


def _coff(body, lines, debug_end):
    return make_coff(
        body=body,
        relocations=(6, body.index(bytes.fromhex("ff15")) + 2),
        lines=lines,
        debug_stream=codeview_stream(len(body), 4, debug_end),
    )


def _donor_coff():
    return _coff(DONOR, ((4, 11), (10, 12), (18, 13), (24, 14)), 28)


def _reference_coff():
    return _coff(REFERENCE, ((4, 11), (10, 12), (16, 13), (22, 14)), 26)


def _author():
    seed = _donor_coff()
    return build_region_resize_rewriting(
        donor=build_extern_run_donor(
            target_id="program",
            translation_unit_id=UNIT,
            build_target="program",
            header_prefix="ReproBitPad",
            header_count=1,
            seat_prefix="ReproBitPadSeat",
            seat_count=0,
            width=3,
            beneficiary_symbols=(TARGET_SYMBOL,),
        ),
        target_id="program",
        translation_unit_id=UNIT,
        build_target="program",
        symbol=TARGET_SYMBOL,
        seed_object=seed,
        donor_object=seed,
        reference_object=_reference_coff(),
    )


def test_discovery_finds_the_bijection_and_round_trips_through_the_dispatcher() -> None:
    authored = _author()
    value = authored.function.intervention.parameters[0].value
    assert value["bijection"] == {"mapping": SWAP, "scopes": [[10, 26]]}
    seed = _donor_coff()
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
    qualify_msvc_reference_object(
        reference_object=_reference_coff(), candidate_object=candidate.output, symbol=TARGET_SYMBOL
    )


def _function():
    authored = _author()
    constraints = merge_candidate_constraints(
        authored.function.intervention, authored.function.receipt
    ).materialize()
    function = json.loads(json.dumps(constraints))
    function.setdefault("splice_class", REGION_RESIZE_CLASS)
    function.setdefault("mangled", TARGET_SYMBOL)
    return function


def test_the_producer_re_proves_the_bijection_and_its_pins() -> None:
    seed = _donor_coff()
    function = _function()
    produce_region_resize_rewriting_candidate(seed, seed, json.loads(json.dumps(function)))
    assert function["region_resize"]["expected_bijection_rewrites"] == [11, 23]
    tampered = json.loads(json.dumps(function))
    tampered["region_resize"]["expected_bijection_rewrites"] = [11]
    with pytest.raises(ByteIdentityError, match="bijection differs"):
        produce_region_resize_rewriting_candidate(seed, seed, tampered)
    unpinned = json.loads(json.dumps(function))
    del unpinned["region_resize"]["expected_bijection_mode_changes"]
    with pytest.raises(ByteIdentityError, match="declared together"):
        produce_region_resize_rewriting_candidate(seed, seed, unpinned)
    narrowed = json.loads(json.dumps(function))
    narrowed["region_resize"]["bijection"]["scopes"] = [[10, 24]]
    with pytest.raises(ByteIdentityError, match="is live at 10"):
        produce_region_resize_rewriting_candidate(seed, seed, narrowed)


# --- relocation pairing by target -------------------------------------------------------

PAIRED_DONOR = bytes.fromhex(HEAD + "8b0500000000" + "8b0d00000000" + "03c1" + "8903" + TAIL)
PAIRED_IMAGE = bytes.fromhex(HEAD + "8b0d00000000" + "8b0500000000" + "03c1" + "8903" + TAIL)


def _paired_rows(offsets=((12, "_a"), (18, "_b"))):
    return _rows((6,)) + [{**_rows((offset,))[0], "target": target} for offset, target in offsets]


def _paired(pairs):
    return apply_region_resize(
        PAIRED_DONOR,
        [
            {
                "region_start": 10,
                "region_end": 22,
                "replacement_instructions": ["8b0d00000000", "8b0500000000"],
                "replacement_relocations": pairs,
            }
        ],
        _paired_rows(),
        1,
        "fixture",
        prologue_length=4,
    )


def test_relocated_fields_may_pair_out_of_order_by_their_target() -> None:
    # The replacement loads _b before _a: its first field takes the donor's
    # second record and the other way round.
    image, proof = _paired([[2, 18], [8, 12]])
    assert image == PAIRED_IMAGE
    assert proof["relocation_reseat"] == [[12, 18], [18, 12]]


def test_a_pairing_that_swaps_the_targets_is_refused() -> None:
    with pytest.raises(ByteIdentityError, match="is live at the exit"):
        _paired([[2, 12], [8, 18]])


def test_a_record_taken_twice_is_refused() -> None:
    with pytest.raises(ByteIdentityError, match="each once"):
        _paired([[2, 12], [8, 12]])


def test_discovery_pairs_relocated_fields_by_symbol() -> None:
    from reprobit.discovery_region_resize import _instruction_keys, _regions_for

    donor_rows = [{**row, "target_type": 0, "target_storage": 2} for row in _paired_rows()]
    reference_rows = [
        {**row, "target_type": 0, "target_storage": 2}
        for row in _paired_rows(((12, "_b"), (18, "_a")))
    ]
    donor_keys = _instruction_keys(PAIRED_DONOR, donor_rows, len(PAIRED_DONOR), "d")
    reference_keys = _instruction_keys(PAIRED_IMAGE, reference_rows, len(PAIRED_IMAGE), "r")
    (region,) = _regions_for(
        [(5, 7, 5, 7)],
        donor_keys,
        reference_keys,
        donor_rows,
        reference_rows,
        len(PAIRED_DONOR),
        len(PAIRED_IMAGE),
        PAIRED_IMAGE,
    )
    assert region["replacement_relocations"] == [[2, 18], [8, 12]]


# --- the accumulator moffs forms ------------------------------------------------------


def test_a_moffs_load_is_a_shorter_absolute_load() -> None:
    body = bytes.fromhex(HEAD + "8b0500000000" + "8903" + TAIL)
    image, proof = apply_region_resize(
        body,
        [
            {
                "region_start": 10,
                "region_end": 16,
                "replacement_instructions": ["a100000000"],
                "replacement_relocations": [[1, 12]],
            }
        ],
        _rows((6, 12)),
        1,
        "fixture",
        prologue_length=4,
    )
    assert image == bytes.fromhex(HEAD + "a100000000" + "8903" + TAIL)
    assert proof["growth"] == -1


@pytest.mark.parametrize(
    ("encoding", "relocations", "why"),
    [
        ("a100000000", {}, "without a relocation"),
        ("66a100000000", {2: "_g"}, "operand-size-prefixed"),
    ],
)
def test_a_moffs_form_outside_the_closed_set_is_refused(
    encoding: str, relocations: dict[int, str], why: str
) -> None:
    code = bytes.fromhex(encoding)
    with pytest.raises(ByteIdentityError, match=why):
        simulate_region(code, 0, len(code), relocations, "t", "moffs")


def test_the_moffs_forms_move_the_accumulator_exactly() -> None:
    code = bytes.fromhex("a100000000" + "a204000000")
    (path,) = simulate_region(code, 0, len(code), {1: "_g", 6: "_g"}, "t", "moffs")
    loaded = path.regs["eax"]
    assert loaded[2][0][0][0] == "ld" and loaded[2][0][0][2] == 4
    ((address, width, value),) = path.stores
    assert width == 1 and address == ("lin", 4, ((("sym", "_g"), 1),))
    assert value[0] == "b" and value[1] == 8


# --- regions with several exits and entries ---------------------------------------------

LEAVING_DONOR = bytes.fromhex(HEAD + "8b4304" + "85c0" + "7402" + "8903" + TAIL)
LEAVING_IMAGE = bytes.fromhex(HEAD + "8b4304" + "83f800" + "7402" + "8903" + TAIL)


def _leaving(replacement):
    return apply_region_resize(
        LEAVING_DONOR,
        [
            {
                "region_start": 10,
                "region_end": 17,
                "replacement_instructions": replacement,
                "replacement_relocations": [],
            }
        ],
        _rows((6,)),
        1,
        "fixture",
        prologue_length=4,
    )


def test_a_region_may_leave_by_a_branch_and_is_compared_where_it_leaves() -> None:
    # je 19 leaves the region [10, 17); the replacement's je, one byte later,
    # must land on M(19) = 20.
    image, proof = _leaving(["8b4304", "83f800", "7402"])
    assert image == LEAVING_IMAGE
    (region,) = proof["regions"]
    assert region["exits"] == [[19, 20]]
    assert region["path_pairs"] == 2
    assert region["compared_registers"] == ["eax", "ebx"]


def test_a_replacement_that_leaves_elsewhere_is_refused() -> None:
    with pytest.raises(ByteIdentityError, match="leave the region at different places"):
        _leaving(["8b4304", "83f800", "7400"])


def test_a_branch_backward_inside_a_region_is_still_refused() -> None:
    body = bytes.fromhex(HEAD + "8b4304" + "85c0" + "75f9" + "8903" + TAIL)
    with pytest.raises(ByteIdentityError, match="backward"):
        apply_region_resize(
            body,
            [
                {
                    "region_start": 10,
                    "region_end": 17,
                    "replacement_instructions": ["8b4304", "85c0", "75f9"],
                    "replacement_relocations": [],
                }
            ],
            _rows((6,)),
            1,
            "fixture",
            prologue_length=4,
        )


ENTERED_DONOR = bytes.fromhex(HEAD + "85db" + "7403" + "8b4304" + "8bc8894b08" + "8903" + TAIL)
ENTERED_IMAGE = bytes.fromhex(HEAD + "85db" + "7403" + "8b4304" + "894308" + "8903" + TAIL)
ENTERED_REGION = {
    "region_start": 14,
    "region_end": 22,
    "replacement_instructions": ["8b4304", "894308"],
    "replacement_relocations": [],
    "replacement_entries": [[17, 3]],
}


def _entered(**changes):
    return apply_region_resize(
        ENTERED_DONOR,
        [{**ENTERED_REGION, **changes}],
        _rows((6,)),
        1,
        "fixture",
        prologue_length=4,
    )


def test_a_declared_entry_admits_a_branch_into_the_region_interior() -> None:
    # je 17 enters the region [14, 22) between its two instructions; from
    # there both versions store the entry EAX.
    image, proof = _entered()
    assert image == ENTERED_IMAGE
    (region,) = proof["regions"]
    assert region["entries"] == [[17, 17]]
    assert region["donor_paths"] == 2 and region["replacement_paths"] == 2


def test_an_undeclared_entry_into_the_interior_is_refused() -> None:
    region = {key: value for key, value in ENTERED_REGION.items() if key != "replacement_entries"}
    with pytest.raises(ByteIdentityError, match="targets the region interior"):
        apply_region_resize(ENTERED_DONOR, [region], _rows((6,)), 1, "fixture", prologue_length=4)


def test_an_entry_mapped_to_the_wrong_replacement_instruction_is_refused() -> None:
    with pytest.raises(ByteIdentityError, match="entry 17"):
        _entered(replacement_entries=[[17, 0]])


@pytest.mark.parametrize(
    "entries", [[[17, 4]], [[14, 0]], [[22, 3]], [[17, 3], [17, 3]], [], [[17, 3, 0]]]
)
def test_a_malformed_entry_is_refused(entries: list) -> None:
    with pytest.raises(ByteIdentityError, match="replacement entries"):
        _entered(replacement_entries=entries)


def test_discovery_maps_a_branch_into_a_run_through_the_aligned_branch() -> None:
    from reprobit.discovery_region_resize import (
        _aligned_offsets,
        _branch_targets,
        _instruction_keys,
        _regions_for,
    )

    rows = [{**row, "target_type": 0, "target_storage": 2} for row in _rows((6,))]
    donor_keys = _instruction_keys(ENTERED_DONOR, rows, len(ENTERED_DONOR), "d")
    reference_keys = _instruction_keys(ENTERED_IMAGE, rows, len(ENTERED_IMAGE), "r")
    branches = (
        _branch_targets(ENTERED_DONOR, rows, len(ENTERED_DONOR), "d"),
        _branch_targets(ENTERED_IMAGE, rows, len(ENTERED_IMAGE), "r"),
        _aligned_offsets(donor_keys, reference_keys),
    )
    # The run [14, 22) of the donor against [14, 20) of the reference.
    (region,) = _regions_for(
        [(7, 10, 7, 9)],
        donor_keys,
        reference_keys,
        rows,
        rows,
        len(ENTERED_DONOR),
        len(ENTERED_IMAGE),
        ENTERED_IMAGE,
        branches,
    )
    assert region["replacement_entries"] == [[17, 3]]
