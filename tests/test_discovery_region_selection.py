"""Tests for region selection: regions end where both versions agree.

Each fixture is a classic-i386 COMDAT with an FPO closure (the re-encoding
suite's), whose body is

     0: 53 56 57 55        push ebx / esi / edi / ebp   <- FPO prologue
     4: 8b 1d <D32>        mov  ebx, [_Nil]
    10: ...                the code under test
     n: 8b 0d <D32>        mov  ecx, [_Nil]
        5d 5f 5e 5b c3     pop ebp / edi / esi / ebx, ret

The search is observed through the prover it calls: every region it
proposes goes to the unchanged `apply_region_resize`.
"""

from __future__ import annotations

from typing import Any

import pytest
from test_classic_register_bijection_reencoding_full import (
    TARGET_SYMBOL,
    codeview_stream,
    make_coff,
)

import reprobit.discovery_region_resize as search_module
from reprobit.binary import ByteIdentityError
from reprobit.classic.rewriting_region_resize import apply_region_resize
from reprobit.discovery_authoring import DiscoveryAuthoringError, build_extern_run_donor
from reprobit.discovery_region_resize import build_region_resize_rewriting
from reprobit.discovery_region_selection import Selection, rename_atoms, version_profile

UNIT = "tu.fixture"
HEAD = "53565755" + "8b1d00000000"
TAIL = "8b0d00000000" + "5d5f5e5bc3"
LOAD = "8b4304"  # mov eax, [ebx+4]
# Six instructions that touch neither EAX, ECX nor [ebx+4..8).
SHUFFLE = "8b53108953148b531889531c8b5320895324"


def _body(middle: str) -> bytes:
    return bytes.fromhex(HEAD + middle + TAIL)


def _coff(body: bytes) -> bytes:
    tail = body.rindex(bytes.fromhex("8b0d"))
    return make_coff(
        body=body,
        relocations=(6, tail + 2),
        lines=((4, 11), (10, 12), (tail, 13)),
        debug_stream=codeview_stream(len(body), 4, tail + 6),
    )


def _author(donor: bytes, reference: bytes) -> Any:
    seed = _coff(donor)
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
        reference_object=_coff(reference),
    )


def _rows(body: bytes) -> list[dict[str, Any]]:
    tail = body.rindex(bytes.fromhex("8b0d"))
    return [
        {
            "offset": offset,
            "width": 4,
            "type": 6,
            "target": "_Nil",
            "target_section": 0,
            "target_value": 0,
            "addend": 0,
        }
        for offset in (6, tail + 2)
    ]


@pytest.fixture
def attempts(monkeypatch: pytest.MonkeyPatch) -> list[list[tuple[int, int]]]:
    """The regions of every prover call the search makes, in order."""
    calls: list[list[tuple[int, int]]] = []

    def recorded(body: bytes, regions: list[Any], *args: Any, **kwargs: Any) -> Any:
        calls.append([(region["region_start"], region["region_end"]) for region in regions])
        return apply_region_resize(body, regions, *args, **kwargs)

    monkeypatch.setattr(search_module, "apply_region_resize", recorded)
    return calls


def _regions(authored: Any) -> list[tuple[int, int]]:
    value = authored.function.intervention.parameters[0].value
    return [(region["region_start"], region["region_end"]) for region in value["regions"]]


# --- growing backward to where the versions agree -------------------------------------

# The donor reloads [ebx+4] into ECX; the reference copies the EAX it loaded
# seven instructions earlier.  The differing run is one instruction:
#
#     donor 31: 8b 4b 04   mov ecx, [ebx+4]   | reference 31: 8b c8   mov ecx, eax
#        34: 89 4b 08      mov [ebx+8], ecx   (equal, ECX live at the run's exit)
GROW_DONOR = _body(LOAD + SHUFFLE + "8b4b04" + "894b08")
GROW_REFERENCE = _body(LOAD + SHUFFLE + "8bc8" + "894b08")


def test_the_minimal_region_refuses_on_a_live_register() -> None:
    region = {
        "region_start": 31,
        "region_end": 34,
        "replacement_instructions": ["8bc8"],
        "replacement_relocations": [],
    }
    with pytest.raises(ByteIdentityError, match="ecx is live at the exit"):
        apply_region_resize(
            GROW_DONOR, [region], _rows(GROW_DONOR), 1, "fixture", prologue_length=4
        )


def test_a_region_grown_back_to_the_agreeing_load_proves_first(
    attempts: list[list[tuple[int, int]]],
) -> None:
    # The leading load is seven aligned instructions back.  The old ladder of
    # extents tried 0, 1, 2, 3, 4 and 6 back first and proved a larger region
    # (8 back) at its seventh attempt; the agreeing extent is proposed first.
    authored = _author(GROW_DONOR, GROW_REFERENCE)
    assert _regions(authored) == [(10, 34)]
    assert attempts == [[(10, 34)]]


def test_the_verdict_names_the_entry_read_and_the_agreeing_extent() -> None:
    selection = Selection(
        version_profile(GROW_DONOR, _rows(GROW_DONOR), len(GROW_DONOR), "donor"),
        version_profile(GROW_REFERENCE, _rows(GROW_REFERENCE), len(GROW_REFERENCE), "ref"),
        4,
    )
    run = (12, 13, 12, 13)  # instruction indices of the differing run
    kind, why = selection.verdict(run, run) or ("", "")
    assert kind == "entry" and why.startswith("eax")
    for back in range(1, 7):
        assert selection.verdict((12 - back, 13, 12 - back, 13), run) is not None
    assert selection.verdict((5, 13, 5, 13), run) is None


# --- merging two runs -------------------------------------------------------------------

# The donor loads ECX before an equal instruction, the reference after it
# (in a longer encoding), so neither run alone leaves ECX equal:
#
#     donor:     mov ecx, [ebx+4]        | reference: mov edx, [ebx+16]
#                mov edx, [ebx+16]       |            mov ecx, [ebx+4] (disp32)
#                mov [ebx+8], ecx        |            mov [ebx+8], ecx
MERGE_DONOR = _body("8b4b04" + "8b5310" + "894b08")
MERGE_REFERENCE = _body("8b5310" + "8b8b04000000" + "894b08")


def test_two_runs_that_disagree_alone_are_merged_before_any_attempt(
    attempts: list[list[tuple[int, int]]],
) -> None:
    authored = _author(MERGE_DONOR, MERGE_REFERENCE)
    assert _regions(authored) == [(10, 16)]
    assert attempts == [[(10, 16)]]


# --- no agreeing boundary -------------------------------------------------------------------


def test_a_run_with_no_agreeing_boundary_refuses_without_an_attempt(
    attempts: list[list[tuple[int, int]]],
) -> None:
    # The donor pushes ECX where the reference does not: every region round
    # the run changes ESP by -4 in one version and 0 in the other.
    donor = _body(LOAD + "51" + "894308")
    reference = _body(LOAD + "90" + "894308")
    with pytest.raises(DiscoveryAuthoringError, match="no boundary where the versions agree"):
        _author(donor, reference)
    assert attempts == []


def test_a_return_inside_the_run_is_never_proposed(
    attempts: list[list[tuple[int, int]]],
) -> None:
    # test eax, eax / jne over the run / the run: a return and two nops.
    donor = _body(LOAD + "85c0" + "7501" + "c3" + "894308")
    reference = _body(LOAD + "85c0" + "7502" + "9090" + "894308")
    with pytest.raises(DiscoveryAuthoringError, match="holds a ret"):
        _author(donor, reference)
    assert attempts == []


# --- the profile ----------------------------------------------------------------------------


def test_rename_atoms_follows_byte_registers() -> None:
    assert rename_atoms(frozenset({"eax.l", "flag.zf"}), {"eax": "ecx", "ecx": "eax"}) == {
        "ecx.l",
        "flag.zf",
    }
    assert rename_atoms(frozenset({"eax.l"}), {"eax": "esi", "esi": "eax"}) == {"esi.w"}
    assert rename_atoms(frozenset({"esi.w"}), {"eax": "esi", "esi": "eax"}) == {
        "eax.h",
        "eax.l",
        "eax.u",
    }


def test_the_profile_measures_stack_and_call_effects() -> None:
    body = bytes.fromhex("6a01" + "e800000000" + "83c404" + "c3")
    rows = [
        {
            "offset": 3,
            "width": 4,
            "type": 20,
            "target": "_f@4",
            "target_section": 0,
            "target_value": 0,
            "addend": 0,
        }
    ]
    profile = version_profile(body, rows, len(body), "profile")
    assert profile.esp == (-4, 4, 4, 0)
    assert profile.barrier[1] is None and profile.barrier[3] is not None
    assert "flag.zf" in profile.writes[1]


def test_a_region_reading_al_starts_where_all_of_eax_is_live() -> None:
    # 0: mov al, [moffs] (keeps EAX's upper bytes) / 5: test al, al /
    # 7: xor eax, eax / 9: ret.  After the partial load only AL is live, so a
    # region starting there reads an EAX whose upper atoms are dead (check 8f).
    body = bytes.fromhex("a00000000084c033c0c3")
    profile = version_profile(body, [], len(body), "partial")
    selection = Selection(profile, profile)
    found = selection.verdict((1, 2, 1, 2), (1, 2, 1, 2))
    assert found is not None and found[0] == "entry" and "dead at the region entry" in found[1]
    assert selection.verdict((0, 2, 0, 2), (1, 2, 1, 2)) is None
