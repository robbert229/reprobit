"""The frame-objects pass (a14) for a donor compiled without /Zi, through its debug sibling.

A unit compiled without ``/Zi`` has no CodeView symbols and no type-server
PDB, which a14 reads the frame's locals and their sizes from.  The pass then
reads them from the donor's *debug sibling*: the same unit compiled with the
same command line plus ``/Zi`` (`frame_objects.sibling_frame_source`),
admitted only when its function's bytes, relocations and FPO record are the
donor's exactly.

1. A real MSVC 5.0 compile without /Zi (``homed.nozi.obj``) is admitted
   against the /Zi compile of the same source, and gives its frame objects.
2. The record: a donor without CodeView proves under a14 through its
   sibling, pins ``frame_objects_from``, and dispatches with the sibling.
3. Refusals: no sibling, a failed sibling compile, a sibling whose code,
   relocations or FPO record differ (``/Zi`` changed the code), a sibling
   without CodeView, and a donor that carries CodeView itself.
4. Grind and the build: grind's donor products carry the sibling for a unit
   without /Zi; the build composes the record from its own sibling and names
   its object and PDB as inputs.
"""

from __future__ import annotations

import struct
from pathlib import Path
from typing import Any

import pytest
from test_classic_frame_objects import (
    REP_D,
    REP_LOCALS,
    REP_P,
    REP_TYPES,
    _compose,
    _debug_s,
    _extern_donor,
    _grind_rewriting,
    _pdb,
    _rep_coff,
    _type_server_stream,
)
from test_classic_register_bijection_reencoding_full import TARGET_SYMBOL, make_coff

from reprobit.binary import ByteIdentityError
from reprobit.classic.coff import _comdat_child
from reprobit.classic.frame_objects import (
    DebugSibling,
    donor_frame_objects,
    sibling_frame_source,
)
from reprobit.classic.debug import parse_fpo_data
from reprobit.classic_donors import merge_candidate_constraints
from reprobit.classic_project import (
    ClassicDispatchMaterials,
    ClassicFamilyDispatcher,
    ClassicProjectError,
)
from reprobit.coff_format import CoffObject, carries_codeview, coff_body
from reprobit.coff_function_view import _sections_of, _serialize, _symbol_records
from reprobit.discovery_authoring import DiscoveryAuthoringError
from reprobit.discovery_function_validation import build_function_validation_rewriting
from reprobit.model import Digest

FIXTURES = Path(__file__).parent / "fixtures" / "frame_objects"
_CODEVIEW_SECTIONS = (".debug$S", ".debug$T")
_MARKER_STORAGE = 101
_FUNCTION_TYPE = 0x20


def without_codeview(data: bytes) -> bytes:
    """The object as MSVC 5.0 writes it without /Zi: no CodeView, no line numbers.

    The ``.debug$S`` and ``.debug$T`` sections and their symbols go, with the
    ``.bf``/``.lf``/``.ef`` markers, every function's definition record and
    every line table (``homed.nozi.obj`` has none of them); the sections after
    them are renumbered and every relocation is re-pointed at its symbol's
    new index.
    """
    coff = CoffObject(data)
    sections = _sections_of(coff)
    dropped = {
        index + 1 for index, item in enumerate(coff.sections) if item["name"] in _CODEVIEW_SECTIONS
    }
    numbers: dict[int, int] = {}
    for number in range(1, len(sections) + 1):
        if number not in dropped:
            numbers[number] = len(numbers) + 1
    records = _symbol_records(coff)
    kept: list[bytearray] = []
    indices: dict[int, int] = {}
    index = 0
    while index < len(records):
        record = records[index]
        (number,) = struct.unpack_from("<h", record, 12)
        auxiliary = record[17]
        drop = number in dropped or record[16] == _MARKER_STORAGE
        if not drop:
            indices[index] = len(kept)
            group = [bytearray(item) for item in records[index : index + 1 + auxiliary]]
            if struct.unpack_from("<H", record, 14)[0] == _FUNCTION_TYPE and number > 0:
                group = group[:1]
                group[0][17] = 0
            if number > 0:
                struct.pack_into("<h", group[0], 12, numbers[number])
                if group[0][16] == 3 and auxiliary and group[0][0:1] == b".":
                    (associated,) = struct.unpack_from("<H", group[1], 12)
                    if associated:
                        struct.pack_into("<H", group[1], 12, numbers[associated])
                    struct.pack_into("<H", group[1], 6, 0)
            kept.extend(group)
        index += 1 + auxiliary
    result = []
    for number, section in enumerate(sections, start=1):
        if number in dropped:
            continue
        table = bytearray()
        for at in range(0, len(section.relocations), 10):
            offset, symbol, kind = struct.unpack_from("<IIH", section.relocations, at)
            table += struct.pack("<IIH", offset, indices[symbol], kind)
        section.relocations = bytes(table)
        section.lines = b""
        result.append(section)
    stripped = _serialize(coff, result, kept)
    assert not carries_codeview(CoffObject(stripped))
    return stripped


def zi_object(
    body: bytes = REP_D, locals_words: int = 7, relocations: tuple[int, ...] = ()
) -> bytes:
    """The fixture's /Zi object, its FPO prologue end at its CodeView debug start (0).

    MSVC writes the two equal; a donor without CodeView reads its debug
    start from the FPO record (`function_validation._debug_range`).
    ``relocations`` places a DIR32 field to ``_Nil`` at each offset.
    """
    data = bytearray(
        make_coff(
            body=body,
            relocations=relocations,
            lines=((0, 10),),
            debug_stream=_debug_s(len(body), REP_LOCALS),
            types=_type_server_stream(),
        )
    )
    fpo = next(item for item in CoffObject(bytes(data)).sections if item["name"] == ".debug$F")
    struct.pack_into("<IHB", data, fpo["raw_offset"] + 8, locals_words, 1, 0)
    return bytes(data)


def _sibling(body: bytes = REP_D) -> DebugSibling:
    return DebugSibling(zi_object(body), _pdb(REP_TYPES))


# --- 1. a real compile -------------------------------------------------------------------


def test_a_real_compile_without_zi_is_admitted_against_its_zi_sibling() -> None:
    # homed.nozi.obj: tests/fixtures/frame_objects/homed.c compiled by MSVC 5.0
    # with homed.obj's command line less /Zi (cl /nologo /TC /ML /O2 /Ob1
    # /Fohomed.nozi.obj /Fdhomed.nozi.obj.pdb -c homed.c), which writes no PDB.
    data = (FIXTURES / "homed.nozi.obj").read_bytes()
    donor = CoffObject(data)
    assert not carries_codeview(donor)
    primary = donor.function_section("_homed_draw")
    sibling = DebugSibling(
        (FIXTURES / "homed.obj").read_bytes(), (FIXTURES / "homed.obj.pdb").read_bytes()
    )
    source, section, types = sibling_frame_source(donor, primary, "_homed_draw", sibling, "x")
    assert bytes(coff_body(source, section)) == bytes(coff_body(donor, primary))
    fpo = parse_fpo_data(
        bytes(coff_body(donor, _comdat_child(donor, primary, ".debug$F"))),
        expected_proc_size=primary["raw_size"],
        body=bytes(coff_body(donor, primary)),
    )
    base, params_end = -4 * fpo["cdwLocals"], 4 + 4 * fpo["cdwParams"]
    objects = donor_frame_objects(
        source, section, types, base=base, params_end=params_end, context="x"
    )
    assert [(item.pin(), item.names) for item in objects.objects] == [
        ([-24, 8], ("pos",)),
        ([4, 4], ("row",)),
        ([8, 4], ("across",)),
        ([12, 4], ("down", "i")),
    ]


# --- 2. the record -----------------------------------------------------------------------


def _author(sibling: DebugSibling | None) -> tuple[bytes, Any]:
    seed = without_codeview(zi_object())
    return seed, build_function_validation_rewriting(
        donor=_extern_donor(),
        target_id="program",
        translation_unit_id="tu.fixture",
        build_target="program",
        symbol=TARGET_SYMBOL,
        seed_object=seed,
        donor_object=seed,
        reference_object=_rep_coff(REP_P),
        donor_debug_sibling=sibling,
    )


def test_a14_proves_a_donor_without_zi_through_its_debug_sibling() -> None:
    sibling = _sibling()
    seed, authored = _author(sibling)
    proof = authored.function.receipt.expected_values["function_validation.expected_proof"]
    assert proof["assumptions"] == ["a14"] and proof["frame_objects"] == [[-16, 16]]
    assert proof["frame_objects_from"] == "debug-sibling"
    composed = CoffObject(authored.candidate_object)
    assert bytes(coff_body(composed, composed.function_section(TARGET_SYMBOL))) == REP_P
    constraints = merge_candidate_constraints(
        authored.function.intervention, authored.function.receipt
    ).materialize()

    def dispatch(given: DebugSibling | None) -> Any:
        return ClassicFamilyDispatcher().dispatch(
            authored.function.intervention,
            ClassicDispatchMaterials(
                seed_object=seed,
                donor_object=seed,
                candidate_constraints=constraints,
                donor_debug_sibling=given,
            ),
        )

    candidate = dispatch(sibling)
    assert candidate.output == authored.candidate_object
    inputs = {
        item["name"]: item["digest"] for item in candidate.semantic_input_statement["binary_inputs"]
    }
    donor_id = authored.function.intervention.dependencies[0]
    assert inputs[f"dependency_debug_sibling:{donor_id}"] == Digest.from_bytes(
        sibling.object_payload or b""
    ).model_dump(mode="json")
    assert inputs[f"dependency_debug_sibling_types:{donor_id}"] == Digest.from_bytes(
        sibling.type_server or b""
    ).model_dump(mode="json")
    assert f"dependency_types:{donor_id}" not in inputs
    with pytest.raises(
        (ByteIdentityError, ClassicProjectError), match=r"no /Zi sibling compile is supplied"
    ):
        dispatch(None)


# --- 3. refusals -------------------------------------------------------------------------


def test_without_a_sibling_the_frame_objects_pass_cannot_run() -> None:
    with pytest.raises(
        DiscoveryAuthoringError,
        match=r"the frame-objects pass \(a14\) cannot run: .* compiles without /Zi, so it has "
        r"neither, and no /Zi sibling compile is supplied",
    ):
        _author(None)


def test_a_sibling_whose_compile_failed_is_its_refusal() -> None:
    with pytest.raises(
        DiscoveryAuthoringError,
        match=r"a14\) cannot run: .*the debug sibling \(the unit compiled with /Zi added\) "
        r"failed: its compile failed: C1001",
    ):
        _author(DebugSibling(None, None, "its compile failed: C1001"))


def test_a_sibling_whose_code_zi_changed_is_refused() -> None:
    # /Zi changed the code: the sibling's body is another body.
    with pytest.raises(
        DiscoveryAuthoringError,
        match=r"the debug sibling's '.*' differs from the donor's: /Zi changed its code",
    ):
        _author(_sibling(REP_P))


def test_a_sibling_whose_frame_record_differs_is_refused() -> None:
    other = zi_object(locals_words=8)
    with pytest.raises(DiscoveryAuthoringError, match=r"FPO record differs from the donor's"):
        _author(DebugSibling(other, _pdb(REP_TYPES)))


def test_a_sibling_whose_relocations_differ_is_refused() -> None:
    # The same bytes, but the sibling's function has a field the donor's does not.
    with pytest.raises(DiscoveryAuthoringError, match=r"relocations differ from the donor's"):
        _author(DebugSibling(zi_object(relocations=(1,)), _pdb(REP_TYPES)))


def test_a_sibling_without_codeview_is_refused() -> None:
    stripped = without_codeview(zi_object())
    with pytest.raises(DiscoveryAuthoringError, match=r"carries no CodeView symbols"):
        _author(DebugSibling(stripped, _pdb(REP_TYPES)))


def test_a_donor_with_codeview_reads_its_own_and_takes_no_sibling() -> None:
    donor = CoffObject(zi_object())
    primary = donor.function_section(TARGET_SYMBOL)
    with pytest.raises(ByteIdentityError, match=r"carries CodeView, so it needs no debug sibling"):
        sibling_frame_source(donor, primary, TARGET_SYMBOL, _sibling(), "x")


def test_a_debug_sibling_is_its_outputs_or_its_refusal() -> None:
    for outputs in ((b"obj", None, None), (None, None, None), (b"obj", b"pdb", "failed")):
        with pytest.raises(ByteIdentityError, match=r"its object and PDB, or the reason"):
            DebugSibling(*outputs)


# --- 4. grind and the build --------------------------------------------------------------


def test_grind_authors_through_the_sibling_and_the_build_composes_from_its_own(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import test_classic_frame_objects as fixture

    stripped = without_codeview(zi_object())
    monkeypatch.setattr(fixture, "_rep_coff", _stripped_seed(stripped))
    sibling = _sibling()
    seed, authored = _grind_rewriting(monkeypatch, None, sibling)
    assert seed == stripped
    proof = authored.function.receipt.expected_values["function_validation.expected_proof"]
    assert proof["frame_objects_from"] == "debug-sibling"

    composed = _compose(seed, authored, None, sibling)
    assert not composed.incomplete
    assert composed.output == authored.candidate_object
    (witness,) = composed.witnesses
    inputs = {
        item["name"]: item["digest"]
        for item in witness.semantic_proof.input_statement["binary_inputs"]
    }
    donor_id = authored.donor.intervention.id
    assert inputs[f"dependency_debug_sibling_types:{donor_id}"] == (
        Digest.from_bytes(sibling.type_server or b"").model_dump(mode="json")
    )
    # The build's own sibling must be the donor's code too.
    with pytest.raises((ByteIdentityError, ClassicProjectError), match=r"/Zi changed its code"):
        _compose(seed, authored, None, _sibling(REP_P))
    with pytest.raises((ByteIdentityError, ClassicProjectError), match=r"no /Zi sibling"):
        _compose(seed, authored, None, None)


def _stripped_seed(stripped: bytes) -> Any:
    """The fixture's objects with the donor (REP_D) compiled without /Zi."""

    def rep_coff(body: bytes) -> bytes:
        return stripped if body == REP_D else _rep_coff(body)

    return rep_coff
