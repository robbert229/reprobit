"""Whole-function proofs through switch tables, labels and recursive calls.

The programs are hand-encoded IA-32 (each listing is in the comment above
it).  The proof engine is exercised through `prove_function` with each
version's data tail (`Tail`); the record, its producer and authoring through
a COFF fixture whose function section carries ``$L`` label symbols, the
in-body relocations of its switch tables and CodeView label records.
"""

from __future__ import annotations

import struct

import pytest
from test_classic_register_bijection_reencoding_full import codeview_stream

from reprobit.binary import ByteIdentityError
from reprobit.classic.function_validation import Program, Tail, proof_summary, prove_function
from reprobit.classic.region_simulation import contradictory, lin, lin_atom
from reprobit.classic.rewriting_region_resize import resized_donor_object
from reprobit.coff_format import CoffObject, coff_body, detailed_relocations
from reprobit.discovery_authoring import DiscoveryAuthoringError, build_extern_run_donor
from reprobit.discovery_function_validation import build_function_validation_rewriting

SYMBOL = "_switch_fn"
UNIT = "tu.switch"
DIR32, REL32, SECREL, SECTION = 0x0006, 0x0014, 0x000B, 0x000A


def _code(text: str) -> bytes:
    return bytes.fromhex(text.replace(" ", ""))


def _table(*targets: int) -> bytes:
    return bytes(4 * len(targets))  # each entry's inline addend is 0


# 0: mov eax,[esp+4] / 4: cmp eax,2 / 7: ja 34 / 9: jmp [eax*4+T]
# 16: mov eax,10 / ret  22: mov eax,20 / ret  28: mov eax,30 / ret  34: xor eax,eax / ret
# tail at 37: lea ecx,[ecx+0] (fill), then T at 40: 16, 22, 28.
SWITCH_D = _code(
    "8b442404 83f802 7719 ff248500000000 b80a000000c3 b814000000c3 b81e000000c3 33c0c3"
)
SWITCH_D_TAIL = Tail(_code("8d4900") + _table(16, 22, 28), {12: 40, 40: 16, 44: 22, 48: 28})
# The index in ECX and the case bodies in another order: 16 returns 30, 22 returns 10,
# 28 returns 20, so T is 22, 28, 16.
SWITCH_P = _code(
    "8b4c2404 83f902 7719 ff248d00000000 b81e000000c3 b80a000000c3 b814000000c3 33c0c3"
)
SWITCH_P_TAIL = Tail(_code("8d4900") + _table(22, 28, 16), {12: 40, 40: 22, 44: 28, 48: 16})


def _prove(donor, donor_tail, image, image_tail, *, donor_relocations=None, image_relocations=None):
    return prove_function(
        donor,
        donor_relocations or {},
        image,
        image_relocations or {},
        {},
        "fixture",
        donor_tail=donor_tail,
        image_tail=image_tail,
    )


def test_a_switch_whose_tables_pair_its_cases_is_proved() -> None:
    proof = _prove(SWITCH_D, SWITCH_D_TAIL, SWITCH_P, SWITCH_P_TAIL)
    assert proof.switches == (1, 1)
    # Three cases and the default return; no pair of different indexes is compared.
    assert proof.returns == 4
    assert proof_summary(proof)["switch_reads"] == [1, 1]


def test_a_proof_without_a_switch_pins_nothing_new() -> None:
    ret = _code("33c0 c3")
    assert "switch_reads" not in proof_summary(prove_function(ret, {}, ret, {}, {}, "fixture"))


def test_a_table_that_sends_an_index_to_another_case_is_refused() -> None:
    wrong = Tail(SWITCH_P_TAIL.data, {12: 40, 40: 16, 44: 22, 48: 28})
    with pytest.raises(ByteIdentityError, match="eax differs at the return"):
        _prove(SWITCH_D, SWITCH_D_TAIL, SWITCH_P, wrong)


def test_a_switch_without_a_bound_check_is_refused() -> None:
    # 0: mov eax,[esp+4] / 4: jmp [eax*4+T] / 11: mov eax,10 / ret  17: xor eax,eax / ret
    unguarded = _code("8b442404 ff248500000000 b80a000000c3 33c0c3")
    tail = Tail(_table(11, 17), {7: 20, 20: 11, 24: 17})
    with pytest.raises(ByteIdentityError, match="not guarded by a bound check"):
        _prove(unguarded, tail, unguarded, tail)


def test_a_bound_beyond_the_table_is_refused() -> None:
    # cmp eax,3 against a table of three entries.
    loose = bytearray(SWITCH_D)
    loose[6] = 3
    with pytest.raises(ByteIdentityError, match="admits indexes up to 3, beyond its table of 3"):
        _prove(bytes(loose), SWITCH_D_TAIL, bytes(loose), SWITCH_D_TAIL)


def test_a_different_bound_check_is_refused() -> None:
    # The replacement sends index 2 to the default (cmp ecx,1; table of two).
    narrow = bytearray(SWITCH_P)
    narrow[6] = 1
    tail = Tail(_code("8d4900") + _table(22, 28) + bytes(4), {12: 40, 40: 22, 44: 28})
    with pytest.raises(ByteIdentityError):
        _prove(SWITCH_D, SWITCH_D_TAIL, bytes(narrow), tail)


# 0: mov ecx,[esp+4] / 4: cmp ecx,3 / 7: ja 36 / 9: xor eax,eax / 11: mov al,[ecx+X]
# 17: jmp [eax*4+T] / 24: mov eax,1 / ret  30: mov eax,2 / ret  36: xor eax,eax / ret
# tail at 39: nop, T at 40: 24, 30; X at 48: 0, 1, 1, 0.
INDEXED_D = _code(
    "8b4c2404 83f903 771b 33c0 8a8100000000 ff248500000000 b801000000c3 b802000000c3 33c0c3"
)
INDEXED_D_TAIL = Tail(
    _code("90") + _table(24, 30) + bytes([0, 1, 1, 0]), {13: 48, 20: 40, 40: 24, 44: 30}
)
# One direct table of four: 0: mov eax,[esp+4] / 4: cmp eax,3 / 7: ja 28 / 9: jmp [eax*4+T]
# 16: mov eax,1 / ret  22: mov eax,2 / ret  28: xor eax,eax / ret; T at 32: 16, 22, 22, 16.
DIRECT_P = _code("8b442404 83f803 7713 ff248500000000 b801000000c3 b802000000c3 33c0c3")
DIRECT_P_TAIL = Tail(_code("90") + _table(16, 22, 22, 16), {12: 32, 32: 16, 36: 22, 40: 22, 44: 16})


def test_an_index_table_agreeing_with_a_direct_table_is_proved() -> None:
    proof = _prove(INDEXED_D, INDEXED_D_TAIL, DIRECT_P, DIRECT_P_TAIL)
    assert proof.switches == (2, 1)


def test_an_index_table_that_differs_is_refused() -> None:
    data = _code("90") + _table(24, 30) + bytes([0, 1, 0, 0])
    with pytest.raises(ByteIdentityError, match="eax differs at the return"):
        _prove(INDEXED_D, Tail(data, INDEXED_D_TAIL.internal), DIRECT_P, DIRECT_P_TAIL)


def test_a_label_address_taken_as_data_is_refused() -> None:
    # 0: mov eax, offset L(=6) / 5: ret / 6: ret
    code = _code("b800000000 c3 c3")
    with pytest.raises(ByteIdentityError, match="label address taken as data"):
        Program(code, {}, "D", "fixture", tail=Tail(b"", {1: 6}))


def test_a_tail_that_is_not_fill_and_tables_is_refused() -> None:
    with pytest.raises(ByteIdentityError, match="alignment fill"):
        Program(
            SWITCH_D,
            {},
            "D",
            "fixture",
            tail=Tail(_code("cccccc") + _table(16, 22, 28), SWITCH_D_TAIL.internal),
        )
    stray = {**SWITCH_D_TAIL.internal, 37: 16}
    with pytest.raises(ByteIdentityError, match="no jump table's entries"):
        Program(SWITCH_D, {}, "D", "fixture", tail=Tail(SWITCH_D_TAIL.data, stray))
    with pytest.raises(ByteIdentityError, match="relocated entries"):
        Program(
            SWITCH_D, {}, "D", "fixture", tail=Tail(SWITCH_D_TAIL.data, {12: 40, 40: 16, 44: 22})
        )


def test_two_case_facts_on_one_index_contradict_each_other() -> None:
    v = lin_atom(("reg0", "eax"))
    assert contradictory([(("case", v, 1), True)], [(("case", v, 2), True)])
    assert not contradictory([(("case", v, 1), True)], [(("case", v, 1), True)])
    assert not contradictory([(("case", v, 1), True)], [(("case", lin(5), 2), True)])


# --- the record: a COFF function section with labels ---------------------------------


def _aux(*fields: tuple[str, int, int]) -> bytes:
    raw = bytearray(18)
    for fmt, at, value in fields:
        struct.pack_into(fmt, raw, at, value)
    return bytes(raw)


def switch_coff(
    body: bytes,
    *,
    proc: int | None = None,
    relocations: tuple[tuple[int, str, int], ...] = (),
    labels: tuple[tuple[str, int], ...] = (),
    debug_labels: tuple[tuple[int, str], ...] = (),
    stray_debug: str | None = None,
    recorded_proc: int | None = None,
    debug_end: int | None = None,
) -> bytes:
    """One function COMDAT (padded to 16 with NOP fill) with an FPO and CodeView closure.

    ``relocations`` are (offset, symbol, type) of the function section;
    ``labels`` the section's label symbols (storage class 6); each of
    ``debug_labels`` adds a CodeView record (S_LABEL32 0x0209 or
    S_LDATA32_ST 0x1007) whose offset and segment fields relocate to the
    named label.  ``recorded_proc`` writes a stale procedure size.
    """
    proc = len(body) if proc is None else proc
    raw = body + b"\x90" * ((-len(body)) % 16)
    size = proc if recorded_proc is None else recorded_proc
    stream = codeview_stream(size, 0, size - 1 if debug_end is None else debug_end)
    records = bytearray(stream[:-4])
    debug_rows: list[tuple[int, str, int]] = []
    for kind, name in debug_labels:
        at = len(records)
        if kind == 0x0209:
            payload = bytes(7) + bytes([1]) + b"L"
            field = 4
        else:
            payload = struct.pack("<I", 0x22) + bytes(6) + bytes([0])
            field = 8
        records += struct.pack("<HH", len(payload) + 2, kind) + payload
        debug_rows += [(at + field, name, SECREL), (at + field + 4, name, SECTION)]
    if stray_debug is not None:
        debug_rows.append((20, stray_debug, SECREL))
    debug_s = bytes(records) + stream[-4:]
    fpo = struct.pack("<IIIHBB", 0, size, 0, 1, 0, 0x14)
    symbols: list[tuple[str, int, int, int, int, bytes | None]] = [
        (
            ".text",
            0,
            1,
            0,
            3,
            _aux(("<I", 0, len(raw)), ("<H", 4, len(relocations)), ("<H", 6, 1), ("<B", 14, 2)),
        ),
        (".file", 0, -2, 0, 103, b"switch.c\0".ljust(18, b"\0")),
        (SYMBOL, 0, 1, 0x20, 2, None),  # aux filled below
        (".bf", 0, 1, 0, 101, _aux(("<H", 4, 10))),
        (".ef", size, 1, 0, 101, _aux(("<H", 4, 11))),
        (".debug$F", 0, 2, 0, 3, _aux(("<I", 0, len(fpo)), ("<H", 12, 1), ("<B", 14, 5))),
        (
            ".debug$S",
            0,
            3,
            0,
            3,
            _aux(("<I", 0, len(debug_s)), ("<H", 4, len(debug_rows)), ("<H", 12, 1), ("<B", 14, 5)),
        ),
        *[(name, value, 1, 0, 6, None) for name, value in labels],
        ("_g", 0, 0, 0x20, 2, None),
    ]
    index = {}
    count = 0
    for name, _value, _section, _type, storage, aux in symbols:
        if storage != 101:
            index.setdefault(name, count)
        count += 1 + (1 if aux is not None or name == SYMBOL else 0)
    section_inputs = [
        (
            ".text",
            raw,
            [(o, index[n], t) for o, n, t in relocations],
            struct.pack("<IH", index[SYMBOL], 0),
            0x60501020,
        ),
        (".debug$F", fpo, [(0, index[SYMBOL], 0x0007)], b"", 0x42101040),
        (".debug$S", debug_s, [(o, index[n], t) for o, n, t in debug_rows], b"", 0x42101048),
    ]
    cursor = 20 + 40 * len(section_inputs)
    payload = bytearray()
    headers = bytearray()
    line_pointer = 0
    for name, data, rows, lines, characteristics in section_inputs:
        raw_offset = cursor
        payload += data
        cursor += len(data)
        table = b"".join(struct.pack("<IIH", *row) for row in rows)
        relocation_offset = cursor if table else 0
        payload += table
        cursor += len(table)
        line_offset = cursor if lines else 0
        if lines:
            line_pointer = line_offset
        payload += lines
        cursor += len(lines)
        headers += name.encode().ljust(8, b"\0") + struct.pack(
            "<IIIIIIHHI",
            0,
            0,
            len(data),
            raw_offset,
            relocation_offset,
            line_offset,
            len(rows),
            len(lines) // 6,
            characteristics,
        )
    table = bytearray()
    strings = bytearray(4)
    for name, value, section, stype, storage, aux in symbols:
        if name == SYMBOL:
            aux = _aux(("<I", 4, size), ("<I", 8, line_pointer))
        encoded = name.encode()
        if len(encoded) <= 8:
            short = encoded.ljust(8, b"\0")
        else:
            short = b"\0\0\0\0" + struct.pack("<I", len(strings))
            strings += encoded + b"\0"
        table += short + struct.pack("<IhHBB", value, section, stype, storage, 1 if aux else 0)
        if aux:
            table += aux
    struct.pack_into("<I", strings, 0, len(strings))
    header = struct.pack("<HHIIIHH", 0x14C, len(section_inputs), 0, cursor, count, 0, 0)
    return bytes(header + headers + payload + table + strings)


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
        beneficiary_symbols=(SYMBOL,),
    )


def _author(seed: bytes, reference: bytes):
    return build_function_validation_rewriting(
        donor=_donor(),
        target_id="program",
        translation_unit_id=UNIT,
        build_target="program",
        symbol=SYMBOL,
        seed_object=seed,
        donor_object=seed,
        reference_object=reference,
    )


def _switch_object(
    code: bytes, tail: Tail, table: int, cases: tuple[int, ...], base_field: int
) -> bytes:
    names = [f"$L{target}" for target in cases]
    relocations = (
        (base_field, "$L900", DIR32),
        *((table + 4 * k, name, DIR32) for k, name in enumerate(names)),
    )
    labels = (("$L900", table), *dict.fromkeys((f"$L{t}", t) for t in cases))
    return switch_coff(
        code + tail.data,
        relocations=relocations,
        labels=tuple(dict.fromkeys(labels)),
        debug_labels=((0x1007, "$L900"),),
        proc=len(code) + len(tail.data),
        debug_end=len(code) - 1,
    )


# The donor's switch with two more bytes of fill before its table: its table
# lies at 40 + 4 = 44 when the code ends at 37 + 4 (a size gap of four).
def test_a_switch_is_authored_and_installed_with_the_references_table() -> None:
    donor_code = SWITCH_D[:34] + _code("33c0 8bc0 8bc0 c3")  # default: xor eax,eax; mov eax,eax x2
    donor_tail = Tail(_code("8d4900") + _table(16, 22, 28), {})
    seed = _switch_object(donor_code, donor_tail, 44, (16, 22, 28), 12)
    reference = _switch_object(SWITCH_P, SWITCH_P_TAIL, 40, (22, 28, 16), 12)
    authored = _author(seed, reference)
    composed = CoffObject(authored.candidate_object)
    section = composed.function_section(SYMBOL)
    reference_coff = CoffObject(reference)
    assert bytes(coff_body(composed, section)) == bytes(
        coff_body(reference_coff, reference_coff.function_section(SYMBOL))
    )
    places = {row["offset"]: row["target_value"] for row in detailed_relocations(composed, section)}
    assert places == {12: 40, 40: 22, 44: 28, 48: 16}
    spec = authored.function.intervention.parameters[0].value
    assert spec["donor_code_end"] == 41
    # Each case label keeps its place; the table's label moves with the shorter code.
    assert spec["replacement_labels"] == [[16, 16], [22, 22], [28, 28], [44, 40]]


def test_a_reference_with_stale_relocation_offsets_is_refused_precisely() -> None:
    seed = _switch_object(SWITCH_D, SWITCH_D_TAIL, 40, (16, 22, 28), 12)
    stale = _switch_object(SWITCH_P, SWITCH_P_TAIL, 40, (22, 28, 16), 13)
    with pytest.raises(DiscoveryAuthoringError, match="straddle its own instructions"):
        _author(seed, stale)


# 0: mov ecx,[esp+4] / 4: xor eax,eax / 6: add eax,ecx / 8: dec ecx / 9: jne 6 / 11: ret
LOOP_D = _code("8b4c2404 33c0 03c1 49 75fb c3")
# 0: mov edx,[esp+4] / 4: mov eax,0 / 9: add eax,edx / 11: dec edx / 12: jne 9 / 14: ret
LOOP_P = _code("8b542404 b800000000 03c2 4a 75fb c3")


def test_a_goto_label_named_by_its_codeview_record_follows_its_join() -> None:
    seed = switch_coff(LOOP_D, labels=(("$again$1", 6),), debug_labels=((0x0209, "$again$1"),))
    reference = switch_coff(
        LOOP_P, labels=(("$again$1", 9),), debug_labels=((0x0209, "$again$1"),), debug_end=13
    )
    authored = _author(seed, reference)
    assert authored.function.intervention.parameters[0].value["replacement_labels"] == [[6, 9]]
    composed = CoffObject(authored.candidate_object)
    assert bytes(coff_body(composed, composed.function_section(SYMBOL)))[: len(LOOP_P)] == LOOP_P


def test_a_goto_label_declared_away_from_its_join_is_refused() -> None:
    seed = switch_coff(LOOP_D, labels=(("$again$1", 6),), debug_labels=((0x0209, "$again$1"),))
    reference = switch_coff(
        LOOP_P, labels=(("$again$1", 11),), debug_labels=((0x0209, "$again$1"),), debug_end=13
    )
    with pytest.raises(DiscoveryAuthoringError, match="pairs its join with 9"):
        _author(seed, reference)


def test_a_closure_record_naming_an_offset_outside_a_label_record_is_refused() -> None:
    seed = switch_coff(
        LOOP_D,
        labels=(("$again$1", 6),),
        debug_labels=((0x0209, "$again$1"),),
        stray_debug="$again$1",
    )
    reference = switch_coff(
        LOOP_P, labels=(("$again$1", 9),), debug_labels=((0x0209, "$again$1"),), debug_end=13
    )
    with pytest.raises(DiscoveryAuthoringError, match="external entry besides its own"):
        _author(seed, reference)


def test_the_region_install_still_refuses_a_label_record() -> None:
    seed = switch_coff(LOOP_D, labels=(("$again$1", 6),), debug_labels=((0x0209, "$again$1"),))
    proof = {
        "offset_map": {0: 0, 6: 6, len(LOOP_D): len(LOOP_D)},
        "interiors": [],
        "proc_size": len(LOOP_D),
        "image_proc_size": len(LOOP_D),
        "relocation_reseat": [],
    }
    with pytest.raises(ByteIdentityError, match="may carry a code offset"):
        resized_donor_object(seed, SYMBOL, LOOP_D + b"\x90" * 4, proof, "fixture")


# 0: mov eax,[esp+4] / 4: test eax,eax / 6: je 18 / 8: dec eax / 9: push eax
# 10: call _switch_fn / 15: add esp,4 / 18: ret
RECURSE_D = _code("8b442404 85c0 740a 48 50 e800000000 83c404 c3")
# Through ECX: 0: mov ecx,[esp+4] / 4: test ecx,ecx / 6: mov eax,ecx / 8: je 20
# 10: dec ecx / 11: push ecx / 12: call _switch_fn / 17: add esp,4 / 20: ret
RECURSE_P = _code("8b4c2404 85c9 8bc1 740a 49 51 e800000000 83c404 c3")
# ... without 6: mov eax,ecx, so the zero path returns the entry EAX.
RECURSE_P_EAX = _code("8b4c2404 85c9 740a 49 51 e800000000 83c404 c3")


def test_a_recursive_call_is_a_call_of_the_function_itself() -> None:
    seed = switch_coff(RECURSE_D, relocations=((11, SYMBOL, REL32),))
    authored = _author(seed, switch_coff(RECURSE_P, relocations=((13, SYMBOL, REL32),)))
    spec = authored.function.intervention.parameters[0].value
    assert spec["replacement_relocations"] == [[13, 11]]
    with pytest.raises(DiscoveryAuthoringError, match="eax differs at the return"):
        _author(seed, switch_coff(RECURSE_P_EAX, relocations=((11, SYMBOL, REL32),)))


def test_a_relative_field_naming_a_label_is_refused() -> None:
    seed = switch_coff(RECURSE_D, relocations=((11, "$L18", REL32),), labels=(("$L18", 18),))
    reference = switch_coff(RECURSE_P, relocations=((13, "$L18", REL32),), labels=(("$L18", 20),))
    with pytest.raises(DiscoveryAuthoringError, match="not the function itself"):
        _author(seed, reference)


def test_a_reference_with_a_stale_procedure_size_is_measured_from_its_body() -> None:
    # The reference's FPO and CodeView records state the donor's size (12);
    # its code is 15 bytes, ending in the donor's epilogue (ret).
    seed = switch_coff(LOOP_D)
    reference = switch_coff(LOOP_P, recorded_proc=len(LOOP_D), debug_end=len(LOOP_D) - 1)
    authored = _author(seed, reference)
    spec = authored.function.intervention.parameters[0].value
    assert spec["replacement_debug_end"] == len(LOOP_P) - 1
