"""Units compiled without /Gy or /Zi: the function-isolated view and the producers on it.

The objects here are written the way MSVC 5.0 writes a unit compiled without
``/Gy``: every function in one plain ``.text`` section, each padded with NOP
fill to a 16-byte multiple, their FPO records in one plain ``.debug$F``
section and, with ``/Zi``, one line group and one procedure block per
function in the shared line table and ``.debug$S`` stream.  The references
are the producers' own ``/Zi`` ``/Gy`` fixtures, as a grind's are.
"""

from __future__ import annotations

import struct
from dataclasses import dataclass, field

import pytest
import test_classic_instruction_schedule_full as schedule_fixture
import test_classic_register_bijection_reencoding_full as bijection_fixture

from reprobit.binary import ByteIdentityError
from reprobit.classic.coff import FPO_ONLY_CLOSURE, _comdat_child_closure, is_fpo_closure
from reprobit.classic.scheduling_certificates import measure_instruction_schedule_debug_envelope
from reprobit.classic_donors import merge_candidate_constraints
from reprobit.classic_project import ClassicDispatchMaterials, ClassicFamilyDispatcher
from reprobit.coff_format import (
    CoffObject,
    carries_codeview,
    codeview_blind_seat,
    coff_body,
    coff_table,
    detailed_relocations,
    section_definitions,
    structural_seat,
)
from reprobit.coff_function_view import defined_in_plain_text, isolate_functions
from reprobit.discovery_authoring import (
    build_donor_equal_body,
    build_extern_run_donor,
)
from reprobit.discovery_grind import isolated_grind_objects
from reprobit.intervention_metadata import ClassicRecipeFamily
from reprobit.msvc_discovery_coff import qualify_msvc_reference_object
from reprobit.schema import ClassicRecipeIntervention

UNIT = "tu.fixture"
DATA_SYMBOL = "_fixture_data"
CALLEE = "_fixture_callee"
FILL = 0x90
DATA_EXTERNALS = frozenset({bijection_fixture.NIL_SYMBOL})


@dataclass(frozen=True)
class Function:
    name: str
    body: bytes
    static: bool = False
    # (offset, target symbol, relocation type)
    relocations: tuple[tuple[int, str, int], ...] = ()
    # (cdwLocals, cdwParams, cbProlog, packed bits), or None for no FPO record
    fpo: tuple[int, int, int, int] | None = (0, 1, 0, 0)
    # (offset, line) rows, written only with /Zi
    lines: tuple[tuple[int, int], ...] = ((0, 3),)
    debug_range: tuple[int, int] | None = None
    labels: tuple[tuple[str, int], ...] = ()


@dataclass
class _Builder:
    sections: list[dict] = field(default_factory=list)
    symbols: list[tuple[str, int, int, int, int, bytes | None]] = field(default_factory=list)


def _aux(length, relocations, lines, selection=0, associated=0):
    out = bytearray(18)
    struct.pack_into("<IHHIHB", out, 0, length, relocations, lines, 0, associated, selection)
    return bytes(out)


def _padded(body: bytes) -> bytes:
    return body + bytes([FILL]) * (-len(body) % 16)


def _proc_block(length: int, start: int, end: int) -> bytes:
    """An S_GPROC32 record and its S_END, as MSVC 5.0 writes them in objects."""

    # pParent, pEnd, pNext, length, debug start and end, type, offset, segment, flags
    proc = bytearray(35)
    struct.pack_into("<III", proc, 12, length, start, end)
    name = b"fixture"
    payload = bytes(proc) + bytes([len(name)]) + name
    return struct.pack("<HH", len(payload) + 2, 0x100B) + payload + struct.pack("<HH", 2, 0x0006)


def plain_object(functions: list[Function], *, codeview: bool = False) -> bytes:
    """One object as MSVC 5.0 writes a unit compiled without /Gy (and with /Zi if asked)."""

    offsets = []
    text = bytearray()
    for function in functions:
        offsets.append(len(text))
        text += _padded(function.body)
    externals = sorted(
        {target for function in functions for _, target, _ in function.relocations}
        - {function.name for function in functions}
        - {DATA_SYMBOL}
    )
    # Symbol table, by index.
    names: list[
        tuple[str, int, int, int, int, int]
    ] = []  # name, value, section, type, storage, naux
    index_of: dict[str, int] = {}

    def add(name, value, section, kind, storage, naux=0):
        index_of.setdefault(name, len(names) + sum(item[5] for item in names))
        names.append((name, value, section, kind, storage, naux))

    sections = [".drectve", ".text", ".data", ".debug$F"] + ([".debug$S"] if codeview else [])
    for number, name in enumerate(sections, start=1):
        add(f"{name}#{number}", 0, number, 0, 3, 1)
    for function, start in zip(functions, offsets, strict=True):
        add(function.name, start, 2, 0x20, 3 if function.static else 2, 1 if codeview else 0)
        for label, at in function.labels:
            add(label, start + at, 2, 0, 6)
        if codeview:
            add(f".bf#{function.name}", start, 2, 0, 101, 1)
            add(f".lf#{function.name}", len(function.lines) + 1, 2, 0, 101)
            add(f".ef#{function.name}", start + len(function.body), 2, 0, 101, 1)
    add(DATA_SYMBOL, 0, 3, 0, 2)
    for name in externals:
        add(name, 0, 0, 0 if name in DATA_EXTERNALS else 0x20, 2)

    def symbol_index(name: str) -> int:
        return index_of[name]

    text_rows = bytearray()
    lines = bytearray()
    fpo = bytearray()
    fpo_rows = bytearray()
    stream = bytearray(b"\x02\0\0\0")
    stream_rows = bytearray()
    line_groups: dict[str, int] = {}
    for function, start in zip(functions, offsets, strict=True):
        for offset, target, kind in function.relocations:
            text_rows += struct.pack("<IIH", start + offset, symbol_index(target), kind)
        if function.fpo is not None:
            locals_, params, prolog, packed = function.fpo
            fpo_rows += struct.pack("<IIH", len(fpo), symbol_index(function.name), 7)
            fpo += struct.pack("<IIIHBB", 0, len(function.body), locals_, params, prolog, packed)
        if codeview:
            line_groups[function.name] = len(lines) // 6
            lines += struct.pack("<IH", symbol_index(function.name), 0)
            for offset, line in function.lines:
                lines += struct.pack("<IH", start + offset, line)
            debug_start, debug_end = function.debug_range or (0, len(function.body) - 1)
            at = len(stream)
            stream += _proc_block(len(function.body), debug_start, debug_end)
            stream_rows += struct.pack("<IIH", at + 32, symbol_index(function.name), 0x0B)
            stream_rows += struct.pack("<IIH", at + 36, symbol_index(function.name), 0x0A)
    directive = b"-defaultlib:LIBC "
    payloads = [
        (directive, b"", b"", 0x00100A00),
        (bytes(text), bytes(text_rows), bytes(lines), 0x60500020),
        (b"\0\0\0\0", b"", b"", 0xC0300040),
        (bytes(fpo), bytes(fpo_rows), b"", 0x42100048),
    ]
    if codeview:
        payloads.append((bytes(stream), bytes(stream_rows), b"", 0x42100048))
    cursor = 20 + 40 * len(payloads)
    headers = bytearray()
    data = bytearray()
    line_pointer = 0
    for number, (raw, rows, line_rows, characteristics) in enumerate(payloads, start=1):
        pointers = []
        for part in (raw, rows, line_rows):
            pointers.append(cursor if part else 0)
            data += part
            cursor += len(part)
        if number == 2:
            line_pointer = pointers[2]
        name = sections[number - 1].encode().ljust(8, b"\0")
        headers += name + struct.pack(
            "<IIIIIIHHI",
            0,
            0,
            len(raw),
            pointers[0],
            pointers[1],
            pointers[2],
            len(rows) // 10,
            len(line_rows) // 6,
            characteristics,
        )
    records = bytearray()
    strings = bytearray()
    for name, value, section, kind, storage, naux in names:
        plain = name.split("#")[0]
        encoded = plain.encode()
        if len(encoded) <= 8:
            short = encoded.ljust(8, b"\0")
        else:
            short = struct.pack("<II", 0, 4 + len(strings))
            strings += encoded + b"\0"
        records += short + struct.pack("<IhHBB", value, section, kind, storage, naux)
        if not naux:
            continue
        if kind == 0x20:
            function = next(item for item in functions if item.name == plain)
            pointer = line_pointer + 6 * line_groups[plain]
            records += struct.pack("<IIII", 0, len(function.body), pointer, 0) + b"\0\0"
        elif plain in (".bf", ".ef"):
            records += struct.pack("<IHHII", 0, 1, 0, 0, 0) + b"\0\0"
        else:
            raw, rows, line_rows, _ = payloads[section - 1]
            records += _aux(len(raw), len(rows) // 10, len(line_rows) // 6)
    header = struct.pack("<HHIIIHH", 0x14C, len(payloads), 0, cursor, len(records) // 18, 0, 0)
    return bytes(header + headers + data + records + struct.pack("<I", 4 + len(strings)) + strings)


# 0: mov ecx,[esp+4] / 4: xor eax,eax / 6: test ecx,ecx / 8: jle 15
# 10: add eax,ecx / 12: dec ecx / 13: jne 10 / 15: ret; and with EDX for ECX.
SUM_D = bytes.fromhex("8b4c240433c085c97e0503c14975fbc3")
SUM_P = bytes.fromhex("8b54240433c085d27e0503c24a75fbc3")
HELPER = bytes.fromhex("8b442404c3")  # mov eax,[esp+4] / ret
CALLER = bytes.fromhex("6a01e800000000 83c404 a100000000 c3".replace(" ", ""))


def _neighbours(target: Function) -> list[Function]:
    """The target between a static helper before it and an external caller after it."""

    return [
        Function("_fixture_helper", HELPER, static=True),
        target,
        Function(
            "_fixture_caller",
            CALLER,
            relocations=((3, "_fixture_helper", 0x14), (11, DATA_SYMBOL, 0x06)),
        ),
    ]


def _extern_donor(symbol):
    return build_extern_run_donor(
        target_id="program",
        translation_unit_id=UNIT,
        build_target="program",
        header_prefix="ReproBitPad",
        header_count=1,
        seat_prefix="ReproBitPadSeat",
        seat_count=0,
        width=3,
        beneficiary_symbols=(symbol,),
    )


def _range(data: bytes, symbol: str) -> bytes:
    coff = CoffObject(data)
    item = next(item for item in coff.symbols.values() if item["name"] == symbol)
    text = coff.sections[item["section"] - 1]
    starts = sorted(
        other["value"]
        for other in coff.symbols.values()
        if other["section"] == item["section"] and other["type"] == 0x20
    )
    later = [value for value in starts if value > item["value"]]
    end = later[0] if later else text["raw_size"]
    return bytes(coff_body(coff, text))[item["value"] : end]


def _install(authored, seed: bytes, donor: bytes) -> bytes:
    """Replay a record through its schema and the build dispatcher on the real objects."""

    intervention = ClassicRecipeIntervention.model_validate_json(
        authored.function.intervention.model_dump_json()
    )
    constraints = merge_candidate_constraints(intervention, authored.function.receipt).materialize()
    candidate = ClassicFamilyDispatcher().dispatch(
        intervention,
        ClassicDispatchMaterials(
            seed_object=seed,
            donor_object=donor,
            target_donor_object=donor,
            candidate_constraints=constraints,
        ),
    )
    assert "function_isolation" in candidate.proof
    return candidate.output


def _require_only_the_target_moved(seed: bytes, output: bytes, symbol: str, image: bytes) -> None:
    assert _range(output, symbol) == _padded(image)
    for other in ("_fixture_helper", "_fixture_caller"):
        assert _range(output, other) == _range(seed, other)
    before, after = CoffObject(seed), CoffObject(output)
    for left, right in zip(before.sections, after.sections, strict=True):
        if left["name"] != ".text" and left["name"] != ".debug$F":
            assert coff_body(before, left) == coff_body(after, right)


# --- the view --------------------------------------------------------------------


@pytest.mark.parametrize("codeview", [False, True])
def test_every_function_becomes_its_own_comdat_and_the_view_projects_back(codeview) -> None:
    target = Function(
        "_fixture_target",
        SUM_D,
        lines=((0, 5), (4, 6)),
        labels=(("$L100", 10),),
    )
    data = plain_object(_neighbours(target), codeview=codeview)
    assert defined_in_plain_text(data, "_fixture_target")
    isolated = isolate_functions(data)
    view = CoffObject(isolated.view)
    definitions = section_definitions(view)
    for function in _neighbours(target):
        primary = view.function_section(function.name)
        assert primary["characteristics"] == 0x60501020
        assert definitions[primary["number"]]["selection"] == 1
        assert bytes(coff_body(view, primary)) == _padded(function.body)
        expected = (2, (".debug$F", ".debug$S")) if codeview else FPO_ONLY_CLOSURE
        assert _comdat_child_closure(view, primary) == expected
    caller = view.function_section("_fixture_caller")
    assert [(row["offset"], row["target"]) for row in detailed_relocations(view, caller)] == [
        (3, "_fixture_helper"),
        (11, DATA_SYMBOL),
    ]
    label = next(item for item in view.symbols.values() if item["name"] == "$L100")
    assert label["section"] == view.function_section("_fixture_target")["number"]
    assert label["value"] == 10
    if codeview:
        primary = view.function_section("_fixture_target")
        assert coff_table(view, primary, "lines")[6:] == struct.pack("<IHIH", 0, 5, 4, 6)
        # Its procedure block, relocated to the function, is its .debug$S child.
        child = next(
            section
            for section in view.sections
            if section["name"] == ".debug$S"
            and section_definitions(view).get(section["number"], {}).get("associated")
            == primary["number"]
        )
        assert [row["target"] for row in detailed_relocations(view, child)] == [
            "_fixture_target",
            "_fixture_target",
        ]
    assert isolated.project(isolated.view) == data


def _rewritten_view(data: bytes, symbol: str, body: bytes) -> bytes:
    """The view with one function's COMDAT body replaced by ``body`` (resized if needed)."""

    view = bytearray(isolate_functions(data).view)
    coff = CoffObject(bytes(view))
    primary = coff.function_section(symbol)
    start = primary["raw_offset"]
    old = primary["raw_size"]
    view[start : start + old] = body
    delta = len(body) - old
    out = CoffObject(bytes(view)) if delta == 0 else None
    if out is not None:
        return bytes(view)
    # Shift every later file pointer and restate the section's size.
    header = primary["header_offset"]
    struct.pack_into("<I", view, header + 16, len(body))
    for section in coff.sections:
        at = section["header_offset"]
        for field_at, key in ((20, "raw_offset"), (24, "relocation_offset"), (28, "line_offset")):
            if section[key] > start:
                struct.pack_into("<I", view, at + field_at, section[key] + delta)
    struct.pack_into("<I", view, 8, coff.symbol_offset + delta)
    return bytes(view)


def test_a_replaced_body_goes_back_into_its_own_range_only() -> None:
    data = plain_object(_neighbours(Function("_fixture_target", SUM_D)))
    composed = _rewritten_view(data, "_fixture_target", _padded(SUM_P))
    projected = isolate_functions(data).project(composed)
    _require_only_the_target_moved(data, projected, "_fixture_target", SUM_P)
    assert isolate_functions(projected).view == composed


def test_a_shorter_body_keeps_its_range_with_nop_fill() -> None:
    long_body = bytes.fromhex("33c0") * 9 + b"\xc3"  # 19 bytes: a 32-byte range
    short_body = bytes.fromhex("33c0") * 8 + b"\xc3"  # 17 bytes: still a 32-byte range
    data = plain_object(_neighbours(Function("_fixture_target", long_body)))
    projected = isolate_functions(data).project(
        _rewritten_view(data, "_fixture_target", short_body)
    )
    assert _range(projected, "_fixture_target") == _padded(short_body)
    assert len(_range(projected, "_fixture_target")) == 32


def test_a_body_that_outgrows_its_range_is_refused() -> None:
    data = plain_object(_neighbours(Function("_fixture_target", SUM_D)))
    composed = _rewritten_view(data, "_fixture_target", SUM_D + b"\x90")
    with pytest.raises(ByteIdentityError, match="does not fit its 16-byte range"):
        isolate_functions(data).project(composed)


def test_a_change_outside_the_functions_is_refused() -> None:
    data = plain_object(_neighbours(Function("_fixture_target", SUM_D)))
    view = bytearray(isolate_functions(data).view)
    coff = CoffObject(bytes(view))
    data_section = next(section for section in coff.sections if section["name"] == ".data")
    view[data_section["raw_offset"]] ^= 0xFF
    with pytest.raises(ByteIdentityError, match="not the view of any object"):
        isolate_functions(data).project(bytes(view))


def test_a_relocation_naming_a_view_only_symbol_is_refused() -> None:
    data = plain_object(_neighbours(Function("_fixture_target", SUM_D)))
    view = bytearray(isolate_functions(data).view)
    coff = CoffObject(bytes(view))
    caller = coff.function_section("_fixture_caller")
    struct.pack_into("<I", view, caller["relocation_offset"] + 4, coff.symbol_count - 2)
    with pytest.raises(ByteIdentityError, match="only the view defines"):
        isolate_functions(data).project(bytes(view))


def test_bytes_before_the_first_function_are_refused() -> None:
    data = bytearray(plain_object(_neighbours(Function("_fixture_target", HELPER))))
    coff = CoffObject(bytes(data))
    helper = next(
        index for index, item in coff.symbols.items() if item["name"] == "_fixture_helper"
    )
    struct.pack_into("<I", data, coff.symbol_offset + helper * 18 + 8, 1)
    with pytest.raises(ByteIdentityError, match="before its first function"):
        isolate_functions(bytes(data))


def test_a_relocation_straddling_two_functions_is_refused() -> None:
    first = Function("_first", bytes.fromhex("33c0c3"), relocations=((14, "_second", 0x14),))
    data = plain_object([first, Function("_second", HELPER)])
    with pytest.raises(ByteIdentityError, match="straddles two functions"):
        isolate_functions(data)


# --- debug formats -----------------------------------------------------------------


def test_the_fpo_record_alone_is_a_closure_only_without_codeview() -> None:
    without = CoffObject(isolate_functions(plain_object(_neighbours(Function("_t", HELPER)))).view)
    assert not carries_codeview(without)
    assert is_fpo_closure(without, FPO_ONLY_CLOSURE)
    with_codeview = CoffObject(bijection_fixture.make_coff())
    assert carries_codeview(with_codeview)
    assert not is_fpo_closure(with_codeview, FPO_ONLY_CLOSURE)


def test_without_codeview_the_procedure_range_is_the_fpo_records() -> None:
    body = schedule_fixture.BODY + b"\x90" * 4  # a whole 32-byte range: FPO sizes it
    target = Function("_t", body, fpo=(0, 1, 2, 0))
    view = CoffObject(isolate_functions(plain_object(_neighbours(target))).view)
    envelope = measure_instruction_schedule_debug_envelope(view, view.function_section("_t"), "x")
    assert envelope["procedure_range"] == [len(body), 2]
    assert envelope["code_symbol_references"] == [[".debug$F", "_t", 0]]


def test_seats_compare_across_debug_formats_and_layouts() -> None:
    reference = CoffObject(bijection_fixture.make_coff())
    debug = next(section for section in reference.sections if section["name"] == ".debug$S")
    with pytest.raises(ByteIdentityError, match="CodeView section"):
        codeview_blind_seat(reference, debug["number"])
    assert codeview_blind_seat(reference, len(reference.sections)) == len(reference.sections) - 1
    view = CoffObject(isolate_functions(plain_object(_neighbours(Function("_t", HELPER)))).view)
    seat = structural_seat(view, view.function_section("_t")["number"])
    assert seat == ("comdat", ("_t", 0x20, 2, ".text", 1, (".debug$F",)))
    assert structural_seat(view, 3) == ("plain", ".data", 0xC0300040, 0)


# --- each producer on a unit compiled without /Gy (and without /Zi) ----------------


def _reference(target: Function) -> bytes:
    """A /Zi /Gy compile of the unit with the target's reference body, as a grind's."""

    return isolate_functions(plain_object(_neighbours(target), codeview=True)).view


def _author_on_views(build, seed, donor, reference, symbol, **extra):
    seed_view, donor_view, isolated = isolated_grind_objects(seed, donor, symbol)
    assert isolated
    authored = build(
        donor=_extern_donor(symbol),
        target_id="program",
        translation_unit_id=UNIT,
        build_target="program",
        symbol=symbol,
        seed_object=seed_view,
        donor_object=donor_view,
        **({"reference_object": reference} if reference is not None else {}),
        **extra,
    )
    return authored


def _qualify(reference: bytes, candidate: bytes, symbol: str) -> None:
    qualify_msvc_reference_object(
        reference_object=reference, candidate_object=candidate, symbol=symbol, isolated=True
    )


@pytest.mark.parametrize("codeview", [False, True])
def test_the_strict_equal_body_splice_installs_into_a_shared_text_section(codeview) -> None:
    symbol = schedule_fixture.TARGET_SYMBOL
    seed = plain_object(_neighbours(Function(symbol, schedule_fixture.BODY)), codeview=codeview)
    donor = plain_object(_neighbours(Function(symbol, schedule_fixture.IMAGE)), codeview=codeview)
    reference = _reference(Function(symbol, schedule_fixture.IMAGE, fpo=(0, 1, 2, 0)))
    authored = _author_on_views(build_donor_equal_body, seed, donor, None, symbol)
    assert authored.function.intervention.family is ClassicRecipeFamily.EQUAL_BODY_STRICT
    _qualify(reference, authored.candidate_object, symbol)
    output = _install(authored, seed, donor)
    _require_only_the_target_moved(seed, output, symbol, schedule_fixture.IMAGE)
