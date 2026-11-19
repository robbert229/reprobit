"""Equivalences a whole-function proof admits in its second pass (a10).

`function_validation.prove_function` runs every proof first exactly as the
records made before were proved; only when that refuses does it run again
with the normal forms of `region_simulation._equivalences` and the object
model of a10 (`region_simulation.ObjectModel`).  The programs are
hand-encoded IA-32 assembled with GNU as (each listing in the comment above
it; a call's PC-relative field holds 0, the addend the closed set admits):

1. A compiler helper's return address is a code address: the function's
   entry plus the offset after the call, one value in both versions when
   the calls end at the same offset (``mov eax, n; call __chkstk``).
2. Distinct objects: the own frame, an undefined external and each section
   of this object; a read-only section's data no store reaches.
3. x87 commutation: two registers commute (already, since PR #28); a memory
   operand is not the loaded register, so two memory operands never
   commute (`tests/fixtures/x87_probe/memory_operands.out`).
4. Products modulo 2**32: constant factors and nested factors normalised.
5. Shared-frame slots that are never addressed are still memory: refused.
6. A store whose bytes a later store overwrites leaves no trace.
7. An undefined x87 condition bit named without the memory operand's
   address.
8. EAX at the return is compared whatever the function's type.
"""

from __future__ import annotations

import subprocess
from pathlib import Path
from types import SimpleNamespace
from typing import Any

import pytest
from test_classic_function_validation import _coff, _extern_donor
from test_classic_helper_and_vtable_calls import _helpers
from test_classic_register_bijection_reencoding_full import TARGET_SYMBOL

from reprobit.binary import ByteIdentityError
from reprobit.classic.function_validation import (
    FrameFacts,
    FrameModel,
    ValidationProof,
    object_model,
    prove_function,
)
from reprobit.classic.region_simulation import (
    CODE_ENTRY,
    ObjectModel,
    PathState,
    SymbolObject,
    _Undefined,
    address_relation,
    lin,
    lin_atom,
    product,
    run_helper,
    simulate_region,
)
from reprobit.classic_donors import merge_candidate_constraints
from reprobit.classic_project import ClassicDispatchMaterials, ClassicFamilyDispatcher
from reprobit.discovery_function_validation import (
    _pair_relocations,
    build_function_validation_rewriting,
)

PROBE = Path(__file__).parent / "fixtures" / "x87_probe"
ESP0 = ("reg0", "esp")
# Any object model turns the second pass on; these name the fixtures' symbols.
EXTERNS = ObjectModel(
    {name: SymbolObject(("extern", name), 0, None) for name in ("_a", "_b", "_c")}, 4
)


def _code(text: str) -> bytes:
    return bytes.fromhex(text.replace(" ", ""))


def _prove(
    donor: bytes,
    image: bytes,
    relocations: dict[int, Any] | None = None,
    image_relocations: dict[int, Any] | None = None,
    *,
    objects: ObjectModel | None = EXTERNS,
    frame: FrameFacts | None = None,
    helpers: dict[str, Any] | None = None,
) -> ValidationProof:
    return prove_function(
        donor,
        relocations or {},
        image,
        image_relocations if image_relocations is not None else relocations or {},
        {},
        "fixture",
        private_frame=frame,
        helpers=helpers,
        objects=objects,
    )


def _both_passes_refuse(*args: Any, match: str, **kwargs: Any) -> None:
    for objects in (None, kwargs.pop("objects", EXTERNS)):
        with pytest.raises(ByteIdentityError, match=match):
            _prove(*args, objects=objects, **kwargs)


def _only_the_second_pass_proves(*args: Any, **kwargs: Any) -> ValidationProof:
    objects = kwargs.pop("objects", EXTERNS)
    with pytest.raises(ByteIdentityError):
        _prove(*args, objects=None, **kwargs)
    proof = _prove(*args, objects=objects, **kwargs)
    assert proof.frame.equivalences
    return proof


# --- 1. a compiler helper's return address ---------------------------------------------

# 0: mov eax,0x2000 / 5: call __chkstk / 10: lea ecx,[esp] / 13: push ecx / 14: call _g
# 19: add esp,0x2004 / 25: ret
CHKSTK_D = _code("b800200000 e800000000 8d0c24 51 e800000000 81c404200000 c3")
CHKSTK_D_RELOCATIONS = {6: ("rel32", "__chkstk"), 15: ("rel32", "_g")}
# 10: mov edx,esp / 12: push edx / 13: call _g / 18: add esp,0x2004 / 24: ret
CHKSTK_P = _code("b800200000 e800000000 89e2 52 e800000000 81c404200000 c3")
CHKSTK_P_RELOCATIONS = {6: ("rel32", "__chkstk"), 14: ("rel32", "_g")}
# ... with a nop first, so the helper returns to offset 11.
CHKSTK_P_LATE = _code("90 b800200000 e800000000 89e2 52 e800000000 81c404200000 c3")
CHKSTK_P_LATE_RELOCATIONS = {7: ("rel32", "__chkstk"), 15: ("rel32", "_g")}


def test_the_probe_return_address_left_in_a_shared_frame_is_one_code_address() -> None:
    # The word __chkstk's call leaves at ESP0-4 lies inside the frame it
    # allocates, and the call to _g names it in its store log: the entry
    # address plus 10 in both versions.
    proof = _only_the_second_pass_proves(
        CHKSTK_D,
        CHKSTK_P,
        CHKSTK_D_RELOCATIONS,
        CHKSTK_P_RELOCATIONS,
        helpers=_helpers("__chkstk"),
    )
    assert not proof.frame.private


def test_a_probe_call_ending_at_another_offset_leaves_another_word() -> None:
    _both_passes_refuse(
        CHKSTK_D,
        CHKSTK_P_LATE,
        CHKSTK_D_RELOCATIONS,
        CHKSTK_P_LATE_RELOCATIONS,
        helpers=_helpers("__chkstk"),
        match="make different calls",
    )


def test_the_return_address_is_the_entry_plus_the_offset_after_the_call() -> None:
    helper = _helpers("__chkstk")["__chkstk"]
    pushed = []
    for frame in (None, FrameModel(FrameFacts(False, equivalences=True), context="fixture")):
        state = PathState({name: lin_atom(("reg0", name)) for name in _REGS}, {})
        state.regs["eax"] = lin(16)
        state.frame = frame
        run_helper(state, helper, _Undefined("D"), "fixture", 10)
        pushed.append([value for _address, _width, value in state.stores])
    # The first store is the call's return address (the probe then saves ECX).
    assert pushed[1][0] == lin(10, ((CODE_ENTRY, 1),))
    assert pushed[0][0][2][0][0][0] == "retaddr"  # a region proof's fresh atom


_REGS = ("eax", "ecx", "edx", "ebx", "esp", "ebp", "esi", "edi")


# --- 2. distinct objects ----------------------------------------------------------------

# 0: mov dword [_a],1 / 10: mov dword [_b],2 / 20: call _g / 25: ret
GLOBALS_D = _code("c705 00000000 01000000 c705 00000000 02000000 e800000000 c3")
GLOBALS_D_RELOCATIONS = {2: "_a", 12: "_b", 21: ("rel32", "_g")}
# The two stores in the other order.
GLOBALS_P = _code("c705 00000000 02000000 c705 00000000 01000000 e800000000 c3")
GLOBALS_P_RELOCATIONS = {2: "_b", 12: "_a", 21: ("rel32", "_g")}
# 0: mov dword [_a],2 / 10: push 1 / 12: call _g / 17: add esp,4 / 20: ret
STACK_D = _code("c705 00000000 02000000 6a01 e800000000 83c404 c3")
STACK_D_RELOCATIONS = {2: "_a", 13: ("rel32", "_g")}
# 0: push 1 / 2: mov dword [_a],2 / 12: call _g / 17: add esp,4 / 20: ret
STACK_P = _code("6a01 c705 00000000 02000000 e800000000 83c404 c3")
STACK_P_RELOCATIONS = {4: "_a", 13: ("rel32", "_g")}
# 0: mov eax,[esp+4] / 4: mov dword [eax],1 / 10: mov ecx,[_c] / 16: mov [eax+4],ecx / 19: ret
LITERAL_D = _code("8b442404 c70001000000 8b0d00000000 894804 c3")
# The load of _c before the store through the pointer.
LITERAL_P = _code("8b442404 8b0d00000000 c70001000000 894804 c3")


def _section_model(*, writable: bool, size: int = 8) -> ObjectModel:
    base = ("section", 2)
    return ObjectModel(
        {"_c": SymbolObject(base, 0, size), "_d": SymbolObject(base, 2, size)},
        4,
        frozenset() if writable else frozenset({base}),
    )


def test_stores_to_two_externals_in_either_order_leave_the_same_memory() -> None:
    _only_the_second_pass_proves(GLOBALS_D, GLOBALS_P, GLOBALS_D_RELOCATIONS, GLOBALS_P_RELOCATIONS)


def test_a_global_store_moves_past_a_push_onto_the_own_frame() -> None:
    _only_the_second_pass_proves(STACK_D, STACK_P, STACK_D_RELOCATIONS, STACK_P_RELOCATIONS)


def test_read_only_data_is_read_past_a_store_through_a_pointer() -> None:
    _only_the_second_pass_proves(
        LITERAL_D, LITERAL_P, {12: "_c"}, {6: "_c"}, objects=_section_model(writable=False)
    )


def test_writable_data_is_not_read_past_a_store_through_a_pointer() -> None:
    # The pointer may hold _c's address: the load depends on the store.
    _both_passes_refuse(
        LITERAL_D,
        LITERAL_P,
        {12: "_c"},
        {6: "_c"},
        objects=_section_model(writable=True),
        match="leave different memory",
    )


def test_an_external_is_not_read_past_a_store_through_a_pointer() -> None:
    _both_passes_refuse(LITERAL_D, LITERAL_P, {12: "_c"}, {6: "_c"}, match="leave different memory")


def _sym(name: str, offset: int = 0) -> Any:
    return lin(offset, ((("sym", name), 1),))


def _stack(offset: int) -> Any:
    return lin(offset, ((ESP0, 1),))


@pytest.mark.parametrize(
    ("left", "right", "relation"),
    [
        # Distinct undefined externals, and the own frame against either.
        ((_sym("_a"), 4), (_sym("_b", 8), 4), "disjoint"),
        ((_stack(-8), 4), (_sym("_a", 12), 4), "disjoint"),
        # The stack above the parameter words (E = 8 here) has no object.
        ((_stack(8), 4), (_sym("_a"), 4), "unknown"),
        ((_stack(4), 4), (_sym("_a"), 4), "disjoint"),
        # A pointer has no object.
        ((lin_atom(("reg0", "ecx")), 4), (_sym("_a"), 4), "unknown"),
        ((lin_atom(("reg0", "ecx")), 4), (_stack(-4), 4), "unknown"),
        # Two labels of one section: related by their offsets in it.
        ((_sym("_c"), 2), (_sym("_d"), 2), "disjoint"),
        ((_sym("_c"), 4), (_sym("_d"), 4), "unknown"),
        ((_sym("_c", 2), 2), (_sym("_d"), 2), "same"),
        # Outside the section's size: no object.
        ((_sym("_d", 8), 4), (_sym("_e"), 4), "unknown"),
        # Two sections of the object, and a section against an external.
        ((_sym("_c"), 4), (_sym("_e"), 4), "disjoint"),
        ((_sym("_e"), 4), (_sym("_a"), 4), "disjoint"),
    ],
)
def test_the_object_model_relates_addresses_by_object(left, right, relation) -> None:
    model = ObjectModel(
        {
            "_a": SymbolObject(("extern", "_a"), 0, None),
            "_b": SymbolObject(("extern", "_b"), 0, None),
            "_c": SymbolObject(("section", 2), 0, 8),
            "_d": SymbolObject(("section", 2), 2, 8),
            "_e": SymbolObject(("section", 3), 0, 4),
        },
        8,
    )
    assert address_relation(*left, *right, model) == relation
    assert address_relation(*right, *left, model) == relation
    if relation != "same":
        assert address_relation(*left, *right) == "unknown"  # a region proof's relation


def test_the_object_model_places_each_symbol_from_its_coff_record() -> None:
    coff = SimpleNamespace(
        sections=[
            {"characteristics": 0x60500020, "raw_size": 64},  # 1 .text
            {"characteristics": 0x40300040, "raw_size": 16},  # 2 .rdata
            {"characteristics": 0xC0400040, "raw_size": 32},  # 3 .data
            {"characteristics": 0x40301040, "raw_size": 8},  # 4 a COMDAT
        ]
    )

    def row(name: str, storage: int, section: int, value: int = 0, kind: int = 0) -> dict:
        return {
            "target": name,
            "target_storage": storage,
            "target_section": section,
            "target_value": value,
            "target_type": kind,
        }

    model = object_model(
        coff,  # type: ignore[arg-type]
        [
            row("_extern", 2, 0),
            row("_common", 2, 0, 12),
            row("$T1", 3, 2, 4),
            row("_data", 2, 3, 8),
            row("_comdat", 2, 4),
            row("$Lstatic", 3, 4),
            row("_function", 2, 0, kind=0x20),
            row("_weak", 105, 0),
        ],
        8,
    )
    assert model.symbols == {
        "_extern": SymbolObject(("extern", "_extern"), 0, None),
        "_common": SymbolObject(("extern", "_common"), 0, 12),
        "$T1": SymbolObject(("section", 2), 4, 16),
        "_data": SymbolObject(("section", 3), 8, 32),
        "_comdat": SymbolObject(("extern", "_comdat"), 0, 8),
    }
    assert model.read_only == frozenset({("section", 2)})
    assert model.constant(_sym("$T1"), 4) and not model.constant(_sym("$T1", 12), 4)
    assert not model.constant(_sym("_data"), 4)


def test_a_field_takes_the_donor_record_of_its_own_addend() -> None:
    def row(offset: int, addend: int) -> dict:
        return {
            "offset": offset,
            "target": "_legoGlobs",
            "target_storage": 2,
            "target_section": 0,
            "target_value": 0,
            "target_type": 0,
            "type": 6,
            "addend": addend,
        }

    donor = [row(2, 0x98), row(12, 0x454)]
    reference = [row(2, 0x454), row(12, 0x98)]
    assert _pair_relocations(donor, reference) == [[2, 12], [12, 2]]
    assert _pair_relocations(donor, donor) == [[2, 2], [12, 12]]


# --- 3. x87 commutation ---------------------------------------------------------------

# 0: fld dword [esp+4] / 4: fld dword [esp+8] / 8: faddp st(1),st / 10: ret
FREG_D = _code("d9442404 d9442408 dec1 c3")
# The operands loaded in the other order.
FREG_P = _code("d9442408 d9442404 dec1 c3")
# ... with fmulp st(1),st.
FMUL_D = _code("d9442404 d9442408 dec9 c3")
FMUL_P = _code("d9442408 d9442404 dec9 c3")
# 0: fld dword [esp+4] / 4: fadd dword [esp+8] / 8: ret
FMEM_D = _code("d9442404 d8442408 c3")
# 0: fld dword [esp+8] / 4: fadd dword [esp+4] / 8: ret
FMEM_P = _code("d9442408 d8442404 c3")
# 8: fsubp st(1),st after the loads in either order.
FSUB_D = _code("d9442404 d9442408 dee9 c3")
FSUB_P = _code("d9442408 d9442404 dee9 c3")
# (a + b) + c against (b + c) + a, through registers.
# 0: fld [esp+4] / 4: fld [esp+8] / 8: faddp / 10: fld [esp+12] / 14: faddp / 16: ret
FASSOC_D = _code("d9442404 d9442408 dec1 d944240c dec1 c3")
FASSOC_P = _code("d9442408 d944240c dec1 d9442404 dec1 c3")


@pytest.mark.parametrize(("donor", "image"), [(FREG_D, FREG_P), (FMUL_D, FMUL_P)])
def test_two_x87_registers_commute_under_add_and_multiply(donor, image) -> None:
    assert _prove(donor, image, objects=None).returns == 1


def test_two_memory_operands_do_not_commute() -> None:
    # fld m32 quiets an SNaN and raises DE for a denormal before the add;
    # fadd m32 meets the raw operand, and with a NaN partner raises no DE.
    # The probe finds the result or the flags differ in 64 of its 200 pairs.
    _both_passes_refuse(FMEM_D, FMEM_P, match="access different memory|x87 stacks")


def test_the_probe_shows_memory_operands_differ_only_with_a_nan() -> None:
    rows = [line.split() for line in (PROBE / "memory_operands.out").read_text().splitlines()]
    assert len(rows) == 200
    verdicts: dict[str, list[tuple[str, str]]] = {}
    for _op, a, b, *checks in rows:
        for check in checks:
            name, verdict = check.split("=")
            if verdict == "DIFF":
                verdicts.setdefault(name, []).append((a, b))
    assert "commute-register" not in verdicts
    assert len(verdicts["commute-memory"]) == 64
    assert len(verdicts["memory-as-register"]) == 32
    for pairs in verdicts.values():
        assert all("nan" in a or "nan" in b for a, b in pairs)
    # A QNaN with a denormal: only the flags (DE) differ.
    assert ("qnan.c0", "denormal") in verdicts["commute-memory"]


@pytest.mark.skipif(
    subprocess.run(["sh", "-c", "command -v gcc"], capture_output=True).returncode != 0,
    reason="needs gcc to rerun the probe",
)
def test_the_probe_source_reproduces_its_recorded_output(tmp_path: Path) -> None:
    binary = tmp_path / "memory_operands"
    built = subprocess.run(
        ["gcc", "-O0", "-o", str(binary), str(PROBE / "memory_operands.c")], capture_output=True
    )
    if built.returncode != 0:
        pytest.skip("the host compiler cannot build the probe")
    output = subprocess.run([str(binary)], capture_output=True, text=True, check=True).stdout
    assert output == (PROBE / "memory_operands.out").read_text()


def test_a_subtraction_does_not_commute() -> None:
    _both_passes_refuse(FSUB_D, FSUB_P, match="x87 stacks|access different memory")


def test_an_x87_sum_is_not_reassociated() -> None:
    _both_passes_refuse(FASSOC_D, FASSOC_P, match="x87 stacks|access different memory")


# --- 4. products modulo 2**32 ----------------------------------------------------------

# 0: mov eax,[esp+4] / 4: imul eax,[esp+8] / 9: shl eax,4 / 12: ret  (16 * (S * V))
SCALE_D = _code("8b442404 0faf442408 c1e004 c3")
# 0: mov ecx,[esp+8] / 4: add ecx,ecx / 6: mov eax,[esp+4] / 10: imul eax,ecx
# 13: shl eax,3 / 16: ret  (8 * (S * (2 * V)))
SCALE_P = _code("8b4c2408 01c9 8b442404 0fafc1 c1e003 c3")
# (a * b) * c against (b * c) * a.
ASSOC_D = _code("8b442404 0faf442408 0faf44240c c3")
ASSOC_P = _code("8b442408 0faf44240c 0faf442404 c3")
# a * (b + c) against a * b + a * c.
# 0: mov eax,[esp+8] / 4: add eax,[esp+12] / 8: imul eax,[esp+4] / 13: ret
DISTRIB_D = _code("8b442408 0344240c 0faf442404 c3")
# 0: mov eax,[esp+4] / 4: mov ecx,eax / 6: imul eax,[esp+8] / 11: imul ecx,[esp+12]
# 16: add eax,ecx / 18: ret
DISTRIB_P = _code("8b442404 89c1 0faf442408 0faf4c240c 01c8 c3")
# SCALE_D and SCALE_P with 9 (13): jo over the shift.
SCALE_OF_D = _code("8b442404 0faf442408 7003 c1e004 c3")
SCALE_OF_P = _code("8b4c2408 01c9 8b442404 0fafc1 7003 c1e003 c3")


def test_a_constant_factor_commutes_out_of_a_product() -> None:
    _only_the_second_pass_proves(SCALE_D, SCALE_P)


def test_a_product_is_associative() -> None:
    _only_the_second_pass_proves(ASSOC_D, ASSOC_P)


def test_a_product_is_not_distributed_over_a_sum() -> None:
    _both_passes_refuse(DISTRIB_D, DISTRIB_P, match="eax differs at the return")


def test_the_overflow_flag_of_a_product_names_its_own_operands() -> None:
    # S * V and S * 2V overflow differently, whatever their low halves.
    # The jo conditions are different terms, so each path of one version is
    # consistent with both of the other's, and the shifted results meet.
    _both_passes_refuse(SCALE_OF_D, SCALE_OF_P, match="eax differs at the return")


def test_the_product_normal_form() -> None:
    s, v = lin_atom(("reg0", "esi")), lin_atom(("reg0", "edi"))
    assert lin_scale16(product(s, v)) == lin_scale8(product(s, lin(0, ((("reg0", "edi"), 2),))))
    assert product(product(s, v), s) == product(s, product(v, s))
    total = lin(1, ((("reg0", "edi"), 1),))  # v + 1 stays one factor
    assert product(s, total)[2][0][0][3] == tuple(sorted((s, total), key=repr))


def lin_scale16(value: Any) -> Any:
    return lin(0, ((atom, k * 16) for atom, k in value[2]))


def lin_scale8(value: Any) -> Any:
    return lin(0, ((atom, k * 8) for atom, k in value[2]))


# --- 5. shared-frame slots never addressed ----------------------------------------------

# 0: sub esp,12 / 3: mov ecx,[esp+16] / 7: mov [esp+4],ecx / 11: lea eax,[esp+8]
# 15: push eax / 16: call _g / 21: add esp,4 / 24: mov eax,[esp+4] / 28: add esp,12 / 31: ret
SLOTS_D = _code("83ec0c 8b4c2410 894c2404 8d442408 50 e800000000 83c404 8b442404 83c40c c3")
# The parameter kept in the slot at [esp] instead: 7: mov [esp],ecx / 10: lea eax,[esp+8]
# 14: push eax / 15: call _g / 20: add esp,4 / 23: mov eax,[esp] / 26: add esp,12 / 29: ret
SLOTS_P = _code("83ec0c 8b4c2410 890c24 8d442408 50 e800000000 83c404 8b0424 83c40c c3")


def test_a_slot_swap_in_a_shared_frame_is_refused() -> None:
    # The frame is shared because ESP0-4 is passed to _g.  Nothing in the
    # object bounds the object that address points into (the types are in a
    # PDB type server), so _g may read every word of the frame, and the two
    # versions leave the parameter at ESP0-8 and at ESP0-12.
    _both_passes_refuse(
        SLOTS_D,
        SLOTS_P,
        {17: ("rel32", "_g")},
        {16: ("rel32", "_g")},
        frame=FrameFacts(True, base=-12, params_end=8),
        match="make different calls",
    )


# --- 6. covered stores ------------------------------------------------------------------

# 0: push ecx / 1: mov dword [esp],5 / 8: call _g / 13: add esp,4 / 16: ret
PUSHED_D = _code("51 c7042405000000 e800000000 83c404 c3")
# 0: push 5 / 2: call _g / 7: add esp,4 / 10: ret
PUSHED_P = _code("6a05 e800000000 83c404 c3")
# 0: fld dword [esp+4] / 4: push ecx / 5: fstp dword [esp] / 8: call _g / 13: add esp,4 / 16: ret
FSTP_D = _code("d9442404 51 d91c24 e800000000 83c404 c3")
# ... pushing EAX.
FSTP_P = _code("d9442404 50 d91c24 e800000000 83c404 c3")
# 0: push ecx / 1: mov word [esp],5 / 7: call _g / 12: add esp,4 / 15: ret
HALF_D = _code("51 66c704240500 e800000000 83c404 c3")
HALF_P = _code("50 66c704240500 e800000000 83c404 c3")
# 0: push ecx / 1: call _g / 6: add esp,4 / 9: ret
LIVE_D = _code("51 e800000000 83c404 c3")
LIVE_P = _code("50 e800000000 83c404 c3")


def test_a_pushed_register_overwritten_before_the_call_is_dead() -> None:
    _only_the_second_pass_proves(PUSHED_D, PUSHED_P, {9: ("rel32", "_g")}, {3: ("rel32", "_g")})


def test_an_argument_slot_filled_by_fstp_is_dead_whatever_was_pushed() -> None:
    _only_the_second_pass_proves(FSTP_D, FSTP_P, {9: ("rel32", "_g")})


def test_a_partly_overwritten_pushed_word_is_compared() -> None:
    _both_passes_refuse(HALF_D, HALF_P, {8: ("rel32", "_g")}, match="make different calls")


def test_a_pushed_word_the_callee_reads_is_compared() -> None:
    _both_passes_refuse(LIVE_D, LIVE_P, {2: ("rel32", "_g")}, match="make different calls")


# --- 7. an undefined x87 condition bit ------------------------------------------------

FRAME8 = FrameFacts(True, base=-8, params_end=12)
# 0: sub esp,8 / 3: fld dword [esp+12] / 7: fcom dword [esp+16] / 11: fstp dword [esp]
# 14: fnstsw ax / 16: test ah,0x41 / 19: jne 28 / 21: mov eax,[esp] / 24: add esp,8 / 27: ret
# 28: xor eax,eax / 30: add esp,8 / 33: ret
CC_D = _code("83ec08 d944240c d8542410 d91c24 dfe0 f6c441 7507 8b0424 83c408 c3 31c0 83c408 c3")
# The same with the value stored to the slot at [esp+4]: 11: fstp dword [esp+4]
# 15: fnstsw ax / 17: test ah,0x41 / 20: jne 30 / 22: mov eax,[esp+4] / 26: add esp,8
# 29: ret / 30: xor eax,eax / 32: add esp,8 / 35: ret
CC_P = _code("83ec08 d944240c d8542410 d95c2404 dfe0 f6c441 7508 8b442404 83c408 c3 31c0 83c408 c3")
# 11: fnstsw ax / 13: fstp dword [esp+4]: the compare's own bits are read.
CC_P_COMPARE = _code(
    "83ec08 d944240c d8542410 dfe0 d95c2404 f6c441 7508 8b442404 83c408 c3 31c0 83c408 c3"
)
# 7: fstp dword [esp] / 10: fld dword [esp] / 13: fcomp dword [esp+16] / 17: fnstsw ax
# 19: test ah,0x41 / 22: jne 31 / 24: mov eax,[esp] / 27: add esp,8 / 30: ret
# 31: xor eax,eax / 33: add esp,8 / 36: ret: the rounded value is compared (as 0x460360).
CC_P_ROUNDED = _code(
    "83ec08 d944240c d91c24 d90424 d85c2410 dfe0 f6c441 7507 8b0424 83c408 c3 31c0 83c408 c3"
)


def test_the_same_store_to_another_slot_leaves_the_same_undefined_bits() -> None:
    proof = _only_the_second_pass_proves(CC_D, CC_P, frame=FRAME8)
    assert proof.frame.private and proof.returns == 2


def test_an_undefined_bit_is_not_the_compares_bit() -> None:
    _both_passes_refuse(CC_D, CC_P_COMPARE, frame=FRAME8, match="Intel leaves C0-C3 undefined")


def test_a_compare_of_the_rounded_value_is_refused() -> None:
    _both_passes_refuse(CC_D, CC_P_ROUNDED, frame=FRAME8, match="access different memory")


# --- 8. EAX at the return ----------------------------------------------------------------

# 0: mov eax,[esp+4] / 4: mov [_a],eax / 9: ret  (EAX left holding the parameter)
VOID_D = _code("8b442404 a300000000 c3")
# 0: mov ecx,[esp+4] / 4: mov [_a],ecx / 10: ret  (EAX untouched)
VOID_P = _code("8b4c2404 890d00000000 c3")


def test_eax_at_the_return_is_compared_whatever_the_function_returns() -> None:
    # Nothing in the object says the function is void: its S_GPROC32 names a
    # type in the PDB type server, not in the object.
    _both_passes_refuse(VOID_D, VOID_P, {5: "_a"}, {6: "_a"}, match="eax differs at the return")


# --- the record --------------------------------------------------------------------------


def _author(reference: bytes) -> Any:
    seed = _coff(SCALE_D)
    return seed, build_function_validation_rewriting(
        donor=_extern_donor(),
        target_id="program",
        translation_unit_id="tu.fixture",
        build_target="program",
        symbol=TARGET_SYMBOL,
        seed_object=seed,
        donor_object=seed,
        reference_object=_coff(reference),
    )


def test_a_second_pass_record_pins_it_and_dispatches() -> None:
    seed, authored = _author(SCALE_P)
    proof = authored.function.receipt.expected_values["function_validation.expected_proof"]
    assert proof["equivalences"] is True
    constraints = merge_candidate_constraints(
        authored.function.intervention, authored.function.receipt
    ).materialize()
    candidate = ClassicFamilyDispatcher().dispatch(
        authored.function.intervention,
        ClassicDispatchMaterials(
            seed_object=seed, donor_object=seed, candidate_constraints=constraints
        ),
    )
    assert candidate.output == authored.candidate_object


def test_a_first_pass_record_pins_no_second_pass() -> None:
    _seed, authored = _author(_code("8b4c2408 8b442404 0fafc1 c1e004 c3"))
    proof = authored.function.receipt.expected_values["function_validation.expected_proof"]
    assert "equivalences" not in proof


def test_the_region_simulator_keeps_its_own_return_address_and_products() -> None:
    paths = simulate_region(SCALE_P, 0, 16, {}, "donor", "fixture")
    (path,) = paths
    assert path.regs["eax"][2][0][0][:3] == ("op", "mul", 32)
    assert path.regs["eax"][2][0][1] == 8
