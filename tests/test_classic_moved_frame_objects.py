"""The moved-objects pass of a whole-function proof (a15).

`function_validation.prove_function` runs the moved-objects pass only after
the frame-objects pass (a14) refuses.  The replacement may keep an escaping
frame object at another offset than the donor, at the donor's extent; the
two versions' addresses of corresponding objects are one term, and a15
assumes neither the function nor a callee observes an address's numeric
value.  What the function itself does with such an address is checked.  The
programs are hand-encoded IA-32 (each listing in the comment above it; a
call's PC-relative field holds 0, the addend the closed set admits).

1. Proofs: an escaping array at two offsets, by a call and by a block event.
2. Refusals: a pointer compare, a pointer subtraction, an integer cast
   reaching arithmetic, an address as a string count, different extents, a
   read of the object's entry bytes, and an address returned past the frame.
3. The record: authored and dispatched with the donor's type server,
   pinning a14, a15 and the moves.
"""

from __future__ import annotations

from typing import Any

import pytest
from test_classic_frame_objects import (
    T_INT4,
    T_RCHAR,
    _array,
    _code,
    _coff,
    _objects,
    _pdb,
    _type_server_stream,
)
from test_classic_function_validation import _extern_donor
from test_classic_register_bijection_reencoding_full import TARGET_SYMBOL

from reprobit.binary import ByteIdentityError
from reprobit.classic.frame_objects import FrameObjects
from reprobit.classic.function_validation import (
    FrameFacts,
    observes_moved,
    pointer_form,
    proof_summary,
    prove_function,
)
from reprobit.classic.region_simulation import ObjectModel, lin, lin_atom
from reprobit.classic_donors import merge_candidate_constraints
from reprobit.classic_project import ClassicDispatchMaterials, ClassicFamilyDispatcher
from reprobit.coff_format import CoffObject, coff_body
from reprobit.discovery_function_validation import build_function_validation_rewriting

OBJECTS = ObjectModel({}, 8)
# sub esp,0x20 allocates eight words; the one parameter n lies at ESP0+4.
FRAME = FrameFacts(True, base=-32, params_end=8)
# buf is char[16] at ESP0-16 in the donor.  No local ends where it starts, so
# a pointer to it is not also one past another object's end (a14).
LOCALS = (("buf", -16, 16), ("n", 4, 4))
CALL_D = {14: ("rel32", "_g")}


def _prove(
    donor: bytes,
    image: bytes,
    relocations: dict[int, Any],
    image_relocations: dict[int, Any],
    frame_objects: FrameObjects,
    *,
    moved: bool = True,
) -> Any:
    return prove_function(
        donor,
        relocations,
        image,
        image_relocations,
        {},
        "fixture",
        private_frame=FRAME,
        objects=OBJECTS,
        frame_objects=frame_objects,
        moved_objects=moved,
    )


# --- 1. proofs ---------------------------------------------------------------------------

# 0: sub esp,0x20 / 3: mov byte [esp+0x10],0 / 8: lea eax,[esp+0x10] / 12: push eax
# 13: call _g / 18: add esp,4 / 21: movsx eax,byte [esp+0x10] / 26: add esp,0x20
# 29: ret: buf[0] = 0; g(buf); return buf[0], with buf at ESP0-16.
CALL_DONOR = _code("83ec20 c644241000 8d442410 50 e800000000 83c404 0fbe442410 83c420 c3")
# The same with buf at ESP0-32: 3: mov byte [esp],0 / 7: lea eax,[esp] / 10: push eax
# 11: call _g / 16: add esp,4 / 19: movsx eax,byte [esp] / 23: add esp,0x20 / 26: ret
CALL_IMAGE = _code("83ec20 c6042400 8d0424 50 e800000000 83c404 0fbe0424 83c420 c3")
CALL_P = {12: ("rel32", "_g")}


def test_an_escaping_array_at_another_offset_is_proved_under_a15() -> None:
    # The frame-objects pass relates objects by equal starts: the
    # replacement's address ESP0-32 lies in no object the donor declares.
    with pytest.raises(ByteIdentityError, match=r"ESP0-32 lies in no local"):
        _prove(CALL_DONOR, CALL_IMAGE, CALL_D, CALL_P, _objects(*LOCALS), moved=False)
    summary = proof_summary(_prove(CALL_DONOR, CALL_IMAGE, CALL_D, CALL_P, _objects(*LOCALS)))
    assert summary["frame"] == "private"
    assert summary["frame_objects"] == [[-16, 16]]
    assert summary["moved_frame_objects"] == [[-16, -32]]
    assert summary["assumptions"] == ["a14", "a15"]


def test_an_object_at_the_same_offset_needs_no_a15() -> None:
    # The moved-objects pass on a pair that keeps the object in place moves
    # nothing and pins only a14.
    summary = proof_summary(_prove(CALL_DONOR, CALL_DONOR, CALL_D, CALL_D, _objects(*LOCALS)))
    assert "moved_frame_objects" not in summary
    assert summary["assumptions"] == ["a14"]


def test_pointer_form_admits_one_object_plus_an_offset() -> None:
    moved = frozenset({("fobj", -16, 16)})
    other = ("fobj", -32, 16)
    index = ("reg0", "ecx")
    assert pointer_form(lin(4, [(("fobj", -16, 16), 1), (index, 1)]), moved)
    assert pointer_form(lin(0, [(other, 1), (index, 1)]), moved)  # not moved
    assert not pointer_form(lin(0, [(("fobj", -16, 16), 2)]), moved)
    assert not pointer_form(lin(0, [(("fobj", -16, 16), -1), (index, 1)]), moved)
    assert not pointer_form(("b", 8, ("part", lin_atom(("fobj", -16, 16)), 0, 1)), moved)
    # A load through the address reads the object's bytes: not an observation.
    loaded = lin_atom(("ld", lin(4, [(("fobj", -16, 16), 1)]), 4, ()))
    assert pointer_form(loaded, moved) and not observes_moved(loaded, moved)
    assert observes_moved(("and", lin_atom(("fobj", -16, 16)), lin(15)), moved)


# --- 2. refusals -------------------------------------------------------------------------

# 0: sub esp,0x20 / 3: mov ecx,[esp+0x24] / 7: lea eax,[esp+0x10] / 11: cmp eax,ecx
# 13: jne 20 / 15: mov byte [esp+0x10],0 / 20: push eax / 21: call _g / 26: add esp,4
# 29: add esp,0x20 / 32: ret: if (buf == (char *)n) buf[0] = 0; g(buf).
COMPARE_DONOR = _code(
    "83ec20 8b4c2424 8d442410 3bc1 7505 c644241000 50 e800000000 83c404 83c420 c3"
)
# ... with buf at ESP0-32: 7: lea eax,[esp] / 10: cmp eax,ecx / 12: jne 18
# 14: mov byte [esp],0 / 18: push eax / 19: call _g ...
COMPARE_IMAGE = _code("83ec20 8b4c2424 8d0424 3bc1 7504 c6042400 50 e800000000 83c404 83c420 c3")


def test_a_compare_of_a_moved_object_s_address_is_refused() -> None:
    with pytest.raises(ByteIdentityError, match=r"branches on the address .* pointer compare"):
        _prove(
            COMPARE_DONOR,
            COMPARE_IMAGE,
            {22: ("rel32", "_g")},
            {20: ("rel32", "_g")},
            _objects(*LOCALS),
        )


# 0: sub esp,0x20 / 3: lea eax,[esp+0x18] / 7: lea ecx,[esp+8] / 11: mov edx,eax
# 13: sub edx,ecx / 15: push edx / 16: push ecx / 17: push eax / 18: call _g
# 23: add esp,12 / 26: add esp,0x20 / 29: ret: g(a, b, a - b), char a[8] at ESP0-8 and
# char b[8] at ESP0-24.
SUBTRACT_DONOR = _code("83ec20 8d442418 8d4c2408 8bd0 2bd1 52 51 50 e800000000 83c40c 83c420 c3")
# ... with a and b swapped: 3: lea eax,[esp+8] / 7: lea ecx,[esp+0x18]
SUBTRACT_IMAGE = _code("83ec20 8d442408 8d4c2418 8bd0 2bd1 52 51 50 e800000000 83c40c 83c420 c3")
TWO_ARRAYS = (("a", -8, 8), ("b", -24, 8), ("n", 4, 4))


def test_a_subtraction_of_two_moved_objects_addresses_is_refused() -> None:
    # The run suggests both moves (a to ESP0-24, b to ESP0-8, which fit), and
    # a - b is then 16 in the donor and -16 in the replacement.
    relocations = {19: ("rel32", "_g")}
    with pytest.raises(ByteIdentityError, match=r"edx after 13: .* used as a number"):
        _prove(SUBTRACT_DONOR, SUBTRACT_IMAGE, relocations, relocations, _objects(*TWO_ARRAYS))


# 0: sub esp,0x20 / 3: lea eax,[esp+0x10] / 7: push eax / 8: call _g / 13: add esp,4
# 16: lea eax,[esp+0x10] / 20: and eax,0xf / 23: add esp,0x20 / 26: ret:
# g(buf); return (int)buf & 15.
CAST_DONOR = _code("83ec20 8d442410 50 e800000000 83c404 8d442410 83e00f 83c420 c3")
# ... with buf at ESP0-32: 3: lea eax,[esp] / 6: push eax / 7: call _g / 12: add esp,4
# 15: lea eax,[esp] / 18: and eax,0xf / 21: add esp,0x20 / 24: ret
CAST_IMAGE = _code("83ec20 8d0424 50 e800000000 83c404 8d0424 83e00f 83c420 c3")


def test_an_integer_cast_reaching_arithmetic_is_refused() -> None:
    with pytest.raises(ByteIdentityError, match=r"eax after 20: .* used as a number"):
        _prove(
            CAST_DONOR, CAST_IMAGE, {9: ("rel32", "_g")}, {8: ("rel32", "_g")}, _objects(*LOCALS)
        )


# 0: sub esp,0x20 / 3: push edi / 4: lea edi,[esp+0x14] / 8: mov ecx,edi / 10: xor eax,eax
# 12: rep stosb / 14: pop edi / 15: add esp,0x20 / 18: ret: a block of buf's address
# (as a number) zero bytes from buf.
COUNT_DONOR = _code("83ec20 57 8d7c2414 8bcf 33c0 f3aa 5f 83c420 c3")
# ... with buf at ESP0-32: 4: lea edi,[esp+4]
COUNT_IMAGE = _code("83ec20 57 8d7c2404 8bcf 33c0 f3aa 5f 83c420 c3")


def test_a_string_instruction_counting_with_an_address_is_refused() -> None:
    with pytest.raises(ByteIdentityError, match=r"string instruction uses ecx"):
        _prove(COUNT_DONOR, COUNT_IMAGE, {}, {}, _objects(*LOCALS))


# 0: sub esp,0x20 / 3: lea eax,[esp+8] / 7: lea ecx,[esp+0x10] / 11: push ecx
# 12: push eax / 13: call _g / 18: add esp,8 / 21: add esp,0x20 / 24: ret: g(x, y), char
# x[8] at ESP0-24 and char y[16] at ESP0-16.
EXTENTS_DONOR = _code("83ec20 8d442408 8d4c2410 51 50 e800000000 83c408 83c420 c3")
# ... with x at ESP0-16 and y at ESP0-24, where only eight bytes lie before x.
EXTENTS_IMAGE = _code("83ec20 8d442410 8d4c2408 51 50 e800000000 83c408 83c420 c3")
X_AND_Y = (("x", -24, 8), ("y", -16, 16), ("spare", -32, 8), ("n", 4, 4))


def test_objects_with_different_extents_are_refused() -> None:
    relocations = {14: ("rel32", "_g")}
    with pytest.raises(
        ByteIdentityError,
        match=r"keeps the frame object of x at ESP0-16, inside the 16 bytes of y .* different "
        r"extents",
    ):
        _prove(EXTENTS_DONOR, EXTENTS_IMAGE, relocations, relocations, _objects(*X_AND_Y))


# 0: sub esp,0x20 / 3: lea eax,[esp+0x10] / 7: movsx edx,byte [esp+0x10] / 12: push eax
# 13: push edx / 14: call _g / 19: add esp,8 / 22: add esp,0x20 / 25: ret:
# g(buf[0], buf) before anything writes buf.
UNWRITTEN_DONOR = _code("83ec20 8d442410 0fbe542410 50 52 e800000000 83c408 83c420 c3")
# ... with buf at ESP0-32: 3: lea eax,[esp] / 6: movsx edx,byte [esp] / 10: push eax
# 11: push edx / 12: call _g ...
UNWRITTEN_IMAGE = _code("83ec20 8d0424 0fbe1424 50 52 e800000000 83c408 83c420 c3")


def test_a_read_of_a_moved_object_s_entry_bytes_is_refused() -> None:
    with pytest.raises(ByteIdentityError, match=r"no store has written since the entry"):
        _prove(
            UNWRITTEN_DONOR,
            UNWRITTEN_IMAGE,
            {15: ("rel32", "_g")},
            {13: ("rel32", "_g")},
            _objects(*LOCALS),
        )


# 0: sub esp,0x20 / 3: lea eax,[esp+0x10] / 7: push eax / 8: call _g / 13: add esp,4
# 16: lea eax,[esp+0x10] / 20: add esp,0x20 / 23: ret: g(buf); return buf.
DANGLING_DONOR = _code("83ec20 8d442410 50 e800000000 83c404 8d442410 83c420 c3")
# ... with buf at ESP0-32.
DANGLING_IMAGE = _code("83ec20 8d0424 50 e800000000 83c404 8d0424 83c420 c3")


def test_a_moved_object_s_address_returned_past_the_frame_is_refused() -> None:
    with pytest.raises(ByteIdentityError, match=r"eax holds the address of a frame object"):
        _prove(
            DANGLING_DONOR,
            DANGLING_IMAGE,
            {9: ("rel32", "_g")},
            {8: ("rel32", "_g")},
            _objects(*LOCALS),
        )


# --- 3. the record -----------------------------------------------------------------------

# 0: sub esp,0x2c / 3: push edi / 4: mov ecx,[esp+0x34] / 8: mov [esp+8],ecx
# 12: lea edi,[esp+0x20] / 16: xor eax,eax / 18: rep stosb / 20: mov eax,[esp+8]
# 24: pop edi / 25: add esp,0x2c / 28: ret: memset(buf, 0, n) of a char buf[16] at
# ESP0-16, n kept in the compiler's slot ESP0-40.
REP_DONOR = _code("83ec2c 57 8b4c2434 894c2408 8d7c2420 33c0 f3aa 8b442408 5f 83c42c c3")
# ... with buf at ESP0-32: 12: lea edi,[esp+0x10]
REP_IMAGE = _code("83ec2c 57 8b4c2434 894c2408 8d7c2410 33c0 f3aa 8b442408 5f 83c42c c3")
# buf is char[16] (type 0x1000 in the type server); the slot ESP0-32 the
# replacement keeps it at is no local's in the donor.
REP_LOCALS = [("buf", -16, 0x1000), ("n", 4, T_INT4)]


def _rep_coff(body: bytes) -> bytes:
    return _coff(body, REP_LOCALS, types=_type_server_stream(), locals_words=11, params=1)


def test_a_moved_objects_record_pins_a15_and_dispatches_with_the_type_server() -> None:
    server = _pdb([_array(T_RCHAR, 16)])
    seed = _rep_coff(REP_DONOR)
    authored = build_function_validation_rewriting(
        donor=_extern_donor(),
        target_id="program",
        translation_unit_id="tu.fixture",
        build_target="program",
        symbol=TARGET_SYMBOL,
        seed_object=seed,
        donor_object=seed,
        reference_object=_rep_coff(REP_IMAGE),
        donor_type_server=server,
    )
    proof = authored.function.receipt.expected_values["function_validation.expected_proof"]
    assert proof["assumptions"] == ["a14", "a15"]
    assert proof["frame_objects"] == [[-16, 16]]
    assert proof["moved_frame_objects"] == [[-16, -32]]
    composed = CoffObject(authored.candidate_object)
    assert bytes(coff_body(composed, composed.function_section(TARGET_SYMBOL))) == REP_IMAGE
    constraints = merge_candidate_constraints(
        authored.function.intervention, authored.function.receipt
    ).materialize()
    candidate = ClassicFamilyDispatcher().dispatch(
        authored.function.intervention,
        ClassicDispatchMaterials(
            seed_object=seed,
            donor_object=seed,
            candidate_constraints=constraints,
            donor_type_server=server,
        ),
    )
    assert candidate.output == authored.candidate_object
