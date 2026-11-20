"""Frame objects at their edges: straddling accesses and boundary pointers (a18).

Every function here is hand-encoded IA-32 written for these tests (each
listing in the comment above it).  The proofs run through `prove_function`
with the donor's frame objects given directly, as `test_classic_frame_objects`
does.
"""

from __future__ import annotations

from typing import Any

import pytest

from reprobit.binary import ByteIdentityError
from reprobit.classic.frame_objects import FrameLocal, FrameObjects, merge_frame_objects
from reprobit.classic.function_validation import (
    FrameFacts,
    frame_object_boundaries,
    proof_summary,
    prove_function,
)
from reprobit.classic.region_simulation import ObjectModel


def _code(text: str) -> bytes:
    return bytes.fromhex(text.replace(" ", ""))


OBJECTS = ObjectModel({}, 8)
FRAME = FrameFacts(True, base=-16, params_end=8)


def _objects(*records: tuple[str, int, int]) -> FrameObjects:
    return merge_frame_objects(tuple(FrameLocal(name, at, size, 0) for name, at, size in records))


def _prove(
    donor: bytes,
    image: bytes,
    relocations: dict[int, Any],
    image_relocations: dict[int, Any],
    frame_objects: FrameObjects | None,
    *,
    boundaries: bool = False,
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
        boundaries=boundaries,
    )


# --- 1. an access straddling an escaping object's edge -----------------------------------

# int x at ESP0-8, whose address g receives; p the parameter.
# 0: sub esp,0x10 / 3: mov ecx,[esp+0x14] / 7: mov [esp],ecx / 10: mov dword [esp+4],0
# 18: fild qword [esp] / 21: fstp dword [esp+0xc] / 25: mov dword [esp+8],5
# 33: lea eax,[esp+8] / 37: push eax / 38: call _g / 43: add esp,4 / 46: mov eax,[esp+8]
# 50: add eax,[esp+0xc] / 54: add esp,0x10 / 57: ret: the 64-bit temporary of (float)p
# in [ESP0-16, ESP0-8), below x; then x = 5; g(&x); return x + the float's bits.
TEMPORARY_D = _code(
    "83ec10 8b4c2414 890c24 c7442404 00000000 df2c24 d95c240c c7442408 05000000 "
    "8d442408 50 e800000000 83c404 8b442408 0344240c 83c410 c3"
)
# ... the temporary in [ESP0-12, ESP0-4), its high word in x's bytes (MSVC 5.0's
# reuse of a local's slot before its address is taken): 7: mov [esp+4],ecx
# 11: mov dword [esp+8],0 / 19: fild qword [esp+4] / 23: fstp dword [esp+0xc] ...
TEMPORARY_P = _code(
    "83ec10 8b4c2414 894c2404 c7442408 00000000 df6c2404 d95c240c c7442408 05000000 "
    "8d442408 50 e800000000 83c404 8b442408 0344240c 83c410 c3"
)
# The same two without x = 5: the replacement's temporary is still in x when g reads it.
STALE_D = _code(
    "83ec10 8b4c2414 890c24 c7442404 00000000 df2c24 d95c240c "
    "8d442408 50 e800000000 83c404 8b442408 0344240c 83c410 c3"
)
STALE_P = _code(
    "83ec10 8b4c2414 894c2404 c7442408 00000000 df6c2404 d95c240c "
    "8d442408 50 e800000000 83c404 8b442408 0344240c 83c410 c3"
)
# 0: sub esp,0x10 / 3: lea eax,[esp+8] / 7: mov [esp+6],eax / 11: push eax / 12: call _g
# 17: add esp,4 / 20: add esp,0x10 / 23: ret: x's address stored across x's start.
POINTER_ACROSS = _code("83ec10 8d442408 89442406 50 e800000000 83c404 83c410 c3")
X_OBJECTS = (("x", -8, 4), ("p", 4, 4))


def test_a_temporary_straddling_an_escaping_local_is_split_into_its_runs() -> None:
    # Before the frame-objects pass the address of x escapes, and the shared
    # frame compares the temporaries' different bytes.
    with pytest.raises(ByteIdentityError, match=r"different"):
        _prove(TEMPORARY_D, TEMPORARY_P, {39: ("rel32", "_g")}, {41: ("rel32", "_g")}, None)
    proof = _prove(
        TEMPORARY_D,
        TEMPORARY_P,
        {39: ("rel32", "_g")},
        {41: ("rel32", "_g")},
        _objects(*X_OBJECTS),
    )
    summary = proof_summary(proof)
    # x's bytes are memory, the rest private slots: the replacement's eight-byte
    # load reads one run of each, and x = 5 overwrites its high word before g.
    assert summary["frame_objects"] == [[-8, 4]]
    assert summary["assumptions"] == ["a14"]


def test_a_straddling_write_that_reaches_a_callee_is_refused() -> None:
    # Without x = 5 the replacement's x holds the temporary's high word at the
    # call and the donor's does not: the split write is compared as memory.
    with pytest.raises(ByteIdentityError, match=r"different memory|make different calls"):
        _prove(
            STALE_D,
            STALE_P,
            {31: ("rel32", "_g")},
            {33: ("rel32", "_g")},
            _objects(*X_OBJECTS),
        )


def test_a_stack_address_stored_across_an_object_s_edge_is_refused() -> None:
    relocations = {13: ("rel32", "_g")}
    with pytest.raises(ByteIdentityError, match=r"stored across the edge of an escaping"):
        _prove(POINTER_ACROSS, POINTER_ACROSS, relocations, relocations, _objects(*X_OBJECTS))


# --- 2. a pointer at one object's end and the next one's start (a18) ---------------------

# struct { int a, b; } s at ESP0-8; p's copy in the local `copy` at ESP0-12, which ends
# where s starts.  0: sub esp,0x10 / 3: mov ecx,[esp+0x14] / 7: mov [esp+8],ecx
# 11: mov dword [esp+0xc],0 / 19: mov [esp+4],ecx / 23: lea eax,[esp+8] / 27: push eax
# 28: call _g / 33: add esp,4 / 36: mov eax,[esp+4] / 40: add esp,0x10 / 43: ret:
# s = {p, 0}; g(&s); return copy.
BOUNDARY_D = _code(
    "83ec10 8b4c2414 894c2408 c744240c00000000 894c2404 8d442408 50 e800000000 83c404 "
    "8b442404 83c410 c3"
)
# ... with p's copy in the compiler's slot ESP0-16: 15: mov [esp],ecx / 35: mov eax,[esp]
BOUNDARY_P = _code(
    "83ec10 8b4c2414 c744240c00000000 894c2408 890c24 8d442408 50 e800000000 83c404 "
    "8b0424 83c410 c3"
)
BOUNDARY_OBJECTS = (("s", -8, 8), ("p", 4, 4), ("copy", -12, 4))
# 0: sub esp,0x10 / 3: mov dword [esp+4],7 / 11: lea eax,[esp+8] / 15: mov eax,[eax-4]
# 18: add esp,0x10 / 21: ret: copy = 7; return ((int *)&s)[-1] -- copy read back through
# the boundary pointer, as one past copy's end.
BACK_THROUGH = _code("83ec10 c744240407000000 8d442408 8b40fc 83c410 c3")


def test_without_a18_the_object_a_boundary_pointer_ends_escapes_too() -> None:
    with pytest.raises(ByteIdentityError, match=r"leave different memory|make different calls"):
        _prove(
            BOUNDARY_D,
            BOUNDARY_P,
            {29: ("rel32", "_g")},
            {28: ("rel32", "_g")},
            _objects(*BOUNDARY_OBJECTS),
        )


def test_a_boundary_pointer_is_the_starting_object_s_under_a18() -> None:
    proof = _prove(
        BOUNDARY_D,
        BOUNDARY_P,
        {29: ("rel32", "_g")},
        {28: ("rel32", "_g")},
        _objects(*BOUNDARY_OBJECTS),
        boundaries=True,
    )
    summary = proof_summary(proof)
    # Only s escapes; copy stays a private slot, kept elsewhere by the replacement.
    assert summary["frame_objects"] == [[-8, 8]]
    assert summary["frame_object_boundaries"] == [-8]
    assert summary["assumptions"] == ["a14", "a18"]


def test_a_boundary_pointer_dereferenced_below_its_start_is_refused() -> None:
    # The access through it lies in copy, one past whose end the pointer would
    # have to be: a18 takes it as s's, and s's atom minus 4 leaves s.
    with pytest.raises(ByteIdentityError, match=r"access at offset -4 .* leaves it"):
        _prove(BACK_THROUGH, BACK_THROUGH, {}, {}, _objects(*BOUNDARY_OBJECTS), boundaries=True)


def test_the_pinned_boundaries_are_escaping_starts_over_private_objects() -> None:
    objects = _objects(("a", -16, 4), ("b", -12, 4), ("c", -8, 8))
    assert frame_object_boundaries(objects, {-12, -8}) == [-12]
    assert frame_object_boundaries(objects, {-16, -12, -8}) == []
    assert frame_object_boundaries(objects, {-8}) == [-8]
