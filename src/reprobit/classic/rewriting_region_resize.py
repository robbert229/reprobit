"""Classic compiler algorithms: a length-changing region rewrite proved by simulation.

`retail_exact_region_resize_rewriting` installs a declared replacement for one
or more regions of a freshly compiled donor body.  A replacement may be longer
or shorter than the region it replaces; the function is then laid out again at
its new length and installed through the same-slot resize delegate.  The
record carries each replacement as a list of instruction encodings (hex
text).  Those bytes are untrusted input: nothing about them is believed
except what the checks below measure, and every check compares them with the
donor the build compiles from source.  The build never reads a reference
image.

Theorem.  Let D be the donor body, R_1..R_n disjoint donor regions
[s_i, e_i), P_i the declared replacements, and I the image
``D[:s_1] P_1 D[e_1:s_2] ... P_n D[e_n:]`` laid out by the offset map M of
check 6.  If checks 1 to 9 hold, then for every entry state, D and I, run from
the function's entry or from any of its external entries, perform the same
sequence of memory writes and calls with the same arguments, and return with
the same EAX, the same callee-saved registers, the same ESP and the same
memory -- under the model every classic rewriting uses: one thread, ordinary
(non-volatile, non-device) memory, and callees that honour the MSVC calling
convention.  A region of D faults exactly when its replacement does; the
state at a fault is not compared.

Proof sketch.  Outside the regions D and I execute the same instructions
(check 6), so an invariant "the two states agree on memory, ESP, and every
register and flag live at this point in D or in I" is preserved by each of
them: a live set computed by backward liveness satisfies
``L(p) >= use(p) | (L(succ) - def(p))`` on its own control-flow graph, the two
graphs are equal outside the regions under M, and so is the union of the two
live sets.  At a region entry (its start or a declared interior entry, which
every edge into the region reaches by check 2) the states agree on the union
live set there, and every entry value a region reads before writing it is in
that set (check 8f).  Check 8 then shows, for every pair of paths through
R_i and P_i that the same entry state can take from that entry, that both
leave at corresponding points x and M(x) and the two states there agree on
memory, ESP, and every register and flag live at x in D or at M(x) in I.  So
the invariant holds again wherever control leaves the region, and at every
return it covers EAX, the callee-saved registers and ESP, which the liveness
treats as read by ``ret``.

Checks (each is a refusal):

1. Shape.  Every region lies on instruction boundaries of D's code, inside
   the code (before any switch table or fill), after the FPO prologue, and
   does not reach the code end; regions are sorted and disjoint.
2. Entries.  A region is entered at its start and at the interior points
   it declares, each paired with an instruction of P_i (M maps the point
   there).  No branch outside a region targets any other interior offset,
   no external entry (an entry the flow walk finds, or an in-body relocated
   target) lies on one, and no symbol of the function's section,
   line-independent debug offset (the CodeView procedure range) or
   closure-child code reference names an interior offset.
3. Forward CFG, any exits.  Inside R_i and P_i every instruction falls
   through, branches strictly forward to an instruction of the same region
   or to its end, or leaves for a point outside every region interior (or a
   declared entry of another region) in the code, or is a direct call to a
   register-free callee (``call rel32`` with its REL32 record, ``call
   [abs32]``); there is no other call, no return, indirect transfer or
   relocated branch.  The CFG is therefore a DAG; its paths from each entry
   are enumerated (at most 64) and each ends at the region's end or at the
   point a branch leaves for.
4. Decoding.  P_i decodes, instruction by instruction, to exactly the
   declared encodings, and I re-decodes to exhaustion with each P_i on its
   own boundaries.
5. Relocations.  R_i's relocated fields are all 32-bit `DIR32` fields that
   name a symbol outside the function's own section.  P_i declares its
   relocated fields, sorted by offset, as a bijection onto them: each field
   of P_i takes one of R_i's relocation records whole (its type and target
   symbol), and every record is taken once.  The order is free because the
   simulator names a relocated value by its target alone: it reads every
   relocated field of R_i and P_i as ``("sym", target)`` plus the field's
   own inline addend, so a field paired with another record of the same
   target denotes the same value and one paired with another target a
   different atom.  It refuses any relocated field it does not consume as
   an address displacement or an immediate, so every record is read.
6. Layout.  M is the identity before s_1 and shifts by the accumulated
   length change after each region; the code's data tail (switch tables)
   moves with the last instruction.  A relative call without a relocation
   (a call to a label of this body) is refused.  Every relative branch outside the
   regions keeps its encoding width and is re-encoded for M; one that no
   longer fits is refused (a short branch is never widened: that would be a
   code change no region proves).  Every in-body relocation (a switch table
   entry, a table base) has its addend re-encoded for M and must name an
   instruction boundary or a tail offset.  The re-decoded image keeps every
   outside instruction's length, opcode, flow class and mapped target.
7. Liveness.  Register and per-flag liveness are computed on D and on I.
8. Simulation (`region_simulation`).  R_i and P_i are executed from one
   symbolic entry state, once from each entry (the start, and each declared
   entry and its P_i instruction).  For every pair of paths whose conditions
   do not contradict each other (two paths of a deterministic run from one
   entry state never do), the donor's path leaves at some x and the
   replacement's at M(x), and at that exit (its liveness, its mapping):
   a. ESP is equal;
   b. every register with an atom live at the exit in D or in I is equal;
   c. every flag live at the exit in D or in I is equal (ZF compared by its
      exact normal form, see `region_simulation.canonical_flag`);
   d. the two versions make the same calls (event terms, see
      `region_simulation._call`: a call is admitted only to a callee whose C
      decoration fixes a register-free convention, and is named by the
      callee, ESP, the canonical store log since the previous call and that
      call), and the store sequences after the last call are equal up to
      reordering provably disjoint stores (pushes included);
   e. the two memory footprints (address and width of every access) are
      equal, so one faults exactly when the other does; and
   f. every entry register and flag that any compared term, store, access
      or path condition mentions is live at the region entry in D or in I
      (all of its atoms), so the symbolic entry state stands for values the
      two programs really share; a register both versions leave exactly at
      its entry value needs only its exit-live atoms live at the entry.
   g. x87 (when either version runs an x87 instruction): every entry depth
      the donor's stack discipline allows at the region entry
      (`region_x87.x87_stack_depths`) covers the deepest entry register
      either version touches and leaves room for its highest push; both
      leave the same net push and equal terms in every register from TOP
      down (`region_simulation.x87_stacks_equivalent`); every C0-C3 bit live
      at the exit in D or in I is equal; and neither body stores the x87
      environment (`fnstenv`, `fnsave`, `fxsave`).  Sticky exception flags
      are covered by 8e: every operation that can raise one is in the
      footprint.  The x87 state is compared even when neither version
      touches it (it then passes through, or is the same call's result).
      A direct call inside the region to a C function whose x87 return
      count r the donor's discipline determines
      (`region_x87.x87_stack_solution`) leaves a stack of exactly r values,
      the callee's result term named by the call's event on top, and x87
      code may follow it (`region_simulation._call`); the stack must be
      empty at the call: from the region's entry frame the entry depth on
      that path is then -push, which must lie in the donor's depth interval
      at the region entry, and after an earlier such call the simulator
      requires push 0.
9. Pins.  The image digest and length, the per-region length change, the
   branch re-encodings, relocation reseats, addend repairs, path counts, the
   bijection's rewritten bytes and changes of mapping, an x87 region's
   entry depths, need, peak, compared condition bits and the x87 return
   counts of the callees it calls (`call_returns`, present when it calls
   one), and the derived
   donor's procedure range are all pinned by the declaration and re-measured
   here, and the derived donor object is re-parsed and checked before the
   same-slot delegate installs it.

10. Scope bijection (optional).  A record may declare a register
    permutation sigma (fixing ESP; naming EBP only with the frame-pointer-free
    proof of `register_reencoding`: an FPO record with FRAME_FPO and no SEH,
    and no instruction deriving EBP from ESP) and scopes, disjoint ranges of
    D's instruction boundaries.  A point p outside every region interior is
    *mapped* when it lies in a scope.

    a. Every instruction outside the regions at a mapped point is rewritten
       field by field under sigma (a byte field stays within AL..BL/AH..BH),
       and may touch a support register only through such a field: an
       implicit operand (a call's arguments or clobbers, a return's live set,
       a frozen sub-register or string operand) is refused.  The re-decoded
       image instruction keeps length, opcode (the register bits of an
       opcode-register form aside), flow and mapped target; its register
       reads and writes are sigma's image of the donor's, its atoms on every
       other register are the donor's, and it touches no support register
       implicitly either.
    b. On every CFG edge from an instruction outside the regions whose two
       ends differ in mapping, and at every entry (the function's, an
       external entry, a relocated in-body target) that is mapped, every
       support register is dead in D and in I, at atom and at register
       granularity.
    c. Check 8 runs with the replacement started from the renamed entry
       state (its sigma(r) holds D's entry r when the region's start is
       mapped) and compares D's r with I's sigma(r) at the exit when the end
       is mapped.

    The invariant at a mapped point p is: memory, ESP and the live flags are
    equal; every register sigma leaves alone agrees atom by atom on the
    union of the two atom live sets; and I's sigma(r) equals D's r in all 32
    bits for every support register r that D has live, or whose image I has
    live, at *register* granularity (a write narrower than 32 bits counts as
    a read, so a partial write never re-establishes a whole register).  A
    rewritten instruction preserves it because it computes the same function
    of sigma-renamed inputs into sigma-renamed outputs (10a); a region
    preserves it by check 8 under the renaming (8f then asks that a support
    register read at a mapped entry be live there at register granularity);
    and at a change of mapping both correspondences agree because no support
    register is live (10b).  Outside every scope the invariant is the
    unmapped one above.

x87.  The invariant at a point also says the two x87 units agree on TOP,
on every full register (and so on the tag word), on the control word and
the sticky exception flags, and on the C0-C3 bits live there.  An outside
instruction preserves it because it is the same instruction on equal
inputs; check 8g re-establishes it at a region exit.  Assumptions: (x1)
MSVC 5.0's x87 discipline in D, as `region_x87` states it -- one depth per
program point, an empty stack at every call to a C function and at the
function's entries, 0 or 1 values at a return, and each callee leaving the
fixed number of values its prototype names, so a callee whose count the
donor's own uses determine leaves that many values at a call inside a
region too; (x2) the contents of empty
registers and the x87 instruction and data pointers are not inputs of any
callee (the bodies themselves are checked not to store them); (x3) C0-C3
are not inputs of a callee; and (x4) the shared control word masks every
floating-point exception (MSVC's CRT default 0x27F; lrr's objects contain
no `fldcw`), so an exception changes only the sticky flags, which the
footprint covers, and never traps between the two versions' differing
schedules.  No precision or rounding mode is assumed: no term identity
depends on one.

Compiler helpers.  A direct call inside a region to a compiler helper
(``__ftol``, ``__chkstk``) runs the helper's own bytes inline, read from
the authenticated toolchain library (:func:`region_helper_callees`,
`toolchain_helpers`); its ``fldcw`` must keep the shared word's exception
masks, so x4 still holds.  The record pins the library and body digests
(``expected_helper_callees``); a helper the donor calls outside every
region is neither simulated nor pinned.  An inlined helper's stores wholly
below ESP after it returns are dead stack and leave the store log, as a
call event's callee frame does (`function_validation`'s a6).

Calls.  A direct call to a symbol whose MSVC C decoration is ``_name`` or
``_name@N`` (or that thunk's ``__imp_`` slot) reads no general register: only
``__fastcall`` and C++ member functions take register arguments.  Compiler
and runtime helpers (an identifier that itself starts with an underscore) and
every other callee keep the decoder's EAX/ECX/EDX reads.  This is the same
callee model as above: a callee honours the convention its decoration names.

Line rows inside a region interior are carried to the replacement's first
byte: rows are debug metadata only, and the count is kept.
"""

from __future__ import annotations

import itertools
from collections.abc import Iterator, Mapping
from contextlib import contextmanager
from typing import Any, cast

from reprobit.binary import ByteIdentityError, require
from reprobit.coff_format import (
    CoffObject,
    coff_auxiliary,
    coff_body,
    coff_unpack,
    detailed_relocations,
)
from reprobit.ia32_decode import supported_ia32_instruction_length

from .candidate_recipe import (
    CandidateRecipe,
    candidate_proof,
    candidate_relocation_semantics,
    install_same_slot,
    internal_relocation_targets,
    open_candidate_seats,
    pin_candidate_bodies,
    relocation_symbol_map,
    require_declared_internal_targets,
    require_pinned_length,
    same_slot_effective,
)
from .coff import (
    _coff_marker,
    _coff_section_symbol,
    _coff_table_bytes,
    _comdat_child,
    _comdat_child_closure,
    comdat_primary_identity_multiset,
    function_multiset,
    function_symbol,
)
from .debug import (
    CODEVIEW_PROCEDURE_RECORD_TYPES,
    MSVC50_FUNCTION_FILL_BYTE,
    _apply_replacements,
    parse_codeview_symbol_stream,
    parse_fpo_data,
    shifted_pointer,
)
from .foundation import local_symbol_kind, require_payload_free_declaration, sha256_bytes
from .region_simulation import (
    FLAG_NAMES,
    X87_CONDITION_BITS,
    HelperCode,
    RelocationTarget,
    canonical_flag,
    contradictory,
    lin_atom,
    register_free_callee,
    simulate_region,
    stores_equivalent,
    term_atoms,
    x87_stacks_equivalent,
)
from .region_x87 import (
    require_x87_depth,
    x87_condition_liveness,
    x87_environment_exposures,
    x87_stack_solution,
)
from .register_reencoding import require_frame_pointer_free_frame
from .register_semantics import (
    _IA32_ATOMS_OF,
    _IA32_REGISTER_NUMBERS,
    IA32_GENERAL_REGISTER_NAMES,
    _bijection_form_for,
    _ia32_backward_liveness,
    _register_bijection_live_sets,
    decode_ia32_bijection_body,
    ia32_register_atoms,
)
from .relational import (
    ia32_relational_flag_liveness,
    ia32_relational_flow_walk,
    relational_form_external_entries,
)
from .toolchain_helpers import HelperLibrary, compiler_helper

REGION_RESIZE_KIND = "simulated_region_resize_v1"
REGION_RESIZE_CLASS = "retail_exact_region_resize_rewriting"
_DIR32 = 0x0006
_DIR32NB = 0x0007
_CODE_RELOCATION_TYPES = frozenset({_DIR32, _DIR32NB, 0x0014})
# CodeView records that carry no code offset of their own: the procedure
# record (handled), locals, register and constant records, UDTs, the end.
_OFFSET_FREE_CODEVIEW_TYPES = frozenset(
    {0x0001, 0x0002, 0x0003, 0x0004, 0x0006, 0x0200, 0x1001, 0x1002, 0x1003, 0x1006}
)
_BRANCH_FORMS = {**{0x70 | code: 1 for code in range(16)}, 0xEB: 1, 0xE9: 4}


class RegionRefusal(ByteIdentityError):
    """A refusal that one declared region (``region``, its ordinal) caused."""

    def __init__(self, message: str, region: int) -> None:
        super().__init__(message)
        self.region = region


@contextmanager
def _region_refusals(ordinal: int) -> Iterator[None]:
    """Name the region a refusal inside its own checks belongs to."""
    try:
        yield
    except RegionRefusal:
        raise
    except ByteIdentityError as exc:
        raise RegionRefusal(str(exc), ordinal) from exc


_BYTE_REGISTERS = frozenset({"eax", "ecx", "edx", "ebx"})
_CALL_CLOBBERED = frozenset({"eax", "ecx", "edx"})
_REL32 = 0x0014


class ScopeBoundRefusal(ByteIdentityError):
    """A refusal of check 10b: ``offset`` is a scope bound where a support register is live."""

    def __init__(self, message: str, offset: int) -> None:
        super().__init__(message)
        self.offset = offset


def refine_call_reads(
    instructions: list[dict[str, Any]], relocations: dict[int, Any]
) -> list[dict[str, Any]]:
    """The decoded body with a register-free direct call reading no caller-saved register.

    The decoder lets every call to an undecorated or C callee read EAX, ECX
    and EDX, since it cannot tell a register argument from none.  A direct
    ``call rel32`` or ``call [abs32]`` whose relocated callee
    :func:`register_free_callee` admits reads only the stack; it still
    clobbers the three registers.
    """
    refined = []
    for item in instructions:
        if item["flow"] == "call" and not (item["reads"] & {"ebx", "esi", "edi", "ebp"}):
            field = item["offset"] + item["length"] - 4
            row = relocations.get(field)
            memory = item["memory"]
            direct = memory is None or (
                memory["absolute"] and memory["base"] is None and memory["index"] is None
            )
            if (
                direct
                and row is not None
                and row.get("width") == 4
                and register_free_callee(row.get("target"))
            ):
                item = {
                    **item,
                    "reads": frozenset(item["reads"] - _CALL_CLOBBERED),
                    "read_atoms": frozenset(
                        item["read_atoms"] - ia32_register_atoms(_CALL_CLOBBERED)
                    ),
                }
        refined.append(item)
    return refined


def _validate_bijection(
    value: object,
    boundaries: set[int],
    limit: int,
    frame_pointer_free: bool,
    context: str,
) -> tuple[dict[str, str], list[tuple[int, int]]]:
    """The declared scope bijection: a register permutation and the ranges it rules."""
    require_payload_free_declaration(value, f"{context} bijection declaration")
    require(
        isinstance(value, dict) and set(value) == {"mapping", "scopes"},
        f"{context}: the bijection names an unknown or missing field",
    )
    item = cast(dict[str, Any], value)
    mapping = item["mapping"]
    require(
        isinstance(mapping, dict)
        and bool(mapping)
        and all(
            isinstance(key, str) and isinstance(target, str) for key, target in mapping.items()
        ),
        f"{context}: the bijection mapping is not a register map",
    )
    mapping = cast(dict[str, str], mapping)
    require(
        set(mapping) <= set(_IA32_REGISTER_NUMBERS)
        and set(mapping.values()) == set(mapping)
        and len(set(mapping.values())) == len(mapping)
        and all(source != target for source, target in mapping.items()),
        f"{context}: the bijection mapping is not a fixed-point-free permutation of one "
        "register set",
    )
    require(
        "esp" not in mapping,
        f"{context}: the bijection names ESP, whose encodings carry ModRM/SIB structure",
    )
    require(
        frame_pointer_free or "ebp" not in mapping,
        f"{context}: the bijection names EBP without a frame-pointer-free proof for this body",
    )
    scopes = item["scopes"]
    require(
        isinstance(scopes, list)
        and bool(scopes)
        and all(
            isinstance(pair, list) and len(pair) == 2 and all(type(bound) is int for bound in pair)
            for pair in scopes
        ),
        f"{context}: the bijection scopes are not a list of ranges",
    )
    ranges = [(int(pair[0]), int(pair[1])) for pair in cast(list[list[int]], scopes)]
    for start, end in ranges:
        require(
            0 <= start < end <= limit
            and start in boundaries
            and (end in boundaries or end == limit),
            f"{context}: the bijection scope [{start}, {end}) is not on instruction boundaries "
            "of the code",
        )
    for (_left_start, left_end), (right_start, _right_end) in itertools.pairwise(ranges):
        require(
            left_end < right_start,
            f"{context}: the bijection scopes are unsorted, overlapping or adjacent",
        )
    return dict(mapping), ranges


def _field_registers(code: bytes, item: dict[str, Any]) -> set[str]:
    """The general registers an instruction names through a rewritable field."""
    names = IA32_GENERAL_REGISTER_NAMES
    found = {names[code[at] >> shift & 7] for at, shift in item["fields"]}
    found |= {names[code[at] >> shift & 3] for at, shift in item.get("byte_fields", ())}
    return found


def _touched_registers(item: dict[str, Any]) -> set[str]:
    """Every general register an instruction reads or writes, at any width."""
    atoms = set(item["read_atoms"]) | set(item["write_atoms"])
    return set(item["reads"]) | set(item["writes"]) | {atom.split(".")[0] for atom in atoms}


def _implicit_support(code: bytes, item: dict[str, Any], support: set[str]) -> list[str]:
    """Support registers the instruction touches other than through a rewritable field."""
    frozen = set(item.get("frozen", frozenset())) - set(item.get("byte_frozen", frozenset()))
    implicit = (_touched_registers(item) - _field_registers(code, item)) | frozen
    return sorted(implicit & support)


def _sigma_rewrite(
    image: bytearray,
    item: dict[str, Any],
    mapping: dict[str, str],
    relocated_fields: set[int],
    context: str,
) -> list[int]:
    """Rewrite one instruction's register fields under ``mapping``; the changed offsets.

    The instruction must name every support register it touches through a
    rewritable field: an implicit operand (a call's clobbers or arguments, a
    return's live set, a frozen sub-register or string operand) would keep
    its register while the value moved, so it is refused.  A byte field may
    only move within AL..BL / AH..BH.
    """
    support = set(mapping)
    numbers = {
        _IA32_REGISTER_NUMBERS[key]: _IA32_REGISTER_NUMBERS[value] for key, value in mapping.items()
    }
    at = item["offset"]
    implicit = _implicit_support(bytes(image), item, support)
    require(
        not implicit,
        f"{context}: the instruction at {at} touches {implicit} other than through a field the "
        "bijection can rewrite",
    )
    stranded = sorted(
        name
        for name in support
        if any(
            IA32_GENERAL_REGISTER_NAMES[image[byte] >> shift & 3] == name
            for byte, shift in item.get("byte_fields", ())
        )
        and (name not in _BYTE_REGISTERS or mapping[name] not in _BYTE_REGISTERS)
    )
    require(
        not stranded,
        f"{context}: {stranded} is named by a byte field at {at} that the bijection would move off "
        "a byte register",
    )
    changed = []
    for byte, shift in item["fields"]:
        value = image[byte] >> shift & 7
        if value not in numbers:
            continue
        require(
            byte not in relocated_fields,
            f"{context}: a rewritten register field at {byte} overlaps a relocation",
        )
        image[byte] = (image[byte] & ~(7 << shift) | numbers[value] << shift) & 0xFF
        changed.append(byte)
    for byte, shift in item.get("byte_fields", ()):
        value = image[byte] >> shift & 7
        if value & 3 not in numbers:
            continue
        require(
            byte not in relocated_fields,
            f"{context}: a rewritten register field at {byte} overlaps a relocation",
        )
        image[byte] = (
            image[byte] & ~(7 << shift) | (numbers[value & 3] | value & 4) << shift
        ) & 0xFF
        changed.append(byte)
    return sorted(set(changed))


def _require_sigma_image(
    item: dict[str, Any],
    image_bytes: bytes,
    other: dict[str, Any],
    mapping: dict[str, str],
    context: str,
) -> None:
    """The re-decoded image instruction is exactly the bijection's image of the donor's."""
    support = set(mapping)

    def image_of(names: Any) -> frozenset[str]:
        return frozenset(mapping.get(name, name) for name in names)

    def split(atoms: Any) -> tuple[frozenset[str], frozenset[str]]:
        plain = frozenset(atom for atom in atoms if atom.split(".")[0] not in support)
        mapped = frozenset(atom.split(".")[0] for atom in atoms if atom.split(".")[0] in support)
        return plain, mapped

    at = item["offset"]
    require(
        other["reads"] == image_of(item["reads"]) and other["writes"] == image_of(item["writes"]),
        f"{context}: the image's operand set at donor {at} is not the bijection's image",
    )
    for key in ("read_atoms", "write_atoms"):
        plain, mapped = split(item[key])
        other_plain, other_mapped = split(other[key])
        require(
            other_plain == plain and other_mapped == image_of(mapped),
            f"{context}: the image's {key.replace('_', ' ')} at donor {at} are not the "
            "bijection's image",
        )
    implicit = _implicit_support(image_bytes, other, support)
    require(
        not implicit,
        f"{context}: the image instruction for donor {at} touches {implicit} implicitly",
    )


def _register_level_live(
    instructions: list[dict[str, Any]], successors: list[list[int]], context: str
) -> list[frozenset[str]]:
    """Whole-register liveness: a write narrower than 32 bits is a read and never a kill.

    The decoder's ``reads``/``writes`` sets are exactly this view for every
    register an instruction names through a field, which is every support
    register an in-scope instruction may touch.
    """
    view = [
        {"read_atoms": frozenset(item["reads"]), "write_atoms": frozenset(item["writes"])}
        for item in instructions
    ]
    return _ia32_backward_liveness(view, successors, context)


def _cover(
    name: str,
    sigma: dict[str, str],
    live: tuple[frozenset[str], frozenset[str], frozenset[str], frozenset[str]],
) -> frozenset[str]:
    """The atoms of donor register ``name`` the two states agree on at one point.

    ``live`` is (donor atoms, image atoms, donor registers, image registers)
    live at the point.  Outside a scope, or for a register the bijection does
    not move, the states agree atom by atom on the union of the two atom live
    sets.  Inside a scope a moved register is compared whole: the image's
    ``sigma(name)`` equals the donor's ``name`` in all 32 bits whenever the
    donor has ``name`` or the image has ``sigma(name)`` live at register
    granularity, and nothing is known otherwise.
    """
    donor_atoms, image_atoms, donor_registers, image_registers = live
    atoms = _IA32_ATOMS_OF[name]
    if name in sigma:
        if name in donor_registers or sigma[name] in image_registers:
            return atoms
        return frozenset()
    return atoms & (donor_atoms | image_atoms)


def _hex_instruction(text: object, context: str) -> bytes:
    require(
        isinstance(text, str) and bool(text) and len(text) % 2 == 0 and len(text) <= 30,
        f"{context}: an encoding is not a hex instruction",
    )
    try:
        raw = bytes.fromhex(cast(str, text))
    except ValueError as exc:
        raise ByteIdentityError(f"{context}: an encoding is not a hex instruction") from exc
    require(
        cast(str, text) == raw.hex(),
        f"{context}: an encoding is not canonical lowercase hex",
    )
    length = supported_ia32_instruction_length(raw, context)
    require(length == len(raw), f"{context}: an encoding is not exactly one instruction")
    return raw


def _branch_width(body: bytes, item: dict[str, Any], context: str) -> int:
    opcode = body[item["offset"]]
    if opcode == 0x0F:
        require(
            0x80 <= body[item["offset"] + 1] <= 0x8F,
            f"{context}: the branch at {item['offset']} has an unknown form",
        )
        return 4
    width = _BRANCH_FORMS.get(opcode)
    require(
        width is not None, f"{context}: the branch at {item['offset']} has a prefix or unknown form"
    )
    return cast(int, width)


def _validate_regions(regions: object, context: str) -> list[dict[str, Any]]:
    require_payload_free_declaration(regions, f"{context} region-resize declaration")
    require(isinstance(regions, list) and bool(regions), f"{context}: no region is declared")
    validated = []
    for ordinal, item in enumerate(cast(list[Any], regions)):
        item_context = f"{context} region {ordinal}"
        require(isinstance(item, dict), f"{item_context}: the region is not an object")
        require(
            {
                "region_start",
                "region_end",
                "replacement_instructions",
                "replacement_relocations",
            }
            <= set(item)
            <= {
                "region_start",
                "region_end",
                "replacement_instructions",
                "replacement_relocations",
                "replacement_entries",
            },
            f"{item_context}: the region names an unknown or missing field",
        )
        start, end = item["region_start"], item["region_end"]
        require(
            type(start) is int and type(end) is int and 0 <= start < end,
            f"{item_context}: bounds are invalid",
        )
        encodings = item["replacement_instructions"]
        require(
            isinstance(encodings, list) and len(encodings) <= 256,
            f"{item_context}: the replacement is not a list of encodings",
        )
        pieces = [_hex_instruction(text, item_context) for text in encodings]
        pairs = item["replacement_relocations"]
        require(
            isinstance(pairs, list)
            and all(
                isinstance(pair, list)
                and len(pair) == 2
                and all(type(value) is int and value >= 0 for value in pair)
                for pair in pairs
            ),
            f"{item_context}: the replacement relocations are invalid",
        )
        boundaries = [sum(len(piece) for piece in pieces[:k]) for k in range(len(pieces))]
        entries = item.get("replacement_entries", [])
        require(
            isinstance(entries, list)
            and bool(entries) == ("replacement_entries" in item)
            and all(
                isinstance(pair, list)
                and len(pair) == 2
                and all(type(value) is int for value in pair)
                and start < pair[0] < end
                and pair[1] in boundaries
                for pair in entries
            )
            and [pair[0] for pair in entries] == sorted({pair[0] for pair in entries}),
            f"{item_context}: the replacement entries are not sorted interior points mapped to "
            "replacement instructions",
        )
        validated.append(
            {
                "start": start,
                "end": end,
                "replacement": b"".join(pieces),
                "boundaries": boundaries,
                "relocations": [tuple(pair) for pair in pairs],
                "entries": {int(pair[0]): int(pair[1]) for pair in entries},
            }
        )
    for left, right in itertools.pairwise(validated):
        require(left["end"] <= right["start"], f"{context}: regions are unsorted or overlapping")
    return validated


def apply_region_resize(
    body: bytes,
    regions: list[Any],
    rows: list[dict[str, Any]],
    section_number: int,
    context: str,
    *,
    code_length: int | None = None,
    proc_size: int | None = None,
    external_entries: frozenset[int] = frozenset(),
    protected_offsets: frozenset[int] = frozenset(),
    prologue_length: int = 0,
    bijection: object = None,
    frame_pointer_free: bool = False,
    helpers: Mapping[str, HelperCode] | None = None,
) -> tuple[bytes, dict[str, Any]]:
    """Install each declared replacement, relay the body out, and prove it (checks 1-8).

    ``rows`` are the donor's detailed relocation records; ``code_length`` the
    end of its code (before any switch table), ``proc_size`` the end of its
    procedure (before MSVC 5.0's alignment fill; the body's length when
    None).  ``protected_offsets`` are offsets other records name (section
    symbols, the CodeView procedure range, closure-child references), none of
    which may lie in a region interior.  ``bijection``, when given, is the
    declared scope bijection of check 10; ``frame_pointer_free`` states that
    the caller proved EBP is not this body's frame pointer.  ``helpers`` maps
    each compiler helper a region calls to its verified body
    (:func:`region_helper_callees`), which the simulator runs inline.
    Returns the unpadded image (code and tail) and the proof; the caller
    pads it.
    """
    body = bytes(body)
    require(bool(body), f"{context}: body is empty")
    declared = _validate_regions(regions, context)
    proc = len(body) if proc_size is None else proc_size
    limit = proc if code_length is None else code_length
    require(
        0 < limit <= proc <= len(body), f"{context}: the code and procedure extents are invalid"
    )
    require(
        all(byte == MSVC50_FUNCTION_FILL_BYTE for byte in body[proc:]),
        f"{context}: the bytes after the procedure are not alignment fill",
    )
    for row in rows:
        require(
            row["type"] in _CODE_RELOCATION_TYPES or row["offset"] >= limit,
            f"{context}: the relocation at {row['offset']} has a type outside the closed set",
        )
    relocated_fields = {row["offset"] for row in rows}
    relocation_view = relocation_symbol_map(rows)
    decode_view = None if limit == len(body) else limit
    donor_body = body[:proc]
    instructions = refine_call_reads(
        decode_ia32_bijection_body(body, f"{context} donor", relocation_view, decode_view),
        relocation_view,
    )
    index_of = {item["offset"]: index for index, item in enumerate(instructions)}
    for item in instructions:
        # A relative call without a relocation names an offset of this body
        # that the decoder does not report as a branch target, so the layout
        # could neither repair nor check it.
        require(
            not (item["flow"] == "call" and body[item["offset"]] == 0xE8)
            or item["offset"] + 1 in relocated_fields,
            f"{context}: the relative call at {item['offset']} has no relocation; a layout change "
            "would retarget it",
        )
    internal_targets = internal_relocation_targets(rows, section_number)
    items, successors, entries = ia32_relational_flow_walk(
        body, relocation_view, f"{context} donor flow", decode_view, external_entries
    )
    entry_offsets = {items[index]["offset"] for index in entries[1:]}
    own_rows = [row for row in rows if row["target_section"] == section_number]
    # Checks 1-3 on the donor side.
    for ordinal, region in enumerate(declared):
        with _region_refusals(ordinal):
            region_context = f"{context} region {ordinal}"
            start, end = region["start"], region["end"]
            require(
                start in index_of and end in index_of and end < limit,
                f"{region_context}: the region is not on instruction boundaries inside the code",
            )
            require(
                start >= prologue_length, f"{region_context}: the region overlaps the FPO prologue"
            )

            declared_entries = region["entries"]

            def interior(
                offset: int, start: int = start, end: int = end, entries: Any = declared_entries
            ) -> bool:
                """An interior offset that is not a declared entry."""
                return start < offset < end and offset not in entries

            for offset in declared_entries:
                require(
                    offset in index_of,
                    f"{region_context}: the declared entry {offset} is not an instruction boundary",
                )
            for item in instructions:
                if item["target"] is not None and not start <= item["offset"] < end:
                    require(
                        not interior(item["target"]),
                        f"{region_context}: the branch at {item['offset']} targets the region "
                        "interior",
                    )
            for offset in entry_offsets | set(internal_targets):
                require(
                    not interior(offset),
                    f"{region_context}: an external entry or relocated target at {offset} lies "
                    "inside the region",
                )
            for offset in protected_offsets:
                require(
                    not interior(offset),
                    f"{region_context}: a symbol or debug record names the region interior at "
                    f"{offset}",
                )
            for item in instructions:
                if not start <= item["offset"] < end:
                    continue
                require(
                    item["flow"] in ("fall", "jcc", "jmp", "call") and not item["indirect"],
                    f"{region_context}: the region holds a {item['flow']} at {item['offset']}",
                )
                if item["flow"] in ("jcc", "jmp"):
                    target = item["target"]
                    require(
                        target is not None
                        and (item["offset"] < target <= end or not start <= target <= end)
                        and target < limit,
                        f"{region_context}: the branch at {item['offset']} goes backward inside "
                        "the region or leaves the code",
                    )
            region_rows = [row for row in rows if start <= row["offset"] < end]
            call_fields = {
                item["offset"] + 1
                for item in instructions
                if start <= item["offset"] < end
                and item["flow"] == "call"
                and body[item["offset"]] == 0xE8
            }
            for row in region_rows:
                require(
                    row["offset"] + row["width"] <= end
                    and (
                        row["type"] == _DIR32
                        or (row["type"] == _REL32 and row["offset"] in call_fields)
                    )
                    and row["width"] == 4
                    and row["target_section"] != section_number,
                    f"{region_context}: the relocation at {row['offset']} is neither an external "
                    "DIR32 field nor a call's REL32 field",
                )
            # Check 5: a bijection of relocated fields, each keeping its record.
            pairs = region["relocations"]
            require(
                sorted(donor for _local, donor in pairs)
                == sorted(row["offset"] for row in region_rows)
                and len({donor for _local, donor in pairs}) == len(pairs),
                f"{region_context}: the replacement's relocations are not the region's, each once",
            )
            locals_ = [local for local, _donor in pairs]
            require(
                locals_ == sorted(set(locals_))
                and all(local + 4 <= len(region["replacement"]) for local in locals_),
                f"{region_context}: the replacement's relocated fields are unsorted or out of "
                "range",
            )
            region["rows"] = region_rows
    # Check 10a: the scope bijection's declaration and its rewrite.
    sigma: dict[str, str] = {}
    scopes: list[tuple[int, int]] = []
    if bijection is not None:
        sigma, scopes = _validate_bijection(
            bijection, set(index_of), limit, frame_pointer_free, f"{context} bijection"
        )

    def scoped(offset: int) -> bool:
        return any(left <= offset < right for left, right in scopes)

    def outside_regions(offset: int) -> bool:
        return not any(region["start"] <= offset < region["end"] for region in declared)

    def a_point(offset: int) -> bool:
        """Outside every region interior, or a declared entry of one."""
        return not any(
            region["start"] < offset < region["end"] and offset not in region["entries"]
            for region in declared
        )

    for ordinal, region in enumerate(declared):
        with _region_refusals(ordinal):
            exits = set()
            for item in instructions:
                if region["start"] <= item["offset"] < region["end"] and item["flow"] in (
                    "jcc",
                    "jmp",
                ):
                    target = item["target"]
                    if not region["start"] <= target <= region["end"]:
                        require(
                            a_point(target),
                            f"{context} region {ordinal}: the branch at {item['offset']} leaves "
                            f"for {target}, inside another region",
                        )
                        exits.add(target)
            region["exits"] = exits

    base = bytearray(donor_body)
    sigma_bytes: set[int] = set()
    for item in instructions:
        if outside_regions(item["offset"]) and scoped(item["offset"]):
            sigma_bytes |= set(
                _sigma_rewrite(base, item, sigma, relocated_fields, f"{context} bijection")
            )
    # Check 6: the layout.
    shifts: list[tuple[int, int, int]] = []
    delta = 0
    for region in declared:
        growth = len(region["replacement"]) - (region["end"] - region["start"])
        region["image_start"] = region["start"] + delta
        delta += growth
        region["growth"] = growth
        shifts.append((region["start"], region["end"], delta))

    def mapped(offset: int) -> int:
        """M on every offset outside a region interior (and region starts and entries)."""
        moved = 0
        for (start, end, accumulated), region in zip(shifts, declared, strict=True):
            if offset >= end:
                moved = accumulated
            elif offset > start:
                if offset in region["entries"]:
                    return cast(int, region["image_start"] + region["entries"][offset])
                raise ByteIdentityError(f"{context}: offset {offset} lies inside a region")
        return offset + moved

    pieces: list[bytes] = []
    cursor = 0
    for region in declared:
        pieces.append(bytes(base[cursor : region["start"]]))
        pieces.append(region["replacement"])
        cursor = region["end"]
    pieces.append(bytes(base[cursor:]))
    image = bytearray(b"".join(pieces))
    image_limit = mapped(limit)
    image_proc = mapped(proc)
    require(
        len(image) == image_proc and image_proc > 0,
        f"{context}: the image is not the concatenation of its pieces",
    )
    branch_repairs = []
    for item in instructions:
        if item["flow"] not in ("jcc", "jmp") or item["target"] is None:
            continue
        if any(region["start"] <= item["offset"] < region["end"] for region in declared):
            continue
        width = _branch_width(body, item, context)
        new_at = mapped(item["offset"])
        new_end = new_at + item["length"]
        displacement = mapped(item["target"]) - new_end
        require(
            -(1 << (8 * width - 1)) <= displacement < 1 << (8 * width - 1),
            f"{context}: the branch at {item['offset']} no longer reaches its target in "
            f"{width} displacement byte(s); widening it is a code change no region proves",
        )
        encoded = displacement.to_bytes(width, "little", signed=True)
        if bytes(image[new_end - width : new_end]) != encoded:
            image[new_end - width : new_end] = encoded
            branch_repairs.append(new_at)
    reseat: list[list[int]] = []
    image_view: dict[int, dict[str, Any]] = {}
    region_maps: list[dict[int, RelocationTarget]] = [{} for _region in declared]
    for row in rows:
        owner = next(
            (
                position
                for position, region in enumerate(declared)
                if region["start"] <= row["offset"] < region["end"]
            ),
            None,
        )
        if owner is None:
            new_offset = mapped(row["offset"]) if row["offset"] < limit else row["offset"] + delta
        else:
            region = declared[owner]
            local = next(local for local, donor in region["relocations"] if donor == row["offset"])
            new_offset = region["image_start"] + local
            region_maps[owner][local] = (
                ("rel32", row["target"]) if row["type"] == _REL32 else row["target"]
            )
        if new_offset != row["offset"]:
            reseat.append([row["offset"], new_offset])
        image_view[new_offset] = {"width": row["width"], "target": row["target"]}
    require(len(image_view) == len(rows), f"{context}: the reseat collides two relocation records")
    moved = {old: new for old, new in reseat}
    addend_repairs = []
    symbol_values = {row["target"]: row["target_value"] for row in own_rows}
    for row in own_rows:
        require(
            row["type"] in (_DIR32, _DIR32NB) and row["width"] == 4,
            f"{context}: the in-body relocation at {row['offset']} is not a 32-bit absolute field",
        )
        at = moved.get(row["offset"], row["offset"])
        addend = int.from_bytes(image[at : at + 4], "little", signed=True)
        base = symbol_values[row["target"]]
        target = base + addend
        require(
            0 <= target < proc and (target in index_of or target >= limit) and a_point(target),
            f"{context}: the in-body relocation at {row['offset']} names {target}, not an "
            "instruction or table offset outside every region",
        )
        new_target = mapped(target) if target < limit else target + delta
        new_base = mapped(base) if base < limit else base + delta
        new_addend = new_target - new_base
        if new_addend != addend:
            image[at : at + 4] = new_addend.to_bytes(4, "little", signed=True)
            addend_repairs.append([at, addend, new_addend])
    image_bytes = bytes(image)
    # Check 4: the image re-decodes on the layout's boundaries.
    image_instructions = refine_call_reads(
        decode_ia32_bijection_body(
            image_bytes,
            f"{context} image",
            image_view,
            None if image_limit == len(image_bytes) else image_limit,
        ),
        image_view,
    )
    image_index = {item["offset"]: index for index, item in enumerate(image_instructions)}
    for region in declared:
        starts = [region["image_start"] + local for local in region["boundaries"]]
        inside = [
            item["offset"]
            for item in image_instructions
            if region["image_start"]
            <= item["offset"]
            < region["image_start"] + len(region["replacement"])
        ]
        require(
            inside == starts,
            f"{context}: the image does not decode the replacement on its own boundaries",
        )
    for item in instructions:
        if any(region["start"] <= item["offset"] < region["end"] for region in declared):
            continue
        new_at = mapped(item["offset"])
        require(
            new_at in image_index,
            f"{context}: the instruction at {item['offset']} did not land where M says",
        )
        other = image_instructions[image_index[new_at]]
        form = _bijection_form_for(item["opcode"])
        opcode_mask = (
            0xF8
            if scoped(item["offset"]) and form is not None and form["opreg"] is not None
            else 0xFFFF
        )
        require(
            other["length"] == item["length"]
            and other["opcode"] & opcode_mask == item["opcode"] & opcode_mask
            and other["flow"] == item["flow"]
            and other["indirect"] == item["indirect"]
            and other["target"] == (None if item["target"] is None else mapped(item["target"])),
            f"{context}: the image changed the instruction at {item['offset']}",
        )
        raw = body[item["offset"] : item["offset"] + item["length"]]
        new_raw = image_bytes[new_at : new_at + item["length"]]
        if scoped(item["offset"]):
            _require_sigma_image(item, image_bytes, other, sigma, f"{context} bijection")
        if raw != new_raw:
            allowed = {
                at - item["offset"]
                for at in sigma_bytes
                if item["offset"] <= at < item["offset"] + item["length"]
            }
            if new_at in branch_repairs:
                width = _branch_width(body, item, context)
                allowed |= set(range(item["length"] - width, item["length"]))
            for at, _old, _new in addend_repairs:
                if new_at <= at < new_at + item["length"]:
                    allowed |= set(range(at - new_at, at - new_at + 4))
            changed = {index for index in range(item["length"]) if raw[index] != new_raw[index]}
            require(
                changed <= allowed,
                f"{context}: the instruction at {item['offset']} changed outside a branch or "
                "addend repair",
            )
    tail_changes = {
        index for index in range(limit, proc) if body[index] != image_bytes[index + delta]
    }
    tail_allowed = {
        at - delta + k for at, _old, _new in addend_repairs if at >= image_limit for k in range(4)
    }
    require(
        tail_changes <= tail_allowed,
        f"{context}: the image changed the data tail outside an addend repair",
    )
    # Check 7: liveness on both bodies.
    donor_live, donor_successors = _register_bijection_live_sets(
        instructions, f"{context} donor liveness"
    )
    image_live, image_register_successors = _register_bijection_live_sets(
        image_instructions, f"{context} image liveness"
    )
    donor_registers_live = _register_level_live(
        instructions, donor_successors, f"{context} donor register liveness"
    )
    image_registers_live = _register_level_live(
        image_instructions, image_register_successors, f"{context} image register liveness"
    )

    def live_at(
        offset: int,
    ) -> tuple[frozenset[str], frozenset[str], frozenset[str], frozenset[str]]:
        """Donor and image liveness at a donor point outside every region interior."""
        donor_index, image_at = index_of[offset], image_index[mapped(offset)]
        return (
            donor_live[donor_index],
            image_live[image_at],
            donor_registers_live[donor_index],
            image_registers_live[image_at],
        )

    # Check 10b: the correspondence changes only where every support register
    # is dead in both versions, at atom and at register granularity.
    mode_changes: set[int] = set()
    if sigma:
        support = set(sigma)
        support_atoms = ia32_register_atoms(support)

        def require_dead(offset: int, why: str) -> None:
            donor_atoms, image_atoms, donor_registers, image_registers = live_at(offset)
            live_support = sorted(
                (support & (donor_registers | image_registers))
                | {atom.split(".")[0] for atom in support_atoms & (donor_atoms | image_atoms)}
            )
            if live_support:
                raise ScopeBoundRefusal(
                    f"{context} bijection: {live_support} is live at {offset}, where {why}", offset
                )

        for index, item in enumerate(instructions):
            if not outside_regions(item["offset"]):
                continue
            for edge in donor_successors[index]:
                target = instructions[edge]["offset"]
                if scoped(item["offset"]) != scoped(target):
                    require_dead(target, f"the edge from {item['offset']} crosses a scope bound")
                    mode_changes.add(target)
        for offset in sorted({0} | entry_offsets | set(internal_targets)):
            if offset < limit and scoped(offset):
                require(
                    offset in index_of,
                    f"{context} bijection: the entry {offset} is not an instruction boundary",
                )
                require_dead(offset, "control may enter the scope from outside the body's flow")
        require(
            bool(sigma_bytes)
            or any(scoped(region["start"]) or scoped(region["end"]) for region in declared),
            f"{context} bijection: the bijection rewrites nothing and rules no region bound",
        )
    donor_flag_live = ia32_relational_flag_liveness(items, successors, f"{context} donor flags")
    donor_item_index = {item["offset"]: index for index, item in enumerate(items)}
    image_items, image_successors, _image_entries = ia32_relational_flow_walk(
        image_bytes,
        image_view,
        f"{context} image flow",
        None if image_limit == len(image_bytes) else image_limit,
        frozenset(mapped(offset) for offset in external_entries),
    )
    image_flag_live = ia32_relational_flag_liveness(
        image_items, image_successors, f"{context} image flags"
    )
    image_item_index = {item["offset"]: index for index, item in enumerate(image_items)}
    # Check 7 (x87): C0-C3 liveness on both bodies, the environment stores of
    # either, and the donor's stack depths (computed only if a region needs them).
    donor_cc_live = x87_condition_liveness(items, successors, body, f"{context} donor x87 status")
    image_cc_live = x87_condition_liveness(
        image_items, image_successors, image_bytes, f"{context} image x87 status"
    )
    x87_exposures = x87_environment_exposures(items, body) + x87_environment_exposures(
        image_items, image_bytes
    )
    # The donor's stack discipline: the depth at every point and the x87
    # return count of every C callee it determines (for calls inside a region).
    x87_solution = x87_stack_solution(items, successors, entries, body, relocation_view)
    x87_returns = {} if x87_solution is None else x87_solution[1]

    def x87_depth(offset: int) -> tuple[int, int] | None:
        return None if x87_solution is None else x87_solution[0][donor_item_index[offset]]

    def x87_facts(offset: int) -> tuple[frozenset[str], Any]:
        """C0-C3 live at a donor point in D or at its image in I, and the x87 depth oracle."""
        return (
            donor_cc_live[donor_item_index[offset]]
            | image_cc_live[image_item_index[mapped(offset)]]
        ), x87_depth

    # Check 8: the simulation.
    proved = []
    for ordinal, region in enumerate(declared):
        with _region_refusals(ordinal):
            region_context = f"{context} region {ordinal}"
            start, end = region["start"], region["end"]
            image_start = region["image_start"]
            image_end = image_start + len(region["replacement"])
            donor_relocations: dict[int, RelocationTarget] = {
                row["offset"]: ("rel32", row["target"]) if row["type"] == _REL32 else row["target"]
                for row in region["rows"]
            }
            pairs = 0
            donor_count = 0
            image_count = 0
            compared_union: set[str] = set()
            flags_union: set[str] = set()
            entry_sigma = sigma if scoped(start) else {}
            exit_sigma = sigma if scoped(end) else {}
            x87_record: dict[str, Any] = {}
            for donor_entry, image_local in [(start, 0), *sorted(region["entries"].items())]:
                proof_context = (
                    region_context
                    if donor_entry == start
                    else f"{region_context} entry {donor_entry}"
                )
                pairs_here, compared, flags, counts = _prove_region_entry(
                    donor_body,
                    region,
                    region_maps[ordinal],
                    donor_relocations,
                    donor_entry,
                    image_local,
                    sigma if scoped(donor_entry) else {},
                    {
                        exit_point: sigma if scoped(exit_point) else {}
                        for exit_point in {end, *region["exits"]}
                    },
                    mapped,
                    live_at,
                    lambda offset: (
                        donor_flag_live[donor_item_index[offset]]
                        | image_flag_live[image_item_index[mapped(offset)]]
                    ),
                    proof_context,
                    x87_facts=x87_facts,
                    x87_exposures=x87_exposures,
                    x87_record=x87_record,
                    x87_returns=x87_returns,
                    helpers=helpers,
                )
                pairs += pairs_here
                donor_count += counts[0]
                image_count += counts[1]
                compared_union |= compared
                flags_union |= flags
            compared_registers = sorted(compared_union)
            compared_flags = sorted(flags_union)
            record = {
                "region_start": start,
                "region_end": end,
                "image_start": image_start,
                "image_end": image_end,
                "growth": region["growth"],
                "donor_paths": donor_count,
                "replacement_paths": image_count,
                "path_pairs": pairs,
                "compared_registers": compared_registers,
                "compared_flags": compared_flags,
            }
            if x87_record:
                record["x87"] = {
                    "entry_depths": [list(depth) for depth in sorted(x87_record["entry_depths"])],
                    "need": x87_record["need"],
                    "peak": x87_record["peak"],
                    "compared_condition_bits": sorted(x87_record["compared_condition_bits"]),
                }
                if x87_record.get("call_returns"):
                    record["x87"]["call_returns"] = dict(sorted(x87_record["call_returns"].items()))
            if sigma:
                record["entry_mapped"] = bool(entry_sigma)
                record["exit_mapped"] = bool(exit_sigma)
            if region["entries"]:
                record["entries"] = [
                    [offset, image_start + local]
                    for offset, local in sorted(region["entries"].items())
                ]
            if region["exits"]:
                record["exits"] = [[offset, mapped(offset)] for offset in sorted(region["exits"])]
            proved.append(record)
    offset_map: dict[int, int] = {}
    for item in instructions:
        if a_point(item["offset"]):
            offset_map[item["offset"]] = mapped(item["offset"])
    for offset in range(limit, len(body) + 1):
        offset_map[offset] = offset + delta
    proof: dict[str, Any] = {
        "kind": REGION_RESIZE_KIND,
        "regions": proved,
        "growth": delta,
        "code_length": limit,
        "image_code_length": image_limit,
        "proc_size": proc,
        "image_proc_size": image_proc,
        "branch_repairs": sorted(branch_repairs),
        "relocation_reseat": sorted(reseat),
        "addend_repairs": sorted(addend_repairs),
        "instruction_count": len(image_instructions),
        "offset_map": offset_map,
        "interiors": [
            [region["start"], region["end"], region["image_start"]] for region in declared
        ],
    }
    if sigma:
        proof["bijection_rewrites"] = sorted(mapped(at) for at in sigma_bytes)
        proof["bijection_mode_changes"] = sorted(mapped(at) for at in mode_changes)
    return image_bytes, proof


def _prove_region_entry(
    donor_body: bytes,
    region: dict[str, Any],
    image_relocations: dict[int, RelocationTarget],
    donor_relocations: dict[int, RelocationTarget],
    donor_entry: int,
    image_local: int,
    entry_sigma: dict[str, str],
    exit_sigmas: dict[int, dict[str, str]],
    mapped: Any,
    live_at: Any,
    flags_live: Any,
    context: str,
    *,
    x87_facts: Any = None,
    x87_exposures: list[int] | None = None,
    x87_record: dict[str, Any] | None = None,
    x87_returns: dict[str, int] | None = None,
    helpers: Mapping[str, HelperCode] | None = None,
) -> tuple[int, set[str], set[str], tuple[int, int]]:
    """Check 8 for the run of one region from one of its entries.

    Both versions are executed from ``donor_entry`` and ``image_local`` (the
    region's start and 0, or a declared interior entry and its replacement
    instruction) to wherever they leave the region.  Every pair of paths
    whose conditions do not contradict each other must leave at
    corresponding points (the donor's exit ``x`` and the image's ``M(x)``),
    and is compared there under that exit's liveness and mapping.  Returns
    the pair count, the registers and flags compared, and the path counts.
    """
    start, end = region["start"], region["end"]
    image_start = region["image_start"]
    replacement = region["replacement"]
    donor_paths = simulate_region(
        donor_body,
        start,
        end,
        donor_relocations,
        "donor",
        f"{context} donor",
        begin=donor_entry,
        leave=True,
        x87_returns=x87_returns,
        helpers=helpers,
    )
    image_paths = simulate_region(
        replacement,
        0,
        len(replacement),
        image_relocations,
        "replacement",
        f"{context} replacement",
        entry_names={entry_sigma.get(name, name): name for name in IA32_GENERAL_REGISTER_NAMES},
        begin=image_local,
        leave=True,
        x87_returns=x87_returns,
        helpers=helpers,
    )
    entry_live = live_at(donor_entry)
    entry_flags = flags_live(donor_entry)
    x87_used = any(path.x87.used for path in (*donor_paths, *image_paths))
    entry_cc: frozenset[str] = frozenset()
    if x87_facts is not None:
        entry_cc = x87_facts(donor_entry)[0]
    if x87_used:
        require(
            x87_facts is not None,
            f"{context}: the region uses the x87 unit but no x87 facts were supplied",
        )
        require(
            not x87_exposures,
            f"{context}: the region uses the x87 unit and the body stores the x87 environment at "
            f"{sorted(set(x87_exposures or []))}, which would expose state the proof does not "
            "compare",
        )
        depth_of = x87_facts(donor_entry)[1]
        need = max(path.x87.need for path in (*donor_paths, *image_paths))
        peak = max(path.x87.peak for path in (*donor_paths, *image_paths))
        entry_depth = depth_of(donor_entry)
        require_x87_depth(entry_depth, need, peak, context)
        low, high = entry_depth
        # A call of known return count made from the entry frame finds the
        # stack empty (x1), so the entry depth on that path is -push: it must
        # be one the donor's discipline allows.
        for path in (*donor_paths, *image_paths):
            for push in path.x87.call_pushes:
                require(
                    low <= -push <= high,
                    f"{context}: a call inside the region is made {push:+d} x87 values from the "
                    f"region entry, so the stack is empty there only at entry depth {-push}, "
                    f"which the donor's depths [{low}, {high}] do not allow",
                )
        called = {
            event[1][1]
            for path in (*donor_paths, *image_paths)
            for event in path.events
            if event[1][0] == "direct" and event[1][1] in (x87_returns or {})
        }
        if x87_record is not None:
            x87_record.setdefault("entry_depths", set()).add(tuple(entry_depth))
            x87_record["need"] = max(x87_record.get("need", 0), need)
            x87_record["peak"] = max(x87_record.get("peak", 0), peak)
            x87_record.setdefault("compared_condition_bits", set())
            x87_record.setdefault("call_returns", {}).update(
                {symbol: (x87_returns or {})[symbol] for symbol in called}
            )

    def entry_cover(name: str) -> frozenset[str]:
        return _cover(name, entry_sigma, entry_live)

    pairs = 0
    mentioned: set[Any] = set()
    compared_union: set[str] = set()
    flags_union: set[str] = set()
    for left in donor_paths:
        require(
            left.exit in exit_sigmas,
            f"{context}: the donor leaves the region for {left.exit}, which no branch names",
        )
        exit_sigma = exit_sigmas[left.exit]
        exit_live = live_at(left.exit)
        exit_flags = flags_live(left.exit)

        def exit_cover(
            name: str, sigma_out: dict[str, str] = exit_sigma, live: Any = exit_live
        ) -> frozenset[str]:
            return _cover(name, sigma_out, live)

        compared_registers = sorted(
            name for name in IA32_GENERAL_REGISTER_NAMES if name != "esp" and exit_cover(name)
        )
        compared_flags = sorted(name for name in FLAG_NAMES if name in exit_flags)
        for right in image_paths:
            if contradictory(left.conditions, right.conditions):
                continue
            pairs += 1
            require(
                image_start + right.exit == mapped(left.exit),
                f"{context}: the two versions leave the region at different places "
                f"(the donor for {left.exit}, the replacement for {image_start + right.exit})",
            )
            compared_union |= set(compared_registers)
            flags_union |= set(compared_flags)
            require(
                left.events == right.events,
                f"{context}: the two versions make different calls",
            )
            require(
                left.regs["esp"] == right.regs["esp"],
                f"{context}: the two versions leave a different stack pointer",
            )
            for name in compared_registers:
                require(
                    left.regs[name] == right.regs[exit_sigma.get(name, name)],
                    f"{context}: {name} is live at the exit and the two versions leave it different"
                    + (f" (the replacement's {exit_sigma[name]})" if name in exit_sigma else ""),
                )
            for name in compared_flags:
                require(
                    canonical_flag(name, left.flags[name])
                    == canonical_flag(name, right.flags[name]),
                    f"{context}: the flag {name} is live at the exit and the two versions leave it "
                    "different",
                )
            why = x87_stacks_equivalent(left.x87, right.x87)
            require(why is None, f"{context}: the two versions leave different x87 stacks: {why}")
            exit_cc: frozenset[str] = (
                x87_facts(left.exit)[0] if x87_facts is not None else frozenset()
            )
            for name in X87_CONDITION_BITS:
                if name in exit_cc:
                    require(
                        left.fcc[name] == right.fcc[name],
                        f"{context}: the x87 condition bit {name.upper()} is live at the exit and "
                        "the two versions leave it different",
                    )
            if x87_record is not None and x87_used:
                x87_record["compared_condition_bits"] |= set(exit_cc)
            why = stores_equivalent(left.stores, right.stores)
            require(why is None, f"{context}: the two versions leave different memory: {why}")
            require(
                left.footprint == right.footprint,
                f"{context}: the two versions access different memory",
            )
            for path, names in ((left, {}), (right, exit_sigma)):
                for name in ["esp", *compared_registers]:
                    value = path.regs[names.get(name, name)]
                    if name != "esp" and value == lin_atom(("reg0", name)):
                        # A register both versions leave at its entry value
                        # needs only its exit-live atoms shared.
                        missing = exit_cover(name) - entry_cover(name)
                        require(
                            not missing,
                            f"{context}: {name} passes through the region but {sorted(missing)} is "
                            "live only at its exit",
                        )
                        continue
                    term_atoms(value, mentioned)
                for name in compared_flags:
                    term_atoms(path.flags[name], mentioned)
                for name in exit_cc:
                    if path.fcc[name] == ("fcc0", name):
                        # A bit both versions leave at its entry value
                        # needs no liveness at the entry beyond its own.
                        continue
                    term_atoms(path.fcc[name], mentioned)
                term_atoms(path.x87.slots, mentioned)
                term_atoms(path.stores, mentioned)
                term_atoms(path.footprint, mentioned)
                term_atoms(path.conditions, mentioned)
    require(pairs > 0, f"{context}: no pair of paths is consistent")
    for kind, name in sorted(mentioned):
        if kind == "reg0":
            if name == "esp":
                continue
            missing = _IA32_ATOMS_OF[name] - entry_cover(name)
            require(
                not missing,
                f"{context}: the entry value of {name} is read but {sorted(missing)} is dead at "
                "the region entry",
            )
        elif kind == "fcc0":
            require(
                name in entry_cc,
                f"{context}: the entry x87 condition bit {name.upper()} is read but dead at the "
                "region entry",
            )
        else:
            require(
                name in entry_flags,
                f"{context}: the entry flag {name} is read but dead at the region entry",
            )
    return pairs, compared_union, flags_union, (len(donor_paths), len(image_paths))


def region_helper_callees(
    regions: object,
    rows: list[dict[str, Any]],
    library: HelperLibrary | None,
    context: str,
) -> tuple[dict[str, HelperCode], list[dict[str, Any]]]:
    """The compiler helpers a declared region calls: their verified bodies and their pins.

    A helper the donor calls only outside every region is not simulated and
    not pinned.  When a region calls one, ``library`` (the authenticated
    toolchain library) must supply its body.
    """
    declared = _validate_regions(regions, context)
    symbols = sorted(
        {
            row["target"]
            for row in rows
            if row["type"] == _REL32
            and compiler_helper(row["target"])
            and any(region["start"] <= row["offset"] < region["end"] for region in declared)
        }
    )
    if not symbols:
        return {}, []
    require(
        library is not None,
        f"{context}: a region calls the compiler helpers {symbols}, and no authenticated "
        "toolchain library is supplied to read their bodies from",
    )
    bodies = cast(HelperLibrary, library).helpers(symbols)
    return (
        {symbol: body.code for symbol, body in bodies.items()},
        [body.pin() for body in bodies.values()],
    )


def _padded_length(proc_size: int, fill_alignment: int) -> int:
    if fill_alignment == 1:
        return proc_size
    return (proc_size + fill_alignment - 1) // fill_alignment * fill_alignment


def resized_donor_object(
    donor_bytes: bytes,
    mangled: str,
    image: bytes,
    proof: dict[str, Any],
    context: str,
    *,
    debug_range: tuple[int, int] | None = None,
) -> tuple[bytes, dict[str, Any]]:
    """Re-seat one COMDAT's dependent COFF records around a resized body.

    The donor is an authentic compiler object; the result is the same object
    with ``image`` (code, tail and alignment fill) as the target body, and
    every record that states a code offset carried through the proof's
    offset map: COFF line rows (a row inside a region interior goes to the
    replacement's first byte), relocation offsets, the CodeView procedure
    length and debug range, the FPO procedure size, the function's
    TotalSize, the COMDAT's Length, the ``.ef`` marker and every other
    symbol of the section.  It is re-parsed and re-checked before it is
    handed to the installation delegate.  ``debug_range``, when given, is the
    image's CodeView debug range (start, end) in place of the donor's carried
    through the offset map (a whole-function replacement declares its own).
    """
    donor = CoffObject(donor_bytes)
    primary = donor.function_section(mangled)
    offset_map = cast(dict[int, int], proof["offset_map"])
    interiors = proof["interiors"]
    proc_size, image_proc = proof["proc_size"], proof["image_proc_size"]
    body_length = len(image)

    def carried(offset: int) -> int | None:
        if offset in offset_map:
            return offset_map[offset]
        for start, end, image_start in interiors:
            if start < offset < end:
                return cast(int, image_start)
        return None

    line_bytes = _coff_table_bytes(donor, primary, "lines")
    require(
        len(line_bytes) == primary["line_count"] * 6 and primary["line_count"] >= 1,
        f"{context}: the donor line table is missing",
    )
    require(
        coff_unpack("<IH", line_bytes, 0, f"{context} line sentinel")[1] == 0,
        f"{context}: the donor line sentinel is invalid",
    )
    rebuilt_lines = bytearray(line_bytes[:6])
    collapsed = 0
    for position in range(1, primary["line_count"]):
        offset, line = coff_unpack(
            "<IH", line_bytes, position * 6, f"{context} line row {position}"
        )
        target = carried(offset)
        require(
            line != 0 and target is not None,
            f"{context}: line row {position} at {offset} is not an instruction boundary of the "
            "donor",
        )
        if offset not in offset_map:
            collapsed += 1
        rebuilt_lines += cast(int, target).to_bytes(4, "little") + line.to_bytes(2, "little")
    relocation_bytes = _coff_table_bytes(donor, primary, "relocations")
    moved = {old: new for old, new in proof["relocation_reseat"]}
    rebuilt_relocations = bytearray(relocation_bytes)
    for ordinal in range(primary["relocation_count"]):
        at = ordinal * 10
        offset = int.from_bytes(relocation_bytes[at : at + 4], "little")
        rebuilt_relocations[at : at + 4] = moved.get(offset, offset).to_bytes(4, "little")
    debug_child = _comdat_child(donor, primary, ".debug$S")
    debug_raw = bytes(coff_body(donor, debug_child))
    records = parse_codeview_symbol_stream(debug_raw, f"{context} debug$S")
    procedures = [record for record in records if record["type"] in CODEVIEW_PROCEDURE_RECORD_TYPES]
    require(
        len(procedures) == 1 and procedures[0]["offset"] == 0,
        f"{context}: the donor debug$S does not open with its one procedure record",
    )
    for record in records[1:]:
        require(
            record["type"] in _OFFSET_FREE_CODEVIEW_TYPES,
            f"{context}: the debug$S record of type {record['type']:#x} may carry a code offset",
        )
    code_length, debug_start, debug_end = coff_unpack(
        "<III", debug_raw, 16, f"{context} debug range"
    )
    require(
        code_length == proc_size and 0 <= debug_start <= debug_end <= code_length,
        f"{context}: the donor debug procedure range is stale",
    )
    if debug_range is None:
        require(
            debug_start in offset_map and debug_end in offset_map,
            f"{context}: the debug range is not on boundaries outside every region interior",
        )
        image_range = (offset_map[debug_start], offset_map[debug_end])
    else:
        require(
            0 <= debug_range[0] <= debug_range[1] <= image_proc,
            f"{context}: the declared debug range lies outside the image's procedure",
        )
        image_range = debug_range
    rebuilt_debug = bytearray(debug_raw)
    rebuilt_debug[16:28] = (
        image_proc.to_bytes(4, "little")
        + image_range[0].to_bytes(4, "little")
        + image_range[1].to_bytes(4, "little")
    )
    closure = _comdat_child_closure(donor, primary)[1]
    replacements = [
        (primary["raw_offset"], primary["raw_offset"] + primary["raw_size"], bytes(image)),
        (primary["line_offset"], primary["line_offset"] + len(line_bytes), bytes(rebuilt_lines)),
        (
            primary["relocation_offset"],
            primary["relocation_offset"] + len(relocation_bytes),
            bytes(rebuilt_relocations),
        ),
        (
            debug_child["raw_offset"],
            debug_child["raw_offset"] + debug_child["raw_size"],
            bytes(rebuilt_debug),
        ),
    ]
    if ".debug$F" in closure:
        fpo_child = _comdat_child(donor, primary, ".debug$F")
        fpo_raw = bytes(coff_body(donor, fpo_child))
        parse_fpo_data(
            fpo_raw, expected_proc_size=primary["raw_size"], body=coff_body(donor, primary)
        )
        require(
            int.from_bytes(fpo_raw[4:8], "little") == proc_size,
            f"{context}: the FPO procedure size is not the donor's procedure",
        )
        rebuilt_fpo = bytearray(fpo_raw)
        rebuilt_fpo[4:8] = image_proc.to_bytes(4, "little")
        parse_fpo_data(bytes(rebuilt_fpo), expected_proc_size=body_length, body=image)
        replacements.append(
            (
                fpo_child["raw_offset"],
                fpo_child["raw_offset"] + fpo_child["raw_size"],
                bytes(rebuilt_fpo),
            )
        )
    replacements.sort()
    output = bytearray(_apply_replacements(donor_bytes, replacements))

    def shifted(pointer: int) -> int:
        return shifted_pointer(pointer, replacements)

    new_symbol_offset = shifted(donor.symbol_offset)
    output[8:12] = new_symbol_offset.to_bytes(4, "little")
    for section in donor.sections:
        header = 20 + (section["number"] - 1) * 40
        if section["number"] == primary["number"]:
            output[header + 16 : header + 20] = body_length.to_bytes(4, "little")
        for field, relative in (("raw_offset", 20), ("relocation_offset", 24), ("line_offset", 28)):
            pointer = shifted(section[field])
            if pointer != section[field]:
                output[header + relative : header + relative + 4] = pointer.to_bytes(4, "little")
    for symbol_index, item in donor.symbols.items():
        if item["type"] == 32 and item["aux_count"] >= 1:
            auxiliary = coff_auxiliary(donor, symbol_index, item)
            line_pointer = int.from_bytes(auxiliary[8:12], "little")
            mapped_pointer = shifted(line_pointer) if line_pointer else line_pointer
            if mapped_pointer != line_pointer:
                at = new_symbol_offset + (symbol_index + 1) * 18
                output[at + 8 : at + 12] = mapped_pointer.to_bytes(4, "little")
    function_index, function_record = function_symbol(donor, mangled, primary["number"])
    function_aux = coff_auxiliary(donor, function_index, function_record)
    require(
        int.from_bytes(function_aux[4:8], "little") == proc_size,
        f"{context}: the donor Function Definition TotalSize is not its procedure size",
    )
    at = new_symbol_offset + (function_index + 1) * 18
    output[at + 4 : at + 8] = image_proc.to_bytes(4, "little")
    section_index, section_record = _coff_section_symbol(donor, primary)
    require(
        int.from_bytes(coff_auxiliary(donor, section_index, section_record)[0:4], "little")
        == primary["raw_size"],
        f"{context}: the donor COMDAT auxiliary Length is stale",
    )
    aux_at = new_symbol_offset + (section_index + 1) * 18
    output[aux_at : aux_at + 4] = body_length.to_bytes(4, "little")
    end_index, end_symbol = _coff_marker(donor, ".ef", primary["number"])
    require(end_symbol["value"] == proc_size, f"{context}: the donor .ef marker is stale")
    output[new_symbol_offset + end_index * 18 + 8 : new_symbol_offset + end_index * 18 + 12] = (
        image_proc.to_bytes(4, "little")
    )
    carried_symbols = []
    for symbol_index, item in donor.symbols.items():
        if item["section"] != primary["number"]:
            continue
        if symbol_index in (function_index, section_index, end_index):
            continue
        if item["name"] in (".bf", ".lf"):
            continue
        require(
            item["value"] in offset_map,
            f"{context}: the symbol {item['name']} at {item['value']} is not a boundary outside "
            "every region",
        )
        target = offset_map[item["value"]]
        if target != item["value"]:
            at = new_symbol_offset + symbol_index * 18
            output[at + 8 : at + 12] = target.to_bytes(4, "little")
            carried_symbols.append([item["name"], item["value"], target])
    derived = bytes(output)
    checked = CoffObject(derived)
    checked_primary = checked.function_section(mangled)
    require(
        coff_body(checked, checked_primary) == bytes(image),
        f"{context}: the derived donor body is not the image",
    )
    require(
        checked_primary["raw_size"] == body_length
        and checked_primary["line_count"] == primary["line_count"]
        and checked_primary["relocation_count"] == primary["relocation_count"]
        and checked_primary["number"] == primary["number"]
        and checked_primary["characteristics"] == primary["characteristics"],
        f"{context}: the derived donor target header is inconsistent",
    )
    require(
        function_multiset(checked) == function_multiset(donor)
        and comdat_primary_identity_multiset(checked) == comdat_primary_identity_multiset(donor)
        and len(checked.sections) == len(donor.sections),
        f"{context}: the derived donor changed the object's topology",
    )
    require(
        _comdat_child_closure(checked, checked_primary) == _comdat_child_closure(donor, primary),
        f"{context}: the derived donor changed the target closure",
    )
    donor_rows = detailed_relocations(donor, primary)
    checked_rows = detailed_relocations(checked, checked_primary)
    require(
        [row["target"] for row in checked_rows] == [row["target"] for row in donor_rows]
        and [row["type"] for row in checked_rows] == [row["type"] for row in donor_rows]
        and [row["offset"] for row in checked_rows]
        == [moved.get(row["offset"], row["offset"]) for row in donor_rows],
        f"{context}: the derived donor relocation table is not the proved reseat",
    )
    return derived, {
        "carried_code_symbols": carried_symbols,
        "collapsed_line_rows": collapsed,
        "procedure_range": [image_proc, image_range[0], image_range[1]],
    }


REGION_RESIZE_CLOSURES = ((".debug$F", ".debug$S"), (".debug$S", ".xdata$x"))
REGION_RESIZE_RECIPE = CandidateRecipe(
    label="region-resize",
    splice_class=REGION_RESIZE_CLASS,
    spec_key="region_resize",
    admissible_closures=REGION_RESIZE_CLOSURES,
    declaration_label="region-resize rewriting",
    kind=(REGION_RESIZE_KIND, "region-resize kind differs"),
    donor_seat="optional",
    declared_seat_message="region-resize declared donor seat changed",
    donor_section_count="optional",
    census="extras",
    length_pins=("expected_seed_length", "expected_preimage_length"),
    closure_message="region-resize target closure is neither the FPO debug pair nor the EH pair",
)


def protected_code_offsets(
    donor: CoffObject, primary: dict[str, Any], context: str
) -> frozenset[int]:
    """Offsets of the target that a symbol, closure-child reference or debug range names."""
    offsets = set()
    values = {}
    for item in donor.symbols.values():
        if item["section"] == primary["number"] and item["name"] not in (".bf", ".lf", ".ef"):
            offsets.add(item["value"])
            values[item["name"]] = item["value"]
    for child_name in _comdat_child_closure(donor, primary)[1]:
        child = _comdat_child(donor, primary, child_name)
        for row in detailed_relocations(donor, child):
            if row["target"] in values:
                offsets.add(values[row["target"]] + max(row["addend"], 0))
    debug_raw = bytes(coff_body(donor, _comdat_child(donor, primary, ".debug$S")))
    _length, start, end = coff_unpack("<III", debug_raw, 16, f"{context} debug range")
    offsets |= {start, end}
    return frozenset(offsets)


def _composed_identity(row: dict[str, Any]) -> tuple[Any, ...]:
    """A relocation as the composed object must carry it from the derived donor.

    The same-slot composer names a compiler local (``$T<n>``, ``$L<n>``) by
    the seed's symbol of the same kind at the same section and value, after
    proving that section byte-identical in both objects; any declaration
    added to the unit renumbers those serials, so only kind and place are
    compared.  Every other target keeps its name.
    """
    kind = local_symbol_kind(str(row["target"]))
    if kind is not None:
        return (
            row["offset"],
            ("local", kind, row["target_section"], row["target_value"]),
            row["type"],
        )
    return (row["offset"], row["target"], row["type"])


def produce_region_resize_rewriting_candidate(
    seed_bytes: bytes,
    donor_bytes: bytes,
    function: dict[str, Any],
    helper_library: HelperLibrary | None = None,
) -> tuple[bytes, dict[str, Any]]:
    """Produce the resized REWRITE(donor body) of a fresh compiler artifact (check 9).

    ``helper_library`` is the authenticated toolchain library, needed when a
    region calls a compiler helper (its pins are ``expected_helper_callees``).
    """
    seats = open_candidate_seats(seed_bytes, donor_bytes, function, REGION_RESIZE_RECIPE)
    donor, mangled = seats.donor, seats.mangled
    dp, spec = seats.donor_section, seats.spec
    _, donor_body = pin_candidate_bodies(seats, function, REGION_RESIZE_RECIPE)
    donor_body = bytes(donor_body)
    require(
        set(spec)
        <= {
            "kind",
            "regions",
            "expected_code_length",
            "expected_proc_size",
            "expected_fill_alignment",
            "expected_external_entries",
            "expected_internal_relocation_targets",
            "expected_growth",
            "expected_region_proofs",
            "expected_branch_repairs",
            "expected_relocation_reseat",
            "expected_addend_repairs",
            "expected_instruction_count",
            "expected_procedure_range",
            "expected_carried_code_symbols",
            "expected_collapsed_line_rows",
            "bijection",
            "expected_bijection_rewrites",
            "expected_bijection_mode_changes",
            "expected_helper_callees",
        },
        "region-resize declaration names an unknown field",
    )
    bijection = spec.get("bijection")
    require(
        (bijection is None)
        == ("expected_bijection_rewrites" not in spec)
        == ("expected_bijection_mode_changes" not in spec),
        "region-resize bijection and its pins are declared together or not at all",
    )
    donor_rows = detailed_relocations(donor, dp)
    internal_targets = internal_relocation_targets(donor_rows, dp["number"])
    require_declared_internal_targets(spec, internal_targets, "region-resize")
    external_entries = relational_form_external_entries(donor, dp, "region-resize external entries")
    require(
        sorted(external_entries) == spec["expected_external_entries"],
        "region-resize external entry set differs from its declaration",
    )
    proc_size = spec["expected_proc_size"]
    fill_alignment = spec["expected_fill_alignment"]
    require(
        fill_alignment in (1, 16)
        and type(proc_size) is int
        and 0 < proc_size <= len(donor_body)
        and _padded_length(proc_size, fill_alignment) == len(donor_body),
        "region-resize procedure size or fill alignment differs from the donor",
    )
    prologue = 0
    if ".debug$F" in seats.expected_closure:
        fpo = parse_fpo_data(
            bytes(coff_body(donor, _comdat_child(donor, dp, ".debug$F"))),
            expected_proc_size=dp["raw_size"],
            body=donor_body,
        )
        require(fpo["cbProcSize"] == proc_size, "region-resize FPO procedure size differs")
        prologue = fpo["cbProlog"]
    frame_pointer_free = False
    if isinstance(bijection, dict) and "ebp" in (bijection.get("mapping") or {}):
        require_frame_pointer_free_frame(
            donor,
            dp,
            donor_body,
            decode_ia32_bijection_body(
                donor_body,
                "region-resize frame proof",
                relocation_symbol_map(donor_rows),
                spec.get("expected_code_length"),
            ),
            "region-resize frame proof",
        )
        frame_pointer_free = True
    helpers, helper_pins = region_helper_callees(
        spec["regions"], donor_rows, helper_library, "region-resize"
    )
    require(
        spec.get("expected_helper_callees", []) == helper_pins
        and ("expected_helper_callees" in spec) == bool(helper_pins),
        "region-resize helper callees differ from its declaration",
    )
    image, proof = apply_region_resize(
        donor_body,
        spec["regions"],
        donor_rows,
        dp["number"],
        "region-resize image",
        code_length=spec.get("expected_code_length"),
        proc_size=proc_size,
        external_entries=frozenset(external_entries),
        protected_offsets=protected_code_offsets(donor, dp, "region-resize"),
        prologue_length=prologue,
        bijection=bijection,
        frame_pointer_free=frame_pointer_free,
        helpers=helpers,
    )
    if bijection is not None:
        require(
            proof["bijection_rewrites"] == spec["expected_bijection_rewrites"]
            and proof["bijection_mode_changes"] == spec["expected_bijection_mode_changes"],
            "region-resize bijection differs from its declaration",
        )
    padded = _padded_length(proof["image_proc_size"], fill_alignment)
    image = image + bytes([MSVC50_FUNCTION_FILL_BYTE]) * (padded - len(image))
    require(
        proof["growth"] == spec["expected_growth"]
        and proof["regions"] == spec["expected_region_proofs"]
        and proof["branch_repairs"] == spec["expected_branch_repairs"]
        and proof["relocation_reseat"] == spec["expected_relocation_reseat"]
        and proof["addend_repairs"] == spec["expected_addend_repairs"]
        and proof["instruction_count"] == spec["expected_instruction_count"],
        "region-resize image differs from its declaration",
    )
    require(
        sha256_bytes(image) == function["expected_body_sha256"],
        "region-resize image differs from its pin",
    )
    require(
        len(image) == function["expected_body_length"] == function["expected_donor_length"],
        "region-resize image length differs from its pin",
    )
    require(image != donor_body, "region-resize image does not move the donor body")
    require_pinned_length(function, image, "region-resize")
    moved = dict((old, new) for old, new in proof["relocation_reseat"])
    installed_rows = [
        {**row, "offset": moved.get(row["offset"], row["offset"])} for row in donor_rows
    ]
    for at, _old, new in proof["addend_repairs"]:
        for row in installed_rows:
            if row["offset"] == at:
                row["addend"] = new
    semantic_detail = candidate_relocation_semantics(installed_rows, function, "region-resize")
    derived, derived_detail = resized_donor_object(
        donor_bytes, mangled, image, proof, "region-resize derived donor"
    )
    require(
        derived_detail["procedure_range"] == spec["expected_procedure_range"]
        and derived_detail["carried_code_symbols"] == spec["expected_carried_code_symbols"]
        and derived_detail["collapsed_line_rows"] == spec["expected_collapsed_line_rows"],
        "region-resize derived donor differs from its declaration",
    )
    effective = same_slot_effective(function, mangled)
    if "expected_donor_section_number" in function:
        effective["expected_donor_section_number"] = function["expected_donor_section_number"]
    composed, detail, checked, cp = install_same_slot(
        seed_bytes,
        derived,
        effective,
        mangled,
        image,
        "region-resize",
        declared_donor_extras=function.get("expected_donor_extra_functions") or None,
    )
    require(
        [_composed_identity(row) for row in detailed_relocations(checked, cp)]
        == [_composed_identity(row) for row in installed_rows],
        "region-resize composed relocation table is not the proved reseat",
    )
    return composed, candidate_proof(
        detail,
        REGION_RESIZE_CLASS,
        {
            "region_resize": proof["regions"],
            **(
                {}
                if bijection is None
                else {
                    "bijection": {
                        "mapping": bijection["mapping"],
                        "scopes": bijection["scopes"],
                        "rewrites": proof["bijection_rewrites"],
                        "mode_changes": proof["bijection_mode_changes"],
                    }
                }
            ),
            "growth": proof["growth"],
            "branch_repairs": proof["branch_repairs"],
            "relocation_reseat": proof["relocation_reseat"],
            "addend_repairs": proof["addend_repairs"],
            "instruction_count": proof["instruction_count"],
            "carried_code_symbols": derived_detail["carried_code_symbols"],
            "collapsed_line_rows": derived_detail["collapsed_line_rows"],
            "procedure_range": derived_detail["procedure_range"],
            **({"helper_callees": helper_pins} if helper_pins else {}),
        },
        semantic_detail,
    )


__all__ = [
    "REGION_RESIZE_CLASS",
    "REGION_RESIZE_KIND",
    "ScopeBoundRefusal",
    "apply_region_resize",
    "produce_region_resize_rewriting_candidate",
    "protected_code_offsets",
    "refine_call_reads",
    "resized_donor_object",
]
