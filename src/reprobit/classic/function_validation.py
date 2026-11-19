"""Classic compiler algorithms: whole-function translation validation.

`retail_exact_function_translation_validation` installs a declared
replacement for the *whole* code of a freshly compiled donor function: the
original's instructions, which differ from the donor's in register
allocation, spill-slot choice and instruction scheduling while computing the
same thing with the same control flow.  The region rewrite
(:mod:`reprobit.classic.rewriting_region_resize`) proves only local,
loop-free regions; a difference that spans the function -- a register swapped
from the prologue to the epilogue, a value kept in a register on one side and
reloaded on the other across a join or a loop -- is a symptom it cannot see
whole.  This kind uses the standard technique for that, translation
validation (Necula 2000; Pnueli, Siegel and Singerman 1998): it pairs the two
control-flow graphs, infers a state relation at every paired join, and proves
each pair of paths between joins with the region simulator
(:mod:`reprobit.classic.region_simulation`), its memory model and its x87
model.  The record carries the replacement as a list of instruction
encodings (hex text) and a pairing of its relocated fields with the donor's
records.  Those bytes are untrusted input: nothing about them is believed
except what the checks below measure, every check compares them with the
donor the build compiles from source, and the build never reads a reference
image.

Definitions.  D is the donor's code [0, L_D) and P the replacement's
[0, L_P).  A *cut point* of a program is its entry and every reachable
instruction that two or more control-flow edges reach (a join), except a
join that is a ``jmp`` or from which every path is straight-line code to a
return, and every target of a back edge of the depth-first walk from the
entry is a cut point whatever its form.  So every cycle holds a cut point,
and the code between cut points is a tree of paths.  A *path* runs from a cut
point, through any number of instructions, to the next cut point it reaches
or to a return.  A *location* is one of the seven general registers other
than ESP, a stack slot (offset from the entry ESP and width, private frames
only), an x87 register ST(i), or the x87 stack as one value (after a call
whose x87 return count is not known).  A *state relation* at a pair of cut
points (c, c') is: ESP_D = ESP0 + k and ESP_P = ESP0 + k' (ESP0 the function's
entry ESP, k and k' constants); the x87 depths of both (or that each is the
unknown result of a call); a partition of some locations of D at c and of P
at c' into classes, each class asserting that its locations hold one value
(and, for a constant class, that the value is a given closed term: a
constant or a relocated symbol's address plus a constant); the parameter
words each version has written since the function's entry; and memory: in a
*shared* frame, every byte of memory is equal in the two; in a *private*
frame, every byte outside the private stack is equal.

Theorem.  Let D be the donor, P the declared replacement and I the image P
padded with MSVC 5.0's fill to the function's slot.  If checks 1 to 9 hold,
then for every entry state, D and I run from the function's entry make the
same calls in the same order with the same arguments, and either both
return, with the same EAX, EBX, ESI, EDI, EBP and ESP, the same return
address, the same x87 stack, and the same memory outside the dead stack (the
words below the final ESP and the function's own parameter words), or
neither does -- under the model every classic rewriting uses (one thread,
ordinary memory, callees that honour the MSVC calling convention their
decoration names), x1-x4 of `rewriting_region_resize`, and a1-a3 below.  An
access of D faults exactly when the corresponding access of P does, except
an access to the function's own stack frame (a3); the state at a fault is
not compared.

Proof sketch.  Let R(c, c') be the relation check 6 settles at each pair of
cut points.  At the function's entry the two states are equal, which
satisfies R(0, 0).  Suppose both programs are at a pair (c, c') with
states satisfying R(c, c').  Name each class's value by one fresh atom (or
its constant), every unrelated location by an atom of its own side, ESP by
ESP0 plus its constant, and memory by one shared atom (shared frame) or by
one shared atom outside the private stack and the related slots inside it
(private frame).  The simulator's terms are exact functions of those atoms,
so the concrete states are one valuation of them.  D runs one path p from c
and P one path p' from c', both enabled by that valuation, so the two
paths' conditions hold together and do not contradict each other; check 5
compared exactly that pair: the same calls with the same arguments, the
same memory and footprint, and either both returning with equal returned
state, or both reaching a pair (x, x') of cut points that check 4 pairs, with
end states whose equal terms include every class of R(x, x') (check 6), so
the concrete states satisfy R(x, x').  By induction every execution keeps
the two programs at paired points in related states, and the comparison at
the return is the theorem's.  A run that never returns makes the same
calls in the same order on both sides.

Checks (each is a refusal):

1. Shape.  The donor body has no data tail (switch table) and no symbol,
   in-body relocation or debug record naming an offset other than its
   entry and end; the function has no external entry; no branch targets
   offset 0.  P decodes, instruction by instruction, to exactly the
   declared encodings.
2. Closed set.  Every reachable instruction of both is in the simulator's
   closed set or is ``ret``/``ret imm16``; every branch targets an
   instruction of its own program; there is no indirect transfer.  A call
   is a direct call to a callee whose MSVC C decoration fixes a
   register-free convention (``call rel32`` with its REL32 record, ``call
   [abs32]``), exactly as in the region simulator, a call to a verified
   compiler helper, or a COM vtable call (both below).  Two forms are admitted
   here and not in a region proof (`region_simulation._Instruction`'s
   ``extended``): ``lea r, [index*scale + disp32]`` with an unrelocated
   displacement (arithmetic on a constant), and the string forms MSVC 5.0
   emits inline -- ``stos``/``movs`` once or under ``rep`` with a constant
   ECX of at most 1024 (exactly that many element loads and stores) and
   ``repne scasb`` (one opaque term of AL, EDI, ECX and the memory state,
   recorded in the footprint; `region_simulation._string_step`), with the
   direction flag clear as the calling convention leaves it.

   Compiler helpers.  A direct call to a compiler helper (``__ftol``,
   ``__chkstk``: a ``__name`` the decoration rules refuse) is admitted when
   its body comes from the authenticated toolchain library
   (`toolchain_helpers.HelperLibrary`: ``lib/libc.lib`` whose bytes are the
   profile's reviewed authority, the member its symbol index names, a code
   section with no relocation).  The call runs that body inline
   (`region_simulation.run_helper`): a return address of its own version is
   pushed, the helper's instructions run on the caller's state with the
   helper forms ``fwait``, ``leave``, ``fnstcw``/``fldcw`` and ``fist``/
   ``fistp`` admitted, every branch must be decided by constants, and it
   must return to the pushed address with the control word restored.  The
   control word is a term (the shared word until a ``fldcw``); a ``fldcw``
   must keep the shared word's exception masks, and ``fist`` names the word
   it rounds under.  ``__chkstk``'s argument must be a constant (``mov eax,
   n`` before the call), which makes its probe loop a fixed number of
   steps, and a ``mov eax, n; call __chkstk`` prologue whose simulated
   effect is ESP0 - n allocates the FPO locals block as ``sub esp, n``
   does (check 7).  A helper that calls out or names a global (``__CIacos``,
   ``__isctype``) is refused.  The record pins the library, its digest, the
   member and the body's digest (check 8).

   COM vtable calls.  ``call [reg+disp]`` whose address is one 32-bit load
   (the vtable pointer, read from an object) plus a constant is an event
   named like a direct call's, with its callee the slot's word (a term) and
   the bytes it pops: two versions make the same indirect calls exactly
   when they read the same slot of the same vtable from the same memory, in
   the same order, with the same arguments.  After it EAX, ECX and EDX are
   the call's results, EBX, ESI, EDI and EBP are preserved, memory is the
   call's result and no x87 instruction may follow.  The pop is determined
   per version (`indirect_call_pops`): the walk of its code gives ESP at
   every instruction as a constant plus the unknown pops, equal wherever
   edges meet and ESP0 at every return; every pop must be fixed uniquely,
   a multiple of four, and it is part of the event's name, so versions that
   disagree make different calls.  Two vtable calls on every path between
   the same points fix only the sum of their pops and are refused.
3. Relocations.  D's relocated fields are 32-bit `DIR32` fields or a call's
   REL32 field naming a symbol outside the function's own section.  P
   declares its relocated fields, sorted, as a bijection onto D's records:
   each field takes one record whole (type and target), every record once.
   The simulator names a relocated value by its target alone, so the order
   is free; it refuses a relocated field it does not consume as an address
   displacement, an immediate or a call target, and every field of both
   programs is consumed on some path.
4. Pairing.  The cut points of D and P (see Definitions) are paired from
   (0, 0) outwards: wherever a pair of consistent paths (check 5) reaches a
   cut point x of D and x' of P, x is paired with x'.  The pairing must be a
   bijection between the cut points it reaches; a path of one program that
   returns while its consistent partner reaches a cut point is refused.  So
   the two control-flow graphs are isomorphic up to straight-line code,
   empty forwarding blocks and duplicated returning tails, and every branch
   condition of one is matched by the other's (a branch on a different
   condition makes the two paths of one side consistent with one path of
   the other, which then reaches two different points).
5. Paths.  From every paired (c, c') under R(c, c') both programs' paths
   are enumerated (at most 256 each, 20000 steps); for every pair of paths
   whose conditions do not contradict each other (`region_simulation.
   contradictory`):
   a. they make the same calls: equal event terms in the same order (an
      event names the callee, ESP, the canonical store log since the
      previous event, that event, the x87 stack and exception set when
      used, and in a private frame the argument words, check 7);
   b. they leave the same memory: the store logs are equal up to
      reordering provably disjoint stores (`stores_equivalent`) -- every
      store in a shared frame, every store outside the private stack in a
      private one; at a return, stores wholly inside the dead stack are
      not compared;
   c. they access the same memory (equal footprints, including every x87
      operation that can raise an exception and every division), except
      accesses at a constant offset from ESP0 inside the function's own
      frame and parameter words (a3);
   d. in a shared frame ESP is equal at the end (a private frame's ESP is
      compared at calls through 5a and at returns);
   e. at a return (both must return): ESP, the return address, EAX, EBX,
      ESI, EDI, EBP and the x87 stack (depth, every register, or the same
      call's unknown result) are equal;
   f. x87: from a cut point of known depth d, the deepest entry register
      either path touches is below d and d plus its highest push is at most
      eight; a direct call of known x87 return count made from that frame
      finds the stack empty (d plus its push is 0); no path reads a C0-C3
      bit an x87 instruction left undefined.
6. Relations.  R(0, 0) is the identity.  The relation a pair of paths
   ending at (x, x') *establishes* has one class per term that some of
   their end locations hold (keeping a class of two or more locations, or
   of one location holding a closed term as a constant class), the two
   ESP constants and x87 depths, and the union of the parameter words
   written.  R(x, x') is the meet (common refinement) of the relations all
   path pairs reaching it establish, computed to a fixpoint over loops (a
   worklist; relations only shrink, so it terminates), with the ESP
   constants and x87 depths required equal across the paths reaching it.
   A final pass re-runs every pair of cut points under the settled
   relations and requires every established relation to imply the
   relation of the pair it reaches.
7. Frames.  A shared frame is used when either program's stack address
   escapes: a register, stored value or argument comes to hold a value
   computed from ESP0 (``lea r, [esp+k]``, ``mov r, esp``, ``push esp``) or
   a stack access uses a variable offset.  Otherwise the frame is private,
   which needs the donor's FPO record (frame-pointer-free, no SEH) for its
   frame base B = ESP0 - 4 (cdwLocals + cbRegs) and parameter end
   E = ESP0 + 4 + 4 cdwParams.  In a private frame:
   a. every access at ESP0 + k with k < E is a private stack slot: it must
      lie at or above the current ESP and wholly below E; a load must read
      exactly a slot the path stored or the relation carries, or a
      parameter word (k >= 0) neither version has written, which holds the
      entry value; any other read is refused;
   b. a private slot is disjoint from every address that is not a constant
      offset from ESP0: no such address can reach the private stack,
      because no value computed from ESP0 exists outside ESP (7, and the
      check runs after every instruction of every path);
   c. at a call ESP must be at or below B and the words in [ESP, B) must
      be exactly tiled by stored slots, whose values are the call's
      argument words; after the call those words are the call's unknown
      results.
8. Pins.  The image digest and length, the frame kind, the pairs of cut
   points, the path and path-pair counts, the relocation reseat, the
   instruction count, the derived procedure range and collapsed line rows
   are pinned by the declaration and re-measured, and the derived donor
   object is re-parsed and checked before the same-slot delegate installs
   it.
9. Install.  The image is P followed by MSVC 5.0's alignment fill; the
   donor object is re-seated around it (`rewriting_region_resize.
   resized_donor_object`: relocation offsets through the pairing, every
   line row to the image's entry, the FPO and CodeView sizes and the COFF
   lengths), the CodeView debug range is [0, the declared end] within P
   (debug metadata only, which no check relies on), and the same-slot resize
   delegate installs it.

Assumptions beyond the region kinds'.  (a1) The callee owns its argument
words: its caller does not read them after the call returns (MSVC 5.0's
own code spills into its parameter words).  (a2) A callee reads and writes
no word of its caller's stack except its arguments, and in the donor --
compiled code -- the arguments of every call are words pushed or
allocated after the prologue the FPO record describes, so they lie in
[ESP, B) at the call.  Since the replacement's words in that range are
compared with the donor's, the same callee (with its fixed parameter
count) reads the same arguments from both.  (a3) An access at a constant
offset from ESP0 within the allocated frame or the parameter words does
not fault (the stack is committed).  (a4) The donor is compiled code
whose static stack model is its callees' truth: ESP is one constant offset
from ESP0 at every point on every path, and ESP0 at every return, so the
pops its walk determines are the real pops of its vtable callees.  (a5) A
COM method is ``__stdcall``: it takes no argument in a register and pops
its own arguments.  (a6) The stack below ESP is not part of the compared
state: an inlined helper's stores wholly below the caller's ESP after it
returns (its return address, its own frame) are dropped from the store log
-- as the return address and frame of every callee a call event stands for
already are -- and in a private frame nothing below ESP is ever read.  (a7)
The linked image's compiler helper is the library member's section
unchanged (it has no relocation to apply).  No other assumption is made: the
relation is inferred, nothing about the replacement is believed, and the
simulator's term model is exact.
"""

from __future__ import annotations

import hashlib
from collections import Counter
from collections.abc import Iterable, Mapping
from dataclasses import dataclass, field
from fractions import Fraction
from typing import Any, cast

from reprobit.binary import ByteIdentityError, require
from reprobit.coff_format import CoffObject, coff_body, coff_unpack, detailed_relocations

from .candidate_recipe import (
    CandidateRecipe,
    candidate_proof,
    candidate_relocation_semantics,
    install_same_slot,
    internal_relocation_targets,
    open_candidate_seats,
    pin_candidate_bodies,
    relocation_symbol_map,
    require_pinned_length,
    same_slot_effective,
)
from .coff import _comdat_child
from .debug import MSVC50_FUNCTION_FILL_BYTE, parse_fpo_data
from .foundation import require_payload_free_declaration, sha256_bytes
from .region_simulation import (
    _STRING_OPCODES,
    FLAG_NAMES,
    X87_CONDITION_BITS,
    HelperCode,
    PathState,
    RelocationTarget,
    Term,
    X87State,
    _fcc_allowed,
    _Instruction,
    _load,
    _step,
    _Undefined,
    condition,
    const_of,
    contradictory,
    lin,
    lin_atom,
    lin_sub,
    mentions_x87_undefined,
    region_boundaries,
    stores_equivalent,
)
from .region_x87 import x87_stack_solution
from .relational import ia32_relational_flow_walk, relational_form_external_entries
from .rewriting_region_resize import (
    _composed_identity,
    _hex_instruction,
    _padded_length,
    protected_code_offsets,
    resized_donor_object,
)
from .toolchain_helpers import HelperBody, HelperLibrary, compiler_helper

FUNCTION_VALIDATION_KIND = "function_translation_validation_v1"
FUNCTION_VALIDATION_CLASS = "retail_exact_function_translation_validation"

GENERAL_REGISTERS = ("eax", "ecx", "edx", "ebx", "ebp", "esi", "edi")
RETURN_REGISTERS = ("eax", "ebx", "esi", "edi", "ebp")
ESP0 = ("reg0", "esp")
MAX_PATHS = 256
MAX_STEPS = 20000
MAX_VISITS = 64
_MASK = 0xFFFFFFFF


class EscapeRefusal(ByteIdentityError):
    """A stack address escapes, so the frame cannot be private (check 7)."""


def _signed(value: int) -> int:
    value &= _MASK
    return value - (1 << 32) if value >> 31 else value


def _esp_offset(value: Term) -> int | None:
    """k when a 32-bit term is ESP0 + k, else None."""
    if value[0] != "lin" or value[2] != ((ESP0, 1),):
        return None
    return _signed(value[1])


def mentions_stack_address(term: Term) -> bool:
    """Whether a value term mentions ESP0 (outside the event terms that name ESP)."""
    stack = [term]
    seen: set[int] = set()
    while stack:
        current = stack.pop()
        if isinstance(current, (tuple, list, frozenset, set)):
            # Terms share subterms: visit each container once.
            if id(current) in seen:
                continue
            seen.add(id(current))
            if isinstance(current, tuple):
                if current == ESP0:
                    return True
                if current and current[0] in ("call", "call#"):
                    continue
            stack.extend(item for item in current if not isinstance(item, (str, int)))
    return False


def _shaped(atom: Term, shape: Any) -> Term:
    if shape == "lin":
        return lin_atom(atom)
    if isinstance(shape, tuple):
        return ("b", shape[1], atom)
    return atom


def _shape(term: Term) -> Any:
    if term[0] == "lin":
        return "lin"
    if term[0] == "b":
        return ("b", term[1])
    return "x87"


# Function-wide values: no execution point changes a register's entry value
# or the entry value of a parameter word.
_CLOSED_TAGS = frozenset({"lin", "b", "k", "sym", "fconst", "reg0", "pld"})
# A word holding one of these marks a saved register (check 7c).
_SAVED_ENTRY_VALUES = frozenset(lin_atom(("reg0", name)) for name in ("ebx", "ebp", "esi", "edi"))


def closed_term(term: Term) -> bool:
    """A value fixed for the whole execution: a constant, a relocated symbol's
    address, or an entry value (of a register, or of a parameter word neither
    version has written)."""
    stack = [term]
    while stack:
        current = stack.pop()
        if isinstance(current, tuple):
            if current and isinstance(current[0], str) and current[0] not in _CLOSED_TAGS:
                return False
            stack.extend(item for item in current if isinstance(item, tuple))
    return True


# --- the frame model ----------------------------------------------------------------


@dataclass(frozen=True)
class FrameFacts:
    """The frame kind and, for a private frame, its base B and parameter end E (check 7)."""

    private: bool
    base: int = 0
    params_end: int = 4


class FrameModel:
    """One path's stack frame: private slots (check 7) or the shared-frame checks.

    The simulator calls :meth:`load` and :meth:`store` for every memory access
    and :meth:`arguments` and :meth:`after_call` at every call.  In a shared
    frame the model only checks that a stack access lies at or above ESP and
    owns nothing.  In a private frame it owns every access at a constant offset
    k < E from ESP0, keeping the slots in ``slots`` by (k, width); ``dirty``
    holds the parameter bytes (k >= 0) this version has written since the
    function's entry.
    """

    def __init__(
        self,
        facts: FrameFacts,
        slots: dict[tuple[int, int], Term] | None = None,
        dirty: Iterable[int] = (),
        context: str = "",
    ) -> None:
        self.facts = facts
        self.slots = dict(slots or {})
        self.dirty = set(dirty)
        self.context = context
        # While an inlined compiler helper runs (`region_simulation.
        # run_helper`), the source of fresh values for its stack probes.
        self.helper_reads: Any = None

    def fork(self) -> FrameModel:
        return FrameModel(self.facts, self.slots, self.dirty, self.context)

    def _current(self, state: PathState) -> int:
        offset = _esp_offset(state.regs["esp"])
        require(
            offset is not None,
            f"{self.context}: ESP is not a constant offset from its entry value",
        )
        return cast(int, offset)

    def _offset(self, state: PathState, address: Term, *, probe: bool = False) -> int | None:
        """k for an access at ESP0 + k; None for other memory.

        With ``probe`` (a load inside an inlined helper) an access below ESP
        is returned rather than refused; :meth:`load` makes it a fresh value.
        """
        if address[0] != "lin":
            return None
        coefficients = dict(address[2])
        if ESP0 not in coefficients:
            return None
        if len(coefficients) != 1 or coefficients[ESP0] != 1:
            if self.facts.private:
                raise EscapeRefusal(f"{self.context}: a stack access at a variable offset from ESP")
            return None
        offset = _signed(address[1])
        require(
            offset >= self._current(state) or probe,
            f"{self.context}: a stack access at ESP0{offset:+d} lies below ESP",
        )
        return offset

    def _owned(self, offset: int, width: int) -> bool:
        if not self.facts.private or offset >= self.facts.params_end:
            return False
        require(
            offset + width <= self.facts.params_end,
            f"{self.context}: a stack access straddles the end of the parameter words",
        )
        return True

    def _overlapping(self, offset: int, width: int) -> list[tuple[int, int]]:
        return [key for key in self.slots if key[0] < offset + width and offset < key[0] + key[1]]

    def load(self, state: PathState, address: Term, width: int) -> Term | None:
        offset = self._offset(state, address, probe=self.helper_reads is not None)
        if offset is not None and offset < self._current(state):
            # A helper's stack probe below ESP: memory no model owns, so a
            # fresh value of this version (never equal to the other's).
            state.footprint.add((address, width))
            fresh = self.helper_reads
            fresh.count += 1
            return _width_term(("probe", fresh.tag, fresh.count), width)
        if offset is None or not self._owned(offset, width):
            return None
        key = (offset, width)
        if key in self.slots:
            return self.slots[key]
        overlapping = sorted(self._overlapping(offset, width))
        if overlapping:
            return self._split_read(offset, width, overlapping)
        require(
            offset >= 0 and not self.dirty & set(range(offset, offset + width)),
            f"{self.context}: a read of the stack slot ESP0{offset:+d} whose value the relation "
            "does not carry",
        )
        atom = ("pld", offset, width)
        return lin_atom(atom) if width == 4 else ("b", width * 8, atom)

    def _split_read(self, offset: int, width: int, overlapping: list[tuple[int, int]]) -> Term:
        """A read that one wider slot holds or narrower slots tile exactly.

        A part of a slot is ``("part", value, at, width)`` -- the bytes
        [at, at + width) of the stored value -- unless the slot was itself
        tiled from parts, and a tiling of parts of one value in order is that
        value.  Both are exact functions of the stored bytes.
        """
        if len(overlapping) == 1:
            start, size = overlapping[0]
            require(
                start <= offset and offset + width <= start + size,
                f"{self.context}: a read of ESP0{offset:+d} ({width} bytes) partly overlaps a "
                "stack slot",
            )
            return _part(self.slots[(start, size)], offset - start, width)
        cursor = offset
        tiles = []
        for start, size in overlapping:
            require(
                start == cursor and start + size <= offset + width,
                f"{self.context}: a read of ESP0{offset:+d} ({width} bytes) partly overlaps a "
                "stack slot",
            )
            tiles.append((start - offset, size, self.slots[(start, size)]))
            cursor = start + size
        require(
            cursor == offset + width,
            f"{self.context}: a read of ESP0{offset:+d} ({width} bytes) partly overlaps a "
            "stack slot",
        )
        return _tiled(tuple(tiles), width)

    def store(self, state: PathState, address: Term, width: int, value: Term) -> bool:
        if self.facts.private and mentions_stack_address(value):
            raise EscapeRefusal(f"{self.context}: a stack address is stored to memory")
        offset = self._offset(state, address)
        if offset is None or not self._owned(offset, width):
            return False
        for key in self._overlapping(offset, width):
            del self.slots[key]
        self.slots[(offset, width)] = value
        self.dirty |= {byte for byte in range(offset, offset + width) if byte >= 0}
        return True

    def _window(self, state: PathState, context: str) -> tuple[int, int]:
        """The argument window [ESP, W) at a call (check 7c).

        W is the first saved-register word above ESP (a word holding a
        callee-saved register's entry value), or the bottom of the locals
        block B when there is none.
        """
        current = self._current(state)
        base = self.facts.base
        require(
            current <= base,
            f"{context}: a call is made with ESP at ESP0{current:+d}, above the frame base "
            f"ESP0{base:+d}",
        )
        cursor = current
        for offset, width in sorted(self._overlapping(current, base - current)):
            if offset == cursor and self.slots[(offset, width)] in _SAVED_ENTRY_VALUES:
                return current, cursor
            require(
                offset == cursor and offset + width <= base,
                f"{context}: the stack words a callee may read as arguments are not all stored",
            )
            cursor = offset + width
        require(
            cursor == base,
            f"{context}: the stack words a callee may read as arguments are not all stored",
        )
        return current, cursor

    def arguments(self, state: PathState, context: str) -> Term:
        """The words of the argument window, relative to ESP (check 7c)."""
        if not self.facts.private:
            return None
        current, end = self._window(state, context)
        return tuple(
            (offset - current, width, self.slots[(offset, width)])
            for offset, width in sorted(self._overlapping(current, end - current))
        )

    @staticmethod
    def event_name(identity: Term) -> Term:
        """A call event's name in later terms: the SHA-256 of its term's text."""
        return ("call#", hashlib.sha256(repr(identity).encode()).hexdigest())

    @staticmethod
    def digest(tag: str, value: Term) -> Term:
        """A term's name in later terms: equal terms have equal text, so equal names.

        Terms share subterms; naming the large ones (a load's dependent
        stores, a scan's memory) keeps every later term's text linear.
        """
        return (f"{tag}#", hashlib.sha256(repr(value).encode()).hexdigest())

    def after_call(self, state: PathState, identity: Term) -> None:
        """The callee may have written its argument words (a1, a2)."""
        if not self.facts.private:
            return
        current, end = self._window(state, self.context)
        for key in self._overlapping(current, end - current):
            del self.slots[key]
        for offset in range(current, end, 4):
            self.slots[(offset, 4)] = lin_atom(("argout", identity, offset - current))


def _width_term(atom: Term, width: int) -> Term:
    return lin_atom(atom) if width == 4 else ("b", width * 8, atom)


def _inner(value: Term) -> Term:
    """The atom a 4-byte (``lin``) or other-width (``b``) value term wraps, if any."""
    if value[0] == "lin" and value[1] == 0 and len(value[2]) == 1 and value[2][0][1] == 1:
        return value[2][0][0]
    if value[0] == "b":
        return value[2]
    return None


def _part(value: Term, at: int, width: int) -> Term:
    inner = _inner(value)
    if isinstance(inner, tuple) and inner and inner[0] == "tiled":
        for tile_at, tile_width, tile in inner[1]:
            if (tile_at, tile_width) == (at, width):
                return tile
    return _width_term(("part", value, at, width), width)


def _tiled(tiles: tuple[tuple[int, int, Term], ...], width: int) -> Term:
    sources = set()
    for at, size, tile in tiles:
        inner = _inner(tile)
        if not (
            isinstance(inner, tuple) and inner and inner[0] == "part" and inner[2:] == (at, size)
        ):
            break
        sources.add(inner[1])
    else:
        if len(sources) == 1:
            whole = next(iter(sources))
            if _width_of(whole) == width:
                return cast(Term, whole)
    return _width_term(("tiled", tiles), width)


def _width_of(value: Term) -> int | None:
    if value[0] == "lin":
        return 4
    if value[0] == "b":
        return cast(int, value[1]) // 8
    return None


# --- programs and their cut points ---------------------------------------------------


class Program:
    """One version's code: its instructions, static flow and cut points.

    ``helpers`` maps each compiler helper the code calls to its verified body
    (check 2); every indirect call through a vtable slot gets the argument
    pop its stack relation determines (:func:`indirect_call_pops`).
    """

    def __init__(
        self,
        code: bytes,
        relocations: Mapping[int, RelocationTarget],
        side: str,
        context: str,
        helpers: Mapping[str, HelperCode] | None = None,
    ) -> None:
        self.code = code
        self.side = side
        self.context = context
        self.relocations = dict(relocations)
        self.helpers = dict(helpers or {})
        starts = region_boundaries(code, 0, len(code), context)
        self.instructions = {
            offset: _Instruction(code, offset, self.relocations, context, extended=True)
            for offset in starts
        }
        self.successors: dict[int, tuple[int, ...]] = {}
        for offset, item in self.instructions.items():
            self.successors[offset] = self._flow(item)
        self.reachable = self._reach()
        self.cuts = self._cut_points()
        self.indirect_pops = indirect_call_pops(self)
        for offset, pop in self.indirect_pops.items():
            self.instructions[offset].indirect_pop = pop

    def is_return(self, item: _Instruction) -> bool:
        return item.opcode in (0xC3, 0xC2) and not item.operand16

    def _flow(self, item: _Instruction) -> tuple[int, ...]:
        end = item.offset + item.length
        op = item.opcode
        if self.is_return(item):
            return ()
        if 0x70 <= op <= 0x7F or 0x0F80 <= op <= 0x0F8F:
            size = 1 if op <= 0x7F else 4
            return (end, end + _displacement(item, size))
        if op in (0xEB, 0xE9):
            return (end + _displacement(item, 1 if op == 0xEB else 4),)
        if op == 0xFF and item.modrm()[1] in (4, 5):
            raise ByteIdentityError(
                f"{item.context}: an indirect jump is outside the closed set (no switch table "
                "is admitted)"
            )
        return (end,)

    def _reach(self) -> list[int]:
        seen: set[int] = set()
        order = []
        stack = [0]
        while stack:
            offset = stack.pop()
            if offset in seen:
                continue
            require(
                offset in self.instructions,
                f"{self.context}: control reaches {offset}, which is not an instruction of the "
                "code",
            )
            seen.add(offset)
            order.append(offset)
            stack.extend(reversed(self.successors[offset]))
        return sorted(order)

    def _straight_to_return(self, offset: int) -> bool:
        seen = set()
        while offset not in seen:
            seen.add(offset)
            item = self.instructions[offset]
            if self.is_return(item):
                return True
            following = self.successors[offset]
            if len(following) != 1:
                return False
            offset = following[0]
        return False

    def _cut_points(self) -> frozenset[int]:
        predecessors: Counter[int] = Counter()
        for offset in self.reachable:
            for target in self.successors[offset]:
                predecessors[target] += 1
        require(
            predecessors[0] == 0,
            f"{self.context}: a branch targets the function's entry",
        )
        headers = set()
        state: dict[int, int] = {}
        stack: list[tuple[int, int]] = [(0, 0)]
        while stack:
            offset, index = stack.pop()
            if index == 0:
                state[offset] = 1
            following = self.successors[offset]
            if index < len(following):
                stack.append((offset, index + 1))
                target = following[index]
                if state.get(target) == 1:
                    headers.add(target)
                elif target not in state:
                    stack.append((target, 0))
            else:
                state[offset] = 2
        cuts = {0} | headers
        for offset in self.reachable:
            if predecessors[offset] < 2 or offset in cuts:
                continue
            item = self.instructions[offset]
            if item.opcode in (0xEB, 0xE9) or self._straight_to_return(offset):
                continue
            cuts.add(offset)
        return frozenset(cuts)


def vtable_call(item: _Instruction) -> bool:
    """Whether an instruction is ``call [reg+disp]`` (``FF /2``, memory, not ``[abs32]``)."""
    if item.opcode != 0xFF or item.operand16:
        return False
    mod, digit, rm = item.modrm()
    return digit == 2 and mod != 3 and not (mod == 0 and rm == 5)


MAX_INDIRECT_POP = 4096


def _scratch_state(eax: int | None) -> PathState:
    regs = {name: lin_atom(("reg0", name)) for name in (*GENERAL_REGISTERS, "esp")}
    if eax is not None:
        regs["eax"] = lin(eax)
    return PathState(regs, {name: ("flag0", name) for name in FLAG_NAMES})


def _stack_change(program: Program, item: _Instruction, eax: int | None) -> int:
    """ESP after the instruction minus ESP before it, by the simulator's own semantics.

    ``eax`` is EAX when the instruction before is ``mov eax, imm32`` (the
    argument of ``__chkstk``).  A change that is not a constant refuses.
    """
    if 0xD8 <= item.opcode <= 0xDF or item.opcode in _STRING_OPCODES:
        return 0  # x87 and string instructions do not touch ESP
    state = _scratch_state(eax)
    before = state.regs["esp"]
    _step(state, item, _Undefined(f"{program.side}-stack"), None, program.helpers)
    change = const_of(lin_sub(state.regs["esp"], before))
    require(
        change is not None,
        f"{item.context}: ESP changes by a non-constant amount, so the stack relation does not "
        "determine an indirect callee's argument pop",
    )
    return _signed(cast(int, change))


def indirect_call_pops(program: Program) -> dict[int, int]:
    """The bytes each vtable call's callee pops, determined by the stack relation.

    Each indirect call site i gets an unknown n_i.  A walk of the reachable
    code from the entry (ESP = ESP0) gives ESP - ESP0 at every instruction
    as a form c + sum(k_i n_i): every other instruction changes ESP by the
    constant its simulated semantics give (a direct call by its decoration's
    pop, a helper by its simulated effect), a vtable call by n_i.  Wherever
    two edges meet the forms must be equal, and at every ``ret`` ESP is ESP0
    (the return address is on top).  The solution must be unique for every
    n_i, and each n_i a multiple of four in [0, MAX_INDIRECT_POP]; otherwise
    the pop is not determined and the call is refused.  Under a4 (module
    docstring) the donor's solution is its callees' real pops; the
    replacement's must agree, which the call events check (the pop is part
    of each event's name).
    """
    sites = [offset for offset in program.reachable if vtable_call(program.instructions[offset])]
    if not sites:
        return {}
    index = {site: number for number, site in enumerate(sites)}
    count = len(sites)
    forms: dict[int, tuple[Fraction, ...]] = {}
    equations: list[tuple[Fraction, ...]] = []
    eax_before: dict[int, int | None] = {}
    stack: list[tuple[int, tuple[Fraction, ...], int | None]] = [
        (0, (Fraction(0),) * (count + 1), None)
    ]
    while stack:
        offset, form, eax = stack.pop()
        if offset in forms:
            if forms[offset] != form:
                equations.append(tuple(a - b for a, b in zip(forms[offset], form, strict=True)))
            require(
                eax_before[offset] == eax or not _helper_call(program, offset),
                f"{program.context}: the helper call at {offset} is reached with different "
                "arguments",
            )
            continue
        forms[offset] = form
        eax_before[offset] = eax
        item = program.instructions[offset]
        if program.is_return(item):
            equations.append(form)
            continue
        if offset in index:
            following = list(form)
            following[1 + index[offset]] += 1
            after: tuple[Fraction, ...] = tuple(following)
        else:
            change = _stack_change(program, item, eax)
            after = (form[0] + change, *form[1:])
        known = None
        if item.opcode == 0xB8 and not item.operand16 and offset + 1 not in program.relocations:
            known = int.from_bytes(item.raw[item.cursor : item.cursor + 4], "little")
        for target in program.successors[offset]:
            stack.append((target, after, known))
    values = _solve(equations, count)
    pops = {}
    for site in sites:
        value = values[index[site]]
        require(
            value is not None,
            f"{program.context}: the stack relation does not determine the argument pop of the "
            f"indirect call at {site}",
        )
        pop = cast(Fraction, value)
        require(
            pop.denominator == 1 and 0 <= pop <= MAX_INDIRECT_POP and int(pop) % 4 == 0,
            f"{program.context}: the indirect call at {site} would pop {pop} bytes",
        )
        pops[site] = int(pop)
    return pops


def _helper_call(program: Program, offset: int) -> bool:
    item = program.instructions[offset]
    target = program.relocations.get(offset + 1)
    return (
        item.opcode == 0xE8
        and isinstance(target, tuple)
        and target[0] == "rel32"
        and target[1] in program.helpers
    )


def _solve(equations: list[tuple[Fraction, ...]], count: int) -> list[Fraction | None]:
    """The unknowns c + sum(k_i n_i) = 0 fix uniquely (None for one they do not), or refuse."""
    rows = [list(row) for row in equations]
    pivots: list[tuple[int, int]] = []
    rank = 0
    for column in range(1, count + 1):
        chosen = next((r for r in range(rank, len(rows)) if rows[r][column] != 0), None)
        if chosen is None:
            continue
        rows[rank], rows[chosen] = rows[chosen], rows[rank]
        lead = rows[rank][column]
        rows[rank] = [value / lead for value in rows[rank]]
        for other in range(len(rows)):
            if other != rank and rows[other][column] != 0:
                factor = rows[other][column]
                rows[other] = [a - factor * b for a, b in zip(rows[other], rows[rank], strict=True)]
        pivots.append((rank, column))
        rank += 1
    for leftover in rows[rank:]:
        require(
            leftover[0] == 0,
            "the stack relation is inconsistent: ESP differs between paths that meet",
        )
    values: list[Fraction | None] = [None] * count
    pivot_columns = {column for _row, column in pivots}
    for row, column in pivots:
        if all(
            rows[row][other] == 0 for other in range(1, count + 1) if other not in pivot_columns
        ):
            values[column - 1] = -rows[row][0]
    return values


def _displacement(item: _Instruction, size: int) -> int:
    require(
        item.offset + item.cursor not in item.relocations,
        f"{item.context}: a relocated branch is outside the closed set",
    )
    return int.from_bytes(item.raw[item.cursor : item.cursor + size], "little", signed=True)


# --- relations ----------------------------------------------------------------------


Location = tuple[Any, ...]
Member = tuple[str, Location]


@dataclass(frozen=True)
class ValueClass:
    """Locations of D and P that hold one value (a constant when ``constant`` is set)."""

    members: frozenset[Member]
    constant: Term
    shape: Any


@dataclass(frozen=True)
class SideFacts:
    """One version's ESP constant, x87 depth (or "after" a call) and dirty parameter bytes."""

    esp: int
    x87: tuple[Any, ...]
    dirty: frozenset[int] = frozenset()


@dataclass(frozen=True)
class Relation:
    """A state relation at a pair of cut points (see Definitions)."""

    classes: frozenset[ValueClass]
    donor: SideFacts
    image: SideFacts

    def side(self, side: str) -> SideFacts:
        return self.donor if side == "D" else self.image


def establish(
    donor: Mapping[Location, Term],
    image: Mapping[Location, Term],
    donor_facts: SideFacts,
    image_facts: SideFacts,
) -> Relation:
    """The relation a pair of path ends establishes (check 6)."""
    by_term: dict[Term, set[Member]] = {}
    for side, locations in (("D", donor), ("P", image)):
        for location, term in locations.items():
            by_term.setdefault(term, set()).add((side, location))
    classes = set()
    for term, members in by_term.items():
        constant = term if closed_term(term) else None
        if len(members) >= 2 or constant is not None:
            classes.add(ValueClass(frozenset(members), constant, _shape(term)))
    return Relation(frozenset(classes), donor_facts, image_facts)


def meet(left: Relation, right: Relation, context: str) -> Relation:
    """The common refinement of two relations at one pair of cut points (check 6)."""
    for name, a, b in (
        ("donor", left.donor, right.donor),
        ("replacement", left.image, right.image),
    ):
        require(
            a.esp == b.esp,
            f"{context}: the {name}'s stack depth differs between the paths reaching it "
            f"(ESP0{a.esp:+d} and ESP0{b.esp:+d})",
        )
        require(
            a.x87 == b.x87,
            f"{context}: the {name}'s x87 stack differs between the paths reaching it",
        )
    first = {member: cls for cls in left.classes for member in cls.members}
    second = {member: cls for cls in right.classes for member in cls.members}
    groups: dict[tuple[ValueClass, ValueClass], set[Member]] = {}
    for member in first.keys() & second.keys():
        groups.setdefault((first[member], second[member]), set()).add(member)
    classes = set()
    for (a_class, b_class), members in groups.items():
        if a_class.shape != b_class.shape:
            continue
        constant = (
            a_class.constant
            if a_class.constant is not None and a_class.constant == b_class.constant
            else None
        )
        if len(members) >= 2 or constant is not None:
            classes.add(ValueClass(frozenset(members), constant, a_class.shape))
    return Relation(
        frozenset(classes),
        SideFacts(left.donor.esp, left.donor.x87, left.donor.dirty | right.donor.dirty),
        SideFacts(left.image.esp, left.image.x87, left.image.dirty | right.image.dirty),
    )


def implies(established: Relation, target: Relation) -> str | None:
    """None when every fact of ``target`` holds wherever ``established`` does, else why."""
    for name, a, b in (
        ("donor", established.donor, target.donor),
        ("replacement", established.image, target.image),
    ):
        if a.esp != b.esp or a.x87 != b.x87:
            return f"the {name}'s stack depth or x87 stack differs from the relation's"
        if not a.dirty <= b.dirty:
            return f"the {name} has written a parameter word the relation calls unwritten"
    owner = {member: cls for cls in established.classes for member in cls.members}
    for cls in target.classes:
        holders = {owner.get(member) for member in cls.members}
        if len(holders) != 1 or None in holders:
            return "a class of the relation is not one value at the end of a path"
        holder = cast(ValueClass, next(iter(holders)))
        if cls.constant is not None and holder.constant != cls.constant:
            return "a constant class of the relation is not that constant at the end of a path"
    return None


# --- paths --------------------------------------------------------------------------


@dataclass
class PathEnd:
    """A path from a cut point: where it ended and its state there."""

    kind: str
    at: int
    state: PathState
    start_depth: Any
    return_address: Term = None
    locations: dict[Location, Term] = field(default_factory=dict)
    facts: SideFacts | None = None


def entry_state(
    side: str,
    key: tuple[int, int],
    relation: Relation | None,
    frame: FrameFacts,
    context: str,
) -> tuple[PathState, Any]:
    """The symbolic state of one version at a pair of cut points, and its x87 depth.

    ``relation`` None is the function's entry: both versions start from one
    machine state, every register r holding ``("reg0", r)``.
    """
    if relation is None:
        state = PathState(
            {name: lin_atom(("reg0", name)) for name in (*GENERAL_REGISTERS, "esp")},
            {name: ("flag0", name) for name in FLAG_NAMES},
        )
        state.frame = FrameModel(frame, context=context)
        return state, ("depth", 0)
    terms: dict[Member, Term] = {}
    for index, cls in enumerate(
        sorted(relation.classes, key=lambda item: repr(sorted(item.members)))
    ):
        named = cls.constant if cls.constant is not None else _shaped(("cv", key, index), cls.shape)
        for member in cls.members:
            terms[member] = named

    def value(location: Location, shape: Any) -> Term:
        member = (side, location)
        if member in terms:
            return terms[member]
        return _shaped(("free", side, key, location), shape)

    facts = relation.side(side)
    regs = {name: value(("r", name), "lin") for name in GENERAL_REGISTERS}
    regs["esp"] = lin(facts.esp, [(ESP0, 1)])
    flags = {name: ("free", side, key, ("flag", name)) for name in FLAG_NAMES}
    cc = {name: ("free", side, key, ("cc", name)) for name in X87_CONDITION_BITS}
    if facts.x87[0] == "depth":
        depth = facts.x87[1]
        fpu = X87State(slots={i: value(("st", i), "x87") for i in range(depth)}, cc=cc)
    else:
        fpu = X87State(base=value(("x87",), "x87"), cc=cc, after_call=True)
    slots = {}
    for member in terms:
        if member[0] == side and member[1][0] == "m":
            _tag, offset, width = member[1]
            slots[(offset, width)] = terms[member]
    state = PathState(regs, flags, fpu=fpu, epoch=("mem@", key))
    state.frame = FrameModel(frame, slots, facts.dirty, context)
    return state, facts.x87


def run_paths(
    program: Program,
    start: int,
    state: PathState,
    start_depth: Any,
    frame: FrameFacts,
    x87_returns: Mapping[str, int],
    context: str,
) -> list[PathEnd]:
    """Every path of ``program`` from the cut point ``start`` to the next cut point or return."""
    undefined = _Undefined(f"{program.side}{start}")
    results: list[PathEnd] = []
    pending: list[tuple[int, PathState, bool]] = [(start, state, True)]
    steps = 0
    while pending:
        offset, path, first = pending.pop()
        while True:
            if not first and offset in program.cuts:
                results.append(PathEnd("cut", offset, path, start_depth))
                break
            first = False
            steps += 1
            require(steps <= MAX_STEPS, f"{context}: the paths exceed the step bound")
            require(
                offset in program.instructions,
                f"{context}: control reaches {offset}, which is not an instruction",
            )
            item = program.instructions[offset]
            if program.is_return(item):
                pop = 4
                if item.opcode == 0xC2:
                    pop += int.from_bytes(item.raw[item.cursor : item.cursor + 2], "little")
                address = _load(path, path.regs["esp"], 4)
                path.regs["esp"] = lin_sub(path.regs["esp"], lin(-pop))
                results.append(PathEnd("ret", offset, path, start_depth, address))
                break
            action, detail = _step(path, item, undefined, x87_returns, program.helpers)
            if frame.private:
                for name in GENERAL_REGISTERS:
                    if mentions_stack_address(path.regs[name]):
                        raise EscapeRefusal(
                            f"{context}: {name} holds a value computed from ESP at {offset}"
                        )
            require(
                _esp_offset(path.regs["esp"]) is not None,
                f"{context}: ESP is not a constant offset from its entry value after {offset}",
            )
            following = offset + item.length
            if action == "fall":
                offset = following
                continue
            if action == "jump":
                offset = detail
                continue
            code_value, target = detail
            decided = condition(code_value, path.flags)
            if isinstance(decided, bool):
                offset = target if decided else following
                continue
            atom, taken_value = decided
            known = dict(path.conditions)
            if atom in known:
                offset = target if known[atom] == taken_value else following
                continue
            if atom[0] == "fcc":
                allowed = _fcc_allowed(path.conditions).get(atom[1])
                if allowed is not None and (allowed <= set(atom[2]) or not allowed & set(atom[2])):
                    holds = allowed <= set(atom[2])
                    offset = target if holds == taken_value else following
                    continue
            other = path.fork()
            other.conditions.append((atom, not taken_value))
            path.conditions.append((atom, taken_value))
            pending.append((following, other, False))
            require(
                len(results) + len(pending) + 1 <= MAX_PATHS,
                f"{context}: more than {MAX_PATHS} paths leave one cut point",
            )
            offset = target
    for end in results:
        require(
            not mentions_x87_undefined(
                (end.state.conditions, end.state.stores, end.state.footprint)
            ),
            f"{context}: a path reads an x87 condition bit the last x87 instruction left undefined",
        )
        _summarise(end, frame, context)
    return results


def _summarise(end: PathEnd, frame: FrameFacts, context: str) -> None:
    """The end locations and side facts of a path, checking its x87 bounds (check 5f)."""
    state = end.state
    fpu = state.fpu
    locations: dict[Location, Term] = {("r", name): state.regs[name] for name in GENERAL_REGISTERS}
    if frame.private:
        for (offset, width), term in state.frame.slots.items():
            locations[("m", offset, width)] = term
    start = end.start_depth
    if start[0] == "depth" and fpu.used:
        depth = start[1]
        require(
            fpu.need <= depth,
            f"{context}: a path reads x87 register {fpu.need - 1} of a stack {depth} deep",
        )
        require(depth + fpu.peak <= 8, f"{context}: a path overflows the x87 stack")
        for push in fpu.call_pushes:
            require(
                depth + push == 0,
                f"{context}: a call is made with {depth + push} values on the x87 stack",
            )
    if fpu.after_call:
        x87: tuple[Any, ...] = ("after",)
        locations[("x87",)] = fpu.base
    else:
        if fpu.call_frame:
            depth_now = fpu.push
        else:
            require(start[0] == "depth", f"{context}: an x87 frame of unknown depth")
            depth_now = start[1] + fpu.push
        x87 = ("depth", depth_now)
        for index in range(depth_now):
            position = index - fpu.push
            locations[("st", index)] = fpu.slots.get(position, fpu.entry_term(position))
    end.locations = locations
    end.facts = SideFacts(
        cast(int, _esp_offset(state.regs["esp"])), x87, frozenset(state.frame.dirty)
    )


def _dead_stack_store(store: tuple[Term, int, Term], frame: FrameFacts) -> bool:
    offset = _esp_offset(store[0])
    if offset is None:
        return False
    return offset + store[1] <= 0 or (offset >= 4 and offset + store[1] <= frame.params_end)


def _footprint(path: PathState, frame: FrameFacts) -> frozenset[Term]:
    """The footprint without own-frame accesses (a3)."""
    kept = set()
    for entry in path.footprint:
        if (
            isinstance(entry, tuple)
            and len(entry) == 2
            and isinstance(entry[1], int)
            and entry[0][0] == "lin"
        ):
            offset = _esp_offset(entry[0])
            if offset is not None and offset + entry[1] <= frame.params_end:
                continue
        kept.add(entry)
    return frozenset(kept)


def _compare_pair(left: PathEnd, right: PathEnd, frame: FrameFacts, context: str) -> None:
    """Check 5 for one consistent pair of paths."""
    where = f"{context} (the donor's path to {left.at}, the replacement's to {right.at})"
    require(
        left.state.events == right.state.events,
        f"{where}: the two versions make different calls",
    )
    returning = left.kind == "ret"
    require(
        left.kind == right.kind,
        f"{where}: one version returns where the other reaches a join",
    )
    if returning:
        stores_left = tuple(s for s in left.state.stores if not _dead_stack_store(s, frame))
        stores_right = tuple(s for s in right.state.stores if not _dead_stack_store(s, frame))
    else:
        stores_left, stores_right = tuple(left.state.stores), tuple(right.state.stores)
    why = stores_equivalent(stores_left, stores_right)
    require(why is None, f"{where}: the two versions leave different memory: {why}")
    require(
        _footprint(left.state, frame) == _footprint(right.state, frame),
        f"{where}: the two versions access different memory",
    )
    if not frame.private or returning:
        require(
            left.state.regs["esp"] == right.state.regs["esp"],
            f"{where}: the two versions leave a different stack pointer",
        )
    if returning:
        require(
            left.return_address == right.return_address,
            f"{where}: the two versions return to different addresses",
        )
        for name in RETURN_REGISTERS:
            require(
                left.state.regs[name] == right.state.regs[name],
                f"{where}: {name} differs at the return",
            )
        x87_left = {k: v for k, v in left.locations.items() if k[0] in ("st", "x87")}
        x87_right = {k: v for k, v in right.locations.items() if k[0] in ("st", "x87")}
        require(
            x87_left == x87_right and left.facts.x87 == right.facts.x87,  # type: ignore[union-attr]
            f"{where}: the two versions return different x87 stacks",
        )


# --- the proof ----------------------------------------------------------------------


@dataclass
class ValidationProof:
    """What the fixpoint settled: the pairing, the relations and the counts."""

    frame: FrameFacts
    pairs: dict[int, int]
    relations: dict[tuple[int, int], Relation]
    path_counts: tuple[int, int]
    path_pairs: int
    returns: int


def validate_function(
    donor: Program,
    image: Program,
    frame: FrameFacts,
    x87_returns: Mapping[str, int],
    context: str,
) -> ValidationProof:
    """Checks 4-6: pair the cut points, settle the relations, prove every path pair.

    Each program carries its verified helper bodies (``Program.helpers``).
    """
    relations: dict[tuple[int, int], Relation | None] = {(0, 0): None}
    pair_of_donor = {0: 0}
    pair_of_image = {0: 0}
    queue = [(0, 0)]
    visits: Counter[tuple[int, int]] = Counter()

    def run(key: tuple[int, int]) -> list[tuple[PathEnd, PathEnd]]:
        relation = relations[key]
        here = f"{context} from ({key[0]}, {key[1]})"
        ends = []
        for program, start in ((donor, key[0]), (image, key[1])):
            state, depth = entry_state(program.side, key, relation, frame, f"{here} {program.side}")
            ends.append(
                run_paths(
                    program, start, state, depth, frame, x87_returns, f"{here} {program.side}"
                )
            )
        consistent = [
            (left, right)
            for left in ends[0]
            for right in ends[1]
            if not contradictory(left.state.conditions, right.state.conditions)
        ]
        require(bool(consistent), f"{here}: no pair of paths is consistent")
        for left, right in consistent:
            _compare_pair(left, right, frame, here)
        return consistent

    def pair(left: PathEnd, right: PathEnd, here: str) -> tuple[int, int]:
        x, y = left.at, right.at
        require(
            pair_of_donor.get(x, y) == y and pair_of_image.get(y, x) == x,
            f"{here}: the control-flow graphs differ (the donor's {x} meets the replacement's "
            f"{y}, but they are paired with {pair_of_donor.get(x)} and {pair_of_image.get(y)})",
        )
        pair_of_donor[x] = y
        pair_of_image[y] = x
        return (x, y)

    while queue:
        key = queue.pop(0)
        visits[key] += 1
        require(
            visits[key] <= MAX_VISITS,
            f"{context}: the relation at ({key[0]}, {key[1]}) does not settle",
        )
        for left, right in run(key):
            if left.kind == "ret":
                continue
            target = pair(left, right, f"{context} from ({key[0]}, {key[1]})")
            established = establish(
                left.locations,
                right.locations,
                cast(SideFacts, left.facts),
                cast(SideFacts, right.facts),
            )
            old = relations.get(target)
            new = (
                established
                if target not in relations
                else meet(cast(Relation, old), established, f"{context} at {target}")
            )
            require(target != (0, 0), f"{context}: a branch targets the function's entry")
            if target not in relations or new != old:
                relations[target] = new
                if target not in queue:
                    queue.append(target)
    # The final pass under the settled relations.
    path_pairs = 0
    returns = 0
    donor_paths = 0
    image_paths = 0
    for key in sorted(relations):
        consistent = run(key)
        donor_paths += len({id(left) for left, _right in consistent})
        image_paths += len({id(right) for _left, right in consistent})
        for left, right in consistent:
            path_pairs += 1
            if left.kind == "ret":
                returns += 1
                continue
            target = (left.at, right.at)
            require(
                pair_of_donor.get(left.at) == right.at,
                f"{context}: the final pass reaches an unpaired cut point",
            )
            established = establish(
                left.locations,
                right.locations,
                cast(SideFacts, left.facts),
                cast(SideFacts, right.facts),
            )
            why = implies(established, cast(Relation, relations[target]))
            require(
                why is None,
                f"{context}: the path pair from ({key[0]}, {key[1]}) to {target} breaks the "
                f"relation there: {why}",
            )
    for program in (donor, image):
        consumed: set[int] = set()
        for item in program.instructions.values():
            consumed |= item.consumed
        unread = sorted(set(program.relocations) - consumed)
        require(
            not unread,
            f"{context}: the {program.side} relocated fields at {unread} are not read on any path",
        )
    return ValidationProof(
        frame,
        dict(sorted(pair_of_donor.items())),
        {key: value for key, value in relations.items() if value is not None},
        (donor_paths, image_paths),
        path_pairs,
        returns,
    )


def locals_block_first(program: Program, base: int) -> bool:
    """Whether the donor's first stack change is ``sub esp, -base`` (check 7, a2).

    The FPO record's cdwLocals is the block MSVC 5.0's prologue allocates
    first, at ESP0; saved registers (some pushed lazily, after early calls),
    spills and arguments all lie below it.  A block of a page or more is
    allocated by ``mov eax, n; call __chkstk`` instead: when the helper is a
    verified body, its simulated effect on ESP (with EAX = n) must be -base.
    """
    if base == 0:
        return True
    offset = 0
    eax: int | None = None
    for _ in range(len(program.instructions)):
        item = program.instructions[offset]
        raw, op = item.raw[item.cursor :], item.opcode
        if op in (0x81, 0x83) and item.modrm() == (3, 5, 4) and not item.operand16:
            size = 1 if op == 0x83 else 4
            amount = int.from_bytes(raw[1 : 1 + size], "little", signed=True)
            return amount == -base
        if _helper_call(program, offset) and eax is not None:
            return _stack_change(program, item, eax) == base
        eax = None
        if op == 0xB8 and not item.operand16 and offset + 1 not in program.relocations:
            eax = int.from_bytes(raw[:4], "little")
        changes_stack = (
            0x50 <= op <= 0x61
            or op in (0x68, 0x6A, 0xE8, 0xC2, 0xC3, 0x8F, 0x9C, 0x9D)
            or (op == 0xFF and item.modrm()[1] in (2, 6))
            or (
                op in (0x81, 0x83, 0x89, 0x8B, 0x8D)
                and 4 in (item.modrm()[2], item.modrm()[1])
                and item.modrm()[0] == 3
            )
        )
        following = program.successors[offset]
        if changes_stack or len(following) != 1:
            return False
        offset = following[0]
    return False


def prove_function(
    donor_code: bytes,
    donor_relocations: Mapping[int, RelocationTarget],
    image_code: bytes,
    image_relocations: Mapping[int, RelocationTarget],
    x87_returns: Mapping[str, int],
    context: str,
    *,
    private_frame: FrameFacts | None = None,
    helpers: Mapping[str, HelperCode] | None = None,
) -> ValidationProof:
    """Checks 2 and 4-7: a private frame when one is given and no stack address escapes.

    A refusal of the private frame because a stack address escapes falls back
    to the shared frame; any other refusal stands.  ``helpers`` maps every
    compiler helper either version calls to its verified body.
    """
    donor = Program(donor_code, donor_relocations, "D", f"{context} donor", helpers)
    image = Program(image_code, image_relocations, "P", f"{context} replacement", helpers)
    shared = FrameFacts(False, params_end=4 if private_frame is None else private_frame.params_end)
    if private_frame is not None and locals_block_first(donor, private_frame.base):
        try:
            return validate_function(
                donor, image, private_frame, x87_returns, f"{context} (private frame)"
            )
        except EscapeRefusal:
            donor = Program(donor_code, donor_relocations, "D", f"{context} donor", helpers)
            image = Program(image_code, image_relocations, "P", f"{context} replacement", helpers)
    return validate_function(donor, image, shared, x87_returns, f"{context} (shared frame)")


def proof_summary(proof: ValidationProof) -> dict[str, Any]:
    """The pinned measurements of a proof (check 8)."""
    return {
        "frame": "private" if proof.frame.private else "shared",
        "frame_base": proof.frame.base if proof.frame.private else None,
        "params_end": proof.frame.params_end,
        "cut_pairs": [[left, right] for left, right in sorted(proof.pairs.items())],
        "donor_paths": proof.path_counts[0],
        "replacement_paths": proof.path_counts[1],
        "path_pairs": proof.path_pairs,
        "returning_pairs": proof.returns,
        "related_locations": sum(
            len(cls.members) for relation in proof.relations.values() for cls in relation.classes
        ),
    }


# --- the record, the image and its installation (checks 1, 3, 8, 9) -------------------

_DIR32 = 0x0006
_REL32 = 0x0014
FUNCTION_VALIDATION_CLOSURES = ((".debug$F", ".debug$S"), (".debug$S", ".xdata$x"))
FUNCTION_VALIDATION_RECIPE = CandidateRecipe(
    label="function-validation",
    splice_class=FUNCTION_VALIDATION_CLASS,
    spec_key="function_validation",
    admissible_closures=FUNCTION_VALIDATION_CLOSURES,
    declaration_label="function-validation rewriting",
    kind=(FUNCTION_VALIDATION_KIND, "function-validation kind differs"),
    donor_seat="optional",
    declared_seat_message="function-validation declared donor seat changed",
    donor_section_count="optional",
    census="extras",
    length_pins=("expected_seed_length", "expected_preimage_length"),
    closure_message=(
        "function-validation target closure is neither the FPO debug pair nor the EH pair"
    ),
)
_SPEC_FIELDS = frozenset(
    {
        "kind",
        "replacement_instructions",
        "replacement_relocations",
        "replacement_debug_end",
        "expected_proc_size",
        "expected_fill_alignment",
        "expected_proof",
        "expected_relocation_reseat",
        "expected_instruction_count",
        "expected_procedure_range",
        "expected_collapsed_line_rows",
        "expected_helper_callees",
    }
)


def donor_relocation_targets(
    rows: list[dict[str, Any]], section_number: int, limit: int, context: str
) -> dict[int, RelocationTarget]:
    """Check 3 on the donor: each record is an external DIR32 field or a call's REL32 field."""
    targets: dict[int, RelocationTarget] = {}
    for row in rows:
        require(
            row["type"] in (_DIR32, _REL32)
            and row["width"] == 4
            and row["target_section"] != section_number
            and row["offset"] + 4 <= limit,
            f"{context}: the relocation at {row['offset']} is neither an external DIR32 field "
            "nor a call's REL32 field",
        )
        targets[row["offset"]] = (
            ("rel32", row["target"]) if row["type"] == _REL32 else row["target"]
        )
    return targets


def validate_replacement(
    spec: dict[str, Any], rows: list[dict[str, Any]], context: str
) -> tuple[bytes, list[int], dict[int, RelocationTarget], list[list[int]], int]:
    """The declared replacement: its code, boundaries, relocation map, reseat and debug end."""
    require_payload_free_declaration(spec, f"{context} declaration")
    encodings = spec["replacement_instructions"]
    require(
        isinstance(encodings, list) and 0 < len(encodings) <= 8192,
        f"{context}: the replacement is not a list of encodings",
    )
    pieces = [_hex_instruction(text, context) for text in encodings]
    code = b"".join(pieces)
    boundaries = [sum(len(piece) for piece in pieces[:k]) for k in range(len(pieces))]
    pairs = spec["replacement_relocations"]
    require(
        isinstance(pairs, list)
        and all(
            isinstance(pair, list)
            and len(pair) == 2
            and all(type(value) is int and value >= 0 for value in pair)
            for pair in pairs
        ),
        f"{context}: the replacement relocations are invalid",
    )
    by_offset = {row["offset"]: row for row in rows}
    locals_ = [pair[0] for pair in pairs]
    donors = [pair[1] for pair in pairs]
    require(
        locals_ == sorted(set(locals_))
        and all(local + 4 <= len(code) for local in locals_)
        and sorted(donors) == sorted(by_offset)
        and len(set(donors)) == len(donors),
        f"{context}: the replacement's relocations are not a sorted bijection onto the donor's",
    )
    targets: dict[int, RelocationTarget] = {}
    reseat = []
    for local, donor in pairs:
        row = by_offset[donor]
        targets[local] = ("rel32", row["target"]) if row["type"] == _REL32 else row["target"]
        if local != donor:
            reseat.append([donor, local])
    debug_end = spec["replacement_debug_end"]
    require(
        type(debug_end) is int and 0 <= debug_end <= len(code),
        f"{context}: the declared debug end lies outside the replacement",
    )
    return code, boundaries, targets, sorted(reseat), debug_end


@dataclass
class FunctionValidationMeasure:
    """Everything the producer measures before it compares the declaration's pins."""

    image: bytes
    derived: bytes
    rows: list[dict[str, Any]]
    reseat: list[list[int]]
    pins: dict[str, Any]


def measure_function_validation(
    donor_bytes: bytes,
    mangled: str,
    spec: dict[str, Any],
    closure: Iterable[str],
    helper_library: HelperLibrary | None = None,
) -> FunctionValidationMeasure:
    """Checks 1-7 and 9 on a donor object and a declaration; the measured pins of check 8.

    ``spec`` needs the replacement, its relocations and debug end, and the
    procedure size and fill alignment (both checked against the donor).
    ``helper_library`` is the authenticated toolchain library the bodies of
    the compiler helpers the donor calls are read from (check 2).
    """
    label = "function-validation"
    donor = CoffObject(donor_bytes)
    dp = donor.function_section(mangled)
    donor_body = bytes(coff_body(donor, dp))
    proc = spec["expected_proc_size"]
    fill_alignment = spec["expected_fill_alignment"]
    require(
        fill_alignment in (1, 16)
        and type(proc) is int
        and 0 < proc <= len(donor_body)
        and _padded_length(proc, fill_alignment) == len(donor_body)
        and all(byte == MSVC50_FUNCTION_FILL_BYTE for byte in donor_body[proc:]),
        f"{label} procedure size or fill alignment differs from the donor",
    )
    rows = detailed_relocations(donor, dp)
    # Check 1: one entry, no data tail, nothing naming an interior offset.
    require(
        not internal_relocation_targets(rows, dp["number"]),
        f"{label}: the donor relocates into its own section (a switch table or a label)",
    )
    require(
        not relational_form_external_entries(donor, dp, f"{label} external entries"),
        f"{label}: the donor has an external entry besides its own",
    )
    debug_start, debug_end_donor = _debug_range(donor, dp, label)
    require(debug_start == 0, f"{label}: the donor's debug range does not start at its entry")
    named = sorted(
        offset
        for offset in protected_code_offsets(donor, dp, label)
        if offset not in (0, proc, debug_end_donor)
    )
    require(not named, f"{label}: a symbol or closure record names the donor's offsets {named}")
    donor_targets = donor_relocation_targets(rows, dp["number"], proc, label)
    helper_symbols = sorted(
        {row["target"] for row in rows if row["type"] == _REL32 and compiler_helper(row["target"])}
    )
    bodies: dict[str, HelperBody] = {}
    if helper_symbols:
        require(
            helper_library is not None,
            f"{label}: the donor calls the compiler helpers {helper_symbols}, and no "
            "authenticated toolchain library is supplied to read their bodies from",
        )
        bodies = cast(HelperLibrary, helper_library).helpers(helper_symbols)
    helpers = {symbol: body.code for symbol, body in bodies.items()}
    code, boundaries, image_targets, reseat, debug_end = validate_replacement(spec, rows, label)
    require(
        sorted(Program(code, image_targets, "P", label, helpers).instructions) == boundaries,
        f"{label}: the replacement does not decode on its declared boundaries",
    )
    private_frame = None
    if ".debug$F" in closure:
        fpo = parse_fpo_data(
            bytes(coff_body(donor, _comdat_child(donor, dp, ".debug$F"))),
            expected_proc_size=dp["raw_size"],
            body=donor_body,
        )
        require(fpo["cbProcSize"] == proc, f"{label} FPO procedure size differs")
        if fpo["cbFrame"] == 0 and not fpo["fHasSEH"]:
            private_frame = FrameFacts(True, -4 * fpo["cdwLocals"], 4 + 4 * fpo["cdwParams"])
    view = relocation_symbol_map(rows)
    items, successors, entries = ia32_relational_flow_walk(
        donor_body[:proc], view, f"{label} donor flow", None, frozenset()
    )
    solution = x87_stack_solution(items, successors, entries, donor_body[:proc], view)
    x87_returns = {} if solution is None else solution[1]
    proof = prove_function(
        donor_body[:proc],
        donor_targets,
        code,
        image_targets,
        x87_returns,
        f"{label} proof",
        private_frame=private_frame,
        helpers=helpers,
    )
    image = code + bytes([MSVC50_FUNCTION_FILL_BYTE]) * (
        _padded_length(len(code), fill_alignment) - len(code)
    )
    require(image != donor_body, f"{label} image does not move the donor body")
    derived, derived_detail = resized_donor_object(
        donor_bytes,
        mangled,
        image,
        {
            "offset_map": {0: 0, proc: len(code)},
            "interiors": [[0, proc, 0]],
            "proc_size": proc,
            "image_proc_size": len(code),
            "relocation_reseat": reseat,
        },
        f"{label} derived donor",
        debug_range=(0, debug_end),
    )
    moved = {old: new for old, new in reseat}
    pins: dict[str, Any] = {
        "expected_proof": proof_summary(proof),
        "expected_relocation_reseat": reseat,
        "expected_instruction_count": len(boundaries),
        "expected_procedure_range": derived_detail["procedure_range"],
        "expected_collapsed_line_rows": derived_detail["collapsed_line_rows"],
    }
    if bodies:
        pins["expected_helper_callees"] = [body.pin() for body in bodies.values()]
    return FunctionValidationMeasure(
        image,
        derived,
        [{**row, "offset": moved.get(row["offset"], row["offset"])} for row in rows],
        reseat,
        pins,
    )


def _static_base(row: Mapping[str, Any]) -> str | None:
    """The base name of a file static ``<base>$S<serial>`` (storage class 3), else None."""
    base, separator, serial = str(row["target"]).rpartition("$S")
    if row.get("target_storage") == 3 and separator and base and serial.isdigit():
        return base
    return None


def require_composed_relocations(
    composed: list[dict[str, Any]], installed: list[dict[str, Any]], context: str
) -> None:
    """The composed table is the proved reseat, up to the composer's renumbering.

    The same-slot composer names a compiler local (``$T<n>``, ``$L<n>``) by
    the seed's symbol of the same kind at the same place, after proving that
    section byte-identical in both objects, and a file static
    ``<base>$S<serial>`` by the seed's static of the same base name: any
    declaration a grind donor adds renumbers both serials while the body's
    bytes stay the same.  So a local is compared by kind and place
    (`rewriting_region_resize._composed_identity`), a static by its base,
    type and storage, every other target by name; and the renaming of
    statics must be one bijection over the whole table, so two statics that
    share a base are never taken for each other.
    """

    def identity(row: dict[str, Any]) -> tuple[Any, ...]:
        base = _static_base(row)
        if base is not None:
            return (
                row["offset"],
                ("static", base, row["target_type"], row["target_storage"]),
                row["type"],
            )
        return _composed_identity(row)

    require(
        [identity(row) for row in composed] == [identity(row) for row in installed],
        f"{context} is not the proved reseat",
    )
    forward: dict[str, str] = {}
    backward: dict[str, str] = {}
    for left, right in zip(composed, installed, strict=True):
        if _static_base(right) is None:
            continue
        require(
            forward.setdefault(right["target"], left["target"]) == left["target"]
            and backward.setdefault(left["target"], right["target"]) == right["target"],
            f"{context} renames the file statics inconsistently",
        )


def produce_function_validation_candidate(
    seed_bytes: bytes,
    donor_bytes: bytes,
    function: dict[str, Any],
    helper_library: HelperLibrary | None = None,
) -> tuple[bytes, dict[str, Any]]:
    """Produce the translation-validated replacement of a fresh donor body (checks 1-9).

    ``helper_library`` is the authenticated toolchain library, needed when
    the donor calls a compiler helper.
    """
    label = "function-validation"
    seats = open_candidate_seats(seed_bytes, donor_bytes, function, FUNCTION_VALIDATION_RECIPE)
    mangled, spec = seats.mangled, seats.spec
    pin_candidate_bodies(seats, function, FUNCTION_VALIDATION_RECIPE)
    require(set(spec) <= _SPEC_FIELDS, f"{label} declaration names an unknown field")
    measured = measure_function_validation(
        donor_bytes, mangled, spec, seats.expected_closure, helper_library
    )
    for key, value in measured.pins.items():
        require(
            spec.get(key) == value,
            f"{label} {key.removeprefix('expected_')} differs from its declaration",
        )
    require(
        ("expected_helper_callees" in spec) == ("expected_helper_callees" in measured.pins),
        f"{label} helper callees differ from its declaration",
    )
    image = measured.image
    require(
        sha256_bytes(image) == function["expected_body_sha256"],
        f"{label} image differs from its pin",
    )
    require(
        len(image) == function["expected_body_length"] == function["expected_donor_length"],
        f"{label} image length differs from its pin",
    )
    require_pinned_length(function, image, label)
    semantic_detail = candidate_relocation_semantics(measured.rows, function, label)
    effective = same_slot_effective(function, mangled)
    if "expected_donor_section_number" in function:
        effective["expected_donor_section_number"] = function["expected_donor_section_number"]
    composed, detail, checked, cp = install_same_slot(
        seed_bytes,
        measured.derived,
        effective,
        mangled,
        image,
        label,
        declared_donor_extras=function.get("expected_donor_extra_functions") or None,
    )
    require_composed_relocations(
        detailed_relocations(checked, cp), measured.rows, f"{label} composed relocation table"
    )
    return composed, candidate_proof(
        detail,
        FUNCTION_VALIDATION_CLASS,
        {
            "function_validation": measured.pins["expected_proof"],
            "relocation_reseat": measured.reseat,
            "instruction_count": measured.pins["expected_instruction_count"],
            "collapsed_line_rows": measured.pins["expected_collapsed_line_rows"],
            "procedure_range": measured.pins["expected_procedure_range"],
            **(
                {"helper_callees": measured.pins["expected_helper_callees"]}
                if "expected_helper_callees" in measured.pins
                else {}
            ),
        },
        semantic_detail,
    )


def _debug_range(donor: CoffObject, section: dict[str, Any], context: str) -> tuple[int, int]:
    raw = bytes(coff_body(donor, _comdat_child(donor, section, ".debug$S")))
    _length, start, end = coff_unpack("<III", raw, 16, f"{context} debug range")
    return start, end


__all__ = [
    "FUNCTION_VALIDATION_CLASS",
    "FUNCTION_VALIDATION_KIND",
    "EscapeRefusal",
    "FrameFacts",
    "Program",
    "Relation",
    "ValidationProof",
    "donor_relocation_targets",
    "measure_function_validation",
    "produce_function_validation_candidate",
    "proof_summary",
    "prove_function",
    "require_composed_relocations",
    "validate_function",
    "validate_replacement",
]
