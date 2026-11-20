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
decoration names), x1-x4 of `rewriting_region_resize`, and a1-a9 below.  An
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
   compiler helper, or a COM vtable call (both below).  Three groups of
   forms are admitted here and not in a region proof (`region_simulation.
   _Instruction`'s ``extended``): ``lea r, [index*scale + disp32]`` with an
   unrelocated displacement (arithmetic on a constant); the string forms
   MSVC 5.0 emits inline -- ``stos``/``movs`` once or under ``rep`` with a
   constant ECX of at most 1024 (exactly that many element loads and
   stores), ``rep stos``/``rep movs`` of any other count (one block event,
   below) and ``repne scasb`` (one opaque term of AL, EDI, ECX and the
   memory state, recorded in the footprint; `region_simulation.
   _string_step`); and the x87 D9 forms beyond the region set
   (`region_simulation._x87_extended`): ``fsin``, ``fcos``, ``f2xm1``,
   ``frndint``, ``fpatan``, ``fyl2x``, ``fyl2xp1``, ``fscale``, ``fprem``,
   ``fprem1``, ``fxtract``, ``ftst``, ``fxam``, the named constants and
   ``fnop``, each an uninterpreted term of its exact operands (never
   evaluated), its exception an event in the footprint, and the condition
   bits it defines (C1 after a rounding, C2 "out of range" after ``fsin``/
   ``fcos``, all four after ``fprem`` and ``fxam``) functions of the same
   operands.  ``fptan`` and ``fsincos`` are refused: they push a second
   value only when the operand is in range, so the stack depth after them
   depends on the operand.  ``std``, ``cld``, ``popf`` and every other
   instruction that could change the direction flag are outside the closed
   set, so the direction flag is clear wherever a string form runs (the
   calling convention clears it at every entry and after every call).

   Further forms.  Also admitted here, each with its exact semantics
   (`region_simulation`'s module docstring): x87 arithmetic and compares on
   an integer in memory (``fiadd`` ... ``fidivr``, ``ficom``/``ficomp``,
   m32int and m16int), whose integer converts exactly, so the operand is the
   term ``fild`` gives the same load; shifts of 8- and 16-bit operands and by
   CL, the count masked to five bits and never assumed non-zero (the flags
   are functions of the value, the masked count and the flag before; CF of
   a narrow shift by CL, OF and AF are undefined); ``adc`` and ``sbb``, the
   carry the canonical CF bit (``sbb r, r`` is ``-CF``); byte-wide ``not``,
   ``neg``, ``mul``, ``imul``, ``div`` and ``idiv`` (a division an event in
   the footprint); and ``movzx``/``movsx`` into a 16-bit register.  Every
   other operand-size-prefixed form is refused.

   Block string moves.  ``rep stos``/``rep movs`` whose ECX is not a
   constant of at most 1024 is one event (`region_simulation.
   _block_string`): a term of its kind, element width, ECX, EDI, ESI (movs),
   the value (stos), the canonical store log since the last event and that
   event.  With the direction flag clear the block's effect on memory is a
   function of exactly those, whether or not source and destination
   overlap, so equal events leave equal memory; it joins the call events
   (5a), so both versions must make the same block moves in the same order
   relative to their calls.  Memory after it is the event's result (the
   store log restarts, later loads name it); ECX is 0 and EDI (and ESI)
   advance by ECX times the width.  Each pointer is checked by the frame
   (`FrameModel.block_start`): a private frame admits no stack address (so
   the block cannot reach a private slot, 7b); a shared frame admits a
   stack address only at a constant offset at or above ESP, or at a small
   constant from where an earlier block or scan from such an address ended
   (an inline ``strcpy``'s second ``rep movsb``, an inline ``strcat``'s copy
   after its scan): by a9 the block then lies at or above ESP, in the
   compared memory.  ``repe``/``repne`` with ``movs``/``stos`` and every
   ``cmps`` are refused.

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
   the same points fix only the sum of their pops and are refused; the
   refusal states the one equation that binds them.  Nothing else fixes
   them soundly: ESP is a known constant only at the entry and at every
   ``ret`` (the walk's equations), a ``[esp+k]`` access between the calls
   constrains nothing, and assuming the words pushed before a call are
   exactly its arguments would be an assumption about the callee that a5
   does not make.
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
   a. they make the same calls and block string moves: equal event terms in
      the same order (a call event names the callee, ESP, the canonical
      store log since the previous event, that event, the x87 stack and
      exception set when used, and in a private frame the argument words,
      check 7; a block event is described in check 2);
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
      finds the stack empty (d plus its push is 0).  A C0-C3 bit an x87
      instruction leaves undefined (every non-compare that does not define
      it, per Intel) is the term ``("x87cc", bit, name)``, ``name`` a digest
      of the instruction's form (opcode and ModR/M register or digit), its
      memory operand's address (in the first pass only), the whole x87 state
      before it (the entry
      depth, TOP, every written register, C0-C3, the exception set and the
      control word) and the stack after it (`region_simulation._X87.
      undefine`).  By a8 the two versions' bits are equal when these terms
      are; such a bit is never equal to a compare's bit, a constant, or the
      bit another instruction or another state leaves, so a version that
      branches on one where the other branches on a compare's bit makes
      the two paths of one side consistent with both of the other's, and
      checks 4 and 5 refuse it (the refusal names the instruction).
      Return counts.  The donor's stack-depth solver (`region_x87`) fixes
      some callees' x87 return counts; a callee it leaves open still
      leaves one fixed count (x1), so the proof is run once for every
      assignment of the open counts that propagation does not refute
      (`region_x87.x87_return_cases`, at most 2**4 cases) and must hold in
      each: the true assignment is among them.  Both versions make the same
      calls (5a), so the case gives both the same counts.  A call through an
      import slot takes its slot symbol's count, as the solver keys it.  The
      pins record each case and its proof.
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
   it.  A proof the equivalences pass made (below) pins ``equivalences``.
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
unchanged (it has no relocation to apply).  (a8) The x87 unit is
deterministic: a condition bit Intel leaves undefined after an instruction
holds, on a given processor, a fixed function of the instruction's form,
its memory operand's address and the x87 state it runs from and leaves
(the registers, TOP and tags, C0-C3, the exception flags and the control
word) -- not of the code address it runs at, the last-instruction
pointers, or any integer state; the same instruction from the same state
leaves the same bit.  The equivalences pass (below) takes the address out
of that list too: it is integer state, and the value it gives the
last-data pointer, both of which a8 already excludes, and the value the
operand carries is part of the x87 state (a load's value is the stack it
leaves, a store's the register it stores).  (Real
processors keep C0, C2 and C3 across ``fld``, ``fst``, ``fxch`` and the
arithmetic, which MSVC 5.0's scheduling relies on, but no such value is
assumed: the bit is related only to the same instruction's from the same
state.)  (a9) A string instruction with the direction flag clear never
wraps around the address space: the top 64 KiB is never accessible (Win32
reserves it and the system half below it), so an operation running upward
from an address faults before it could wrap, and every address it touches
lies at or above where it started.  (a10) Code addresses and objects, for
the equivalences pass only (below): both versions run from one entry
address -- the image is installed in the donor's own slot (check 9) -- so a
code address of either is that address plus its offset; and the function's
own frame and parameter words (ESP0 + c below E, the committed stack of a3)
lie in the thread's stack, which no section of the image overlaps; an
undefined external data symbol names one definition elsewhere (the linker
resolves a name to one definition, and a common symbol to one merged
block), which the donor -- compiled C -- accesses at a constant offset from
the symbol only inside that object (a field or element its declared type
fixes), so distinct definitions are distinct objects, disjoint from each
other, from the stack and from every section this object defines; a symbol
this object defines lies in its section at its value, and two sections of
one object are placed apart.  Only identical read-only data may share an
address (a linker folds no written object), and a store that reached it
would fault.  The replacement's accesses are the donor's (5c compares the
footprints path by path), so they too lie inside their objects.  A section
without IMAGE_SCN_MEM_WRITE is mapped read-only, and neither the function
nor any callee changes the protection of the image's pages (no admitted
instruction can; a callee would have to call ``VirtualProtect`` on them), so
a load inside it reads its initial bytes whatever store comes first: a
store that reached them faults, and the state at a fault is not compared.
(a14) Frame objects, for the
frame-objects pass only (below): when a stack address p escapes -- it is
passed to a call, stored to memory, used by a block string operation, or
held in a register -- the callee, and the donor itself, read and write only
within the local object p points into.  That object is a contiguous range of
the frame, [ESP0 + s, ESP0 + s + n) for a local or parameter the donor's
``S_BPREL32`` record places at s with a type of n bytes
(`frame_objects.donor_frame_objects`), and no access through p, or through
a pointer derived from it, goes past either end.  This is ISO C's rule
against out-of-bounds pointer arithmetic (C90 6.3.6, C99 6.5.6p8: a pointer
into an object, plus or minus an integer, points into the same object or one
past its end, and nothing else is defined), applied to compiled code: the
donor is compiled C, so every access it makes through a pointer is in the
object the pointer was derived from, and a callee that keeps the pointer
obeys the same rule whenever it uses it.  The replacement's accesses that
are not at a constant offset from ESP0 are the donor's (5c compares the
footprints path by path), and its constant-offset accesses are classified
by the same extents, so the two versions agree on which bytes are memory.
No other assumption is made: the relation is inferred, nothing about the
replacement is believed, and the simulator's term model is exact.

The equivalences pass.  Every proof runs first exactly as the records made
before this pass were proved, and its pins are theirs.  Only when that
refuses does it run again (`measure_function_validation`), with these
normal forms, each exact (`region_simulation._equivalences`):

- A compiler helper's return address is the entry address plus the offset
  after the call (a10), not a fresh atom of its version: ``mov eax, n; call
  __chkstk`` at the entry of both leaves the same word in the frame it
  allocates, where a shared frame's call events see it.  Calls that end at
  different offsets leave different words.
- The object model of a10 (`region_simulation.ObjectModel`): an access at
  ESP0 + c below E and one through a relocated data symbol, or through two
  symbols of different objects, are disjoint; two labels of one section are
  related by their offsets in it when both accesses lie inside its size,
  and refused (unknown) when those may overlap; a load from a read-only
  section depends on no store.  An address that is not one of these -- a
  pointer, an index, the stack above E -- keeps the old relation: unknown
  unless its difference is a constant.
- A product of two non-constant terms is normalised modulo 2**32
  (`region_simulation.product`): constant factors commute out and nested
  products flatten, so ``16 * (S * V)`` meets ``8 * (S * (2 * V))``.  No
  distribution, and the flags stay named by the instruction's own operands.
- A store drops every earlier logged store whose bytes it overwrites:
  memory after it does not depend on them.  So the ECX of a ``push ecx``
  that allocates an argument slot, then filled by ``mov [esp], x`` or
  ``fstp [esp]`` before the call, is dead in both versions.  A word the
  callee can read (no overwrite, or only part of it) is still compared.
- An undefined x87 condition bit (check 5f, a8) is named without the memory
  operand's address: that address is integer state and the new last-data
  pointer, which a8 excludes, and the operand's value is already named.  So
  ``fcom m; fxch; fmul; fxch; fstp [esp+0x14]; fnstsw`` meets the same with
  ``fstp [esp+0x10]``.

The frame-objects pass (a14).  When every earlier pass refuses and the
private frame was given up because a stack address escapes (`prove_function`
records it on the refusal), a frame-pointer-free donor runs once more in a
private frame whose escaping objects are memory.

- The extents.  Every ``S_BPREL32`` local of the donor function, its size
  from a CodeView primitive or a type record of the object (``/Z7``) or of
  the PDB type server the object names (``/Zi``), which must carry the
  signature and age the object records (`frame_objects`).  Each lies in the
  locals block [B, ESP0) or the parameter words [ESP0 + 4, E); locals of
  sibling scopes that share bytes are merged into one object.  A local MSVC
  5.0 keeps in a dead parameter's word is recorded 4 bytes above it, and is
  placed there by telling the parameters (the procedure type's count of
  first records) from the later records.  A local of unknown size refuses
  the pass.
- The objects' starts are related by equality: an escaping object lies at
  the same offset from ESP0 in both versions, so its address is one value in
  both, named ``("fobj", s, n)`` (`frame_object_atom`).  A replacement that
  keeps the object elsewhere passes another address and makes another call.
- A value computed from ESP0 must be ESP0 + k for a constant k inside an
  object or one past its end, and becomes that object's atom plus k - s
  (`FrameModel.canonical`), in every register after every instruction and in
  every stored value.  Its object escapes; so does the object k is one past
  the end of, when k is both an object's start and another's end (the
  pointer may be either, and C lets a pointer one past the end reach back
  into its object).  The pass starts with no object escaping and runs again
  with every object a run finds escaping (`ObjectEscape`), until none is new.
- Only a register may hold ESP0 + k for a k in no object (``mov ecx, esp``
  building a structure argument in the outgoing argument block).  It stays
  ESP0 + k: every access through it is at a constant offset from ESP0, a
  private slot related as any other, and no callee receives it, because a
  call's event names no register and every callee admitted takes no
  argument in one (its decoration, a5, a12).  No assumption is added.
- An access at ESP0 + k inside an escaping object, or through its atom, is
  memory, at the atom's address (`FrameModel.memory_address`): in the store
  log, the footprint and the call and block events, compared as any memory
  is, so each escaping object is compared as a unit at every call, and after
  a call its bytes are the call's result, one term in both versions.  Two
  escaping objects, or one and a symbol of a10, are disjoint objects
  (`region_simulation.ObjectModel`).  Every other access at ESP0 + k below E
  is a private slot, related as check 7 relates one: by a14 no callee and no
  pointer reaches it.  At a return the objects' stores are dead stack.
- Refused: a stack address that is not ESP0 plus a constant, or one in no
  object that is stored or starts a block string operation (a compiler
  temporary has no record, so its extent is unknown);
  an access at a variable offset from ESP itself (its displacement may fold
  an index, so its object is not known); an access that lies partly inside
  an escaping object; an access at a constant offset from an object's atom
  that leaves the object; a stored pointer at a constant offset outside its
  object, one past its end included (``va_start``'s address past the last
  parameter, which a callee walks beyond the object); an address combining
  objects' atoms other than as one pointer.

A record this pass made pins ``frame_objects`` (the escaping objects'
starts and sizes) and ``assumptions: ["a14"]``; records of the earlier
passes pin neither.  The build re-derives the extents from the donor it
compiles and the PDB that compile wrote (`classic_project.
ClassicDispatchMaterials.donor_type_server`).

Still refused, with the reason.  x87 operands are commuted only between
registers (since `region_simulation`'s commutativity probe): a memory
operand is not the register a load of it gives, because ``fld m32`` quiets
an SNaN and raises DE for a denormal before the operation, while ``fadd
m32`` meets the raw operand -- with two NaNs the result's payload differs,
and with a NaN and a denormal the DE flag does
(`tests/fixtures/x87_probe/memory_operands.out`: 64 of 200 operand pairs
differ under commuted memory operands, 32 between a memory operand and its
loaded register, none under commuted registers; every one has a NaN).  So
``fld A; fadd B`` never meets ``fld B; fadd A``, and nothing is
reassociated.  In a shared frame (a stack address escapes) every frame byte
is still memory, compared exactly, even a slot whose address is never
taken; only the frame-objects pass, under a14 and the extents the donor's
debug records and type server give, relates such slots.  An escaping object
the replacement keeps at another offset is refused: relating two addresses
of one object would need a callee never to observe a pointer's value (only
its object and offset), and the memory a function leaves could then hold
different dangling pointers to its dead frame.  ESP is part of every call
event, so two frames of different sizes make different calls.  And EAX is
compared at every return: no type in the object says a function is void (its
S_GPROC32 names a type in the PDB type server), and a caller's use of EAX
would be a whole-program fact.
"""

from __future__ import annotations

import hashlib
from collections import Counter
from collections.abc import Iterable, Mapping
from dataclasses import dataclass, field, replace
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
from .frame_objects import FrameObject, FrameObjects, donor_frame_objects
from .region_simulation import (
    _STRING_OPCODES,
    FLAG_NAMES,
    X87_CONDITION_BITS,
    HelperCode,
    ObjectModel,
    PathState,
    RelocationTarget,
    SymbolObject,
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
from .region_x87 import x87_return_cases, x87_stack_solution
from .relational import ia32_relational_flow_walk, relational_form_external_entries
from .rewriting_region_resize import (
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


class ObjectEscape(ByteIdentityError):
    """A frame object's address escapes that the run took as private (a14).

    The frame-objects pass runs again with ``starts`` added to the escaping
    objects (`prove_function`).
    """

    def __init__(self, message: str, starts: Iterable[int]) -> None:
        super().__init__(message)
        self.starts = frozenset(starts)


class UncarriedSlot(ByteIdentityError):
    """A read of a private slot this version wrote, whose value the relation lost.

    ``side`` is the reading version ("D" or "P") and ``offsets`` the bytes it
    wrote.  ``causes`` (`validate_function`) are the (version, byte) pairs of
    slots that a class holding those bytes also held, and that were unwritten
    on another path into a join where the class was lost.  With partial slot
    relations (`prove_function`'s ``partial_slots``) the proof runs again with
    those bytes splitting the relation at every join (`FrameFacts.split`), so
    the paths that wrote them are related apart from the paths that did not.
    """

    def __init__(self, message: str, side: str, offsets: Iterable[int]) -> None:
        super().__init__(message)
        self.side = side
        self.offsets = frozenset(offsets)
        self.causes: frozenset[tuple[str, int]] = frozenset()


def frame_object_atom(item: FrameObject) -> Term:
    """The atom of a frame object's address: ESP0 + its start, in both versions (a14)."""
    return ("fobj", item.start, item.size)


def _frame_object_terms(term: Term) -> list[tuple[Term, int]]:
    """The frame-object atoms of a 32-bit linear term with their coefficients."""
    if term[0] != "lin":
        return []
    return [
        (atom, _signed(coefficient))
        for atom, coefficient in term[2]
        if isinstance(atom, tuple) and atom and atom[0] == "fobj"
    ]


def computed_from_frame_object(term: Term) -> bool:
    """Whether a value is computed from a frame object's address (a14).

    As :func:`computed_from_stack`: a word loaded from memory is whatever was
    stored there, so a load's address (and an event's name) is not part of
    the value's computation.
    """
    stack = [term]
    seen: set[int] = set()
    while stack:
        current = stack.pop()
        if isinstance(current, (tuple, list, frozenset, set)):
            if id(current) in seen:
                continue
            seen.add(id(current))
            if isinstance(current, tuple):
                if current and current[0] == "fobj":
                    return True
                if current and current[0] in ("call", "call#", "ld"):
                    continue
            stack.extend(item for item in current if not isinstance(item, (str, int)))
    return False


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


def computed_from_stack(term: Term) -> bool:
    """Whether a value is computed from ESP0 (not merely loaded from a stack address).

    Like :func:`mentions_stack_address`, but a load's address is not part of
    its value: a word read from the stack is whatever was stored there, and
    a term that names ESP0 only inside load addresses (and event names) is
    not a stack address by its computation.
    """
    stack = [term]
    seen: set[int] = set()
    while stack:
        current = stack.pop()
        if isinstance(current, (tuple, list, frozenset, set)):
            if id(current) in seen:
                continue
            seen.add(id(current))
            if isinstance(current, tuple):
                if current == ESP0:
                    return True
                if current and current[0] in ("call", "call#", "ld"):
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
_CLOSED_TAGS = frozenset({"lin", "b", "k", "sym", "fconst", "reg0", "pld", "fobj"})
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
    """The frame kind and, for a private frame, its base B and parameter end E (check 7).

    ``objects`` is the object model of a10 (`region_simulation.ObjectModel`),
    or None to relate addresses by their constant differences alone.
    """

    private: bool
    base: int = 0
    params_end: int = 4
    objects: ObjectModel | None = None
    # The equivalences pass (`region_simulation._equivalences`, a10).
    equivalences: bool = False
    # The frame-objects pass (a14): the donor's frame objects, and the starts
    # of those whose address escapes in either version.  Their bytes are
    # memory, at addresses named by `frame_object_atom`; every other byte
    # below E is a private slot.
    frame_objects: FrameObjects | None = None
    escaping: frozenset[int] = frozenset()
    # Partial slot relations: the (version, byte) pairs whose writes split the
    # relation at every join (`validate_function`).  A path end belongs to
    # the variant named by which of these bytes it has written since the
    # entry, and each variant is its own relation.
    split: frozenset[tuple[str, int]] = frozenset()
    # Whether partial slot relations run: then every byte's writes are
    # tracked (``FrameModel.dirty``), the locals' in every pass.
    partial: bool = False

    def tracks(self, byte: int) -> bool:
        """Whether ``FrameModel.dirty`` records writes to the byte at ESP0 + byte."""
        return byte >= 0 or self.equivalences or self.partial


_IMAGE_SCN_LNK_COMDAT = 0x1000
_IMAGE_SCN_MEM_WRITE = 0x80000000
_STORAGE_EXTERNAL = 2
_STORAGE_STATIC = 3


def object_model(
    coff: CoffObject, rows: Iterable[Mapping[str, Any]], stack_end: int
) -> ObjectModel:
    """The objects a10 relates the donor's relocated data symbols to.

    Each symbol a relocation names is placed: an undefined external (or a
    common symbol, whose value is its size) in the definition the linker
    resolves its name to, ``("extern", name)``; a symbol this object defines
    in its section, ``("section", number)``, at its value, bounded by the
    section's size -- except an external defined in a COMDAT section, which
    the linker may resolve to another object's copy, so it too is its own
    ``("extern", name)``.  A non-COMDAT section without
    IMAGE_SCN_MEM_WRITE (``.rdata``: the float literals) is read-only.  A
    function symbol, a static label inside a COMDAT section, a weak external
    and every other storage class is left out, so an address through it has
    no object.  ``stack_end`` is E: the own frame
    and parameter words, which a3 already takes as the committed stack.
    """
    symbols: dict[str, SymbolObject] = {}
    read_only: set[Term] = set()
    for row in rows:
        name = row["target"]
        storage, number, value = row["target_storage"], row["target_section"], row["target_value"]
        if (row["target_type"] >> 4) & 3 == 2:
            continue  # a function: code, never a data object
        placed: SymbolObject | None = None
        if storage == _STORAGE_EXTERNAL and number == 0:
            placed = SymbolObject(("extern", name), 0, value or None)
        elif storage in (_STORAGE_EXTERNAL, _STORAGE_STATIC) and 0 < number <= len(coff.sections):
            section = coff.sections[number - 1]
            if section["characteristics"] & _IMAGE_SCN_LNK_COMDAT:
                if storage == _STORAGE_EXTERNAL:
                    placed = SymbolObject(
                        ("extern", name), 0, max(int(section["raw_size"]) - value, 0) or None
                    )
            else:
                placed = SymbolObject(("section", number), value, int(section["raw_size"]))
                if not section["characteristics"] & _IMAGE_SCN_MEM_WRITE:
                    read_only.add(placed.base)
        if placed is not None:
            symbols[name] = placed
    return ObjectModel(symbols, stack_end, frozenset(read_only))


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
        cc_sites: dict[Term, str] | None = None,
        side: str = "",
    ) -> None:
        self.facts = facts
        # The version this frame belongs to ("D" or "P"), for `UncarriedSlot`.
        self.side = side
        # The object model of a10 (`region_simulation.ObjectModel`) and
        # whether the proof runs its equivalences pass.
        self.objects = facts.objects
        self.equivalences = facts.equivalences
        self.slots = dict(slots or {})
        self.dirty = set(dirty)
        self.context = context
        # While an inlined compiler helper runs (`region_simulation.
        # run_helper`), the source of fresh values for its stack probes.
        self.helper_reads: Any = None
        # The instruction behind each named set of undefined x87 condition
        # bits (`region_simulation._X87.undefine`), shared by the paths of one
        # run; it only words refusals.
        self.cc_sites: dict[Term, str] = {} if cc_sites is None else cc_sites
        # Pointers a block string operation left, each with the constant k
        # such that the pointer lies at or above ESP0 + k (`block_end`).
        self.block_floors: dict[Term, int] = {}

    def fork(self) -> FrameModel:
        forked = FrameModel(
            self.facts, self.slots, self.dirty, self.context, self.cc_sites, self.side
        )
        forked.block_floors = dict(self.block_floors)
        return forked

    def block_start(self, state: PathState, pointer: Term, context: str) -> None:
        """Check one pointer of a block string operation (`region_simulation._block_string`).

        A private frame admits no stack address: none exists outside ESP
        there (check 7), so the block, which starts at a non-stack address
        and runs upward, cannot reach a private slot (7b).  A shared frame
        admits a stack address only at a constant offset at or above ESP: the
        block then lies wholly at or above ESP (a9), in the compared memory.
        """
        if not computed_from_stack(pointer):
            return
        if self.facts.private:
            raise EscapeRefusal(f"{context} is a stack address")
        offset = self._floor(pointer)
        require(
            offset is not None,
            f"{context} is a stack address at a variable offset, which a block string operation "
            "is not admitted from",
        )
        current = self._current(state)
        require(
            cast(int, offset) >= current,
            f"{context} ESP0{offset:+d} lies below ESP (ESP0{current:+d})",
        )

    def _floor(self, pointer: Term) -> int | None:
        """The k with the pointer at or above ESP0 + k, when this path knows one.

        ESP0 + k itself, or a recorded block end T (``block_end``) plus a
        constant c with |c| < 2**16: T + c >= ESP0 + k + c, since T + c does
        not wrap (a9: T is one past an accessed byte, and the top 64 KiB of
        the address space is never accessible).
        """
        offset = _esp_offset(pointer)
        if offset is not None:
            return offset
        floors = [
            floor + _signed(difference)
            for known, floor in self.block_floors.items()
            if (difference := const_of(lin_sub(pointer, known))) is not None
            and abs(_signed(difference)) < 1 << 16
        ]
        return max(floors) if floors else None

    def block_end(self, start: Term, end: Term) -> None:
        """Record that a string operation's end pointer lies at or above its start (a9).

        A ``rep movs``/``rep stos`` block or a ``repne scasb`` scan that
        started at a stack address known to be at or above ESP0 + k leaves
        its pointer at or above ESP0 + k: it ran upward over accessed bytes
        without wrapping, or it faulted and nothing follows.  A later block
        may start there (``block_start``), as the second half of an inline
        ``strcpy`` (``rep movsd`` then ``rep movsb``) and an inline
        ``strcat`` (a scan to the end, ``dec edi``, then the copy) do.
        """
        offset = self._floor(start)
        if offset is not None:
            self.block_floors[end] = offset

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
            require(
                self.facts.frame_objects is None,
                f"{self.context}: a stack access at a variable offset from ESP, which a14 "
                "attributes to no frame object (the displacement may fold an index)",
            )
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
        return self._escaping_object(offset, width) is None

    def _escaping_object(self, offset: int, width: int) -> FrameObject | None:
        """The escaping frame object an access at ESP0 + offset lies in (a14), or None.

        An access that lies partly inside an escaping object is refused: its
        bytes would be both memory and a private slot.
        """
        objects = self.facts.frame_objects
        if objects is None:
            return None
        for item in objects.objects:
            if (
                item.start in self.facts.escaping
                and item.start < offset + width
                and offset < item.end
            ):
                require(
                    item.start <= offset and offset + width <= item.end,
                    f"{self.context}: a stack access at ESP0{offset:+d} ({width} bytes) straddles "
                    f"the escaping frame object [ESP0{item.start:+d}, ESP0{item.end:+d}) of "
                    f"{', '.join(item.names)}",
                )
                return item
        return None

    # --- the frame-objects pass (a14) ------------------------------------------------

    def canonical(self, value: Term, context: str, *, register: bool = False) -> Term:
        """A value with every stack address it holds named by its frame object (a14).

        A value computed from ESP0 must be ESP0 + k for a constant k: a pointer
        into the frame object k lies in (or one past the end of one), which
        becomes ``frame_object_atom(object) + (k - start)``.  Its object must
        already escape; when it does not, the pass runs again with it escaping
        (`ObjectEscape`).  A variable or scaled stack address, and a value
        naming ESP0 only through a load from the stack outside the frame, are
        refused.  A k outside every object the donor declares is refused too,
        except in a ``register``: there ESP0 + k stays as it is, a compiler
        temporary's address (``mov ecx, esp`` builds a structure argument in
        the outgoing argument block) that only the function itself uses.
        Every access through it is at a constant offset from ESP0, a private
        slot; storing it (`memory_value`) or starting a block string
        operation from it is refused; and no callee receives it, since a
        call's event names no register and every callee admitted takes no
        argument in one (its decoration, a5, a12).
        """
        if not mentions_stack_address(value):
            return value
        require(
            computed_from_stack(value),
            f"{context}: a value read from the stack above the parameter words reaches a "
            "register or memory",
        )
        offset = _esp_offset(value)
        require(
            offset is not None,
            f"{context}: a stack address that is not ESP0 plus a constant, which a14 attributes "
            "to no frame object",
        )
        objects = cast(FrameObjects, self.facts.frame_objects)
        pointees = objects.pointees(cast(int, offset))
        if register and not pointees:
            return value
        require(
            bool(pointees),
            f"{context}: the stack address ESP0{offset:+d} lies in no local the donor's debug "
            "records declare, so its object has no extent",
        )
        missing = sorted({item.start for item in pointees} - self.facts.escaping)
        if missing:
            raise ObjectEscape(
                f"{context}: the address of the frame object at ESP0{missing[0]:+d} escapes",
                missing,
            )
        own = pointees[0]
        return lin(cast(int, offset) - own.start, [(frame_object_atom(own), 1)])

    def _object_access(self, address: Term, width: int, context: str) -> None:
        """Check an access through a frame object's address (a14).

        The address must name one object, once: at a constant offset the access
        must lie wholly inside it (pointer arithmetic that leaves the object is
        refused); at a variable offset it lies inside by a14, as C's rule
        against out-of-bounds arithmetic places every access of the donor.
        """
        named = _frame_object_terms(address)
        if not named:
            require(
                not computed_from_frame_object(address),
                f"{context}: an address combines a frame object's address other than linearly",
            )
            return
        require(
            len(named) == 1 and named[0][1] == 1,
            f"{context}: an address combines frame objects' addresses other than as one pointer",
        )
        atom = named[0][0]
        if len(address[2]) == 1:
            at = _signed(address[1])
            require(
                at >= 0 and at + width <= atom[2],
                f"{context}: an access at offset {at} ({width} bytes) of the frame object "
                f"[ESP0{atom[1]:+d}, ESP0{atom[1] + atom[2]:+d}) leaves it",
            )

    def memory_address(self, state: PathState, address: Term, width: int) -> Term:
        """The address a memory access uses (a14: an escaping object's bytes by its atom)."""
        if self.facts.frame_objects is None:
            return address
        offset = _esp_offset(address) if address[0] == "lin" else None
        if offset is not None:
            item = self._escaping_object(offset, width)
            if item is not None:
                address = lin(offset - item.start, [(frame_object_atom(item), 1)])
        self._object_access(address, width, self.context)
        return address

    def memory_value(self, value: Term) -> Term:
        """A stored value (a14): its stack address named, a stored pointer inside its object.

        A pointer stored at a constant offset of one past the end of its
        object (a ``va_list`` walked from a parameter) is refused: a callee
        could read beyond the object through it.
        """
        if self.facts.frame_objects is None:
            return value
        value = self.canonical(value, self.context)
        named = _frame_object_terms(value)
        if len(named) == 1 and len(value[2]) == 1 and named[0][1] == 1:
            at, size = _signed(value[1]), named[0][0][2]
            require(
                0 <= at < size,
                f"{self.context}: a pointer at offset {at} of the frame object "
                f"[ESP0{named[0][0][1]:+d}, ESP0{named[0][0][1] + size:+d}) is stored, outside "
                "the object",
            )
        return value

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
        written = sorted(self.dirty & set(range(offset, offset + width)))
        if written and self.side:
            # Written on a path to the join this run started from: partial
            # slot relations may split the joins (`prove_function`).
            raise UncarriedSlot(
                f"{self.context}: a read of the stack slot ESP0{offset:+d} whose value the "
                f"relation does not carry (this version wrote its bytes {written[0]:+d}.. on a "
                "path that reaches here, and the relation keeps no value for it)",
                self.side,
                written,
            )
        require(
            offset >= 0 and not written,
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
        if self.facts.frame_objects is not None:
            value = self.memory_value(value)
        elif self.facts.private and mentions_stack_address(value):
            raise EscapeRefusal(f"{self.context}: a stack address is stored to memory")
        offset = self._offset(state, address)
        if offset is None or not self._owned(offset, width):
            return False
        for key in self._overlapping(offset, width):
            del self.slots[key]
        self.slots[(offset, width)] = value
        # Every byte written since the entry: the parameter words always, and
        # with partial slot relations the locals too (`FrameFacts.tracks`).
        self.dirty |= {byte for byte in range(offset, offset + width) if self.facts.tracks(byte)}
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
    values, links = _solve(equations, count)
    pops = {}
    for site in sites:
        value = values[index[site]]
        if value is None:
            linked = links.get(index[site])
            if linked is None:
                why = "no return or join constrains it"
            else:
                coefficients, total = linked
                terms = " + ".join(
                    ("" if k == 1 else f"{k} * ") + f"pop({sites[column]})"
                    for column, k in coefficients
                )
                why = (
                    f"the only constraint is {terms} = {total} bytes: the calls "
                    f"{', '.join(str(sites[column]) for column, _k in coefficients)} lie on the "
                    "same paths, with no return, join or other known stack depth between them "
                    "to separate their pops"
                )
            raise ByteIdentityError(
                f"{program.context}: the stack relation does not determine the argument pop of "
                f"the indirect call at {site}: {why}"
            )
        pop = value
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


def _solve(
    equations: list[tuple[Fraction, ...]], count: int
) -> tuple[list[Fraction | None], dict[int, tuple[list[tuple[int, Fraction]], Fraction]]]:
    """The unknowns c + sum(k_i n_i) = 0 fix uniquely (None for one they do not), or refuse.

    The second result words a refusal: for each unknown left undetermined,
    one reduced equation that mentions it, as its (unknown, coefficient)
    terms (scaled so the first is 1) and the constant they sum to.
    """
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
    links: dict[int, tuple[list[tuple[int, Fraction]], Fraction]] = {}
    for row, _column in pivots:
        terms = [(other - 1, rows[row][other]) for other in range(1, count + 1) if rows[row][other]]
        if len(terms) < 2:
            continue
        lead = terms[0][1]
        scaled = [(unknown, k / lead) for unknown, k in terms]
        for unknown, _k in terms:
            if values[unknown] is None:
                links.setdefault(unknown, (scaled, -rows[row][0] / lead))
    return values, links


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
        state.frame = FrameModel(frame, context=context, side=side)
        state.fpu.origin = 0
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
        fpu = X87State(
            slots={i: value(("st", i), "x87") for i in range(depth)}, cc=cc, origin=depth
        )
    else:
        fpu = X87State(base=value(("x87",), "x87"), cc=cc, after_call=True)
    slots = {}
    for member in terms:
        if member[0] == side and member[1][0] == "m":
            _tag, offset, width = member[1]
            slots[(offset, width)] = terms[member]
    state = PathState(regs, flags, fpu=fpu, epoch=("mem@", key))
    state.frame = FrameModel(frame, slots, facts.dirty, context, side=side)
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
            if frame.frame_objects is not None:
                # a14: a stack address in a register is named by its frame
                # object before any later instruction reads it.
                for name in GENERAL_REGISTERS:
                    path.regs[name] = path.frame.canonical(
                        path.regs[name], f"{context}: {name} after {offset}", register=True
                    )
            elif frame.private:
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
    if frame.frame_objects is not None and _frame_object_terms(store[0]):
        # A store into a frame object (a14): the object lies in the locals
        # block or the parameter words, dead at the return.
        return True
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


def _undefined_bits(end: PathEnd) -> list[str]:
    """Where the path's conditions read x87 condition bits an instruction left undefined."""
    found: list[str] = []
    stack: list[Any] = [end.state.conditions]
    seen: set[int] = set()
    sites = end.state.frame.cc_sites if end.state.frame is not None else {}
    while stack:
        current = stack.pop()
        if isinstance(current, (tuple, list)):
            if id(current) in seen:
                continue
            seen.add(id(current))
            if isinstance(current, tuple) and len(current) == 3 and current[0] == "x87cc":
                site = sites.get(current[2], "an earlier instruction")
                note = f"{current[1].upper()} as {site} left it"
                if note not in found:
                    found.append(note)
                continue
            stack.extend(current)
    return found


def _undefined_bits_note(left: PathEnd, right: PathEnd) -> str:
    """A refusal's note on branches that read undefined x87 condition bits (a8)."""
    parts = []
    for name, end in (("donor", left), ("replacement", right)):
        found = _undefined_bits(end)
        if found:
            parts.append(f"the {name} branches on {', '.join(sorted(found))}")
    if not parts:
        return ""
    return (
        "; " + " and ".join(parts) + " (Intel leaves C0-C3 undefined after it: such a bit is "
        "related only to the bit the same instruction leaves from the same x87 state, never to "
        "a compare's)"
    )


def _compare_pair(left: PathEnd, right: PathEnd, frame: FrameFacts, context: str) -> None:
    """Check 5 for one consistent pair of paths; a refusal notes undefined x87 bits read (a8)."""
    try:
        _compare_paths(left, right, frame, context)
    except ByteIdentityError as error:
        raise ByteIdentityError(f"{error}{_undefined_bits_note(left, right)}") from error


def _entry_values(value: Any) -> set[int]:
    """The offsets of the stack slots whose entry values (a13) a term names."""
    found: set[int] = set()
    stack, seen = [value], set()
    while stack:
        current = stack.pop()
        if isinstance(current, (tuple, list)) and id(current) not in seen:
            seen.add(id(current))
            if (
                isinstance(current, tuple)
                and len(current) == 3
                and current[0] == "pld"
                and isinstance(current[1], int)
            ):
                found.add(current[1])
            else:
                stack.extend(current)
    return found


def _entry_values_note(left: PathEnd, right: PathEnd) -> str:
    """A refusal's note on a call that passes unwritten slots' entry values at other offsets."""
    for number, (donor_event, image_event) in enumerate(
        zip(left.state.events, right.state.events, strict=False), 1
    ):
        donor, image = _entry_values(donor_event), _entry_values(image_event)
        if donor != image:
            return (
                f"; event {number} passes the entry values of stack slots never written since "
                f"the entry (the donor's {_offsets(donor)}, the replacement's "
                f"{_offsets(image)}): an unwritten slot holds whatever the stack held, so it "
                "equals only the other version's slot at the same offset"
            )
    return ""


def _offsets(found: set[int]) -> str:
    return ", ".join(f"ESP0{offset:+d}" for offset in sorted(found)) or "none"


def _compare_paths(left: PathEnd, right: PathEnd, frame: FrameFacts, context: str) -> None:
    where = f"{context} (the donor's path to {left.at}, the replacement's to {right.at})"
    if left.state.events != right.state.events:
        blocks = any(event[0] == "rep" for end in (left, right) for event in end.state.events)
        raise ByteIdentityError(
            f"{where}: the two versions make different calls"
            + (" or block string moves" if blocks else "")
            + _entry_values_note(left, right)
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
    why = stores_equivalent(stores_left, stores_right, frame.objects)
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
    # Every relation the fixpoint settled, by cut pair and variant
    # (`variant_of`); ``relations`` holds those of the unsplit variant.
    variants: dict[tuple[tuple[int, int], Variant], Relation] = field(default_factory=dict)


# Which bytes of the split (`FrameFacts.split`) a path end has written since
# the entry: the donor's, then the replacement's.
Variant = tuple[frozenset[int], frozenset[int]]
UNSPLIT: Variant = (frozenset(), frozenset())
MAX_VARIANTS = 16


def variant_of(frame: FrameFacts, left: SideFacts, right: SideFacts) -> Variant:
    """The variant of the relation a pair of path ends reaches a join in.

    The written bytes are exact facts of each path (``SideFacts.dirty``: a
    byte outside it is not written since the entry), so every pair of paths
    lies in exactly one variant, and each variant is a relation of its own.
    """
    if not frame.split:
        return UNSPLIT
    return (
        frozenset(byte for byte in left.dirty if ("D", byte) in frame.split),
        frozenset(byte for byte in right.dirty if ("P", byte) in frame.split),
    )


def validate_function(
    donor: Program,
    image: Program,
    frame: FrameFacts,
    x87_returns: Mapping[str, int],
    context: str,
) -> ValidationProof:
    """Checks 4-6: pair the cut points, settle the relations, prove every path pair.

    Each program carries its verified helper bodies (``Program.helpers``).
    With a split frame (`FrameFacts.split`) each cut pair holds one relation
    per variant (`variant_of`).  A refusal to read a slot whose class a join
    lost (`UncarriedSlot`) names the slots whose missing writes lost it.
    """
    # For each (version, byte) of a slot whose class a join lost: the slots
    # that class held which were unwritten on another path into the join.
    losses: dict[tuple[str, int], set[tuple[str, int]]] = {}
    try:
        return _settle(donor, image, frame, x87_returns, context, losses)
    except UncarriedSlot as uncarried:
        uncarried.causes = frozenset(
            cause for byte in uncarried.offsets for cause in losses.get((uncarried.side, byte), ())
        )
        raise


def _record_losses(
    frame: FrameFacts,
    old: Relation,
    established: Relation,
    new: Relation,
    losses: dict[tuple[str, int], set[tuple[str, int]]],
) -> None:
    """Note the slots a meet lost a class over because another path left them unwritten.

    A class of one relation that no class of the meet keeps whole lost a
    member.  Each of its slots whose bytes the other relation's paths have not
    written (some byte outside that side's ``dirty``) is a cause: splitting
    the joins on those bytes keeps the paths that wrote them apart.  Only the
    bytes ``dirty`` tracks count (`FrameFacts.tracks`).
    """
    kept = {member: cls.members for cls in new.classes for member in cls.members}
    for relation, other in ((old, established), (established, old)):
        for cls in relation.classes:
            if any(not cls.members <= kept.get(member, frozenset()) for member in cls.members):
                causes = {
                    (side, byte)
                    for side, location in cls.members
                    if location[0] == "m"
                    for byte in range(location[1], location[1] + location[2])
                    if frame.tracks(byte) and byte not in other.side(side).dirty
                }
                if not causes:
                    continue
                for side, location in cls.members:
                    if location[0] == "m":
                        for byte in range(location[1], location[1] + location[2]):
                            losses.setdefault((side, byte), set()).update(causes)


def _settle(
    donor: Program,
    image: Program,
    frame: FrameFacts,
    x87_returns: Mapping[str, int],
    context: str,
    losses: dict[tuple[str, int], set[tuple[str, int]]],
) -> ValidationProof:
    """The fixpoint and the final pass of `validate_function`."""
    Key = tuple[tuple[int, int], Variant]
    relations: dict[Key, Relation | None] = {((0, 0), UNSPLIT): None}
    pair_of_donor = {0: 0}
    pair_of_image = {0: 0}
    queue: list[Key] = [((0, 0), UNSPLIT)]
    visits: Counter[Key] = Counter()

    def run(node: Key) -> list[tuple[PathEnd, PathEnd]]:
        key, variant = node
        relation = relations[node]
        here = f"{context} from ({key[0]}, {key[1]})" + _variant_note(variant)
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
            f"{y}, but they are paired with {pair_of_donor.get(x)} and {pair_of_image.get(y)})"
            + _undefined_bits_note(left, right),
        )
        pair_of_donor[x] = y
        pair_of_image[y] = x
        return (x, y)

    while queue:
        node = queue.pop(0)
        visits[node] += 1
        require(
            visits[node] <= MAX_VISITS,
            f"{context}: the relation at ({node[0][0]}, {node[0][1]}) does not settle",
        )
        for left, right in run(node):
            if left.kind == "ret":
                continue
            target = pair(left, right, f"{context} from ({node[0][0]}, {node[0][1]})")
            require(target != (0, 0), f"{context}: a branch targets the function's entry")
            left_facts, right_facts = cast(SideFacts, left.facts), cast(SideFacts, right.facts)
            established = establish(left.locations, right.locations, left_facts, right_facts)
            reached = (target, variant_of(frame, left_facts, right_facts))
            old = relations.get(reached)
            new = (
                established
                if reached not in relations
                else meet(cast(Relation, old), established, f"{context} at {target}")
            )
            if old is not None:
                _record_losses(frame, old, established, new, losses)
            if reached not in relations:
                require(
                    sum(1 for item in relations if item[0] == target) < MAX_VARIANTS,
                    f"{context}: the relation at {target} splits into more than {MAX_VARIANTS} "
                    "variants, so which paths write its split slots is not decided",
                )
            if reached not in relations or new != old:
                relations[reached] = new
                if reached not in queue:
                    queue.append(reached)
    # The final pass under the settled relations.
    path_pairs = 0
    returns = 0
    donor_paths = 0
    image_paths = 0
    for node in sorted(relations, key=_node_order):
        consistent = run(node)
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
            left_facts, right_facts = cast(SideFacts, left.facts), cast(SideFacts, right.facts)
            established = establish(left.locations, right.locations, left_facts, right_facts)
            reached = (target, variant_of(frame, left_facts, right_facts))
            require(
                reached in relations,
                f"{context}: the final pass reaches a variant of the relation at {target} the "
                "fixpoint did not settle",
            )
            why = implies(established, cast(Relation, relations[reached]))
            require(
                why is None,
                f"{context}: the path pair from ({node[0][0]}, {node[0][1]}) to {target} breaks "
                f"the relation there: {why}",
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
        {
            key: value
            for (key, variant), value in relations.items()
            if value is not None and variant == UNSPLIT
        },
        (donor_paths, image_paths),
        path_pairs,
        returns,
        {node: value for node, value in relations.items() if value is not None},
    )


def _node_order(node: tuple[tuple[int, int], Variant]) -> tuple[Any, ...]:
    key, (donor_bytes, image_bytes) = node
    return (key, sorted(donor_bytes), sorted(image_bytes))


def _variant_note(variant: Variant) -> str:
    """A run's context: the variant of its relation, when the relation is split."""
    if variant == UNSPLIT:
        return ""
    parts = [
        f"the {name} has written {_byte_ranges(written)}"
        for name, written in (("donor", variant[0]), ("replacement", variant[1]))
        if written
    ]
    return f" [the variant where {' and '.join(parts) or 'no split byte is written'}]"


def _byte_ranges(offsets: Iterable[int]) -> str:
    """Stack bytes as ESP0 ranges: ``ESP0-8..-5``."""
    ranges: list[list[int]] = []
    for offset in sorted(offsets):
        if ranges and ranges[-1][1] == offset - 1:
            ranges[-1][1] = offset
        else:
            ranges.append([offset, offset])
    return ", ".join(
        f"ESP0{start:+d}" if start == end else f"ESP0{start:+d}..{end:+d}" for start, end in ranges
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
    objects: ObjectModel | None = None,
    frame_objects: FrameObjects | None = None,
    partial_slots: bool = False,
) -> ValidationProof:
    """Checks 2 and 4-7: a private frame when one is given and no stack address escapes.

    A refusal of the private frame because a stack address escapes falls back
    to the shared frame; any other refusal stands.  ``helpers`` maps every
    compiler helper either version calls to its verified body.  ``objects``,
    the object model of a10 (its stack end is replaced by the frame's E),
    runs the proof's equivalences pass (`region_simulation._equivalences`);
    None runs the first pass.
    ``frame_objects`` (with ``objects`` and the private frame) runs the
    frame-objects pass (a14) instead: the private frame with every escaping
    frame object's bytes as memory.  It starts with no object escaping and
    runs again with each object whose address a run finds escaping
    (`ObjectEscape`), until a run needs no more; there is no shared-frame
    fallback.
    ``partial_slots`` relates a private slot at a join only on the paths
    that wrote it: when a run reads a slot it wrote on only some paths to the
    join it started from (`UncarriedSlot`), the run is repeated with those
    bytes splitting every join (`FrameFacts.split`), until a run needs no
    more.  Without it that read is refused.
    """

    def programs() -> tuple[Program, Program]:
        return (
            Program(donor_code, donor_relocations, "D", f"{context} donor", helpers),
            Program(image_code, image_relocations, "P", f"{context} replacement", helpers),
        )

    donor, image = programs()

    def validate(facts: FrameFacts, note: str) -> ValidationProof:
        # The private frame, split wherever a run reads a slot written on only
        # some paths (partial slot relations); each run starts afresh.
        nonlocal donor, image
        split: frozenset[tuple[str, int]] = frozenset()
        while True:
            try:
                return validate_function(
                    donor,
                    image,
                    replace(facts, split=split, partial=partial_slots),
                    x87_returns,
                    f"{context}{note}",
                )
            except UncarriedSlot as uncarried:
                if not partial_slots:
                    raise
                grown = split | uncarried.causes
                require(
                    grown != split,
                    f"{uncarried}; partial slot relations do not carry it: "
                    + (
                        "every slot whose missing write on a path into a join lost its class "
                        "already splits the joins, so the paths that wrote it leave values "
                        "the relation does not keep"
                        if uncarried.causes
                        else "no path into a join that lost its class left one of the class's "
                        "slots unwritten, so the paths that wrote it leave values the relation "
                        "does not keep"
                    ),
                )
                split = grown
                donor, image = programs()

    params_end = 4 if private_frame is None else private_frame.params_end
    equivalences = objects is not None
    if objects is not None:
        objects = replace(objects, stack_end=params_end)
        if private_frame is not None:
            private_frame = replace(private_frame, objects=objects, equivalences=True)
    shared = FrameFacts(False, params_end=params_end, objects=objects, equivalences=equivalences)
    if frame_objects is not None:
        require(
            private_frame is not None and objects is not None,
            f"{context}: the frame-objects pass needs the donor's FPO frame and the object model",
        )
        frame = cast(FrameFacts, private_frame)
        require(
            locals_block_first(donor, frame.base),
            f"{context}: the frame-objects pass needs the donor to allocate its locals block first",
        )
        # The FPO record's locals block must hold every object below ESP0.
        require(
            all(item.start >= frame.base for item in frame_objects.objects),
            f"{context}: a frame object lies below the locals block",
        )
        escaping: frozenset[int] = frozenset()
        for _ in range(len(frame_objects.objects) + 1):
            facts = replace(frame, frame_objects=frame_objects, escaping=escaping)
            try:
                return validate(facts, " (frame objects)")
            except ObjectEscape as escape:
                grown = escaping | escape.starts
                require(grown != escaping, f"{context}: {escape}, and it already escapes")
                escaping = grown
                donor, image = programs()
        raise ByteIdentityError(f"{context}: the escaping frame objects do not settle")
    escaped = False
    if private_frame is not None and locals_block_first(donor, private_frame.base):
        try:
            return validate(private_frame, " (private frame)")
        except EscapeRefusal:
            donor, image = programs()
            escaped = True
    try:
        return validate_function(donor, image, shared, x87_returns, f"{context} (shared frame)")
    except ByteIdentityError as error:
        # The shared frame was used because a stack address escapes the
        # private one: the case the frame-objects pass (a14) is for.
        error.escaped = escaped  # type: ignore[attr-defined]
        raise


def _x87_case_proofs(
    items: list[dict[str, Any]],
    successors: list[list[int]],
    entries: list[int],
    code: bytes,
    view: Mapping[int, Any],
    prove: Any,
) -> dict[str, Any]:
    """Check 5f's x87 return counts: the proof's pinned summary.

    First the proof under the counts the donor's solver determines, without
    an import slot's (exactly the proof records made before the case split
    pin).  Only when that refuses: once for every case of
    `region_x87.x87_return_cases`, each with every count it determines, an
    import slot's included; every case must prove, and the summary then pins
    each case and its proof.  Each is sound alone: a count left out of a
    proof makes the x87 stack after that call unknown.
    """
    solution = x87_stack_solution(items, successors, entries, code, view)
    determined = {} if solution is None else solution[1]
    plain = {s: n for s, n in determined.items() if not s.startswith("__imp_")}
    try:
        return proof_summary(prove(plain, ""))
    except ByteIdentityError:
        cases = x87_return_cases(items, successors, entries, code, view) or [{}]
        if cases == [plain]:
            raise
    varying = sorted(
        symbol
        for symbol in {name for case in cases for name in case}
        if len({case.get(symbol) for case in cases}) > 1
    )
    proofs = [prove(case, f" ({_case_note(case, varying)})" if varying else "") for case in cases]
    summary = proof_summary(proofs[0])
    if len(proofs) > 1:
        summary["x87_return_cases"] = [
            {
                "x87_returns": [[symbol, case.get(symbol)] for symbol in varying],
                "proof": proof_summary(case_proof),
            }
            for case, case_proof in zip(cases, proofs, strict=True)
        ]
    return summary


def _case_note(case: Mapping[str, int], symbols: Iterable[str]) -> str:
    """The x87 return counts one case of check 5f assumes, for a refusal's context."""
    return "the case where " + ", ".join(
        f"{symbol} returns {case.get(symbol, 'an undetermined number of')} x87 values"
        for symbol in symbols
    )


def proof_summary(proof: ValidationProof) -> dict[str, Any]:
    """The pinned measurements of a proof (check 8)."""
    summary: dict[str, Any] = {
        "frame": "private" if proof.frame.private else "shared",
        "frame_base": proof.frame.base if proof.frame.private else None,
        "params_end": proof.frame.params_end,
        "cut_pairs": [[left, right] for left, right in sorted(proof.pairs.items())],
        "donor_paths": proof.path_counts[0],
        "replacement_paths": proof.path_counts[1],
        "path_pairs": proof.path_pairs,
        "returning_pairs": proof.returns,
        "related_locations": sum(
            len(cls.members) for relation in proof.variants.values() for cls in relation.classes
        ),
    }
    if proof.frame.split:
        # Only a proof that split its joins pins the split bytes and its
        # variants, so earlier records keep their pins.
        summary["partial_slots"] = [[side, offset] for side, offset in sorted(proof.frame.split)]
        summary["relation_variants"] = len(proof.variants)
    objects = proof.frame.frame_objects
    if objects is not None:
        # Only a frame-objects proof pins its escaping objects and a14.
        summary["frame_objects"] = [
            item.pin() for item in objects.objects if item.start in proof.frame.escaping
        ]
        summary["assumptions"] = ["a14"]
    return summary


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
    donor_type_server: bytes | None = None,
) -> FunctionValidationMeasure:
    """Checks 1-7 and 9 on a donor object and a declaration; the measured pins of check 8.

    ``spec`` needs the replacement, its relocations and debug end, and the
    procedure size and fill alignment (both checked against the donor).
    ``helper_library`` is the authenticated toolchain library the bodies of
    the compiler helpers the donor calls are read from (check 2).
    ``donor_type_server`` is the PDB the donor's compile wrote its types to
    (``/Zi``), which only the frame-objects pass reads (a14,
    `frame_objects.object_type_records`).
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
    objects = object_model(donor, rows, 4 if private_frame is None else private_frame.params_end)
    view = relocation_symbol_map(rows)
    items, successors, entries = ia32_relational_flow_walk(
        donor_body[:proc], view, f"{label} donor flow", None, frozenset()
    )

    # Whether partial slot relations run, and whether a run without them
    # refused a slot written on only some paths (`UncarriedSlot`).
    partial = {"on": False, "needed": False}

    def summary(
        model: ObjectModel | None, tag: str, frame_objects: FrameObjects | None = None
    ) -> dict[str, Any]:
        tag += " (partial slots)" if partial["on"] else ""

        def prove_case(counts: Mapping[str, int], note: str) -> ValidationProof:
            try:
                return prove_function(
                    donor_body[:proc],
                    donor_targets,
                    code,
                    image_targets,
                    counts,
                    f"{label} proof{tag}{note}",
                    private_frame=private_frame,
                    helpers=helpers,
                    objects=model,
                    frame_objects=frame_objects,
                    partial_slots=partial["on"],
                )
            except UncarriedSlot:
                partial["needed"] = True
                raise

        return _x87_case_proofs(items, successors, entries, donor_body[:proc], view, prove_case)

    def frame_objects_pass(earlier: ByteIdentityError) -> dict[str, Any]:
        # Only when every earlier pass refuses because a stack address
        # escapes, and only in an FPO frame: the frame-objects pass (a14),
        # whose summary pins its escaping objects and the assumption.  A
        # record made by an earlier pass never needs it.
        frame = cast(FrameFacts, private_frame)
        try:
            frame_objects = donor_frame_objects(
                donor,
                dp,
                donor_type_server,
                base=frame.base,
                params_end=frame.params_end,
                context=label,
            )
        except ByteIdentityError as missing:
            raise ByteIdentityError(
                f"{earlier}; the frame-objects pass (a14) cannot run: {missing}"
            ) from earlier
        if not locals_block_first(
            Program(donor_body[:proc], donor_targets, "D", label, helpers), frame.base
        ):
            raise ByteIdentityError(
                f"{earlier}; the frame-objects pass (a14) cannot run: the donor does not allocate "
                "its locals block first"
            ) from earlier
        return {
            **summary(objects, " (frame-objects pass)", frame_objects=frame_objects),
            "equivalences": True,
        }

    # The first pass is the proof every record made before the equivalences
    # pass pins; only when it refuses does the second run, under a10 and the
    # normal forms of `region_simulation._equivalences`, and its summary
    # then says so.  Each pass is sound alone.
    def passes() -> dict[str, Any]:
        try:
            return summary(None, "")
        except ByteIdentityError:
            try:
                return {**summary(objects, " (equivalences pass)"), "equivalences": True}
            except ByteIdentityError as earlier:
                if private_frame is None or not getattr(earlier, "escaped", False):
                    raise
                return frame_objects_pass(earlier)

    try:
        proof_summary_pin = passes()
    except ByteIdentityError:
        # Only when every pass refuses, and some run refused a private slot
        # written on only some paths to a join: every pass again, with
        # partial slot relations.  A record made without them never needs
        # them, and one that does pins its split bytes (`proof_summary`).
        if not partial["needed"]:
            raise
        partial["on"] = True
        proof_summary_pin = passes()
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
        "expected_proof": proof_summary_pin,
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


def produce_function_validation_candidate(
    seed_bytes: bytes,
    donor_bytes: bytes,
    function: dict[str, Any],
    helper_library: HelperLibrary | None = None,
    donor_type_server: bytes | None = None,
) -> tuple[bytes, dict[str, Any]]:
    """Produce the translation-validated replacement of a fresh donor body (checks 1-9).

    ``helper_library`` is the authenticated toolchain library, needed when
    the donor calls a compiler helper.  ``donor_type_server`` is the PDB the
    donor's compile wrote, needed only by a record of the frame-objects pass
    (a14).
    """
    label = "function-validation"
    seats = open_candidate_seats(seed_bytes, donor_bytes, function, FUNCTION_VALIDATION_RECIPE)
    mangled, spec = seats.mangled, seats.spec
    pin_candidate_bodies(seats, function, FUNCTION_VALIDATION_RECIPE)
    require(set(spec) <= _SPEC_FIELDS, f"{label} declaration names an unknown field")
    measured = measure_function_validation(
        donor_bytes, mangled, spec, seats.expected_closure, helper_library, donor_type_server
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
    require(
        [(row["offset"], row["target"], row["type"]) for row in detailed_relocations(checked, cp)]
        == [(row["offset"], row["target"], row["type"]) for row in measured.rows],
        f"{label} composed relocation table is not the proved reseat",
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
    "validate_function",
    "validate_replacement",
]
