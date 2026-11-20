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
calls in the same order on both sides.  A table read is a branch like any
other: the concrete index is one constant i, and the path of index i (and
only paths whose indexes may equal i) is enabled on each side.  A
recursive call names the function itself: by induction on the depth of
recursion, an inner call of D and the same inner call of I (made with the
same arguments from the same memory, check 5a) both return with the same
returned state and memory outside the callee's dead stack, or neither
returns, which is exactly what a call event assumes of its callee; under
a1 the caller never reads the callee's dead stack.

Checks (each is a refusal):

1. Shape.  D's code is [0, c) for the declared code end c and its data
   tail [c, L_D); P's code is the declared encodings and its tail the
   declared ``replacement_tail``.  A tail is MSVC 5.0 alignment fill up to
   its first switch table, then switch tables, each extending to the next
   table's base or the procedure's end: a jump table is wholly 4-byte
   relocated fields naming offsets of the code, an index table holds no
   relocated field, and every relocated field of the tail is some jump
   table's entry (`Program._switches`).  Every relocated field of the code
   that names an offset of the function is the base of a table read
   (check 2); any other (a label's address taken as data) is refused.  A
   symbol of the function's section other than the function, its section
   and the ``.bf``/``.lf``/``.ef`` markers is a *label*; the declaration
   gives each label's place in P (``replacement_labels``), inside P's
   procedure.  A closure record naming an interior offset must be a
   CodeView S_LABEL32 record (a C ``goto`` label) or S_LDATA32_ST record
   (MSVC 5.0's nameless record for a switch table) of ``.debug$S``, whose
   offset and segment fields relocate to a label: debug metadata, never an
   entry (`debug_label_values`); every other one (an EH funclet head, say)
   is refused as an external entry.  No other symbol, closure record or
   debug range names an offset other than the entry and end; no branch
   targets offset 0.  P decodes, instruction by instruction, to exactly
   the declared encodings.  When an S_LABEL32 label lies at a cut point
   the proof pairs, its declared place is the paired point.
2. Closed set.  Every reachable instruction of both is in the simulator's
   closed set or is ``ret``/``ret imm16``; every branch targets an
   instruction of its own program; there is no indirect transfer but a
   switch table read (below).  A call
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

   Switch tables.  ``jmp [r*4 + T]`` (``FF /4`` with a scaled-index SIB and
   no base) and ``mov r8, [r + X]`` (``8A /r``, disp32), whose displacement
   is a relocated field naming a table of the tail, are table reads
   (`Switch`, `_dispatch`).  The index register holds a term v.  If v is a
   constant, or an earlier read on the path fixed it, the read takes that
   one entry, which must lie in the table.  Otherwise the path's conditions
   must bound it: ``not (N <u v)`` (the fall-through of ``cmp v, N; ja``)
   or ``v <u N + 1`` (``jb``), each a fact of the path, with N below the
   table's size (`switch_bound`); a read with no such bound is refused.
   The read is then a multi-way branch into N + 1 paths, path i holding the
   fact ``("case", v, i)``; `region_simulation.contradictory` knows two such
   facts for one v and different constants contradict, so a donor path and
   a replacement path are compared exactly when their indexes may be equal.
   Path i of a jump table jumps to entry i's target; path i of an index
   table writes byte i of the table, an exact constant, to its register.
   The tables are the function's own read-only code, so the reads are not
   in the footprint.  The pairing of the two tables is therefore not
   declared: the paths of index i of both versions reach paired cut
   points with related states (checks 4-6), or the proof refuses; so the
   two bound checks agree wherever both versions could take the table, and
   an index table must agree with the other version's dispatch value by
   value.  Every entry must be read on some path (check 3).

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
   does (check 7).  The record pins the library, its digest, the member and
   the body's digest (check 8).

   A helper body may have relocated fields (`toolchain_helpers`): a DIR32
   field is a data symbol's address, named as the linker resolves it (an
   external by its name, which is the caller's own read of it too; a static
   qualified by its member), so the helper's reads and writes of globals
   (``__isctype``'s ``__pctype`` table) are loads and stores of the shared
   memory like the caller's own, the same in both versions because the body
   is the same; a REL32 field of a call or jump names another compiler
   helper, which the library resolves too, transitively within bounds (at
   most eight bodies, four calls deep), and the run enters its body (a
   nested call pushes a fresh return address, a tail jump continues there).
   A run that reaches a call to anything else -- a C function, an import,
   a helper beyond the bounds -- reaches the environment and is refused.
   The run still does not fork; besides constants and the path's facts, a
   branch is decided when the compared values' terms bound them
   (`region_simulation.interval_truth`: a zero-extended byte plus one lies
   in [1, 256], so ``__isctype``'s ``cmp eax, 0x100; ja`` is not taken for
   a character its caller zero-extends).  A helper call whose effect on ESP
   the body does not show in isolation (it branches on its stack argument)
   is an unknown of the stack walk, solved like an indirect call's pop, and
   every run of it must change ESP by that solution.  The record pins the
   digest of the body's relocated fields and of every body its closure
   holds.  ``__CIacos`` is still refused: its body branches on its operand
   (the exponent test of ``__checkTOS_withFB``), and the paths that branch
   leads to reach the CRT's error handler (``__startOneArgErrorHandling``,
   then ``__87except``: a switch table, ``__raise_exc``, the replaceable
   ``__matherr`` hook, ``__set_errno``), the environment.  A call to a
   helper is never an event: a ``__name`` decoration fixes no convention,
   and an event would need one -- the registers the body reads, those it
   keeps, its pop and its x87 effect -- proved on every path of the body;
   across a call the body makes, keeping a saved register needs the callee
   not to write its slot, which a frame that passes a stack address (as
   ``__isctype``'s slow path does) cannot show without object extents.

   Calls through a pointer.  ``call r/m32`` (``FF /2``) other than ``call
   [abs32]`` -- a register (``call eax``), a COM vtable's slot, a structure
   field, an argument -- is an event named like a direct call's, with its
   callee the pointer's term (a register's term, or the word loaded from the
   operand) and the bytes it pops: two versions make the same indirect calls
   exactly when their pointers are equal terms (for a load: the same address
   read from the same memory), in the same order, with the same arguments.
   A pointer that is a code address of this function (``CODE_ENTRY`` plus an
   offset) is refused.  After it EAX, ECX and EDX are the call's results,
   EBX, ESI, EDI and EBP are preserved (a5 for a COM method, a12 for any
   other pointer), memory is the call's result and no x87 instruction may
   follow.  The pop is determined per version (`indirect_call_pops`): the
   walk of its code gives ESP at every instruction as a constant plus the
   unknown pops, equal wherever edges meet and ESP0 at every return; every
   pop must be fixed uniquely, a multiple of four, and it is part of the
   event's name, so versions that disagree make different calls.  Two
   calls on every path between the same points fix only the sum of their
   pops.  The argument pushes then separate them (a11,
   `argument_push_equations`): for a call whose every path back reaches the
   instruction after a previous call p (or after p's caller cleanup, ``add
   esp, n`` or ``pop r`` straight after it) without another call, through
   code that changes ESP only by ``push``, ESP after the call equals ESP
   there -- the call pops exactly the words pushed since p returned.  That
   holds when no word pushed in between belongs to another call and none
   of the call's arguments precedes p, and both fail only for a call made
   while another call's arguments are evaluated, whose value then reaches
   them; so the call's and every p's results (EAX, ECX, EDX, the flags, an
   x87 value) must be dead before the next call (`results_dead`), and at
   the call none of the words its pop counts may hold a saved register's
   entry value (a lazy ``push esi`` is not an argument).  The equations
   join the walk's; a contradiction refuses the pushes, and a pop still not
   fixed is refused with its one equation and why the pushes did not
   apply.  Proofs whose pops the walk alone fixes are unchanged.
3. Relocations.  D's relocated fields are 32-bit `DIR32` fields, a call's
   REL32 field naming a symbol outside the function's own section or the
   function itself (a recursive call: a call event naming the function's
   symbol, below), or DIR32 fields naming an offset of the function (check
   1), each resolved to that offset: its label's place plus its inline
   addend (`donor_fields`).  P's field taking a record of the label at
   donor place x resolves to the label's declared place in P plus P's own
   inline addend (`replacement_internal`): exactly what the installed
   object links to, since the install keeps the donor's records, moves each
   label symbol to its declared place and keeps P's bytes as the addends.  P
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
      entry value -- and, in the equivalences pass, a word of the locals
      block [B, ESP0) this version has not written, which holds its entry
      value too (a13); any other read is refused;
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
   it.  A proof the equivalences pass made (below) pins ``equivalences``,
   one the entry-values pass made ``entry_values`` too.
9. Install.  The image is P followed by MSVC 5.0's alignment fill; the
   donor object is re-seated around it (`rewriting_region_resize.
   resized_donor_object`: relocation offsets through the pairing, every
   line row to the image's entry, the FPO and CodeView sizes and the COFF
   lengths), the procedure size is P's code and tail, each label symbol
   moves to its declared place (with the CodeView label and switch-table
   records that name it), the CodeView debug range is [0, the declared end]
   within P (debug metadata only, which no check relies on), and the
   same-slot resize delegate installs it.  The delegate moves a compiler
   local (``$L<n>``) a relocation names to the derived donor's place; a C
   ``goto`` label's symbol (not a compiler local) keeps the seed's place in
   the installed object, which changes only the debug record, never a
   linked byte.

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
(a11) Argument pushes, for a call whose pop the stack walk leaves open
(check 2): the donor -- compiled C -- pushes a call's arguments after the
previous call returns, and every word it pushes between one call's return
(and that call's caller cleanup) and the next call is an argument of the
next call.  MSVC 5.0 evaluates a call's arguments right to left and pushes
each as it is evaluated, immediately before the call; a word pushed for a
later call can precede an earlier call only when the earlier call is made
while the later call's arguments are evaluated -- a nested call -- and a
call nested in an argument passes its value to that argument, which the
checks refuse wherever the value is in a register or an x87 register
(`results_dead`).  What a11 assumes is the rest: that no argument of the
donor discards a nested call's value (the comma operator) or receives it
only through memory (a structure returned through a hidden pointer and
copied from the caller's temporary).  It is a statement about the
caller's code, which both versions' bytes show, not about the callee.
(a12) A function reached through a pointer that is not a COM vtable's slot
(a structure field, a variable, an argument) is a C function: it takes no
argument in a register and keeps EBX, ESI, EDI and EBP, as ``__cdecl`` and
``__stdcall`` do; MSVC 5.0 C passes register arguments only to
``__fastcall`` functions, whose pointer type must say so.  Its pop is
determined as a vtable call's is.  (a13) Entry values: both versions run
from one machine state, the stack below ESP0 included, so a byte of the
locals block [B, ESP0) holds the same entry value in both until a version
writes it; no callee writes it (a2: every call is made with ESP at or below
B, and a callee writes only below its ESP and its arguments), an inlined
helper's stores are the version's own (tracked), and no address that is not
a constant offset from ESP0 can reach it in a private frame (7b).  A read of
such a byte that neither path of this version wrote (an uninitialised
local, C's undefined behaviour, compiled to a read of its slot) is the
entry value ``("pld", k, width)``, equal in the two versions exactly when
they read the same slot.  Below B a callee's frame may have overwritten the
entry value, so such a read is still refused.  (a14) Frame objects, for the
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

The entry-values pass.  When the equivalences pass refuses too, a
private frame runs once more with one change: a read of an entry value
(a parameter word or, by a13, a local) is carried as the slot it read
(`FrameModel.load`), which it holds until a store.  So where one path
writes ``p = f(p)`` and keeps it in a register and another reads ``p`` into
the same register, the join relates the slot on both paths, and a later
read of it is the related value (0x4512d0's shape).  Carried slots change
the relations, so a record this pass made pins ``entry_values``; records
of the first two passes keep theirs.

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
    open_candidate_seats,
    pin_candidate_bodies,
    relocation_symbol_map,
    require_pinned_length,
    same_slot_effective,
)
from .coff import _comdat_child, _comdat_child_closure
from .debug import MSVC50_FUNCTION_FILL_BYTE, parse_codeview_symbol_stream, parse_fpo_data
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
    _set,
    _small,
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
from .relational import ia32_relational_flow_walk
from .rewriting_region_resize import (
    CARRIED_DEBUG_RECORDS,
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
    # The entry-values pass (a13): a read of a word's entry value is carried
    # as the slot it reads (`FrameModel.load`).
    entry_values: bool = False
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
        # The bytes' entry value (a13): a parameter word, or -- in the
        # equivalences pass -- a word of the locals block [B, ESP0), neither
        # written by this version since the entry.
        in_locals = self.facts.base <= offset and offset + width <= 0
        if written and self.side:
            # Written on a path to the join this run started from: partial
            # slot relations may split the joins (`prove_function`).
            raise UncarriedSlot(
                f"{self.context}: a read of the stack slot ESP0{offset:+d} whose value the "
                "relation does not carry" + self._unread_reason(offset, width, written, in_locals),
                self.side,
                written,
            )
        require(
            not written and (offset >= 0 or (self.equivalences and in_locals)),
            f"{self.context}: a read of the stack slot ESP0{offset:+d} whose value the relation "
            "does not carry" + self._unread_reason(offset, width, written, in_locals),
        )
        atom = ("pld", offset, width)
        value = lin_atom(atom) if width == 4 else ("b", width * 8, atom)
        if self.facts.entry_values:
            # The slot holds that value until a store: carried as a slot, the
            # relation keeps it where another path wrote the same value.
            self.slots[key] = value
        return value

    def _unread_reason(self, offset: int, width: int, written: list[int], in_locals: bool) -> str:
        """Why a read of an unstored slot has no value (a refusal's note)."""
        if written:
            return (
                f" (this version wrote its bytes {written[0]:+d}.. on a path that reaches here, "
                "and the relation keeps no value for it)"
            )
        if offset < 0 and not in_locals:
            return (
                f" (it lies below the locals block, at or above ESP0{self.facts.base:+d}, where an "
                "earlier callee's frame may have overwritten its entry value)"
            )
        if offset < 0:
            return " (an entry value of the locals block is read only in the equivalences pass)"
        return ""

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
        # in the equivalences pass or with partial slot relations the locals
        # too (a13 reads the entry value only of a byte this version has not
        # written; `FrameFacts.tracks`).
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


# --- switch tables (checks 1 and 2) ----------------------------------------------------

# The alignment fill MSVC 5.0 emits between a function's last instruction and
# the switch tables after it: nop, mov edi,edi, and the lea no-ops.
_ALIGNMENT_FILL = frozenset(
    {
        b"\x90",
        b"\x8b\xff",
        b"\x8d\x49\x00",
        b"\x8d\x64\x24\x00",
        b"\x8d\xa4\x24\x00\x00\x00\x00",
        b"\x8d\x9b\x00\x00\x00\x00",
    }
)
SWITCH_JUMP = "jump"
SWITCH_INDEX = "index"
_REGISTER_NAMES = ("eax", "ecx", "edx", "ebx", "esp", "ebp", "esi", "edi")


@dataclass(frozen=True)
class Tail:
    """One version's data tail and the fields that name its own offsets (check 1).

    ``data`` is the bytes the code is followed by, up to the procedure's end
    (alignment fill, then the switch tables); ``internal`` maps every
    relocated 32-bit field of the code or the tail that names an offset of
    this function to the offset the linked image resolves it to (the
    symbol's place plus the field's inline addend).
    """

    data: bytes = b""
    internal: Mapping[int, int] = field(default_factory=dict)


@dataclass(frozen=True)
class Switch:
    """A table read of the code: ``jmp [r*4 + T]`` or ``mov r8, [r + X]`` (check 2).

    ``register`` is the index register's number, ``field`` the relocated
    displacement naming the table, ``base`` the table's offset in the tail
    and ``size`` its number of entries (4-byte jump-table entries, or the
    bytes of an index table); ``destination`` is an index read's 8-bit
    register.
    """

    kind: str
    register: int
    field: int
    base: int
    size: int
    destination: int = 0


def _switch_form(item: _Instruction, at: int) -> tuple[str, int, int] | None:
    """(kind, index register, destination) when ``item`` reads a table through ``at``."""
    if item.operand16 or item.repeat is not None or item.opcode not in (0xFF, 0x8A):
        return None
    local = at - item.offset
    mod, digit, rm = item.modrm()
    if item.opcode == 0xFF and (mod, digit, rm) == (0, 4, 4):
        sib = item.raw[item.modrm_at + 1]
        index = (sib >> 3) & 7
        if sib >> 6 == 2 and sib & 7 == 5 and index != 4 and local == item.modrm_at + 2:
            return (SWITCH_JUMP, index, 0)
    if item.opcode == 0x8A and mod == 2 and rm != 4 and local == item.modrm_at + 1:
        return (SWITCH_INDEX, rm, digit)
    return None


def _require_alignment_fill(data: bytes, context: str) -> None:
    """The bytes between the code and its first table are MSVC 5.0 alignment fill."""
    offset = 0
    while offset < len(data):
        piece = next(
            (
                form
                for form in sorted(_ALIGNMENT_FILL, key=len, reverse=True)
                if data[offset : offset + len(form)] == form
            ),
            None,
        )
        require(
            piece is not None,
            f"{context}: the bytes between the code and its first switch table are not "
            "MSVC 5.0 alignment fill",
        )
        offset += len(cast(bytes, piece))


def switch_bound(conditions: Iterable[tuple[Term, bool]], value: Term) -> int | None:
    """The least N the path conditions establish for ``value <= N`` (unsigned), else None.

    The fall-through of ``cmp v, N; ja default`` holds ``not (N <u v)``; the
    taken side of ``cmp v, M; jb case`` (or the fall-through of ``jae``)
    holds ``v <u M``.  Each is a fact of the path, so the bound is exact.
    """
    best: int | None = None
    for atom, holds in conditions:
        if not (isinstance(atom, tuple) and len(atom) == 4 and atom[:2] == ("ltu", 32)):
            continue
        left, right = atom[2], atom[3]
        bound: int | None = None
        if not holds and right == value and const_of(left) is not None:
            bound = cast(int, const_of(left))
        elif holds and left == value and const_of(right):
            bound = cast(int, const_of(right)) - 1
        if bound is not None:
            best = bound if best is None else min(best, bound)
    return best


# --- programs and their cut points ---------------------------------------------------


class Program:
    """One version's code: its instructions, static flow and cut points.

    ``helpers`` maps each compiler helper the code calls to its verified body
    (check 2); every indirect call through a vtable slot gets the argument
    pop its stack relation determines (:func:`indirect_call_pops`).  ``tail``
    is the data tail after the code and the fields that name this function's
    own offsets; every such field of the code is a switch table's base
    (:class:`Switch`), and every such field of the tail a jump-table entry.
    """

    def __init__(
        self,
        code: bytes,
        relocations: Mapping[int, RelocationTarget],
        side: str,
        context: str,
        helpers: Mapping[str, HelperCode] | None = None,
        tail: Tail | None = None,
    ) -> None:
        self.code = code
        self.side = side
        self.context = context
        self.relocations = dict(relocations)
        self.helpers = dict(helpers or {})
        self.tail = tail or Tail()
        self.code_end = len(code)
        self.end = self.code_end + len(self.tail.data)
        starts = region_boundaries(code, 0, len(code), context)
        self.instructions = {
            offset: _Instruction(code, offset, self.relocations, context, extended=True)
            for offset in starts
        }
        self.switches = self._switches()
        # The jump-table entries a path has read (check 3).
        self.entries_read: set[int] = set()
        self.successors: dict[int, tuple[int, ...]] = {}
        for offset, item in self.instructions.items():
            self.successors[offset] = self._flow(item)
        self.reachable = self._reach()
        self.cuts = self._cut_points()
        # The indirect calls whose pops a11's argument pushes fixed (set by
        # :func:`indirect_call_pops`).
        self.pushed_pops: frozenset[int] = frozenset()
        # The helper calls whose effect on ESP the stack relation solved.
        self.helper_changes: dict[int, int] = {}
        self.indirect_pops = indirect_call_pops(self)
        for offset, change in self.helper_changes.items():
            self.instructions[offset].helper_stack_change = change
        for offset, pop in self.indirect_pops.items():
            self.instructions[offset].indirect_pop = pop
            self.instructions[offset].pushed_pop = offset in self.pushed_pops

    def _switches(self) -> dict[int, Switch]:
        """Every table read of the code, each table's extent, and the tail's shape (check 1).

        A table extends from its base to the next table's base or the
        procedure's end.  A jump table is wholly 4-byte fields naming this
        function's code; an index table holds no relocated field.  The tail
        before the first table is alignment fill, and every relocated field
        of the tail is an entry of some jump table.
        """
        internal = self.tail.internal
        context = self.context
        require(
            not set(internal) & set(self.relocations),
            f"{context}: a relocated field both names this function and another symbol",
        )
        for at, target in internal.items():
            require(
                at >= 0 and at + 4 <= self.end and 0 <= target < self.end,
                f"{context}: the field at {at} names {target}, outside this function",
            )
        found: dict[int, tuple[str, int, int, int, int]] = {}
        for offset, item in self.instructions.items():
            fields = [at for at in range(offset, offset + item.length) if at in internal]
            if not fields:
                continue
            at = fields[0]
            form = _switch_form(item, at) if len(fields) == 1 else None
            require(
                form is not None,
                f"{item.context}: the relocated field at {at} names this function's offset "
                f"{internal[at]}, and only the base of a switch table (jmp [r*4 + table], "
                "mov r8, [r + table]) is admitted there: a label address taken as data is "
                "outside the closed set",
            )
            kind, register, destination = cast(tuple[str, int, int], form)
            base = internal[at]
            require(
                self.code_end <= base < self.end,
                f"{item.context}: the switch table at {base} does not lie in the data tail "
                f"[{self.code_end}, {self.end})",
            )
            found[offset] = (kind, register, at, base, destination)
        kinds: dict[int, str] = {}
        for kind, _register, _at, base, _destination in found.values():
            require(
                kinds.setdefault(base, kind) == kind,
                f"{context}: the table at {base} is read both as a jump table and as an "
                "index table",
            )
        bases = sorted(kinds)
        limits = dict(zip(bases, [*bases[1:], self.end], strict=False))
        entries: set[int] = set()
        switches = {}
        for offset, (kind, register, at, base, destination) in found.items():
            extent = limits[base] - base
            if kind == SWITCH_JUMP:
                require(
                    extent % 4 == 0
                    and all(base + 4 * k in internal for k in range(extent // 4))
                    and all(internal[base + 4 * k] < self.code_end for k in range(extent // 4)),
                    f"{context}: the jump table at {base} is not {extent // 4} relocated entries "
                    "naming this function's code",
                )
                size = extent // 4
                entries |= {base + 4 * k for k in range(size)}
            else:
                require(
                    not any(base - 3 <= other < base + extent for other in internal),
                    f"{context}: the index table at {base} holds a relocated field",
                )
                size = extent
            switches[offset] = Switch(kind, register, at, base, size, destination)
        stray = sorted(at for at in internal if at >= self.code_end and at not in entries)
        require(
            not stray,
            f"{context}: the data tail's relocated fields at {stray} are no jump table's entries",
        )
        require(
            not self.tail.data or bool(bases),
            f"{context}: the code is followed by a data tail that no switch table reads",
        )
        first = bases[0] if bases else self.end
        _require_alignment_fill(self.tail.data[: first - self.code_end], context)
        return switches

    def is_return(self, item: _Instruction) -> bool:
        return item.opcode in (0xC3, 0xC2) and not item.operand16

    def table(self, switch: Switch) -> list[int]:
        """A jump table's targets, entry by entry."""
        return [self.tail.internal[switch.base + 4 * k] for k in range(switch.size)]

    def _flow(self, item: _Instruction) -> tuple[int, ...]:
        end = item.offset + item.length
        op = item.opcode
        if self.is_return(item):
            return ()
        switch = self.switches.get(item.offset)
        if switch is not None and switch.kind == SWITCH_JUMP:
            return tuple(dict.fromkeys(self.table(switch)))
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


def indirect_call(item: _Instruction) -> bool:
    """Whether an instruction is ``call r/m32`` through a pointer (``FF /2``, not ``[abs32]``).

    A register operand (``call eax``) or a memory operand with a base or index
    register (``call [ecx+0x10]``, a vtable slot or a structure field).  A
    ``call [abs32]`` is an import slot's, whose symbol names the callee.
    """
    if item.opcode != 0xFF or item.operand16:
        return False
    mod, digit, rm = item.modrm()
    return digit == 2 and not (mod == 0 and rm == 5)


vtable_call = indirect_call


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
    if item.offset in program.switches:
        return 0  # a table read writes an 8-bit register or jumps
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
    sites = [offset for offset in program.reachable if indirect_call(program.instructions[offset])]
    # A helper call whose effect on ESP its body does not show in isolation
    # (it branches on an argument the walk does not know) is an unknown too;
    # the proof checks every run of it against the solution (`run_helper`).
    solved_helpers = [
        offset
        for offset in program.reachable
        if _helper_call(program, offset) and not _helper_change_known(program, offset)
    ]
    if not sites and not solved_helpers:
        return {}
    columns = sites + solved_helpers
    index = {site: number for number, site in enumerate(columns)}
    count = len(columns)
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
    undetermined = [site for site in sites if values[index[site]] is None]
    notes: dict[int, str] = {}
    pushed: set[int] = set()
    if undetermined:
        # a11: a call pops exactly the words pushed since the previous call
        # returned, where both versions' code shows that no word pushed in
        # between can belong to another call (`argument_push_equations`).
        extra: list[tuple[Fraction, ...]] = []
        for site in undetermined:
            found = argument_push_equations(program, site, forms, index, count)
            if isinstance(found, str):
                notes[site] = found
            else:
                extra.extend(found)
                pushed.add(site)
        if extra:
            try:
                values, links = _solve(equations + extra, count)
            except ByteIdentityError as error:
                raise ByteIdentityError(
                    f"{program.context}: the argument pushes before the indirect calls at "
                    f"{sorted(pushed)} (a11) contradict the stack relation: {error}"
                ) from error
    for offset in solved_helpers:
        solved = values[index[offset]]
        require(
            solved is not None and solved.denominator == 1,
            f"{program.context}: the stack relation does not determine how the helper call at "
            f"{offset} changes ESP (its body branches on a value the walk does not know)",
        )
        program.helper_changes[offset] = int(cast(Fraction, solved))
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
                    ("" if k == 1 else f"{k} * ") + f"pop({columns[column]})"
                    for column, k in coefficients
                )
                why = (
                    f"the only constraint is {terms} = {total} bytes: the calls "
                    f"{', '.join(str(columns[column]) for column, _k in coefficients)} lie on the "
                    "same paths, with no return, join or other known stack depth between them "
                    "to separate their pops"
                )
                unpushed = [
                    f"{columns[column]}: {notes[columns[column]]}"
                    for column, _k in coefficients
                    if columns[column] in notes
                ]
                if unpushed:
                    why += (
                        "; the argument pushes (a11) do not fix them either ("
                        + "; ".join(unpushed)
                        + ")"
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
    program.pushed_pops = frozenset(pushed)
    return pops


# The pushes a11 counts: push r32, push imm32, push imm8 and push r/m32.
_PUSH_OPCODES = frozenset({*range(0x50, 0x58), 0x68, 0x6A})
MAX_PUSH_REGION = 512
MAX_RESULT_STEPS = 2048


def _is_call(program: Program, item: _Instruction) -> bool:
    """Whether an instruction is a call of any kind (direct, helper, import slot or pointer)."""
    return item.opcode in (0xE8, 0x9A) or (item.opcode == 0xFF and item.modrm()[1] in (2, 3))


def _is_push(item: _Instruction) -> bool:
    return not item.operand16 and (
        item.opcode in _PUSH_OPCODES or (item.opcode == 0xFF and item.modrm()[1] == 6)
    )


def argument_push_equations(
    program: Program,
    site: int,
    forms: Mapping[int, tuple[Fraction, ...]],
    index: Mapping[int, int],
    count: int,
) -> list[tuple[Fraction, ...]] | str:
    """a11's equations for the indirect call at ``site``, or why a11 does not apply there.

    The *push region* of the call is every instruction from which the call is
    reached without passing another call: walking back from the call, each
    path must end just after a call p (the call's *previous call* on that
    path) -- never at the function's entry.  The region must make no call,
    read no switch table, and change ESP only by ``push``, but for p's caller
    cleanup (``add esp, n`` or ``pop r``) straight after p, reached from p
    alone.  Then, for each previous call p, ESP after the call equals ESP
    just after p returned and was cleaned up: the call pops exactly the
    words pushed since (one equation per p, in the walk's forms).

    a11 says those words are this call's arguments and that no argument of
    it was pushed before p.  A word pushed between p and the call belongs to
    a later call only if the call is made while that later call's arguments
    are evaluated, and an argument of the call precedes p only if p is made
    while the call's arguments are evaluated: a nested call, whose value
    then reaches the outer call's arguments.  So the call's and every p's
    results must be dead (`results_dead`): what the callee leaves in EAX,
    ECX, EDX, the flags and the x87 stack is read by nothing -- no store,
    condition, call target or preserved register -- before the next call or
    return.  A pushed word that is a saved register's entry value is checked
    at the call itself (`region_simulation._require_pushed_arguments`).
    """
    predecessors: dict[int, list[int]] = {}
    for offset in program.reachable:
        for target in program.successors[offset]:
            predecessors.setdefault(target, []).append(offset)
    region: set[int] = set()
    previous: set[int] = set()
    stack = [site]
    while stack:
        here = stack.pop()
        for before in predecessors.get(here, []):
            item = program.instructions[before]
            if _is_call(program, item):
                previous.add(before)
                continue
            if before in region:
                continue
            region.add(before)
            if len(region) > MAX_PUSH_REGION:
                return "its push region is too large"
            stack.append(before)
        if here != site and not predecessors.get(here):
            return "a path from the function's entry reaches it without a call before it"
    # Each previous call's caller cleanup: the ``add esp, n`` or ``pop r``
    # run straight after it, before the region's pushes (a cdecl callee's
    # arguments, or an earlier call's whose cleanup MSVC deferred).
    starts: dict[int, int] = {}
    for call in sorted(previous):
        start = call + program.instructions[call].length
        while start in region and _is_cleanup(program.instructions[start]):
            if len(predecessors.get(start, [])) != 1:
                return f"the caller cleanup at {start} is also reached from elsewhere"
            start += program.instructions[start].length
        starts[call] = start
    cleanups = {
        offset
        for call in previous
        for offset in region
        if call + program.instructions[call].length <= offset < starts[call]
    }
    for offset in sorted(region):
        item = program.instructions[offset]
        if offset in program.switches:
            return f"its push region reads a switch table at {offset}"
        if offset in cleanups:
            continue
        try:
            change = _stack_change(program, item, None)
        except ByteIdentityError:
            return (
                f"the instruction at {offset} in its push region changes ESP by an unknown amount"
            )
        if change != (-4 if _is_push(item) else 0):
            return (
                f"the instruction at {offset} in its push region changes ESP other than by a push"
            )
    for call in sorted({site} | previous):
        why = results_dead(program, call)
        if why is not None:
            return why
    equations = []
    for call in sorted(previous):
        after = forms[starts[call]]
        following = list(forms[site])
        following[1 + index[site]] += 1
        equations.append(tuple(a - b for a, b in zip(following, after, strict=True)))
    return equations


def _is_cleanup(item: _Instruction) -> bool:
    """``add esp, imm`` or ``pop r32`` (not ``pop esp``): a caller's argument cleanup."""
    if item.operand16:
        return False
    if 0x58 <= item.opcode <= 0x5F:
        return item.opcode != 0x5C
    return item.opcode in (0x81, 0x83) and item.modrm() == (3, 0, 4)


_KEPT_NAMES = ("ebx", "esi", "edi", "ebp")


def _mentions_result(value: Any, call: int) -> bool:
    """Whether a term mentions a result atom ``("result", call, ...)`` of the call."""
    stack = [value]
    seen: set[int] = set()
    while stack:
        current = stack.pop()
        if isinstance(current, (tuple, list, frozenset, set)):
            if id(current) in seen:
                continue
            seen.add(id(current))
            if isinstance(current, tuple) and current[:2] == ("result", call):
                return True
            stack.extend(item for item in current if not isinstance(item, (str, int)))
    return False


def results_dead(program: Program, call: int) -> str | None:
    """None when nothing reads the call's results before the next call or return, else why.

    A scratch run from the instruction after the call follows every path
    (both ways at every branch) to the next call or ``ret``.  What the callee
    leaves is a result atom: EAX, ECX, EDX, every flag, and the x87 stack
    below what the run pushes (a value returned in ST(0)).  The results are
    dead when no condition, no store (address or value), no block string
    operation, no next call's target and no preserved register (EBX, ESI,
    EDI, EBP) at that point mentions one, and no helper is met with one in a
    register.  A path that meets an instruction twice, or runs past
    MAX_RESULT_STEPS, is refused (a loop without a call), as is a switch
    table or an instruction the simulator refuses.
    """
    item = program.instructions[call]
    start = _scratch_state(None)
    for name in ("eax", "ecx", "edx"):
        start.regs[name] = lin_atom(("result", call, name))
    for name in FLAG_NAMES:
        start.flags[name] = ("result", call, "flag", name)
    start.fpu = X87State(base=("result", call, "x87"))
    start.frame = FrameModel(FrameFacts(False), context=f"{program.context} after {call}")

    def used(value: Any) -> bool:
        return _mentions_result(value, call)

    pending: list[tuple[int, PathState, frozenset[int]]] = [
        (call + item.length, start, frozenset())
    ]
    steps = 0
    undefined = _Undefined(f"{program.side}-results{call}")
    while pending:
        offset, state, seen = pending.pop()
        while True:
            steps += 1
            if steps > MAX_RESULT_STEPS or offset in seen:
                return f"the code after the call at {call} loops at {offset} before another call"
            seen = seen | {offset}
            here = program.instructions.get(offset)
            if here is None:
                return f"the code after the call at {call} leaves the function at {offset}"
            if used([state.stores, state.conditions, state.events]):
                return f"the results of the call at {call} are stored or tested before {offset}"
            if program.is_return(here):
                break
            if _is_call(program, here):
                target: Any = None
                if here.opcode == 0xFF:
                    target = (
                        state.regs[_REGISTER_NAMES[here.modrm()[2]]]
                        if here.modrm()[0] == 3
                        else here.address(state.regs)
                    )
                if _helper_call(program, offset) and used([state.regs, state.fpu.slots]):
                    return f"the results of the call at {call} reach the helper call at {offset}"
                if used([[state.regs[name] for name in _KEPT_NAMES], target]):
                    return (
                        f"the results of the call at {call} are kept in a preserved register or "
                        f"called through at {offset}"
                    )
                break
            if offset in program.switches:
                return f"the code after the call at {call} reads a switch table at {offset}"
            try:
                action, detail = _step(state, here, undefined, None, program.helpers)
            except ByteIdentityError as error:
                return f"the code after the call at {call} is not simulated: {error}"
            if action == "fall":
                offset += here.length
                continue
            if action == "jump":
                offset = detail
                continue
            code_value, target_offset = detail
            decided = condition(code_value, state.flags)
            if not isinstance(decided, bool):
                if used(decided):
                    return f"the results of the call at {call} decide the branch at {offset}"
                pending.append((offset + here.length, state.fork(), seen))
                offset = target_offset
                continue
            offset = target_offset if decided else offset + here.length
        if used([state.stores, state.conditions, state.events]):
            return f"the results of the call at {call} are stored or tested before {offset}"
    return None


def _helper_change_known(program: Program, offset: int) -> bool:
    """Whether the helper call's effect on ESP is its body's alone, as the walk runs it.

    The walk knows EAX only after ``mov eax, imm32`` straight before the call
    (``__chkstk``'s argument); with that, the body must run to its return.
    """
    before = program.instructions.get(offset - 5)
    eax = None
    if (
        before is not None
        and before.opcode == 0xB8
        and not before.operand16
        and offset - 4 not in program.relocations
        and program.successors.get(offset - 5) == (offset,)
    ):
        eax = int.from_bytes(before.raw[before.cursor : before.cursor + 4], "little")
    try:
        _stack_change(program, program.instructions[offset], eax)
    except ByteIdentityError:
        return False
    return True


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
            if offset in program.switches:
                forks = _dispatch(program, offset, path, context)
                for target, other in forks[1:]:
                    pending.append((target, other, False))
                require(
                    len(results) + len(pending) + 1 <= MAX_PATHS,
                    f"{context}: more than {MAX_PATHS} paths leave one cut point",
                )
                offset, path = forks[0]
                continue
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


def _dispatch(
    program: Program, offset: int, path: PathState, context: str
) -> list[tuple[int, PathState]]:
    """The paths a table read leaves on: one per index value the path allows (check 2).

    The index register holds a term v.  When v is a constant, or a dispatch
    earlier on the path fixed it (``("case", v, i)``), there is one path.
    Otherwise the path's conditions must bound it (:func:`switch_bound`):
    v <= N with N below the table's size; the read is then a multi-way
    branch into N + 1 paths, path i holding the fact ``("case", v, i)``.
    `region_simulation.contradictory` knows that two such facts for one v
    and different constants contradict each other, so a pair of paths is
    consistent exactly when their indexes may be equal.  A jump-table read
    jumps to entry i's target; an index-table read writes byte i of the
    table (an exact constant, the tail is read-only code) to its 8-bit
    register and falls through.  Neither touches memory the proof compares
    (the tables lie in this function's own code section).
    """
    item, switch = program.instructions[offset], program.switches[offset]
    value = path.regs[_REGISTER_NAMES[switch.register]]
    where = f"{context}: the switch at {item.offset}"
    constant = const_of(value)
    known = next(
        (
            atom[2]
            for atom, holds in path.conditions
            if holds and isinstance(atom, tuple) and len(atom) == 3 and atom[:2] == ("case", value)
        ),
        None,
    )
    choices: list[tuple[int, tuple[Term, bool] | None]]
    if constant is not None or known is not None:
        index = cast(int, constant if constant is not None else known)
        require(
            index < switch.size,
            f"{where} reads entry {index} of a table of {switch.size}",
        )
        choices = [(index, None)]
    else:
        bound = switch_bound(path.conditions, value)
        require(
            bound is not None,
            f"{where} is not guarded by a bound check: no condition of the path bounds its "
            "index (cmp index, N; ja default)",
        )
        require(
            cast(int, bound) < switch.size,
            f"{where} admits indexes up to {bound}, beyond its table of {switch.size}",
        )
        choices = [(i, (("case", value, i), True)) for i in range(cast(int, bound) + 1)]
    item.consumed.add(switch.field)
    forks = []
    for number, (index, fact) in enumerate(choices):
        state = path if number == len(choices) - 1 else path.fork()
        if fact is not None:
            state.conditions.append(fact)
        if switch.kind == SWITCH_JUMP:
            entry = switch.base + 4 * index
            program.entries_read.add(entry)
            forks.append((program.tail.internal[entry], state))
        else:
            byte = program.tail.data[switch.base - program.code_end + index]
            _set(state, switch.destination, 8, _small(8, byte))
            forks.append((item.offset + item.length, state))
    return forks


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
    switches: tuple[int, int] = (0, 0)
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
        consumed: set[int] = set(program.entries_read)
        for item in program.instructions.values():
            consumed |= item.consumed
        unread = sorted((set(program.relocations) | set(program.tail.internal)) - consumed)
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
        (len(donor.switches), len(image.switches)),
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
    donor_tail: Tail | None = None,
    image_tail: Tail | None = None,
    objects: ObjectModel | None = None,
    entry_values: bool = False,
    frame_objects: FrameObjects | None = None,
    partial_slots: bool = False,
) -> ValidationProof:
    """Checks 2 and 4-7: a private frame when one is given and no stack address escapes.

    A refusal of the private frame because a stack address escapes falls back
    to the shared frame; any other refusal stands.  ``helpers`` maps every
    compiler helper either version calls to its verified body; each tail is
    that version's data tail and the fields naming its own offsets.
    ``objects``, the object model of a10 (its stack end is replaced by the
    frame's E), runs the proof's equivalences pass
    (`region_simulation._equivalences`); None runs the first pass.
    ``entry_values`` (with ``objects``) runs the entry-values pass: a private
    frame carries every entry value it reads as a slot (a13).
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
            Program(donor_code, donor_relocations, "D", f"{context} donor", helpers, donor_tail),
            Program(
                image_code, image_relocations, "P", f"{context} replacement", helpers, image_tail
            ),
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
            private_frame = replace(
                private_frame, objects=objects, equivalences=True, entry_values=entry_values
            )
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
            except ByteIdentityError as error:
                error.private_frame = True  # type: ignore[attr-defined]
                raise
        raise ByteIdentityError(f"{context}: the escaping frame objects do not settle")
    escaped = False
    if private_frame is not None and locals_block_first(donor, private_frame.base):
        try:
            return validate(private_frame, " (private frame)")
        except EscapeRefusal:
            donor, image = programs()
            escaped = True
        except ByteIdentityError as error:
            # The refusal came from the private frame, where the entry-values
            # pass differs (`measure_function_validation`).
            error.private_frame = True  # type: ignore[attr-defined]
            raise
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
    if proof.switches != (0, 0):
        # Only a proof through switch tables pins them, so earlier records keep their pins.
        summary["switch_reads"] = list(proof.switches)
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
        "donor_code_end",
        "replacement_tail",
        "replacement_labels",
    }
)
_SECREL = 0x000B
_SECTION = 0x000A


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


def donor_fields(
    rows: list[dict[str, Any]],
    section_number: int,
    mangled: str,
    limit: int,
    body: bytes,
    context: str,
) -> tuple[dict[int, RelocationTarget], dict[int, int]]:
    """Check 3 on the donor: its symbol fields, and the fields naming its own offsets.

    Each record is an external DIR32 field, a call's REL32 field naming a
    symbol outside the function's section or the function itself (a
    recursive call), or a DIR32 field naming an offset of the function (a
    switch table's base or entry), which the second map resolves to that
    offset: the symbol's place plus the field's inline addend.
    """
    targets: dict[int, RelocationTarget] = {}
    internal: dict[int, int] = {}
    for row in rows:
        offset = row["offset"]
        own = row["target_section"] == section_number
        require(
            row["type"] in (_DIR32, _REL32) and row["width"] == 4 and offset + 4 <= limit,
            f"{context}: the relocation at {offset} is neither a DIR32 field nor a call's "
            "REL32 field",
        )
        if row["type"] == _REL32:
            require(
                not own or (row["target"] == mangled and row["target_value"] == 0),
                f"{context}: the PC-relative field at {offset} names this function's offset "
                f"{row['target_value']}, not the function itself",
            )
            targets[offset] = ("rel32", row["target"])
        elif own:
            addend = int.from_bytes(body[offset : offset + 4], "little", signed=True)
            internal[offset] = row["target_value"] + addend
        else:
            targets[offset] = row["target"]
    return targets, internal


def declared_labels(spec: dict[str, Any], context: str) -> dict[int, int]:
    """The declared place in the replacement of each label of the donor's section."""
    pairs = spec.get("replacement_labels", [])
    require(
        isinstance(pairs, list)
        and all(
            isinstance(pair, list)
            and len(pair) == 2
            and all(type(value) is int and value > 0 for value in pair)
            for pair in pairs
        )
        and [pair[0] for pair in pairs] == sorted({pair[0] for pair in pairs}),
        f"{context}: the replacement labels are not sorted pairs of positive offsets",
    )
    return {donor: image for donor, image in pairs}


def section_label_values(donor: CoffObject, primary: dict[str, Any]) -> frozenset[int]:
    """The interior places the symbols of the function's section name (its labels)."""
    return frozenset(
        item["value"]
        for item in donor.symbols.values()
        if item["section"] == primary["number"]
        and item["name"] not in (".bf", ".lf", ".ef")
        and item["value"] != 0
    )


def debug_label_values(donor: CoffObject, primary: dict[str, Any], context: str) -> frozenset[int]:
    """Check 1: every closure record naming an interior offset is a CodeView label's.

    A C ``goto`` label is a symbol of the function's section named by one
    S_LABEL32 record of its ``.debug$S``, and MSVC 5.0 names each switch
    table by a nameless S_LDATA32_ST record: the record's offset field
    (SECREL) and segment field (SECTION) relocate to the label.  That is
    debug metadata, not an entry: no code or table transfers control through
    it.  Any other closure record naming an interior offset (an EH funclet
    head in ``.xdata$x``, say) is an external entry and is refused.
    """
    number = primary["number"]
    found: set[int] = set()
    for child_name in _comdat_child_closure(donor, primary)[1]:
        child = _comdat_child(donor, primary, child_name)
        rows = [
            row
            for row in detailed_relocations(donor, child)
            if row["target_section"] == number and row["target_value"] != 0
        ]
        if not rows:
            continue
        require(
            child_name == ".debug$S",
            f"{context}: the donor has an external entry besides its own: its {child_name} "
            f"names the offsets {sorted({row['target_value'] for row in rows})}",
        )
        raw = bytes(coff_body(donor, child))
        fields = {
            record["offset"] + CARRIED_DEBUG_RECORDS[record["type"]]: _SECREL
            for record in parse_codeview_symbol_stream(raw, f"{context} debug$S")
            if record["type"] in CARRIED_DEBUG_RECORDS
        }
        fields |= {at + 4: _SECTION for at in list(fields)}
        for row in rows:
            require(
                fields.get(row["offset"]) == row["type"],
                f"{context}: the donor has an external entry besides its own: its .debug$S "
                f"names {row['target_value']} outside a CodeView label or switch-table record",
            )
            found.add(row["target_value"])
    return frozenset(found)


def validate_replacement(
    spec: dict[str, Any],
    rows: list[dict[str, Any]],
    context: str,
    *,
    section_number: int | None = None,
) -> tuple[bytes, list[int], dict[int, RelocationTarget], list[list[int]], int]:
    """The declared replacement: its code, boundaries, relocation map, reseat and debug end.

    The replacement's relocated fields may lie in its declared tail
    (``replacement_tail``); a record naming the function's own section
    (``section_number``) is resolved by :func:`replacement_internal`, not here.
    """
    require_payload_free_declaration(spec, f"{context} declaration")
    encodings = spec["replacement_instructions"]
    require(
        isinstance(encodings, list) and 0 < len(encodings) <= 8192,
        f"{context}: the replacement is not a list of encodings",
    )
    pieces = [_hex_instruction(text, context) for text in encodings]
    code = b"".join(pieces)
    boundaries = [sum(len(piece) for piece in pieces[:k]) for k in range(len(pieces))]
    full = code + replacement_tail(spec, context)
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
        and all(local + 4 <= len(full) for local in locals_)
        and sorted(donors) == sorted(by_offset)
        and len(set(donors)) == len(donors),
        f"{context}: the replacement's relocations are not a sorted bijection onto the donor's",
    )
    targets: dict[int, RelocationTarget] = {}
    reseat = []
    for local, donor in pairs:
        row = by_offset[donor]
        if row["type"] == _DIR32 and row["target_section"] == section_number:
            pass  # a field naming the function's own offset (replacement_internal)
        else:
            targets[local] = ("rel32", row["target"]) if row["type"] == _REL32 else row["target"]
        if local != donor:
            reseat.append([donor, local])
    debug_end = spec["replacement_debug_end"]
    require(
        type(debug_end) is int and 0 <= debug_end <= len(code),
        f"{context}: the declared debug end lies outside the replacement",
    )
    return code, boundaries, targets, sorted(reseat), debug_end


def replacement_tail(spec: dict[str, Any], context: str) -> bytes:
    """The declared data tail after the replacement's code (empty when none is declared)."""
    text = spec.get("replacement_tail", "")
    require(
        isinstance(text, str)
        and len(text) % 2 == 0
        and len(text) <= 2 * 65536
        and all(char in "0123456789abcdef" for char in text),
        f"{context}: the replacement tail is not lowercase hex",
    )
    return bytes.fromhex(text)


def replacement_internal(
    spec: dict[str, Any],
    rows: list[dict[str, Any]],
    full: bytes,
    section_number: int,
    labels: Mapping[int, int],
    context: str,
) -> dict[int, int]:
    """Each replacement field naming the function's own offset, resolved as installed.

    The installed object keeps the donor's records, each label symbol moved
    to its declared place (``labels``), and the replacement's bytes as the
    inline addends; so a field taking a record of the label at donor place
    x names labels[x] plus its own inline addend.
    """
    by_offset = {row["offset"]: row for row in rows}
    internal = {}
    for local, donor in spec["replacement_relocations"]:
        row = by_offset[donor]
        if not (row["type"] == _DIR32 and row["target_section"] == section_number):
            continue
        place = row["target_value"]
        require(
            place in labels,
            f"{context}: the replacement field at {local} takes the label at {place}, which "
            "has no declared place in the replacement",
        )
        addend = int.from_bytes(full[local : local + 4], "little", signed=True)
        internal[local] = labels[place] + addend
    return internal


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
    code_end = spec.get("donor_code_end", proc)
    require(
        type(code_end) is int and 0 < code_end <= proc,
        f"{label}: the donor's declared code end lies outside its procedure",
    )
    # Check 1: one entry; a data tail holds switch tables; nothing else names
    # an interior offset but a label the install carries to its declared place.
    labels = declared_labels(spec, label)
    required_labels = section_label_values(donor, dp)
    require(
        set(labels) == required_labels,
        f"{label}: the declared labels {sorted(labels)} are not the donor section's labels "
        f"{sorted(required_labels)}",
    )
    require(proc not in labels, f"{label}: a label lies at the donor's procedure end")
    debug_labels = debug_label_values(donor, dp, label)
    debug_start, debug_end_donor = _debug_range(donor, dp, label)
    require(debug_start == 0, f"{label}: the donor's debug range does not start at its entry")
    named = sorted(
        offset
        for offset in protected_code_offsets(donor, dp, label)
        if offset not in (0, proc, debug_end_donor) and offset not in labels
    )
    require(not named, f"{label}: a symbol or closure record names the donor's offsets {named}")
    donor_targets, donor_internal = donor_fields(
        rows, dp["number"], mangled, proc, donor_body, label
    )
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
    code, boundaries, image_targets, reseat, debug_end = validate_replacement(
        spec, rows, label, section_number=dp["number"]
    )
    tail = replacement_tail(spec, label)
    image_proc = len(code) + len(tail)
    image_internal = replacement_internal(spec, rows, code + tail, dp["number"], labels, label)
    for donor_place, image_place in labels.items():
        # A label only anchors the fields that name it: each such field is
        # resolved as installed (replacement_internal), and the proof runs on
        # those resolved targets, so a label's own place need only lie inside
        # the procedure (a reference may keep a label's place and move its
        # target by the field's addend).
        require(
            0 < image_place < image_proc,
            f"{label}: the label at {donor_place} is declared at {image_place}, outside the "
            "replacement's procedure",
        )
    donor_tail = Tail(donor_body[code_end:proc], donor_internal)
    image_tail = Tail(tail, image_internal)
    require(
        sorted(Program(code, image_targets, "P", label, helpers, image_tail).instructions)
        == boundaries,
        f"{label}: the replacement does not decode on its declared boundaries",
    )
    donor_program = Program(donor_body[:code_end], donor_targets, "D", label, helpers, donor_tail)
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
    case_targets = frozenset(
        target
        for switch in donor_program.switches.values()
        if switch.kind == SWITCH_JUMP
        for target in donor_program.table(switch)
    )
    items, successors, entries = ia32_relational_flow_walk(
        donor_body[:proc], view, f"{label} donor flow", code_end, case_targets
    )
    # A computed jump's walk edges reach every case target; each switch reaches its own.
    index_of = {item["offset"]: index for index, item in enumerate(items)}
    for offset, switch in donor_program.switches.items():
        if switch.kind == SWITCH_JUMP:
            successors[index_of[offset]] = sorted(
                {index_of[target] for target in donor_program.table(switch)}
            )
    case_proofs: list[ValidationProof] = []
    # Whether partial slot relations run, and whether a run without them
    # refused a slot written on only some paths (`UncarriedSlot`).
    partial = {"on": False, "needed": False}

    def summary(
        model: ObjectModel | None,
        tag: str,
        entry_values: bool = False,
        frame_objects: FrameObjects | None = None,
    ) -> dict[str, Any]:
        case_proofs.clear()
        tag += " (partial slots)" if partial["on"] else ""

        def prove_case(counts: Mapping[str, int], note: str) -> ValidationProof:
            try:
                case_proof = _prove_case(counts, note)
            except UncarriedSlot:
                partial["needed"] = True
                raise
            case_proofs.append(case_proof)
            return case_proof

        def _prove_case(counts: Mapping[str, int], note: str) -> ValidationProof:
            return prove_function(
                donor_body[:code_end],
                donor_targets,
                code,
                image_targets,
                counts,
                f"{label} proof{tag}{note}",
                private_frame=private_frame,
                helpers=helpers,
                donor_tail=donor_tail,
                image_tail=image_tail,
                objects=model,
                entry_values=entry_values,
                frame_objects=frame_objects,
                partial_slots=partial["on"],
            )

        return _x87_case_proofs(items, successors, entries, donor_body[:proc], view, prove_case)

    def earlier_passes() -> dict[str, Any]:
        # The first pass is the proof every record made before the
        # equivalences pass pins; only when it refuses does the second run,
        # under a10 and the normal forms of `region_simulation._equivalences`,
        # and its summary then says so.  Each pass is sound alone.
        try:
            return summary(None, "")
        except ByteIdentityError:
            try:
                return {**summary(objects, " (equivalences pass)"), "equivalences": True}
            except ByteIdentityError as error:
                # The entry-values pass differs from the equivalences pass only
                # in a private frame; its records pin that they needed it.
                if not getattr(error, "private_frame", False):
                    raise
                return {
                    **summary(objects, " (entry-values pass)", entry_values=True),
                    "equivalences": True,
                    "entry_values": True,
                }

    def frame_objects_pass(earlier: ByteIdentityError) -> dict[str, Any]:
        # Only when every earlier pass refuses, and only in an FPO frame: the
        # frame-objects pass (a14), whose summary pins its escaping objects
        # and the assumption.  A record made by an earlier pass never needs it.
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
        if not locals_block_first(donor_program, frame.base):
            raise ByteIdentityError(
                f"{earlier}; the frame-objects pass (a14) cannot run: the donor does not allocate "
                "its locals block first"
            ) from earlier
        try:
            return {
                **summary(objects, " (frame-objects pass)", frame_objects=frame_objects),
                "equivalences": True,
            }
        except ByteIdentityError as error:
            if not getattr(error, "private_frame", False):
                raise
        return {
            **summary(
                objects,
                " (frame-objects pass, entry values)",
                entry_values=True,
                frame_objects=frame_objects,
            ),
            "equivalences": True,
            "entry_values": True,
        }

    def passes() -> dict[str, Any]:
        try:
            return earlier_passes()
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
    for proof in case_proofs:
        for place in sorted(debug_labels):
            paired = proof.pairs.get(place)
            require(
                paired is None or paired == labels[place],
                f"{label}: the CodeView label at {place} is declared at {labels[place]}, but the "
                f"proof pairs its join with {paired}",
            )
    image = (
        code
        + tail
        + bytes([MSVC50_FUNCTION_FILL_BYTE])
        * (_padded_length(image_proc, fill_alignment) - image_proc)
    )
    require(image != donor_body, f"{label} image does not move the donor body")
    derived, derived_detail = resized_donor_object(
        donor_bytes,
        mangled,
        image,
        {
            "offset_map": {0: 0, proc: image_proc},
            "symbol_map": labels,
            "interiors": [[0, proc, 0]],
            "proc_size": proc,
            "image_proc_size": image_proc,
            "relocation_reseat": reseat,
        },
        f"{label} derived donor",
        debug_range=(0, debug_end),
        carried_labels=True,
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
    installed = []
    for row in rows:
        moved_row = {**row, "offset": moved.get(row["offset"], row["offset"])}
        if row["target_section"] == dp["number"] and row["type"] == _DIR32:
            # The label symbol now lies at its declared place, the addend is the image's.
            at = moved_row["offset"]
            moved_row["target_value"] = labels.get(row["target_value"], row["target_value"])
            moved_row["addend"] = int.from_bytes(image[at : at + 4], "little", signed=True)
        installed.append(moved_row)
    return FunctionValidationMeasure(image, derived, installed, reseat, pins)


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
