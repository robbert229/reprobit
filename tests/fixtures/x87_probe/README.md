# x87 hardware probe (region simulator)

Evidence for the x87 semantics `reprobit.classic.region_simulation` admits,
recorded on 2026-11-18 with this project's MSVC 5.0 (`cl /nologo /Od`,
inline `__asm` with raw `_emit` encodings) and run under Wine on an x86-64
host's x87 unit.

- `gen_probe.py` writes `probe.c`: every D8/DC/DE register arithmetic form
  with i = 1 and 2 over four input stacks (`ARITH`), the ten compare forms
  with C0-C3 preset to 0 and to 1 through `fldenv` (`CMP`), and spills
  through m32/m64 under precision control 24, 53 and 64 bits (`SPILL32`,
  `SPILL64`).  Its output is `probe.out`.
- `roles.c` computes every subtract, divide, add and multiply encoding with
  the operands' registers swapped, over 14 x 14 operand pairs (QNaNs of
  equal significand and opposite sign, SNaNs, infinities, signed zeros, a
  denormal, the maximum), and prints the 80-bit result and the exception
  flags.  Its output is `roles.out`.
- `moves.c` runs the register copies and sign operations (`fld st(0)`,
  `fld st(1)`, `fxch st(1)`, `fst st(1)`, `fchs`, `fabs`, `fld1`, `fldz`)
  over SNaN, QNaN, denormal, 1 and -0 operands and prints the exception
  flags and both registers bit for bit.  Its output is `moves.out`.
- `commute.c` runs every add and multiply register encoding (D8 C1/C9,
  DC C1/C9, DE C1/C9) with each operand in each register, over 19 x 19
  operand pairs (the role probe's fourteen, the pseudo-NaN, pseudo-infinity,
  unnormal and pseudo-denormal encodings, and -1 for an exact zero sum),
  under all four rounding modes and the three precision controls (control
  words 0x007F-0x0F7F, every exception masked).  Each line prints the
  distinct `result/flags/C1` values the six runs gave, so one value means
  the operation is symmetric there.  Its output is `commute.out`; recorded on
  2026-11-18 on a 13th Gen Intel Core i5-13400F.
- `memory_operands.c` (GNU C, not MSVC: the x87 unit is the host's either
  way) runs `fadd`/`fmul` with a 32-bit memory operand against the same
  with the operand loaded into a register, and with two memory operands
  commuted, over ten operands (SNaNs and QNaNs of several payloads and
  signs, 1, a denormal, -0, infinity), every exception masked.  Each line
  says whether the commuted memory operands, the memory operand against
  the register, and the commuted registers give the same 80-bit result and
  exception flags.  Its output is `memory_operands.out` (the same 13th Gen
  Intel Core i5-13400F, 2026-11-19): only the registers always commute;
  a memory operand differs from its loaded register when the other operand
  is a NaN (the NaN payload chosen, or DE for a denormal), so the simulator
  never equates `fmem` with `fld` and never commutes two memory operands.
  Reproduce with `gcc -O0 -o memory_operands memory_operands.c &&
  ./memory_operands > memory_operands.out`.
- `memory_commute.c` (GNU C, the host's x87 unit) is the evidence for a19
  of `reprobit.classic.function_validation`.  For m32 and m64, `fadd` and
  `fmul`, every ordered pair of 17 operands of that width (15 non-NaN:
  signed ones and zeros, the smallest and a largest negative denormal, the
  smallest normal, the largest finite values, infinities, 1 + ulp, 2^24
  or 2^53, 2^-24 or 2^-53, 1/3; and a QNaN and an SNaN) and all twelve
  control words 0x007F | RC << 10 | PC << 8 (every exception masked), it
  runs `fld A; fop B`, `fld B; fop A`, `fld A; fld B; fopp` and
  `fld B; fld A; fopp`, and compares the 80-bit result, the exception
  flags, SF, ES and C1.  Each line says whether the commuted memory
  operands, the memory operand against its loaded register and the
  commuted registers agree under every control word, or the first control
  word where they do not.  Its output is `memory_commute.out` (13th Gen
  Intel Core i5-13400F, 2026-11-20): all 900 non-NaN lines agree in all
  three columns; the 40 that differ all have a NaN operand.  Reproduce
  with `gcc -O0 -o memory_commute memory_commute.c && ./memory_commute >
  memory_commute.out`.
- `encodings.txt` is `objdump -d` of the three objects, restricted to x87 lines:
  the bytes each probe executed.  `commute_encodings.txt` is the same for
  `commute.obj`.

Reproduce (inside the `developer` distrobox, toolchain at `$T`):

    python3 gen_probe.py
    WINEDEBUG=-all INCLUDE="Z:$T/include" LIB="Z:$T/lib" wine $T/bin/cl.exe /nologo /Od probe.c
    wine probe.exe > probe.out
    WINEDEBUG=-all INCLUDE="Z:$T/include" LIB="Z:$T/lib" wine $T/bin/cl.exe /nologo /Od roles.c
    wine roles.exe > roles.out
    WINEDEBUG=-all INCLUDE="Z:$T/include" LIB="Z:$T/lib" wine $T/bin/cl.exe /nologo /Od moves.c
    wine moves.exe > moves.out
    WINEDEBUG=-all INCLUDE="Z:$T/include" LIB="Z:$T/lib" wine $T/bin/cl.exe /nologo /Od commute.c
    wine commute.exe > commute.out

`tests/test_classic_region_x87.py` parses these files and checks the
simulator against them.
