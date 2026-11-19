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
