# ruff: noqa: E501, SIM115 -- this script writes C source text verbatim.
# Generates probe.c: one function per x87 encoding, raw bytes via _emit.
arith = []
for base in (0xD8, 0xDC, 0xDE):
    for digit in range(8):
        for i in (1, 2):
            modrm = 0xC0 | (digit << 3) | i
            if base == 0xDE and digit in (2, 3):
                continue  # DE D0-DF: only D9 (fcompp) is defined
            if base == 0xDC and digit in (2, 3):
                continue  # undocumented aliases
            arith.append((base, modrm))
compares = [
    ("D8 /2 m32 fcom", "fcom_m32"),
    ("D8 /3 m32 fcomp", "fcomp_m32"),
    ("DC /2 m64 fcom", "fcom_m64"),
    ("DC /3 m64 fcomp", "fcomp_m64"),
    ("D8 D1 fcom st1", "D8D1"),
    ("D8 D9 fcomp st1", "D8D9"),
    ("DE D9 fcompp", "DED9"),
    ("DD E1 fucom st1", "DDE1"),
    ("DD E9 fucomp st1", "DDE9"),
    ("DA E9 fucompp", "DAE9"),
]
out = []
out.append(r"""#include <stdio.h>
#include <float.h>
double A, B, C3V, R[4]; float F32; double F64; unsigned short SW0, SW1; unsigned char ENV[28];
unsigned short TAGW;
""")
for base, modrm in arith:
    out.append(f"""static void a_{base:02X}{modrm:02X}(void) {{ __asm {{
  finit
  fld C3V
  fld A
  fld B
  fnstsw ax
  mov SW0, ax
  _emit 0x{base:02X}
  _emit 0x{modrm:02X}
  fnstsw ax
  mov SW1, ax
  fnstenv ENV
  fldenv ENV
  fstp R
  fstp R+8
  fstp R+16
}} }}""")


def cmpbody(tag, op):
    return f"""static void c_{tag}(int setbits) {{ __asm {{
  finit
  fld C3V
  fld B
  fld A
  fnstenv ENV
  mov ax, word ptr ENV+4
  and ax, 0xB8FF
  cmp setbits, 0
  je skip_{tag}
  or ax, 0x4700
skip_{tag}:
  mov word ptr ENV+4, ax
  fldenv ENV
  fnstsw ax
  mov SW0, ax
  {op}
  fnstsw ax
  mov SW1, ax
  fstp R
  fstp R+8
  fstp R+16
}} }}"""


ops = {
    "fcom_m32": "fcom F32",
    "fcomp_m32": "fcomp F32",
    "fcom_m64": "fcom F64",
    "fcomp_m64": "fcomp F64",
    "D8D1": "_emit 0xD8\n  _emit 0xD1",
    "D8D9": "_emit 0xD8\n  _emit 0xD9",
    "DED9": "_emit 0xDE\n  _emit 0xD9",
    "DDE1": "_emit 0xDD\n  _emit 0xE1",
    "DDE9": "_emit 0xDD\n  _emit 0xE9",
    "DAE9": "_emit 0xDA\n  _emit 0xE9",
}
for _label, tag in compares:
    out.append(cmpbody(tag, ops[tag]))
# spill probes: value kept in register vs spilled through m32/m64 then compared in register
out.append(r"""static unsigned short CW; static double KEEP, SPILL; static float S32; static double S64;
static void spill32(void) { __asm {
  finit
  fldcw CW
  fld A
  fmul B
  fst S32
  fld S32
  fxch st(1)
  fcompp
  fnstsw ax
  mov SW1, ax
  fld A
  fmul B
  fstp KEEP
} }
static void spill64(void) { __asm {
  finit
  fldcw CW
  fld A
  fmul B
  fst S64
  fld S64
  fxch st(1)
  fcompp
  fnstsw ax
  mov SW1, ax
} }""")
out.append(
    "int main(void) {\n  static const double ins[][3] = {{7.0, 2.0, 100.0}, {1.0, 3.0, -9.0}, {-5.0, 0.25, 0.5}, {1e10, 3.0, 7.0}};\n  int k, s, n;"
)
out.append("  for (k = 0; k < 4; k++) { A = ins[k][0]; B = ins[k][1]; C3V = ins[k][2];")
for base, modrm in arith:
    out.append(
        f'    a_{base:02X}{modrm:02X}(); printf("ARITH {base:02X}{modrm:02X} A=%.17g B=%.17g C=%.17g top0=%d top1=%d tag=%04x R0=%.17g R1=%.17g R2=%.17g\\n", A, B, C3V, (SW0>>11)&7, (SW1>>11)&7, *(unsigned short*)(ENV+8), R[0], R[1], R[2]);'
    )
out.append("  }")
out.append(r"""  { static const double cmp[][2] = {{2.0, 1.0}, {1.0, 2.0}, {1.5, 1.5}, {0.0, 0.0}};
    static unsigned long qnan[2] = {0, 0x7ff80000};
    for (n = 0; n < 5; n++) for (s = 0; s < 2; s++) {
      if (n < 4) { A = cmp[n][0]; B = cmp[n][1]; } else { A = *(double*)qnan; B = 1.0; }
      F32 = (float)B; F64 = B; C3V = 42.0;""")
for _label, tag in compares:
    out.append(
        f'      c_{tag}(s); printf("CMP {tag} A=%g B=%g preset=%d swbefore=%04x swafter=%04x top0=%d top1=%d\\n", A, B, s, SW0, SW1, (SW0>>11)&7, (SW1>>11)&7);'
    )
out.append("  } }")
out.append(r"""  { static const unsigned short cws[] = {0x007F, 0x027F, 0x037F};
    static const double sp[][2] = {{1.0, 0.3333333333333333}, {1e30, 1e30}, {1e300, 1e300}, {1e-30, 1e-30}, {0.5, 4.0}};
    for (k = 0; k < 3; k++) for (n = 0; n < 5; n++) {
      CW = cws[k]; A = sp[n][0]; B = sp[n][1];
      spill32(); printf("SPILL32 cw=%04x A=%g B=%g c3c2c0=%d%d%d S32=%.9g\n", CW, A, B, (SW1>>14)&1, (SW1>>10)&1, (SW1>>8)&1, (double)S32);
      spill64(); printf("SPILL64 cw=%04x A=%g B=%g c3c2c0=%d%d%d S64=%.17g\n", CW, A, B, (SW1>>14)&1, (SW1>>10)&1, (SW1>>8)&1, S64);
    } }""")
out.append("  return 0;\n}")
open("probe.c", "w").write("\n".join(out) + "\n")
print(len(arith), "arith encodings")
