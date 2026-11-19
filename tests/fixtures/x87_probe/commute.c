/* Commutativity probe: does every x87 add and multiply register encoding
   give the same 80-bit result, the same exception flags and the same C1
   whichever operand is the destination and whichever register holds it,
   under every rounding mode and precision control?  Raw encodings via _emit.

   For an operand pair (X, Y) each operation runs six ways: D8 C1/C9
   (ST(0) = ST(0) op ST(1)), DC C1/C9 (ST(1) = ST(1) op ST(0)) and DE C1/C9
   (the DC form, then pop), each with X loaded first (ST(0) = Y, ST(1) = X)
   and with Y loaded first (ST(0) = X, ST(1) = Y).  A line prints the
   distinct (result/flags/C1) values the six runs gave, joined by '|'. */
#include <stdio.h>
#include <string.h>
unsigned char X[10], Y[10], RES[10]; unsigned short SW, CW;
#define BODY(b0, b1, first, second) __asm { \
  __asm finit \
  __asm fldcw CW \
  __asm fld tbyte ptr first \
  __asm fld tbyte ptr second \
  __asm fnclex \
  __asm _emit b0 \
  __asm _emit b1 \
  __asm fnstsw ax \
  __asm mov SW, ax }
/* D8 forms leave the result in ST(0); DC forms in ST(1); DE forms pop it into ST(0).
   finit before storing the result would lose it, so the store runs under the
   probe's control word: fstp m80 stores the register exactly. */
static void run(int which) {
  switch (which) {
  case 0: BODY(0xD8, 0xC1, X, Y) __asm { fstp tbyte ptr RES } break;
  case 1: BODY(0xD8, 0xC1, Y, X) __asm { fstp tbyte ptr RES } break;
  case 2: BODY(0xDC, 0xC1, X, Y) __asm { fstp st(0) } __asm { fstp tbyte ptr RES } break;
  case 3: BODY(0xDC, 0xC1, Y, X) __asm { fstp st(0) } __asm { fstp tbyte ptr RES } break;
  case 4: BODY(0xDE, 0xC1, X, Y) __asm { fstp tbyte ptr RES } break;
  case 5: BODY(0xDE, 0xC1, Y, X) __asm { fstp tbyte ptr RES } break;
  case 6: BODY(0xD8, 0xC9, X, Y) __asm { fstp tbyte ptr RES } break;
  case 7: BODY(0xD8, 0xC9, Y, X) __asm { fstp tbyte ptr RES } break;
  case 8: BODY(0xDC, 0xC9, X, Y) __asm { fstp st(0) } __asm { fstp tbyte ptr RES } break;
  case 9: BODY(0xDC, 0xC9, Y, X) __asm { fstp st(0) } __asm { fstp tbyte ptr RES } break;
  case 10: BODY(0xDE, 0xC9, X, Y) __asm { fstp tbyte ptr RES } break;
  case 11: BODY(0xDE, 0xC9, Y, X) __asm { fstp tbyte ptr RES } break;
  }
}
static void set80(unsigned char* p, unsigned short se, unsigned long hi, unsigned long lo) {
  memcpy(p, &lo, 4); memcpy(p + 4, &hi, 4); memcpy(p + 8, &se, 2);
}
int main(void) {
  /* sign/exponent word, significand high, significand low */
  static const unsigned long vals[][3] = {
    /* the role probe's fourteen operands */
    {0x7FFF, 0xC0000000, 0x00000000}, /* +QNaN p0 */
    {0xFFFF, 0xC0000000, 0x00000000}, /* -QNaN p0 (same significand) */
    {0x7FFF, 0xC0000000, 0x00000123}, /* +QNaN p1 */
    {0xFFFF, 0xC0001000, 0x00000000}, /* -QNaN p2 */
    {0x7FFF, 0xA0000000, 0x00000000}, /* +SNaN */
    {0xFFFF, 0xA0000000, 0x00000000}, /* -SNaN same significand */
    {0x7FFF, 0x80000000, 0x00000000}, /* +inf */
    {0xFFFF, 0x80000000, 0x00000000}, /* -inf */
    {0x0000, 0x00000000, 0x00000000}, /* +0 */
    {0x8000, 0x00000000, 0x00000000}, /* -0 */
    {0x3FFF, 0x80000000, 0x00000000}, /* 1 */
    {0x3FFD, 0xAAAAAAAA, 0xAAAAAAAB}, /* ~1/3 */
    {0x0000, 0x00000000, 0x00000001}, /* denormal */
    {0x7FFE, 0xFFFFFFFF, 0xFFFFFFFF}, /* max */
    /* beyond the role probe: the encodings no admitted instruction produces */
    {0x7FFF, 0x40000000, 0x00000000}, /* pseudo-NaN (integer bit clear) */
    {0x7FFF, 0x00000000, 0x00000000}, /* pseudo-infinity */
    {0x3FFF, 0x40000000, 0x00000000}, /* unnormal */
    {0x0000, 0x80000000, 0x00000000}, /* pseudo-denormal */
    /* opposite signs of one magnitude: an exact zero sum */
    {0xBFFF, 0x80000000, 0x00000000}, /* -1 */
  };
  /* all exceptions masked; precision control 24, 53, 64 bits; rounding nearest, down, up, zero */
  static const unsigned short pcs[] = {0x0000, 0x0200, 0x0300};
  int n = sizeof vals / sizeof vals[0], i, j, c, p, r, k, op, d;
  for (p = 0; p < 3; p++) for (r = 0; r < 4; r++) {
    CW = (unsigned short)(0x007F | pcs[p] | (r << 10));
    for (i = 0; i < n; i++) for (j = 0; j < n; j++) {
      set80(X, (unsigned short)vals[i][0], vals[i][1], vals[i][2]);
      set80(Y, (unsigned short)vals[j][0], vals[j][1], vals[j][2]);
      printf("%04x %d %d", CW, i, j);
      for (op = 0; op < 2; op++) {
        char seen[6][40]; int count = 0;
        printf(" %s=", op == 0 ? "add" : "mul");
        for (c = 0; c < 6; c++) {
          unsigned short se; unsigned long hi, lo; char text[40];
          run(op * 6 + c);
          memcpy(&lo, RES, 4); memcpy(&hi, RES + 4, 4); memcpy(&se, RES + 8, 2);
          sprintf(text, "%04x%08lx%08lx/%02x/%d", se, hi, lo, SW & 0x7F, (SW >> 9) & 1);
          for (k = 0, d = 1; k < count; k++) if (!strcmp(seen[k], text)) d = 0;
          if (d) { strcpy(seen[count], text); printf("%s%s", count ? "|" : "", text); count++; }
        }
      }
      printf("\n");
    }
  }
  return 0;
}
