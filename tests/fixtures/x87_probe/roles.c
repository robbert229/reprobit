/* Role probe: does each x87 arithmetic encoding compute one function of
   (minuend, subtrahend) / (dividend, divisor) / (left, right) whichever
   register holds which operand?  80-bit results and the exception flags
   are compared bit for bit.  Raw encodings via _emit. */
#include <stdio.h>
#include <string.h>
unsigned char X[10], Y[10], RES[10]; unsigned short SW;
#define BODY(b0, b1, first, second, pop) __asm { \
  __asm finit \
  __asm fld tbyte ptr first \
  __asm fld tbyte ptr second \
  __asm fnclex \
  __asm _emit b0 \
  __asm _emit b1 \
  __asm fnstsw ax \
  __asm mov SW, ax }
/* Each case leaves the result in ST(0) (D8 forms, or DE pop forms) or ST(1) (DC forms). */
static void run(int which) {
  switch (which) {
  /* st0 = Y (second load), st1 = X (first load) */
  case 0: BODY(0xD8, 0xE1, X, Y, 0) __asm { fstp tbyte ptr RES } break;  /* st0 = st0 - st1 = Y - X */
  case 1: BODY(0xD8, 0xE9, X, Y, 0) __asm { fstp tbyte ptr RES } break;  /* st0 = st1 - st0 = X - Y */
  case 2: BODY(0xDC, 0xE9, X, Y, 0) __asm { fstp st(0) } __asm { fstp tbyte ptr RES } break; /* st1 = st1 - st0 = X - Y */
  case 3: BODY(0xDC, 0xE1, X, Y, 0) __asm { fstp st(0) } __asm { fstp tbyte ptr RES } break; /* st1 = st0 - st1 = Y - X */
  case 4: BODY(0xDE, 0xE9, X, Y, 1) __asm { fstp tbyte ptr RES } break;  /* X - Y, pop */
  case 5: BODY(0xDE, 0xE1, X, Y, 1) __asm { fstp tbyte ptr RES } break;  /* Y - X, pop */
  case 6: BODY(0xD8, 0xF1, X, Y, 0) __asm { fstp tbyte ptr RES } break;  /* Y / X */
  case 7: BODY(0xD8, 0xF9, X, Y, 0) __asm { fstp tbyte ptr RES } break;  /* X / Y */
  case 8: BODY(0xDE, 0xF9, X, Y, 1) __asm { fstp tbyte ptr RES } break;  /* X / Y, pop */
  case 9: BODY(0xDE, 0xF1, X, Y, 1) __asm { fstp tbyte ptr RES } break;  /* Y / X, pop */
  case 10: BODY(0xD8, 0xC1, X, Y, 0) __asm { fstp tbyte ptr RES } break; /* st0 = st0 + st1: dest Y */
  case 11: BODY(0xDE, 0xC1, X, Y, 1) __asm { fstp tbyte ptr RES } break; /* st1 = st1 + st0: dest X */
  case 12: BODY(0xD8, 0xC9, X, Y, 0) __asm { fstp tbyte ptr RES } break; /* mul dest Y */
  case 13: BODY(0xDE, 0xC9, X, Y, 1) __asm { fstp tbyte ptr RES } break; /* mul dest X */
  }
}
static void set80(unsigned char* p, unsigned short se, unsigned long hi, unsigned long lo) {
  memcpy(p, &lo, 4); memcpy(p + 4, &hi, 4); memcpy(p + 8, &se, 2);
}
int main(void) {
  /* sign/exponent word, significand high, significand low */
  static const unsigned long vals[][3] = {
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
  };
  int n = sizeof vals / sizeof vals[0], i, j, c;
  for (i = 0; i < n; i++) for (j = 0; j < n; j++) {
    set80(X, (unsigned short)vals[i][0], vals[i][1], vals[i][2]);
    set80(Y, (unsigned short)vals[j][0], vals[j][1], vals[j][2]);
    printf("%d %d", i, j);
    for (c = 0; c < 14; c++) {
      unsigned short se; unsigned long hi, lo;
      run(c);
      memcpy(&lo, RES, 4); memcpy(&hi, RES + 4, 4); memcpy(&se, RES + 8, 2);
      printf(" %d:%04x%08lx%08lx/%02x", c, se, hi, lo, SW & 0x3F);
    }
    printf("\n");
  }
  return 0;
}
