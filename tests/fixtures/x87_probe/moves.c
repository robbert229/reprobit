/* Move probe: register copies and sign operations on SNaN, QNaN, denormal,
   pseudo-denormal-free extended values; records the exception flags and the
   80-bit ST(0) and ST(1) after each instruction.  Raw encodings via _emit. */
#include <stdio.h>
#include <string.h>
unsigned char V0[10], V1[10], S0[10], S1[10]; unsigned short SW;
#define CASE(b0, b1) __asm { \
  __asm finit \
  __asm fld tbyte ptr V1 \
  __asm fld tbyte ptr V0 \
  __asm fnclex \
  __asm _emit b0 \
  __asm _emit b1 \
  __asm fnstsw ax \
  __asm mov SW, ax \
  __asm fstp tbyte ptr S0 \
  __asm fstp tbyte ptr S1 }
static void run(int c) {
  switch (c) {
  case 0: CASE(0xD9, 0xC1) break; /* fld st(1): S0 = copy of V1, S1 = V0 */
  case 1: CASE(0xD9, 0xC9) break; /* fxch st(1) */
  case 2: CASE(0xDD, 0xD1) break; /* fst st(1) */
  case 3: CASE(0xD9, 0xE0) break; /* fchs */
  case 4: CASE(0xD9, 0xE1) break; /* fabs */
  case 5: CASE(0xD9, 0xC0) break; /* fld st(0) */
  case 6: CASE(0xD9, 0xE8) break; /* fld1 */
  case 7: CASE(0xD9, 0xEE) break; /* fldz */
  }
}
static void put(unsigned char* p, unsigned short se, unsigned long hi, unsigned long lo) {
  memcpy(p, &lo, 4); memcpy(p + 4, &hi, 4); memcpy(p + 8, &se, 2);
}
static void show(const char* tag, unsigned char* p) {
  unsigned short se; unsigned long hi, lo;
  memcpy(&lo, p, 4); memcpy(&hi, p + 4, 4); memcpy(&se, p + 8, 2);
  printf(" %s=%04x%08lx%08lx", tag, se, hi, lo);
}
int main(void) {
  static const unsigned long vals[][3] = {
    {0x7FFF, 0xA0000000, 0x00000001}, /* SNaN */
    {0xFFFF, 0xC0000000, 0x00000002}, /* -QNaN */
    {0x0000, 0x00000000, 0x00000001}, /* denormal */
    {0x3FFF, 0x80000000, 0x00000000}, /* 1 */
    {0x8000, 0x00000000, 0x00000000}, /* -0 */
  };
  int i, j, c;
  for (i = 0; i < 5; i++) for (j = 0; j < 5; j++) for (c = 0; c < 8; c++) {
    put(V0, (unsigned short)vals[i][0], vals[i][1], vals[i][2]);
    put(V1, (unsigned short)vals[j][0], vals[j][1], vals[j][2]);
    run(c);
    printf("MOVE %d %d %d exc=%02x", c, i, j, SW & 0x3F);
    show("V0", V0); show("V1", V1); show("S0", S0); show("S1", S1);
    printf("\n");
  }
  return 0;
}
