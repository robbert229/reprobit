/* Memory-operand commutativity probe for a19: may an x87 add or multiply
   whose second operand is in memory have its two operands swapped when
   neither is a NaN?  And is the memory operand then the register its load
   gives?  GNU C inline assembly (AT&T), run on the host's x87 unit.

   For each width w (m32, m64), each operation (fadd, fmul), each of the
   twelve control words 0x007F | rc << 10 | pc << 8 (every exception masked;
   rounding to nearest, down, up and toward zero; precision control 24, 53
   and 64 bits) and each ordered pair (A, B) of w-bit operands it runs:
     MAB: fld A; fop B           MBA: fld B; fop A
     RAB: fld A; fld B; fopp     RBA: fld B; fld A; fopp
   and records the 80-bit result, the exception flags (status word bits
   0-5), SF and ES (bits 6-7) and C1 (bit 9).  A line per (w, op, A, B)
   says whether MAB = MBA (commuted memory operands), MAB = RAB (a memory
   operand against its loaded register) and RAB = RBA (commuted registers)
   under every one of the twelve control words; a difference names the
   first control word that shows it.  Build: gcc -O0 -o memory_commute
   memory_commute.c */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

struct run {
    unsigned char value[10];
    unsigned short sw;
};

#define RUN(text, in_a, in_b)                                                      \
    __asm__ volatile("fninit; fldcw %3; " text "; fnstsw %%ax; mov %%ax, %4; fstpt %0" \
                     : "=m"(*(char(*)[10])out->value)                              \
                     : "m"(in_a), "m"(in_b), "m"(cw), "m"(out->sw)                 \
                     : "ax")

/* form: 0 memory (fld A; fop B), 1 registers (fld A; fld B; fopp). */
static void run32(uint32_t a, uint32_t b, int mul, int form, unsigned short cw, struct run *out) {
    float fa, fb;
    memcpy(&fa, &a, 4);
    memcpy(&fb, &b, 4);
    if (form == 0) {
        if (mul) RUN("flds %1; fmuls %2", fa, fb); else RUN("flds %1; fadds %2", fa, fb);
    } else {
        if (mul) RUN("flds %1; flds %2; fmulp", fa, fb); else RUN("flds %1; flds %2; faddp", fa, fb);
    }
}

static void run64(uint64_t a, uint64_t b, int mul, int form, unsigned short cw, struct run *out) {
    double fa, fb;
    memcpy(&fa, &a, 8);
    memcpy(&fb, &b, 8);
    if (form == 0) {
        if (mul) RUN("fldl %1; fmull %2", fa, fb); else RUN("fldl %1; faddl %2", fa, fb);
    } else {
        if (mul) RUN("fldl %1; fldl %2; fmulp", fa, fb); else RUN("fldl %1; fldl %2; faddp", fa, fb);
    }
}

/* The result, the exception flags, SF, ES and C1. */
static int same(const struct run *x, const struct run *y) {
    return !memcmp(x->value, y->value, 10) && (x->sw & 0x2FF) == (y->sw & 0x2FF);
}

static const uint32_t values32[] = {
    0x3F800000u, /* 1 */
    0xBF800000u, /* -1 */
    0x00000000u, /* 0 */
    0x80000000u, /* -0 */
    0x00000001u, /* smallest denormal */
    0x807FFFFFu, /* largest negative denormal */
    0x00800000u, /* smallest normal */
    0x7F7FFFFFu, /* largest finite */
    0xFF7FFFFFu, /* -largest finite */
    0x7F800000u, /* inf */
    0xFF800000u, /* -inf */
    0x3F800001u, /* 1 + ulp */
    0x4B800000u, /* 2^24 */
    0x33800000u, /* 2^-24 */
    0x3EAAAAABu, /* 1/3 */
    0x7FC00000u, /* QNaN (a19 excludes it) */
    0x7FA00000u, /* SNaN (a19 excludes it) */
};
static const char *names32[] = {"1", "-1", "0", "-0", "denormal", "-denormal.max", "normal.min",
                                "max", "-max", "inf", "-inf", "1+ulp", "2^24", "2^-24", "1/3",
                                "qnan", "snan"};

static const uint64_t values64[] = {
    0x3FF0000000000000ull, /* 1 */
    0xBFF0000000000000ull, /* -1 */
    0x0000000000000000ull, /* 0 */
    0x8000000000000000ull, /* -0 */
    0x0000000000000001ull, /* smallest denormal */
    0x800FFFFFFFFFFFFFull, /* largest negative denormal */
    0x0010000000000000ull, /* smallest normal */
    0x7FEFFFFFFFFFFFFFull, /* largest finite */
    0xFFEFFFFFFFFFFFFFull, /* -largest finite */
    0x7FF0000000000000ull, /* inf */
    0xFFF0000000000000ull, /* -inf */
    0x3FF0000000000001ull, /* 1 + ulp */
    0x4340000000000000ull, /* 2^53 */
    0x3CA0000000000000ull, /* 2^-53 */
    0x3FD5555555555555ull, /* 1/3 */
    0x7FF8000000000000ull, /* QNaN (a19 excludes it) */
    0x7FF4000000000000ull, /* SNaN (a19 excludes it) */
};
static const char *names64[] = {"1", "-1", "0", "-0", "denormal", "-denormal.max", "normal.min",
                                "max", "-max", "inf", "-inf", "1+ulp", "2^53", "2^-53", "1/3",
                                "qnan", "snan"};

int main(void) {
    const int count = sizeof values32 / sizeof values32[0];
    for (int wide = 0; wide < 2; wide++)
        for (int mul = 0; mul < 2; mul++)
            for (int i = 0; i < count; i++)
                for (int j = 0; j < count; j++) {
                    int verdict[3] = {-1, -1, -1};
                    for (int rc = 0; rc < 4; rc++)
                        for (int pc = 0; pc < 4; pc++) {
                            if (pc == 1) continue; /* reserved */
                            unsigned short cw = (unsigned short)(0x007F | rc << 10 | pc << 8);
                            struct run mab, mba, rab, rba;
                            if (wide) {
                                run64(values64[i], values64[j], mul, 0, cw, &mab);
                                run64(values64[j], values64[i], mul, 0, cw, &mba);
                                run64(values64[i], values64[j], mul, 1, cw, &rab);
                                run64(values64[j], values64[i], mul, 1, cw, &rba);
                            } else {
                                run32(values32[i], values32[j], mul, 0, cw, &mab);
                                run32(values32[j], values32[i], mul, 0, cw, &mba);
                                run32(values32[i], values32[j], mul, 1, cw, &rab);
                                run32(values32[j], values32[i], mul, 1, cw, &rba);
                            }
                            int results[3] = {same(&mab, &mba), same(&mab, &rab), same(&rab, &rba)};
                            for (int k = 0; k < 3; k++)
                                if (!results[k] && verdict[k] < 0) verdict[k] = cw;
                        }
                    const char **names = wide ? names64 : names32;
                    printf("m%d %s %s %s", wide ? 64 : 32, mul ? "fmul" : "fadd", names[i], names[j]);
                    static const char *labels[] = {"commute-memory", "memory-as-register",
                                                   "commute-register"};
                    for (int k = 0; k < 3; k++) {
                        if (verdict[k] < 0)
                            printf(" %s=same", labels[k]);
                        else
                            printf(" %s=DIFF@%04X", labels[k], verdict[k]);
                    }
                    printf("\n");
                }
    return 0;
}
