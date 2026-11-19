/* Memory-operand probe: is an x87 add or multiply with a memory operand the
   same operation as loading that operand first?  And may two memory operands
   be commuted?  GNU C inline assembly (AT&T), every exception masked
   (control word 0x037F), run on the host's x87 unit.

   For each pair (A, B) of 32-bit operands and each of fadd/fmul it runs:
     MAB: flds A; fadds B        MBA: flds B; fadds A
     RAB: flds A; flds B; faddp  RBA: flds B; flds A; faddp
   and prints whether MAB and MBA (commuting two memory operands), MAB and
   RAB (a memory operand against the loaded register) and RAB and RBA
   (commuting two registers) give the same 80-bit result and the same
   exception flags.  Build: gcc -O0 -o memory_operands memory_operands.c */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

struct run {
    unsigned char value[10];
    unsigned short sw;
};

#define MEMORY(op)                                                                    \
    __asm__ volatile("fninit; fldcw %3; flds %1; " op " %2; fnstsw %%ax; mov %%ax, %4; " \
                     "fstpt %0"                                                       \
                     : "=m"(*(char(*)[10])out->value)                                 \
                     : "m"(fa), "m"(fb), "m"(cw), "m"(out->sw)                        \
                     : "ax")
#define REGISTER(op)                                                                  \
    __asm__ volatile("fninit; fldcw %3; flds %1; flds %2; " op "; fnstsw %%ax; "      \
                     "mov %%ax, %4; fstpt %0"                                         \
                     : "=m"(*(char(*)[10])out->value)                                 \
                     : "m"(fa), "m"(fb), "m"(cw), "m"(out->sw)                        \
                     : "ax")

static void run(uint32_t a, uint32_t b, int mul, int memory, struct run *out) {
    float fa, fb;
    unsigned short cw = 0x037F;
    memcpy(&fa, &a, 4);
    memcpy(&fb, &b, 4);
    if (memory) {
        if (mul) MEMORY("fmuls"); else MEMORY("fadds");
    } else {
        if (mul) REGISTER("fmulp"); else REGISTER("faddp");
    }
}

static int same(const struct run *x, const struct run *y) {
    return !memcmp(x->value, y->value, 10) && (x->sw & 0x3F) == (y->sw & 0x3F);
}

int main(void) {
    static const uint32_t values[] = {0x7FA00000u, 0x7F900000u, 0xFFA00001u, 0x7FC00000u,
                                      0x7FE00000u, 0xFFC00001u, 0x3F800000u, 0x00000001u,
                                      0x80000000u, 0x7F800000u};
    static const char *names[] = {"snan.a0", "snan.90", "-snan.a1", "qnan.c0", "qnan.e0",
                                  "-qnan.c1", "1.0", "denormal", "-0", "inf"};
    const int count = sizeof values / sizeof values[0];
    for (int mul = 0; mul < 2; mul++)
        for (int i = 0; i < count; i++)
            for (int j = 0; j < count; j++) {
                struct run mab, mba, rab, rba;
                run(values[i], values[j], mul, 1, &mab);
                run(values[j], values[i], mul, 1, &mba);
                run(values[i], values[j], mul, 0, &rab);
                run(values[j], values[i], mul, 0, &rba);
                printf("%s %s %s commute-memory=%s memory-as-register=%s commute-register=%s\n",
                       mul ? "fmul" : "fadd", names[i], names[j], same(&mab, &mba) ? "same" : "DIFF",
                       same(&mab, &rab) ? "same" : "DIFF", same(&rab, &rba) ? "same" : "DIFF");
            }
    return 0;
}
