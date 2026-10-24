/* Minimal single-source program for the SP3 byte-identity example. */

int transform(void);

int transform(void) {
    int sum = 0;
    int i;
    for (i = 1; i <= 10; ++i) {
        sum += i * i;
    }
    return sum;
}
