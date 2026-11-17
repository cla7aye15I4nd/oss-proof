/* ba829a4: crc32_combine with a negative length.
 * crc32_combine(crc1, crc2, -1) reaches x2nmodp(-1, 3) through crc32_combine_gen64. Its loop
 * `while (n) { ...; n >>= 1; }` never ends for a negative n (the shift keeps -1). The fix returns 0
 * for a negative length, which zlib.h now documents. */
#include <stdio.h>
#include "zlib.h"

int main(void) {
    unsigned long c1 = crc32(0L, (const unsigned char *)"abc", 3);
    unsigned long c2 = crc32(0L, (const unsigned char *)"def", 3);
    unsigned long c = crc32_combine(c1, c2, -1);
    printf("combine=%lu\n", c);
    return 0;
}
