/* local-0002: gzseek after gzungetc at position zero.
 * gzungetc right after gzopen is allowed and sets state->x.pos to -1. gzseek(f, 1, SEEK_CUR) then
 * starts from pos = -1. Without patch 0002 the range check evaluates GZ_OFF_MAX - pos, which
 * overflows z_off64_t. The file is a three-byte transparent file. */
#include <stdio.h>
#include "zlib.h"

int main(void) {
    FILE *raw = fopen("raw.dat", "wb");
    if (raw == NULL || fwrite("abc", 1, 3, raw) != 3 || fclose(raw) != 0) return 2;
    gzFile f = gzopen("raw.dat", "rb");
    if (f == NULL) return 2;
    int u = gzungetc('Q', f);
    long s = (long)gzseek(f, 1L, SEEK_CUR);
    int c = gzclose(f);
    printf("ungetc=%d seek=%ld close=%d\n", u, s, c);
    return 0;
}
