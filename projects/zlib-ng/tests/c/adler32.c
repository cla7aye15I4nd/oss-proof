/* C side of the differential test for adler32.c and arch/generic/adler32_c.c: links the REAL patched
 * zlib-ng (verified configuration). Input and output formats: see tests/README.md. */
#include "common.h"
#include "zlib.h"
#include "zlib64.h"

int main(void) {
    char *line = NULL; size_t cap = 0;
    int bad = 0;
    while (getline(&line, &cap, stdin) >= 0) {
        char *tok[8]; int nt = split(line, tok);
        if (nt == 0) continue;
        const char *fn = tok[0];
        if ((strcmp(fn, "adler32_z") == 0 || strcmp(fn, "adler32") == 0) && nt == 3) {
            uLong a = (uLong)parse_u(tok[1]);
            struct buf b = parse_buf(tok[2]);
            uLong r;
            if (strcmp(fn, "adler32_z") == 0) r = adler32_z(a, b.ptr, (z_size_t)b.len);
            else {
                if (b.len > 0xffffffffUL) { fprintf(stderr, "len does not fit uInt\n"); exit(2); }
                r = adler32(a, b.ptr, (uInt)b.len);
            }
            printf("%lu\n", r);
            free(b.block);
        } else if ((strcmp(fn, "adler32_combine") == 0 || strcmp(fn, "adler32_combine64") == 0) && nt == 4) {
            uLong a1 = (uLong)parse_u(tok[1]), a2 = (uLong)parse_u(tok[2]);
            long long l = parse_i(tok[3]);
            uLong r = strcmp(fn, "adler32_combine") == 0 ? adler32_combine(a1, a2, (z_off_t)l)
                                                         : adler32_combine64(a1, a2, (z_off64_t)l);
            printf("%lu\n", r);
        } else {
            fprintf(stderr, "unknown function or wrong arity: %s\n", fn);
            printf("BADINPUT\n");
            bad = 1;
        }
    }
    free(line);
    return bad;
}
