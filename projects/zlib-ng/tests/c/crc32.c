/* C side of the differential test for crc32.c, arch/generic/crc32_braid_c.c and crc32_braid_comb.c: links
 * the REAL patched zlib-ng (verified configuration). Input and output formats: see tests/README.md. */
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
        if ((strcmp(fn, "crc32_z") == 0 || strcmp(fn, "crc32") == 0) && nt == 3) {
            uLong a = (uLong)parse_u(tok[1]);
            struct buf b = parse_buf(tok[2]);
            uLong r;
            if (strcmp(fn, "crc32_z") == 0) r = crc32_z(a, b.ptr, (z_size_t)b.len);
            else {
                if (b.len > 0xffffffffUL) { fprintf(stderr, "len does not fit uInt\n"); exit(2); }
                r = crc32(a, b.ptr, (uInt)b.len);
            }
            printf("%lu\n", r);
            free(b.block);
        } else if ((strcmp(fn, "crc32_combine") == 0 || strcmp(fn, "crc32_combine64") == 0) && nt == 4) {
            uLong a1 = (uLong)parse_u(tok[1]), a2 = (uLong)parse_u(tok[2]);
            long long l = parse_i(tok[3]);
            uLong r = strcmp(fn, "crc32_combine") == 0 ? crc32_combine(a1, a2, (z_off_t)l)
                                                       : crc32_combine64(a1, a2, (z_off64_t)l);
            printf("%lu\n", r);
        } else if ((strcmp(fn, "crc32_combine_gen") == 0 || strcmp(fn, "crc32_combine_gen64") == 0) && nt == 2) {
            long long l = parse_i(tok[1]);
            uLong r = strcmp(fn, "crc32_combine_gen") == 0 ? crc32_combine_gen((z_off_t)l)
                                                           : crc32_combine_gen64((z_off64_t)l);
            printf("%lu\n", r);
        } else if (strcmp(fn, "crc32_combine_op") == 0 && nt == 4) {
            uLong r = crc32_combine_op((uLong)parse_u(tok[1]), (uLong)parse_u(tok[2]), (uLong)parse_u(tok[3]));
            printf("%lu\n", r);
        } else if (strcmp(fn, "get_crc_table") == 0 && nt == 1) {
            /* read the 256 entries through the returned pointer */
            const z_crc_t *t = get_crc_table();
            for (int i = 0; i < 256; i++) printf(i ? " %lu" : "%lu", (unsigned long)t[i]);
            printf("\n");
        } else {
            fprintf(stderr, "unknown function or wrong arity: %s\n", fn);
            printf("BADINPUT\n");
            bad = 1;
        }
    }
    free(line);
    return bad;
}
