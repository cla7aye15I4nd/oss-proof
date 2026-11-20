/* C side of the differential test for compressBound and compressBound_z (compress.c): links the REAL patched zlib-ng
 * (verified configuration). Input and output formats: see tests/README.md. */
#include "common.h"
#include "zlib.h"

int main(void) {
    char *line = NULL; size_t cap = 0;
    int bad = 0;
    while (getline(&line, &cap, stdin) >= 0) {
        char *tok[8]; int nt = split(line, tok);
        if (nt == 0) continue;
        const char *fn = tok[0];
        if (strcmp(fn, "compressBound") == 0 && nt == 2) {
            printf("%lu\n", compressBound((uLong)parse_u(tok[1])));
        } else if (strcmp(fn, "compressBound_z") == 0 && nt == 2) {
            printf("%zu\n", compressBound_z((z_size_t)parse_u(tok[1])));
        } else {
            fprintf(stderr, "unknown function or wrong arity: %s\n", fn);
            printf("BADINPUT\n");
            bad = 1;
        }
    }
    free(line);
    return bad;
}
