#include "common.h"
#include "jinclude.h"
#include "jpeglib.h"
#include "jpegint.h"

int main(void) {
    char *line = NULL;
    size_t cap = 0;
    int bad = 0;
    while (getline(&line, &cap, stdin) >= 0) {
        char *tok[8];
        int nt = split(line, tok, 8);
        if (nt == 0) continue;
        const char *fn = tok[0];
        if (strcmp(fn, "jdiv_round_up") == 0 && nt == 3) {
            long a = (long)parse_i(tok[1]);
            long b = (long)parse_i(tok[2]);
            printf("%ld\n", jdiv_round_up(a, b));
        } else if (strcmp(fn, "jround_up") == 0 && nt == 3) {
            long a = (long)parse_i(tok[1]);
            long b = (long)parse_i(tok[2]);
            printf("%ld\n", jround_up(a, b));
        } else if (strcmp(fn, "jzero_far") == 0 && nt == 2) {
            size_t len = (size_t)parse_u(tok[1]);
            unsigned char *buf = (unsigned char *)malloc(len ? len : 1);
            if (!buf) { fprintf(stderr, "oom\n"); return 2; }
            for (size_t i = 0; i < (len ? len : 1); i++) buf[i] = 0xa5;
            jzero_far(buf, len);
            for (size_t i = 0; i < len; i++) printf("%02x", buf[i]);
            printf(" %zu\n", len);
            free(buf);
        } else if (strcmp(fn, "natural_order") == 0 && nt == 2) {
            size_t idx = (size_t)parse_u(tok[1]);
            if (idx >= DCTSIZE2 + 16) { printf("OOB\n"); bad = 1; continue; }
            printf("%d\n", jpeg_natural_order[idx]);
        } else {
            fprintf(stderr, "unknown function or wrong arity: %s\n", fn);
            printf("BADINPUT\n");
            bad = 1;
        }
    }
    free(line);
    return bad;
}
