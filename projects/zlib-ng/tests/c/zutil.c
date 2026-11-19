/* C side of the differential test for zutil.c: links the REAL patched zlib-ng (verified configuration).
 * Input and output formats: see tests/README.md. zcalloc, zcfree, zng_alloc_aligned and zng_free_aligned
 * are internal (hidden visibility) but have external linkage in the static library. */
#include "common.h"
#include <stdint.h>
#include "zlib.h"

void *zcalloc(void *opaque, unsigned items, unsigned size);
void zcfree(void *opaque, void *ptr);
void *zng_alloc_aligned(unsigned size, unsigned align);
void zng_free_aligned(void *ptr);

int main(void) {
    char *line = NULL; size_t cap = 0;
    int bad = 0;
    while (getline(&line, &cap, stdin) >= 0) {
        char *tok[8]; int nt = split(line, tok);
        if (nt == 0) continue;
        const char *fn = tok[0];
        if (strcmp(fn, "zlibVersion") == 0 && nt == 1) {
            printf("[%s]\n", zlibVersion());
        } else if (strcmp(fn, "zlibCompileFlags") == 0 && nt == 1) {
            printf("%lu\n", zlibCompileFlags());
        } else if (strcmp(fn, "zError") == 0 && nt == 2) {
            long long e = parse_i(tok[1]);
            if (e < INT32_MIN || e > INT32_MAX) { fprintf(stderr, "does not fit int\n"); exit(2); }
            printf("[%s]\n", zError((int)e));
        } else if (strcmp(fn, "zcalloc_free") == 0 && nt == 3) {
            unsigned items = (unsigned)parse_u(tok[1]), size = (unsigned)parse_u(tok[2]);
            size_t n = (size_t)items * (size_t)size;
            unsigned char *p = zcalloc(NULL, items, size);
            if (!p) { printf("null\n"); continue; }
            unsigned long long sum = 0;
            for (size_t i = 0; i < n; i++) p[i] = (unsigned char)(i * 31 + 7);
            for (size_t i = 0; i < n; i++) sum += p[i];
            zcfree(NULL, p);
            printf("%zu %llu\n", n, sum);
        } else if (strcmp(fn, "zng_alloc_aligned") == 0 && nt == 3) {
            unsigned size = (unsigned)parse_u(tok[1]), align = (unsigned)parse_u(tok[2]);
            unsigned char *p = zng_alloc_aligned(size, align);
            if (!p) { printf("null\n"); continue; }
            int aligned = (uintptr_t)p % align == 0;
            unsigned long long sum = 0;
            for (size_t i = 0; i < size; i++) p[i] = (unsigned char)(i * 13 + 5);
            for (size_t i = 0; i < size; i++) sum += p[i];
            zng_free_aligned(p);
            printf("ok %d %u %llu\n", aligned, size, sum);
        } else if (strcmp(fn, "zng_free_aligned_null") == 0 && nt == 1) {
            zng_free_aligned(NULL);
            printf("ok\n");
        } else {
            fprintf(stderr, "unknown function or wrong arity: %s\n", fn);
            printf("BADINPUT\n");
            bad = 1;
        }
    }
    free(line);
    return bad;
}
