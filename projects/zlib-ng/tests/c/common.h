/* Shared parsing helpers of the C differential-test drivers. Input format: see tests/README.md and
 * tests/lean/DiffTest/Common.lean. */
#ifndef DIFFTEST_COMMON_H
#define DIFFTEST_COMMON_H
/* zlib.h declares the *64 functions (adler32_combine64, crc32_combine64, ...) only with this. */
#define _LARGEFILE64_SOURCE 1
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>

#define UNUSED __attribute__((unused))

UNUSED static unsigned long long parse_u(const char *s) {
    char *e; errno = 0;
    unsigned long long v = strtoull(s, &e, 10);
    if (*s == '\0' || *e != '\0' || errno || *s == '-') { fprintf(stderr, "bad unsigned %s\n", s); exit(2); }
    return v;
}
UNUSED static long long parse_i(const char *s) {
    char *e; errno = 0;
    long long v = strtoll(s, &e, 10);
    if (*s == '\0' || *e != '\0' || errno) { fprintf(stderr, "bad signed %s\n", s); exit(2); }
    return v;
}
UNUSED static int hexval(int c) {
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    if (c >= 'A' && c <= 'F') return c - 'A' + 10;
    return -1;
}

/* A buffer argument: null:<len> (a NULL pointer passed with <len>), hex:<digits> (a pointer to those
 * bytes) or off:<k>:<digits> (a pointer k bytes into a block of k + n bytes whose last n bytes are the
 * digits). The block is malloc'ed with the exact size (at least one byte, so that the pointer of an empty
 * buffer is not NULL), so a sanitizer sees any read outside it. */
struct buf { unsigned char *block; unsigned char *ptr; size_t len; };

UNUSED static struct buf parse_buf(const char *s) {
    struct buf b = { NULL, NULL, 0 };
    size_t off = 0;
    if (strncmp(s, "null:", 5) == 0) { b.len = (size_t)parse_u(s + 5); return b; }
    if (strncmp(s, "off:", 4) == 0) {
        char *e; errno = 0;
        off = (size_t)strtoull(s + 4, &e, 10);
        if (errno || *e != ':' || e == s + 4) { fprintf(stderr, "bad offset buffer\n"); exit(2); }
        s = e + 1;
    } else if (strncmp(s, "hex:", 4) == 0) {
        s += 4;
    } else { fprintf(stderr, "bad buffer\n"); exit(2); }
    size_t n = strlen(s);
    if (n % 2) { fprintf(stderr, "odd hex\n"); exit(2); }
    b.len = n / 2;
    b.block = malloc(off + b.len ? off + b.len : 1);
    if (!b.block) { fprintf(stderr, "out of memory\n"); exit(2); }
    for (size_t i = 0; i < off; i++) b.block[i] = 0;
    b.ptr = b.block + off;
    for (size_t i = 0; i < b.len; i++) {
        int h = hexval(s[2 * i]), l = hexval(s[2 * i + 1]);
        if (h < 0 || l < 0) { fprintf(stderr, "bad hex digit\n"); exit(2); }
        b.ptr[i] = (unsigned char)(h * 16 + l);
    }
    return b;
}

/* Split a line into at most 8 space-separated fields. */
UNUSED static int split(char *line, char **tok) {
    char *save; int nt = 0;
    for (char *t = strtok_r(line, " \t\r\n", &save); t && nt < 8; t = strtok_r(NULL, " \t\r\n", &save))
        tok[nt++] = t;
    return nt;
}

#endif
