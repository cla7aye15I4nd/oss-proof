/* df84af2: a stalled large gzwrite on a non-blocking descriptor (CVE-2026-85091).
 * A transparent writer with gzbuffer(f, 64) gets a gzwrite of 100 bytes, which is compressed (here
 * written) directly from the caller's buffer. write() fails once with EAGAIN. Before the fix,
 * next_in still points into the caller's buffer, with avail_in 100. The next small gzwrite
 * computes its copy position as next_in + avail_in - in, the difference of pointers into
 * different objects, copies its byte there and counts it in avail_in. gzclose then writes the 101
 * bytes from next_in: one byte past the caller's buffer.
 * The write() defined here replaces the one of the C library for the static libz.a; while `inject`
 * is set it fails once with EAGAIN. */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include "zlib.h"

static int inject;

ssize_t write(int fd, const void *buf, size_t count) {
    static ssize_t (*next)(int, const void *, size_t);
    if (next == NULL) next = (ssize_t (*)(int, const void *, size_t))dlsym(RTLD_NEXT, "write");
    if (inject) { inject = 0; errno = EAGAIN; return -1; }
    return next(fd, buf, count);
}

int main(void) {
    gzFile f = gzopen("out.dat", "wT");
    if (f == NULL) return 2;
    int b = gzbuffer(f, 64);
    unsigned char *big = malloc(100);
    memset(big, 'A', 100);
    inject = 1;
    int w1 = gzwrite(f, big, 100);
    int w2 = gzwrite(f, "x", 1);
    int c = gzclose(f);
    free(big);
    FILE *out = fopen("out.dat", "rb");
    long size = -1;
    if (out != NULL && fseek(out, 0, SEEK_END) == 0) size = ftell(out);
    if (out != NULL) fclose(out);
    printf("buffer=%d write100=%d write1=%d close=%d file=%ld\n", b, w1, w2, c, size);
    return 0;
}
