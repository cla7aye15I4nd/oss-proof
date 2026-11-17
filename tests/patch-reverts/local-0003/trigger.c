/* local-0003: a transparent read whose read() returns some bytes and then fails.
 * gzbuffer(f, 16) makes the output buffer 32 bytes. 48 gzgetc calls on a 128-byte raw file use up
 * the first two 32-byte loads exactly: x.have is 0 and x.next is one past the buffer. Then read()
 * returns one byte and fails with EIO. In the COPY case of gz_fetch, gz_load stores x.have = 1 and
 * returns -1. Without patch 0003, gz_fetch returns before it sets x.next = out, and gzread copies
 * one byte from the stale x.next, past the output buffer.
 * The read() defined here replaces the one of the C library for the static libz.a; until `inject`
 * is set it forwards to the next read(). */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <errno.h>
#include <stdio.h>
#include <unistd.h>
#include "zlib.h"

static int inject;

ssize_t read(int fd, void *buf, size_t count) {
    static ssize_t (*next)(int, void *, size_t);
    static int fired;
    if (next == NULL) next = (ssize_t (*)(int, void *, size_t))dlsym(RTLD_NEXT, "read");
    if (inject) {
        if (fired++) { errno = EIO; return -1; }
        return next(fd, buf, count > 1 ? 1 : count);
    }
    return next(fd, buf, count);
}

int main(void) {
    static const unsigned char zeros[128];
    unsigned char buf[1];
    FILE *raw = fopen("raw.dat", "wb");
    if (raw == NULL || fwrite(zeros, 1, sizeof zeros, raw) != sizeof zeros || fclose(raw) != 0) return 2;
    gzFile f = gzopen("raw.dat", "rb");
    if (f == NULL) return 2;
    int b = gzbuffer(f, 16), got = 0;
    for (int i = 0; i < 48; i++)
        got += (gzgetc)(f) == 0;
    inject = 1;
    int n = gzread(f, buf, 1), err;
    gzerror(f, &err);
    int c = gzclose(f);
    printf("buffer=%d getc=%d read=%d err=%d close=%d\n", b, got, n, err, c);
    return 0;
}
