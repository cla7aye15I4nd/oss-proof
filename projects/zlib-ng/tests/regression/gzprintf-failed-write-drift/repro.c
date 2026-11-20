/* Patch 0021. gzvprintf formats into the input buffer at next_in + avail_in and, when the input reaches state->size,
 * compresses state->size bytes from next_in. It relies on next_in + avail_in <= in + size ("the input buffer is
 * double-sized just for this function"). A gz_comp whose write fails returns with next_in moved forward and input left;
 * after gzclearerr the next gzprintf then counts state->size bytes from the moved next_in, so next_in + avail_in passes
 * in + size and grows with each failed round. The formatted text then lands in the output buffer (corrupting the
 * compressed data not yet written) and, a round later, past the end of the buffer block.
 * Documented calls only. The descriptor is the write end of a non-blocking pipe: a write() fails with EAGAIN when
 * the pipe is full, and the program sets the room in the pipe before each call (it fills the pipe with its own bytes
 * in whole pages and reads them back), so each write() either completes or fails without writing anything.
 *   oob:     gzdopen(fd, "wb0"), gzbuffer(file, 262144), gzprintf of 75605 bytes, gzflush(Z_SYNC_FLUSH), gzprintf of
 *            188859 bytes, gzprintf of 102132 bytes (its write fails), gzclearerr, gzprintf of 233532 bytes (one write
 *            succeeds, the next fails), gzclearerr, gzprintf of 176283 bytes, gzprintf of 200000 bytes: the last one
 *            stores next[state->size - 1] beyond the buffer block (heap buffer overflow, gzwrite.c).
 *   corrupt: the same calls up to the gzprintf of 176283 bytes, then gzclose, and the pipe is read and inflated.
 *            Without the patch the gzip stream is damaged (the formatted text overwrote compressed data still in the
 *            output buffer, and the input of the last compression overlaps the output buffer).
 * With patch 0021 both runs end with a valid gzip stream: "<run> close 0 inflate 1 bytes <n> ok" (the formatted
 * text of a gzprintf whose write failed is counted by x.pos but partly dropped, with or without the patch, so <n> is
 * less than the sum of the lengths).
 * On a host that is not Linux (no F_SETPIPE_SZ), write() on the pipe's descriptor is answered as a Linux pipe of 1 MiB
 * answers it here: all the bytes when they fit in the room left, else -1 with EAGAIN. */
#define _GNU_SOURCE                       /* F_SETPIPE_SZ (Linux) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <fcntl.h>
#include <unistd.h>
#include "zlib.h"

#define PAGE 4096
static int rfd, wfd;
static long junk = 0;                      /* bytes of our own at the head of the pipe */
static unsigned char *cap;                 /* the gzip stream read from the pipe */
static long ncap = 0, maxcap = 4 << 20;

#ifndef __linux__
/* Not Linux: the pipe of 1 MiB is modelled in the program (see the top comment). */
#include <dlfcn.h>
static long room = 1 << 20;
static unsigned char *fifo;
static long fhead = 0, ftail = 0;
ssize_t write(int fd, const void *buf, size_t n) {
  if (fd != wfd) {
    ssize_t (*real)(int, const void *, size_t) = (ssize_t (*)(int, const void *, size_t))dlsym(RTLD_NEXT, "write");
    return real(fd, buf, n);
  }
  if ((long)n > room) { errno = EAGAIN; return -1; }
  memcpy(fifo + ftail, buf, n);
  ftail += (long)n; room -= (long)n;
  return (ssize_t)n;
}
static ssize_t pread_fifo(unsigned char *b, size_t n) {
  long k = ftail - fhead < (long)n ? ftail - fhead : (long)n;
  if (k <= 0) return -1;
  memcpy(b, fifo + fhead, (size_t)k);
  fhead += k; room += k;
  return (ssize_t)k;
}
#define read(fd, b, n) pread_fifo(b, n)
#endif

static void drain(long limit) {            /* read up to limit bytes (all if < 0); our own bytes are dropped */
  unsigned char b[PAGE];
  while (limit != 0) {
    long want = limit < 0 || limit > PAGE ? PAGE : limit;
    ssize_t r = read(rfd, b, (size_t)want);
    if (r <= 0) return;
    for (ssize_t i = 0; i < r; i++) {
      if (junk > 0) junk--;
      else if (ncap < maxcap) cap[ncap++] = b[i];
    }
    if (limit > 0) limit -= r;
  }
}

static void fill(void) {                   /* fill the pipe with whole pages of our own bytes */
  unsigned char b[PAGE];
  memset(b, 'j', sizeof b);
  for (;;) {
    ssize_t r = write(wfd, b, sizeof b);
    if (r < 0) return;
    junk += r;
    if (r < PAGE) { printf("partial fill\n"); exit(2); }
  }
}

static char text[262144];
static int pr(gzFile f, size_t len) {
  memset(text, 'a' + (int)(len % 26), len);
  text[len] = 0;
  int r = gzprintf(f, "%s", text);
  gzclearerr(f);
  return r;
}

int main(int argc, char **argv) {
  int oob = argc > 1 && !strcmp(argv[1], "oob");
  int p[2];
  if (pipe(p) != 0) { printf("pipe failed\n"); return 2; }
  rfd = p[0]; wfd = p[1];
#ifdef __linux__
  if (fcntl(wfd, F_SETPIPE_SZ, 1 << 20) < (1 << 20)) { printf("F_SETPIPE_SZ failed\n"); return 2; }
#else
  fifo = malloc(64 << 20);
#endif
  fcntl(wfd, F_SETFL, fcntl(wfd, F_GETFL) | O_NONBLOCK);
  fcntl(rfd, F_SETFL, fcntl(rfd, F_GETFL) | O_NONBLOCK);
  cap = malloc((size_t)maxcap);
  gzFile f = gzdopen(wfd, "wb0");
  if (f == NULL || gzbuffer(f, 262144) != 0) { printf("gzdopen failed\n"); return 2; }
  pr(f, 75605);
  if (gzflush(f, Z_SYNC_FLUSH) != Z_OK) { printf("gzflush failed\n"); return 2; }
  drain(-1);
  pr(f, 188859);
  fill();                                  /* no room: the write fails */
  pr(f, 102132);
  drain(46 * PAGE);                        /* room for one write of up to 46 pages */
  pr(f, 233532);
  pr(f, 176283);
  if (oob) pr(f, 200000);
  drain(-1);                               /* room for the rest */
  int c = gzclose(f);
  drain(-1);
  z_stream s;
  memset(&s, 0, sizeof s);
  inflateInit2(&s, 31);
  static unsigned char out[1 << 21];
  s.next_in = cap; s.avail_in = (uInt)ncap;
  long total = 0;
  int ret;
  do {
    s.next_out = out; s.avail_out = sizeof out;
    ret = inflate(&s, Z_NO_FLUSH);
    total += (long)(sizeof out - s.avail_out);
  } while (ret == Z_OK && s.avail_in > 0);
  int ok = ret == Z_STREAM_END && s.avail_in == 0;
  inflateEnd(&s);
  printf("%s close %d inflate %d bytes %ld %s\n", oob ? "oob" : "corrupt", c, ok, total, ok ? "ok" : "bad");
  return 0;
}
