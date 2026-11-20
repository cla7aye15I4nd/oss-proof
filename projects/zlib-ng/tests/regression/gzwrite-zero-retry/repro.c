/* Patch 0019. gz_zero, which writes the zeros of a forward gzseek on a writer, adds each batch to x.pos before it
 * writes the batch and takes it off the pending skip only after the write succeeded. When the write fails, the
 * batch is counted in x.pos and still in the skip: x.pos + skip passes the position gzseek returned (which patch
 * 0002 keeps at most GZ_OFF_MAX). Documented calls only; the write fails because the descriptor is the write end
 * of a non-blocking pipe that is full (EAGAIN), and succeeds after the reader drains it.
 *   max:   gzseek(file, INT64_MAX, SEEK_SET), a failed gzwrite, then gztell computes x.pos + skip =
 *          INT64_MAX + 4096: signed overflow (ISO C17 §6.5p5) in gztell64.
 *          With patch 0019: "max seek 9223372036854775807 write 0 tell 9223372036854775807".
 *   retry: gzseek(file, 10000, SEEK_SET), a failed gzwrite of "abc", gztell, the reader drains the pipe,
 *          gzclearerr, the same gzwrite again, gztell, gzclose, and the reader reads the file. Without the patch the
 *          4096 zeros of the failed batch are written twice: the file has 14099 bytes and gztell says 14096, then
 *          14099, for a seek to 10000 (a wrong result, no undefined behaviour). With patch 0019:
 *          "retry seek 10000 write 0 tell 10000 write 3 tell 10003 close 0 bytes 10003 ok". */
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <errno.h>
#include <fcntl.h>
#include <unistd.h>
#include "zlib.h"

static int fill(int wfd) {               /* fill the pipe until write() fails with EAGAIN */
  char junk[512];
  memset(junk, 'x', sizeof junk);
  for (;;) {
    ssize_t r = write(wfd, junk, sizeof junk);
    if (r < 0) return errno == EAGAIN ? 0 : -1;
    if (r < (ssize_t)sizeof junk) {      /* partial: the next write fails */
      if (write(wfd, junk, 1) < 0 && errno == EAGAIN) return 0;
    }
  }
}

static long drain(int rfd, unsigned char *keep, long cap, int *ok) {   /* read until EAGAIN or end of file */
  unsigned char b[4096];
  long n = 0;
  for (;;) {
    ssize_t r = read(rfd, b, sizeof b);
    if (r <= 0) return n;
    if (keep) {
      for (ssize_t i = 0; i < r; i++) {
        if (n + i < cap) keep[n + i] = b[i];
        else *ok = 0;
      }
    }
    n += r;
  }
}

int main(int argc, char **argv) {
  int retry = argc > 1 && !strcmp(argv[1], "retry");
  int p[2];
  if (pipe(p) != 0) { printf("pipe failed\n"); return 2; }
  fcntl(p[1], F_SETFL, fcntl(p[1], F_GETFL) | O_NONBLOCK);
  fcntl(p[0], F_SETFL, fcntl(p[0], F_GETFL) | O_NONBLOCK);
  if (fill(p[1]) != 0) { printf("fill failed\n"); return 2; }
  gzFile f = gzdopen(p[1], "wT");
  if (f == NULL || gzbuffer(f, 4096) != 0) { printf("gzdopen failed\n"); return 2; }
  if (!retry) {
    long long s = (long long)gzseek(f, INT64_MAX, SEEK_SET);
    int w = gzwrite(f, "abc", 3);
    long long t = (long long)gztell(f);
    printf("max seek %lld write %d tell %lld\n", s, w, t);
    gzclose(f);
    return 0;
  }
  long long s = (long long)gzseek(f, 10000, SEEK_SET);
  int w1 = gzwrite(f, "abc", 3);
  long long t1 = (long long)gztell(f);
  int ok = 1;
  drain(p[0], NULL, 0, &ok);              /* the junk that filled the pipe */
  gzclearerr(f);
  int w2 = gzwrite(f, "abc", 3);
  long long t2 = (long long)gztell(f);
  int c = gzclose(f);                     /* closes the write end */
  fcntl(p[0], F_SETFL, fcntl(p[0], F_GETFL) & ~O_NONBLOCK);
  static unsigned char got[20000];
  long n = drain(p[0], got, sizeof got, &ok);
  if (n != 10003) ok = 0;
  for (long i = 0; ok && i < 10000; i++) if (got[i] != 0) ok = 0;
  if (ok && memcmp(got + 10000, "abc", 3) != 0) ok = 0;
  printf("retry seek %lld write %d tell %lld write %d tell %lld close %d bytes %ld %s\n", s, w1, t1, w2, t2, c, n,
         ok ? "ok" : "bad");
  return 0;
}
