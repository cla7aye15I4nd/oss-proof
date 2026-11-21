/* Patch 0002 follows zlib (madler/zlib 6995c67b and 6ed77c48): a seek that gzseek refuses returns -1 and leaves the
 * stream position unchanged (zlib.h: "If gzseek returns -1, the stream position is unchanged."). Without the patch a
 * SEEK_CUR refused because its target lies before the start drops the pending skip (on a reader and on a writer: gztell
 * and the next read or write then differ), and after gzungetc at position 0 a SEEK_SET to a negative offset is not
 * refused: it consumes pushed-back bytes and returns a negative position. This is a change of behaviour, not a defect:
 * the case checks that each run prints the line of the documented behaviour with the patch and upstream's line
 * without it. Documented calls only.
 *   read:  a gzip file of 1000 bytes 'a' + i % 26; gzseek(100, SEEK_SET), gzseek(-200, SEEK_CUR) (before the
 *          start: -1), gztell, gzgetc.
 *   write: a gzip writer on a file; gzseek(10, SEEK_SET), gzseek(-20, SEEK_CUR) (-1), gztell, gzputc, gzclose,
 *          the length of the data read back.
 *   unget: a gzip file of 1000 bytes; gzungetc('x'), gzungetc('y') at position 0 (position -2), gzseek(-1,
 *          SEEK_SET), gztell, gzgetc, gzgetc.
 *   raw:   the same on a file that is not gzip (copy mode). */
#include <stdio.h>
#include <string.h>
#include "zlib.h"
static const char *path = "gzseek-refusal-state.gz";
static int make(int gz) {
  char buf[1000];
  for (int i = 0; i < 1000; i++) buf[i] = (char)('a' + i % 26);
  if (!gz) {
    FILE *o = fopen(path, "wb");
    if (o == NULL || fwrite(buf, 1, 1000, o) != 1000) return -1;
    return fclose(o);
  }
  gzFile w = gzopen(path, "wb");
  if (w == NULL || gzwrite(w, buf, 1000) != 1000) return -1;
  return gzclose(w);
}
int main(int argc, char **argv) {
  const char *run = argc > 1 ? argv[1] : "read";
  if (strcmp(run, "write") == 0) {
    gzFile f = gzopen(path, "wb");
    if (f == NULL) { printf("gzopen failed\n"); return 2; }
    long long s1 = (long long)gzseek(f, 10, SEEK_SET);
    long long s2 = (long long)gzseek(f, -20, SEEK_CUR);
    long long t = (long long)gztell(f);
    int p = gzputc(f, 'z');
    int c = gzclose(f);
    char buf[64];
    gzFile r = gzopen(path, "rb");
    int n = r == NULL ? -9 : gzread(r, buf, sizeof buf);
    if (r != NULL) gzclose(r);
    printf("write seek %lld %lld tell %lld putc %d close %d length %d\n", s1, s2, t, p, c, n);
    return 0;
  }
  int raw = strcmp(run, "raw") == 0;
  if (make(!raw) != 0) { printf("setup failed\n"); return 2; }
  gzFile f = gzopen(path, "rb");
  if (f == NULL) { printf("gzopen failed\n"); return 2; }
  if (strcmp(run, "read") == 0) {
    long long s1 = (long long)gzseek(f, 100, SEEK_SET);
    long long s2 = (long long)gzseek(f, -200, SEEK_CUR);
    long long t = (long long)gztell(f);
    int c = gzgetc(f);
    printf("read seek %lld %lld tell %lld getc %d\n", s1, s2, t, c);
  } else {
    int u1 = gzungetc('x', f);
    int u2 = gzungetc('y', f);
    long long t0 = (long long)gztell(f);
    long long s = (long long)gzseek(f, -1, SEEK_SET);
    long long t = (long long)gztell(f);
    int c1 = gzgetc(f);
    int c2 = gzgetc(f);
    printf("%s unget %d %d tell %lld seek %lld tell %lld getc %d %d\n", run, u1, u2, t0, s, t, c1, c2);
  }
  gzclose(f);
  return 0;
}
