/* Patch 0002 refuses every gzseek64 whose arithmetic would overflow, and on every other call runs upstream's
 * statements: the results and the state afterwards are upstream's. Documented calls only. The first version of
 * patch 0002 (first-0002.patch here) computed the target position up front and returned -1 before upstream's own
 * steps, so on well-defined calls it changed the state afterwards: a refused SEEK_CUR kept the pending skip that
 * upstream drops, and a SEEK_SET to a negative offset at a negative position (after gzungetc at the start) was
 * refused where upstream skips. Each run prints the results of its calls; without patch 0002 and with every patch
 * they must be the same line, and with first-0002.patch they differ.
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
