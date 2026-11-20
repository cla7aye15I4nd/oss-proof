/* Patch 0004. gzseek64 normalizes and applies the offset in signed 64-bit arithmetic without bounds. Each run
 * reaches one overflow (ISO C17 §6.5p5) through documented calls; with the patch the seek is refused (-1) without a
 * report, or (lseek) takes the rewind path:
 *   cur:   a writer, gzseek(INT64_MAX, SEEK_SET), gzseek(1, SEEK_CUR): offset += skip overflows. The file is not
 *          closed: gzclose would write the INT64_MAX zero bytes the first seek requested.
 *   set:   a reader of a file that is not gzip, gzungetc at position 0 (x.pos -1), gzseek(INT64_MAX, SEEK_SET):
 *          offset -= x.pos overflows.
 *   pos:   a transparent reader of /dev/zero, gzseek(INT64_MAX - 1, SEEK_SET), gzseek(5, SEEK_CUR): the test of the
 *          raw area computes x.pos + offset, which overflows.
 *   lseek: a transparent reader of /dev/zero with output buffered at a position near INT64_MAX, gzseek(0, SEEK_SET):
 *          the lseek offset offset - x.have overflows. With the patch the seek rewinds instead.
 * The last two need Linux /dev/zero, whose lseek returns 0 without moving and whose reads never end; on a system
 * whose /dev/zero lseek does not behave so, the repro answers lseek on its descriptor as Linux does. */
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <fcntl.h>
#include <unistd.h>
#include "zlib.h"
#ifndef __linux__
static int zfd = -1;
off_t lseek(int fd, off_t off, int whence) {
  if (fd == zfd) return 0;   /* Linux /dev/zero: zero_lseek */
  (void)off; (void)whence;
  return -1;
}
#endif
static gzFile zero(void) {
  int fd = open("/dev/zero", O_RDONLY);
#ifndef __linux__
  zfd = fd;
#endif
  return gzdopen(fd, "r");
}
int main(int argc, char **argv) {
  const char *run = argc > 1 ? argv[1] : "cur";
  if (strcmp(run, "cur") == 0) {
    gzFile f = gzopen("/dev/null", "wb");
    if (f == NULL) { printf("gzopen failed\n"); return 2; }
    z_off_t a = gzseek(f, INT64_MAX, SEEK_SET);
    printf("seek1 %lld\n", (long long)a);
    z_off_t b = gzseek(f, 1, SEEK_CUR);
    printf("seek2 %lld\n", (long long)b);
  } else if (strcmp(run, "set") == 0) {
    FILE *o = fopen("gzseek-offset-overflow.dat", "wb");
    if (o == NULL || fputs("hello", o) < 0 || fclose(o) != 0) { printf("setup failed\n"); return 2; }
    gzFile f = gzopen("gzseek-offset-overflow.dat", "rb");
    if (f == NULL) { printf("gzopen failed\n"); return 2; }
    int u = gzungetc('x', f);
    long long s = (long long)gzseek(f, INT64_MAX, SEEK_SET);
    printf("set unget %d seek %lld tell %lld getc %d\n", u, s, (long long)gztell(f), gzgetc(f));
    gzclose(f);
  } else if (strcmp(run, "pos") == 0) {
    gzFile f = zero();
    if (f == NULL) { printf("gzdopen failed\n"); return 2; }
    int c = gzgetc(f);
    long long s1 = (long long)gzseek(f, INT64_MAX - 1, SEEK_SET);
    long long s2 = (long long)gzseek(f, 5, SEEK_CUR);
    printf("pos getc %d seek %lld seek %lld tell %lld\n", c, s1, s2, (long long)gztell(f));
    gzclose(f);
  } else {
    gzFile f = zero();
    if (f == NULL || gzbuffer(f, 8) != 0) { printf("gzdopen failed\n"); return 2; }
    int c1 = gzgetc(f);
    long long s1 = (long long)gzseek(f, INT64_MAX - 10, SEEK_SET);
    int c2 = gzgetc(f);
    long long s2 = (long long)gzseek(f, 0, SEEK_SET);
    printf("lseek getc %d seek %lld getc %d seek %lld tell %lld\n", c1, s1, c2, s2, (long long)gztell(f));
    gzclose(f);
  }
  return 0;
}
