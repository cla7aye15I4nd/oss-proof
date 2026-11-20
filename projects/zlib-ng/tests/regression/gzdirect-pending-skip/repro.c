/* Patch 0020. gzseek on a reader only records the skip (x.have is 0 afterwards). gzdirect then calls gz_look,
 * which, for a file that is not gzip, copies the input it read into the output buffer: x.have becomes nonzero
 * while the skip is still pending. gzgetc takes a byte from the output buffer without checking for a skip request
 * (the function and the gzgetc() macro of zlib.h alike) and adds 1 to x.pos, so x.pos + skip passes GZ_OFF_MAX;
 * gztell adds the two: signed overflow (ISO C17 §6.5p5) in gztell64. Without a sanitizer gzgetc also returns
 * the first byte of the file instead of the byte at the position sought.
 * With patch 0020 gzdirect skips the buffered bytes the pending seek covers: x.have is 0 again, gzgetc reaches the
 * end of the file and returns -1, and gztell returns 13 (the end): "seek 9223372036854775807 direct 1 getc -1 tell 13". */
#include <stdio.h>
#include <stdint.h>
#include "zlib.h"
int main(void) {
  FILE *o = fopen("gzdirect-pending-skip.txt", "wb");
  if (o == NULL) { printf("fopen failed\n"); return 2; }
  fputs("hello, world\n", o);
  fclose(o);
  gzFile f = gzopen("gzdirect-pending-skip.txt", "rb");
  if (f == NULL) { printf("gzopen failed\n"); return 2; }
  long long s = (long long)gzseek(f, INT64_MAX, SEEK_SET);
  int d = gzdirect(f);
  int c = gzgetc(f);
  long long t = (long long)gztell(f);
  printf("seek %lld direct %d getc %d tell %lld\n", s, d, c, t);
  gzclose(f);
  return 0;
}
