/* Patch 0018. A pending seek on a reader of a file that is not gzip: gzdirect (patch 0017) skips the 3 bytes the
 * file holds, and the read that follows them returns 0, so the end of file is set and the rest of the skip stays
 * pending. Then the file grows (another writer appends to it). gzgets does the pending skip first: gz_skip stops at
 * once, at the end of file, with the skip still pending. gzgets then calls gz_fetch anyway, which in copy mode
 * reads again although the end of file was set, gets the appended bytes and returns them, adding 3 to x.pos while
 * the skip is still pending: x.pos + skip passes GZ_OFF_MAX, and gztell adds the two: signed overflow (ISO C17
 * §6.5p5) in gztell64. gzgets also returns bytes from before the position sought.
 * With patch 0018 gzgets does not fetch while a skip is pending: it reports the end of file (NULL), and gztell
 * returns 3: "seek 9223372036854775807 direct 1 gets null tell 3". */
#include <stdio.h>
#include <stdint.h>
#include "zlib.h"
int main(void) {
  FILE *o = fopen("gzgets-pending-skip.txt", "wb");
  if (o == NULL) { printf("fopen failed\n"); return 2; }
  fputs("abc", o);
  fclose(o);
  gzFile f = gzopen("gzgets-pending-skip.txt", "rb");
  if (f == NULL) { printf("gzopen failed\n"); return 2; }
  long long s = (long long)gzseek(f, INT64_MAX, SEEK_SET);
  int d = gzdirect(f);
  o = fopen("gzgets-pending-skip.txt", "ab");
  if (o == NULL) { printf("fopen failed\n"); return 2; }
  fputs("de\n", o);
  fclose(o);
  char buf[16];
  char *g = gzgets(f, buf, sizeof buf);
  long long t = (long long)gztell(f);
  printf("seek %lld direct %d gets %s tell %lld\n", s, d, g == NULL ? "null" : "data", t);
  gzclose(f);
  return 0;
}
