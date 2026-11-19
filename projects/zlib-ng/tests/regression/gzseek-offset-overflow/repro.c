/* Patch 0004. gzseek64 on a write stream adds the requested offset to the current position in signed
 * 64-bit arithmetic. Unpatched: a signed integer overflow report. Patched: the second seek is refused (-1)
 * without a report. The file is not closed: gzclose would write the INT64_MAX zero bytes the first seek
 * requested. */
#include <stdio.h>
#include <stdint.h>
#include "zlib.h"
int main(void) {
  gzFile f = gzopen("/dev/null", "wb");
  if (f == NULL) { printf("gzopen failed\n"); return 2; }
  z_off_t a = gzseek(f, INT64_MAX, SEEK_SET);
  printf("seek1 %lld\n", (long long)a);
  z_off_t b = gzseek(f, 1, SEEK_CUR);
  printf("seek2 %lld\n", (long long)b);
  return 0;
}
