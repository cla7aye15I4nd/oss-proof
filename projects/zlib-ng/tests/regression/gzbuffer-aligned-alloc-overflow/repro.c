/* Plain regression test (fixed upstream). In zlib-ng 2.3.3 gzbuffer accepted a size up to INT_MAX; the
 * first write then doubled it in int (gz_buffer_alloc: want * 2) and zng_alloc_aligned wrapped its 32-bit
 * size, allocated too little and wrote the saved pointer outside the block. The current upstream clamps
 * the size to GZBUFSIZE_MAX (1 GiB), so every buffer size fits. Expected: the write succeeds without a
 * sanitizer report. */
#include <stdio.h>
#include "zlib.h"
int main(void) {
  gzFile f = gzopen("/dev/null", "wb");
  if (f == NULL) { printf("gzopen failed\n"); return 2; }
  int r = gzbuffer(f, 0x55555540u);
  printf("gzbuffer %d\n", r);
  r = gzwrite(f, "a", 1);
  printf("gzwrite %d\n", r);
  gzclose(f);
  return 0;
}
