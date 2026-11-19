/* Patch 0001. gzbuffer accepts a size up to INT_MAX; the first write then doubles it in int
 * (gz_buffer_alloc: want * 2) and zng_alloc_aligned wraps its 32-bit size, allocates too little and
 * writes the saved pointer outside the block. Unpatched: a sanitizer report. Patched: gzbuffer refuses
 * the size (-1) and the write succeeds with the default buffer. */
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
