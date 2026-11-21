/* Patch 0012. gz_buffer_alloc gets the in/out buffers from zng_alloc_aligned and then computes
 * state->out = state->buffers + in_size before it checks the result: when the allocation fails, that is NULL plus
 * a nonzero offset (ISO C17 §6.5.6p8). gzbuffer(file, 1 << 30), which zlib.h allows, asks for 3 GiB on the first
 * write; the sanitizer's allocator is set to refuse blocks above 1 GiB and return NULL, as malloc does when memory
 * is short. clang's UBSan reports it; GCC's does not report NULL plus an
 * offset, so there run.sh only checks that the unpatched build runs alike. With patch 0012 the null check comes
 * first: "gzwrite 0 0 -4 -4". */
#include <stdio.h>
#include "zlib.h"
const char *__asan_default_options(void) { return "allocator_may_return_null=1:max_allocation_size_mb=1024"; }
int main(void) {
  gzFile f = gzopen("/dev/null", "wb");
  if (f == NULL) { printf("gzopen failed\n"); return 2; }
  int b = gzbuffer(f, 1u << 30);
  int w = gzwrite(f, "abc", 3);
  int err;
  gzerror(f, &err);
  int c = gzclose(f);
  printf("gzwrite %d %d %d %d\n", b, w, err, c);
  return 0;
}
