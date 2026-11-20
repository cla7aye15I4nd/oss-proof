/* Patch 0003. deflateBound adds 2 + extra_len for a user gzip header with an extra field, computed in
 * 32-bit unsigned int, so extra_len = 0xffffffff adds 1 while deflate writes 2 + (extra_len & 0xffff)
 * = 65537 header bytes. zlib.h promises that one deflate(Z_FINISH) call with avail_out at least
 * deflateBound returns Z_STREAM_END. Unpatched: it does not (the line "bound-ok 0"). Patched: it does
 * ("bound-ok 1"). The extra field is 4 GiB of reserved (untouched) memory, as zlib.h requires extra_len
 * readable bytes; deflate reads only the first 65535. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include "zlib.h"
int main(void) {
  z_stream s;
  gz_header head;
  size_t xlen = (size_t)0xffffffffu;
  unsigned char *extra = mmap(NULL, xlen, PROT_READ, MAP_PRIVATE | MAP_ANON, -1, 0);
  if (extra == MAP_FAILED) { printf("mmap failed\n"); return 2; }
  memset(&s, 0, sizeof s);
  memset(&head, 0, sizeof head);
  head.extra = extra;
  head.extra_len = 0xffffffffu;
  if (deflateInit2(&s, 6, Z_DEFLATED, 31, 8, Z_DEFAULT_STRATEGY) != Z_OK) return 2;
  if (deflateSetHeader(&s, &head) != Z_OK) return 2;
  unsigned char in[1] = {'a'};
  unsigned long bound = deflateBound(&s, sizeof in);
  unsigned char *out = malloc(bound);
  if (out == NULL) return 2;
  s.next_in = in; s.avail_in = sizeof in;
  s.next_out = out; s.avail_out = (unsigned)bound;
  int ret = deflate(&s, Z_FINISH);
  printf("bound-ok %d\n", ret == Z_STREAM_END);
  deflateEnd(&s);
  free(out);
  munmap(extra, xlen);
  return 0;
}
