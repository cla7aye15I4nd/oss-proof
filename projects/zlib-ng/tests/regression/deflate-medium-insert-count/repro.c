/* Patch 0010. deflateTune stores max_lazy unchanged; deflate_medium (levels 3-6) uses it as the insert count
 * max_insert_count and computes max_len = 2 * max_insert_count in 32-bit unsigned, which is 0 for
 * max_lazy = INT_MIN. A match at distance 1 (a run of equal bytes) then leaves one position to hash, and
 * insert_knuth_stepped divides by inserts - 1 = 0 (insert_string_p.h:186, ISO C17 6.5.5p5). */
#include <stdio.h>
#include <string.h>
#include <limits.h>
#include "zlib.h"
int main(void) {
  static unsigned char in[4096], out[8192];
  memset(in, 'a', sizeof in);
  z_stream s;
  memset(&s, 0, sizeof s);
  if (deflateInit(&s, 4) != Z_OK) return 2;
  printf("tune %d\n", deflateTune(&s, 8, INT_MIN, 128, 128));
  s.next_in = in; s.avail_in = sizeof in; s.next_out = out; s.avail_out = sizeof out;
  int r = deflate(&s, Z_FINISH);
  printf("deflate %d %lu\n", r, s.total_out);
  deflateEnd(&s);
  return 0;
}
