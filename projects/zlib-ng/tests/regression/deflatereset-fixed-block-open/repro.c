/* Open defect, not patched (functional, no memory error). deflate_quick with strategy Z_FIXED (level 1) opens one
 * static block (block_open = 1) and keeps it open until a flush or the end of the stream. block_open is cleared
 * only by deflateInit2, not by deflateReset (deflateResetKeep + lm_init), so after deflateReset the next stream's
 * deflate_quick continues the old static block: its symbols follow the fresh zlib header without a block header.
 * inflate rejects the result. Calls: deflateInit2(level 1, Z_FIXED), deflate(Z_NO_FLUSH) of 3000 bytes,
 * deflateReset, deflate(Z_FINISH) of 1000 bytes, inflate of that output. */
#include <stdio.h>
#include <string.h>
#include "zlib.h"
int main(void) {
  static unsigned char in[3000], out[20000], back[3000];
  for (int k = 0; k < 3000; k++) in[k] = (unsigned char)("abcdefghij"[(k * 7) % 10]);
  z_stream s;
  memset(&s, 0, sizeof s);
  if (deflateInit2(&s, 1, Z_DEFLATED, 15, 8, Z_FIXED) != Z_OK) return 2;
  s.next_in = in; s.avail_in = 3000; s.next_out = out; s.avail_out = sizeof out;
  int r1 = deflate(&s, Z_NO_FLUSH);
  int r2 = deflateReset(&s);
  s.next_in = in; s.avail_in = 1000; s.next_out = out; s.avail_out = sizeof out;
  int r3 = deflate(&s, Z_FINISH);
  unsigned long len = s.total_out;
  deflateEnd(&s);
  z_stream t;
  memset(&t, 0, sizeof t);
  if (inflateInit(&t) != Z_OK) return 2;
  t.next_in = out; t.avail_in = (unsigned)len; t.next_out = back; t.avail_out = sizeof back;
  int r4 = inflate(&t, Z_FINISH);
  int same = r4 == Z_STREAM_END && t.total_out == 1000 && memcmp(back, in, 1000) == 0;
  inflateEnd(&t);
  printf("deflate %d %d %d %lu inflate %d %d\n", r1, r2, r3, len, r4, same);
  return 0;
}
