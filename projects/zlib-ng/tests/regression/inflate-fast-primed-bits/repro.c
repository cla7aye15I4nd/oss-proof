/* Patch 0007. inflatePrime puts 32 bits into the bit buffer of a raw inflate: a final fixed-code block that is
 * only an end-of-block code (10 bits), then 22 zero bits. inflate decodes the block header and enters
 * inflate_fast with 29 bits held, which assumes fewer than 8. On return inflate_fast gives back bits >> 3 bytes
 * of input, more than it read, so next_in moves 2 bytes before the caller's buffer (ISO C17 6.5.6p8) and
 * avail_in grows past what the caller gave. Comparing next_in with the buffer would itself be undefined, so the
 * case reports avail_in and total_in: "inflate 1 34 4294967294" without the patch, "inflate 1 32 0" with it. */
#include <stdio.h>
#include <string.h>
#include "zlib.h"
int main(void) {
  static unsigned char in[32], out[1000];
  z_stream s;
  memset(&s, 0, sizeof s);
  if (inflateInit2(&s, -15) != Z_OK) return 2;
  if (inflatePrime(&s, 16, 3) != Z_OK || inflatePrime(&s, 16, 0) != Z_OK) return 2;
  s.next_in = in;
  s.avail_in = sizeof in;
  s.next_out = out;
  s.avail_out = sizeof out;
  int r = inflate(&s, Z_NO_FLUSH);
  printf("inflate %d %u %lu\n", r, s.avail_in, s.total_in);
  inflateEnd(&s);
  return 0;
}
