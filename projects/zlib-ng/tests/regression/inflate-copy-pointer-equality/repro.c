/* Patch 0001. inflateCopy tests whether state->lencode points into the state with a >= / <= range test;
 * after a fixed-code block lencode points into the static fixed table, so the test compares pointers into
 * different objects (ISO C17 6.5.8p5). Unpatched: an AddressSanitizer invalid-pointer-pair report (with
 * -fsanitize=pointer-compare and detect_invalid_pointer_pairs=2). Patched: no report. */
#include <stdio.h>
#include <string.h>
#include "zlib.h"
int main(void) {
  unsigned char src[4096], comp[8192], out[16];
  for (int i = 0; i < 4096; i++) src[i] = (unsigned char)(i * 7);
  z_stream d; memset(&d, 0, sizeof d);
  if (deflateInit2(&d, 6, Z_DEFLATED, 15, 8, Z_FIXED) != Z_OK) return 2;
  d.next_in = src; d.avail_in = sizeof src; d.next_out = comp; d.avail_out = sizeof comp;
  deflate(&d, Z_FINISH);
  unsigned clen = (unsigned)(sizeof comp - d.avail_out);
  deflateEnd(&d);
  z_stream s, c; memset(&s, 0, sizeof s);
  if (inflateInit(&s) != Z_OK) return 2;
  s.next_in = comp; s.avail_in = clen; s.next_out = out; s.avail_out = sizeof out;
  int r = inflate(&s, Z_NO_FLUSH);
  printf("inflate %d\n", r);
  r = inflateCopy(&c, &s);
  printf("inflateCopy %d\n", r);
  inflateEnd(&c); inflateEnd(&s);
  return 0;
}
