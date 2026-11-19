/* Patch 0007. inflate copies a match that reaches back into the sliding window with chunkcopy_safe
 * (inflate.c, MATCH state), and inflate_fast copies it with CHUNKCOPY_SAFE / chunkcopy_safe; these compare
 * and subtract a pointer into the window (inside inflate's own allocation) and a pointer into the caller's
 * output buffer: relational comparison and subtraction of pointers into different objects (ISO C17
 * 6.5.8p5, 6.5.6p9). A valid zlib stream with matches into the window, inflated with a small output buffer
 * per call, reaches it. Unpatched: an AddressSanitizer invalid-pointer-pair report (with
 * -fsanitize=pointer-compare,pointer-subtract and detect_invalid_pointer_pairs=2). Patched: no report, and
 * the output is the original data ("inflate 1 1"). Argument: output bytes per inflate() call. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "zlib.h"
int main(int argc, char **argv) {
  size_t chunk = argc > 1 ? (size_t)atoi(argv[1]) : 1;
  static unsigned char src[100000], comp[200000];
  for (int i = 0; i < 100000; i++) src[i] = (unsigned char)("abcdefghij"[i % 10] + (i / 5000));
  uLongf clen = sizeof comp;
  if (compress2(comp, &clen, src, sizeof src, 6) != Z_OK) return 2;
  z_stream s;
  memset(&s, 0, sizeof s);
  if (inflateInit(&s) != Z_OK) return 2;
  unsigned char *out = malloc(sizeof src);
  if (out == NULL) return 2;
  s.next_in = comp;
  s.avail_in = (uInt)clen;
  s.next_out = out;
  int ret = Z_OK;
  while (ret == Z_OK) {
    size_t room = sizeof src - (size_t)(s.next_out - out);
    s.avail_out = (uInt)(room < chunk ? room : chunk);
    ret = inflate(&s, Z_NO_FLUSH);
  }
  printf("inflate %d %d\n", ret, s.total_out == sizeof src && memcmp(out, src, sizeof src) == 0);
  inflateEnd(&s);
  free(out);
  return 0;
}
