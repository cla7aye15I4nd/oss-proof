/* Patch 0009. zlib.h documents Z_STREAM_ERROR for a NULL dictionary. On a raw stream,
 * inflateSetDictionary(strm, NULL, 0) instead calls updatewindow with end = NULL + 0, computes end - 0 and
 * calls memcpy from NULL with length 0 (ISO C17 6.5.6p8, 7.24.1p2), and returns Z_OK. No sanitizer reports
 * these in C; the case shows the behaviour: unpatched "setdict 0", patched "setdict -2". */
#include <stdio.h>
#include <string.h>
#include "zlib.h"
int main(void) {
  z_stream s;
  memset(&s, 0, sizeof s);
  if (inflateInit2(&s, -15) != Z_OK) return 2;
  printf("setdict %d\n", inflateSetDictionary(&s, NULL, 0));
  inflateEnd(&s);
  return 0;
}
