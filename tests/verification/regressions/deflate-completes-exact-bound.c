/* Regression for the statement correction of Goal.deflate_completes_default
 * (ZlibF/Spec/Functional/RoundTrip.lean). The old premise allowed room equal to the rest of the
 * bound: unsaturatedBound(n) <= delivered + avail_out. A default stream can be exactly
 * compressBound(n) bytes long: n = 16383 * 200 + 100 bytes in which no 3-byte string repeats
 * within 65536 positions give no match, every block is stored (16383 + 5 bytes each, the final one
 * 100 + 5), and 2 + 200 * 16388 + 105 + 4 = n + 1011 = compressBound(n). A first deflate(Z_FINISH)
 * with room compressBound(n) - 1 returns Z_OK with one trailer byte pending. A second one with room
 * 1 (so the room premise holds with equality) delivers that byte, has no room left, and returns
 * Z_OK (deflate.c: "if (strm->avail_out == 0) { s->last_flush = -1; return Z_OK; }" after the
 * pending flush), not Z_STREAM_END. Room 2 ends the stream. One call from a fresh stream with
 * exactly deflateBound(n) room ends it (Goal.deflate_bound_default is not affected).
 * Build against zlib/ with the patches of patches/ applied. Expected output:
 *   n=3276700 compressBound=3277711 deflateBound=3277711
 *   equal room: call 1 rc=0 out=3277710, call 2 (room 1) rc=0 out=3277711
 *   more room: call 1 rc=0, call 2 (room 2) rc=1 out=3277711
 *   fresh: one call with deflateBound room rc=1 out=3277711
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "zlib.h"

static long last[1 << 24];

static unsigned char *nomatch(size_t want) {
  unsigned char *out = malloc(want);
  for (long i = 0; i < (1L << 24); i++) last[i] = -1000000;
  unsigned long x = 88172645463325252UL;
  for (size_t i = 0; i < want; i++) {
    for (;;) {
      x ^= x << 13; x ^= x >> 7; x ^= x << 17;
      unsigned char c = (unsigned char)(x >> 24);
      if (i >= 2) {
        long key = ((long)out[i - 2] << 16) | ((long)out[i - 1] << 8) | c;
        if ((long)i - last[key] < 65536) continue;
        last[key] = (long)i;
      }
      out[i] = c;
      break;
    }
  }
  return out;
}

static int finish(z_stream *s, unsigned char *out, size_t at, uInt room) {
  s->next_out = out + at; s->avail_out = room;
  return deflate(s, Z_FINISH);
}

int main(void) {
  unsigned long n = 16383UL * 200 + 100;
  unsigned char *in = nomatch(n);
  unsigned long bound = compressBound(n);
  unsigned char *out = malloc(bound + 64);
  z_stream s; memset(&s, 0, sizeof s);
  if (deflateInit(&s, Z_DEFAULT_COMPRESSION) != Z_OK) return 2;
  printf("n=%lu compressBound=%lu deflateBound=%lu\n", n, bound, deflateBound(&s, n));
  s.next_in = in; s.avail_in = (uInt)n;
  int r1 = finish(&s, out, 0, (uInt)(bound - 1));
  unsigned long o1 = s.total_out;
  int r2 = finish(&s, out, o1, 1);
  printf("equal room: call 1 rc=%d out=%lu, call 2 (room 1) rc=%d out=%lu\n", r1, o1, r2, s.total_out);
  deflateEnd(&s);

  memset(&s, 0, sizeof s);
  deflateInit(&s, Z_DEFAULT_COMPRESSION);
  s.next_in = in; s.avail_in = (uInt)n;
  r1 = finish(&s, out, 0, (uInt)(bound - 1));
  r2 = finish(&s, out, s.total_out, 2);
  printf("more room: call 1 rc=%d, call 2 (room 2) rc=%d out=%lu\n", r1, r2, s.total_out);
  deflateEnd(&s);

  memset(&s, 0, sizeof s);
  deflateInit(&s, Z_DEFAULT_COMPRESSION);
  s.next_in = in; s.avail_in = (uInt)n;
  int r = finish(&s, out, 0, (uInt)deflateBound(&s, n));
  printf("fresh: one call with deflateBound room rc=%d out=%lu\n", r, s.total_out);
  deflateEnd(&s);
  return 0;
}
