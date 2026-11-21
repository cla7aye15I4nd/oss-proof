/* Patch 0009. In the slow longest-match search of levels 7-9 (match_tpl.h), a lazy search that finds an older
 * chain for a substring of the current match moved the match base back: mbase_start -= match_offset and
 * mbase_start = window - match_offset. alloc_deflate puts the window at the start of its block (after at most
 * 63 bytes of alignment padding) and match_offset reaches 256, so the pointer is formed before the start of the
 * allocated object (ISO C17 6.5.6p8). Nothing is read through it out of bounds and no sanitizer reports forming
 * it, so this case cannot show the defect: it runs the two deflate calls of the finding (levels 9, 70000 bytes of
 * mixed random, text and periodic data) and checks that the output (length, CRC-32) is the same with and
 * without the patch. Argument: "f" (windowBits 15, memLevel 4, Z_FILTERED) or "x" (gzip, memLevel 1, Z_FIXED). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include "zlib.h"
int main(int argc, char **argv) {
  int gz = argc > 1 && strcmp(argv[1], "x") == 0;
  uint32_t seed = gz ? 1314757043u : 261107360u, x = seed | 1u;
  size_t n = 70000;
  unsigned char *in = malloc(n), *out = malloc(2 * n + 1000);
  static const char alpha[] = "etaoin shrdlu\n";
  for (size_t i = 0; i < n; i++) {
    x ^= x << 13; x ^= x >> 17; x ^= x << 5;
    switch ("rtpz"[(i / 1000) % 4]) {
    case 'r': in[i] = (unsigned char)(x & 0xff); break;
    case 't': in[i] = (unsigned char)alpha[x % 14]; break;
    case 'p': in[i] = (unsigned char)((i % (1 + seed % 61)) * 7 + 3); break;
    default: in[i] = 0;
    }
  }
  z_stream s;
  memset(&s, 0, sizeof s);
  if (deflateInit2(&s, 9, Z_DEFLATED, gz ? 31 : 15, gz ? 1 : 4, gz ? Z_FIXED : Z_FILTERED) != Z_OK) return 2;
  s.next_in = in; s.avail_in = (uInt)n; s.next_out = out; s.avail_out = (uInt)(2 * n + 1000);
  int r = deflate(&s, Z_FINISH);
  printf("deflate %d %lu %08lx\n", r, s.total_out, crc32(0, out, (uInt)s.total_out));
  deflateEnd(&s);
  free(in); free(out);
  return 0;
}
