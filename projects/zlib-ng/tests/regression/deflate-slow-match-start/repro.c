/* Patch 0016. At levels 7 and 8, deflate_slow takes a match whose start is at or after strstart. After a
 * Z_FULL_FLUSH that empties the lookahead (or deflateReset), strstart restarts at 0 and head is cleared, but prev keeps
 * positions of the earlier input. Levels 2-6 do not insert every position of a long match, so their slots keep those
 * positions, and deflateParams from 2-6 to 7 or 8 does not rebuild the chains. The offset search of
 * longest_match_slow_knuth_c reads prev inside a match, and the chain walk after it (match_tpl.h: the walk of the
 * best_len >= 8 prefilter and the peeled walk for best_len < 8) does not test cur_match >= strstart again, so a stale
 * position ahead of strstart whose bytes match is accepted. deflate_slow then tallies the distance
 * strstart - 1 - prev_match, which wraps: d_code reads far outside dist_code, and the output decodes to wrong data.
 * One raw stream: level L1 on input A with Z_FULL_FLUSH, more input at L1 with Z_NO_FLUSH, deflateParams(L2), the
 * rest with Z_FINISH; then inflate and compare. Usage: repro <seed>; the inputs are generated from the seed. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "zlib.h"
static unsigned long long rs;
static unsigned rnd(void) { rs = rs * 6364136223846793005ULL + 1442695040888963407ULL; return (unsigned)(rs >> 33); }
static unsigned char a[70000], b[70000], all[140000], comp[1 << 18], back[140000];
int main(int argc, char **argv) {
  unsigned long long seed = argc > 1 ? strtoull(argv[1], 0, 10) : 362;
  rs = seed * 7919 + 3;
  int la = 2 + rnd() % 5, lb = 7 + rnd() % 2, alpha1 = 2 + rnd() % 6, alpha2 = 2 + rnd() % 4;
  int mode = rnd() % 2; (void)mode;
  size_t na = 33000 + rnd() % 31000, nb = 34000 + rnd() % 30000, sa = 2000 + rnd() % 20000;
  for (size_t k = 0; k < na; k++) a[k] = 'a' + rnd() % alpha1;
  size_t k = 0;
  while (k < sa) {
    size_t run = 300 + rnd() % 3000, txt = 10 + rnd() % 300; int per = 1 + rnd() % 12;
    unsigned char pat[16]; for (int j = 0; j < per; j++) pat[j] = 'a' + rnd() % alpha2;
    for (size_t j = 0; j < run && k < sa; j++) b[k++] = pat[j % per];
    for (size_t j = 0; j < txt && k < sa; j++) b[k++] = 'a' + rnd() % alpha2;
  }
  while (k < nb) {
    int kind = rnd() % 3;
    if (kind == 0) { size_t off = rnd() % sa, len = 4 + rnd() % 8; for (size_t j = 0; j < len && k < nb; j++) b[k++] = b[off + j]; if (k < nb) b[k++] = 'a' + rnd() % (alpha2 + 1); }
    else if (kind == 1) { size_t len = 1 + rnd() % 40; for (size_t j = 0; j < len && k < nb; j++) b[k++] = 'a' + rnd() % alpha2; }
    else { size_t off = rnd() % k, len = 3 + rnd() % 30; for (size_t j = 0; j < len && k < nb; j++, k++) b[k] = b[off + j]; }
  }
  z_stream s; memset(&s, 0, sizeof s);
  if (deflateInit2(&s, la, Z_DEFLATED, -15, 8, Z_DEFAULT_STRATEGY) != Z_OK) return 2;
  s.next_out = comp; s.avail_out = sizeof comp;
  s.next_in = a; s.avail_in = (unsigned)na;
  int r1 = deflate(&s, Z_FULL_FLUSH);
  s.next_in = b; s.avail_in = (unsigned)sa;
  int r2 = deflate(&s, Z_NO_FLUSH);
  int r3 = deflateParams(&s, lb, Z_DEFAULT_STRATEGY);
  s.next_in = b + sa; s.avail_in = (unsigned)(nb - sa);
  int r4 = deflate(&s, Z_FINISH);
  unsigned long clen = s.total_out;
  deflateEnd(&s);
  printf("levels %d->%d sizes %zu+%zu+%zu deflate %d %d params %d finish %d out %lu\n", la, lb, na, sa, nb - sa, r1, r2, r3, r4, clen);
  memcpy(all, a, na); memcpy(all + na, b, nb);
  z_stream t; memset(&t, 0, sizeof t);
  if (inflateInit2(&t, -15) != Z_OK) return 2;
  t.next_in = comp; t.avail_in = (unsigned)clen; t.next_out = back; t.avail_out = sizeof back;
  int ri = inflate(&t, Z_FINISH);
  int same = t.total_out == na + nb && memcmp(back, all, na + nb) == 0;
  printf("inflate %d%s%s out %lu of %zu round-trip %s\n", ri, t.msg ? " msg " : "", t.msg ? t.msg : "", t.total_out, na + nb, same ? "ok" : "MISMATCH");
  inflateEnd(&t);
  return same ? 0 : 1;
}
