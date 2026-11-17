/* Regression for the write region of inflateGetDictionary and deflateGetDictionary
 * (StreamWriteRegions, ZlibF/Spec/Common/Sequences.lean). The region was 32768 bytes at the
 * dictionary pointer for both calls, while the caller's buffer only needs the dictionary length
 * (inflate: whave; deflate: min(w_size, strstart + lookahead)). The C writes exactly that many
 * bytes, and nothing when the pointer is NULL or the length is 0. Each case below places the
 * caller's buffer of exactly the dictionary length at the start of a 32768 + 4096 byte block filled
 * with a guard byte, and checks that the bytes written are the dictionary and that no byte after
 * the buffer changed: the old region admitted a change of those bytes. The exact-length cases also
 * run on a malloc'ed buffer of exactly that length, for the sanitizers. The inflate cases withhold
 * the 4-byte check value, so that the call stops in CHECK with all output in the window (the call
 * that passes CHECK does not add its own output to the window).
 * Build against zlib/ with the patches of patches/ applied (with -fsanitize=address,undefined).
 * Expected output (one line per case, then "all cases pass"):
 *   inflate n=100: len=100 dict ok guard ok
 *   inflate NULL: rc=0 len=100
 *   inflate fresh: len=0 guard ok
 *   inflate n=40000 (wrapped window): len=32768 dict ok guard ok
 *   inflate windowBits=9 n=1000: len=512 dict ok guard ok
 *   deflate n=100: len=100 dict ok guard ok
 *   deflate NULL: rc=0 len=100
 *   deflate fresh: len=0 guard ok
 *   deflate n=70000: len=32768 dict ok guard ok
 *   deflate setDictionary n=300: len=300 dict ok guard ok
 *   all cases pass
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "zlib.h"

#define BLOCK (32768 + 4096)
#define GUARD 0xA5

static int failures = 0;

static unsigned char *data(size_t n) {
  unsigned char *d = malloc(n ? n : 1);
  unsigned long x = 2463534242UL;
  for (size_t i = 0; i < n; i++) {
    x ^= x << 13; x ^= x >> 17; x ^= x << 5;
    d[i] = (unsigned char)(x % 7 == 0 ? 'a' : x);
  }
  return d;
}

/* The block holds the caller's buffer of `len` bytes; check the dictionary and the guard. */
static void check(const char *name, const unsigned char *block, uInt len,
                  const unsigned char *expect, uInt want) {
  int dictOk = len == want && (len == 0 || memcmp(block, expect, len) == 0);
  int guardOk = 1;
  for (size_t i = want; i < BLOCK; i++)
    if (block[i] != GUARD) { guardOk = 0; break; }
  if (want == 0)
    printf("%s: len=%u guard %s\n", name, len, guardOk ? "ok" : "CHANGED");
  else
    printf("%s: len=%u dict %s guard %s\n", name, len, dictOk ? "ok" : "WRONG",
           guardOk ? "ok" : "CHANGED");
  if (!dictOk || !guardOk) failures++;
}

static void inflate_case(const char *name, int wbits, size_t n, int exact) {
  unsigned char *src = data(n);
  uLong bound = compressBound(n);
  unsigned char *comp = malloc(bound);
  z_stream d; memset(&d, 0, sizeof d);
  deflateInit2(&d, Z_DEFAULT_COMPRESSION, Z_DEFLATED, wbits, 8, Z_DEFAULT_STRATEGY);
  d.next_in = src; d.avail_in = (uInt)n; d.next_out = comp; d.avail_out = (uInt)bound;
  deflate(&d, Z_FINISH);
  uLong clen = d.total_out;
  deflateEnd(&d);
  z_stream s; memset(&s, 0, sizeof s);
  inflateInit2(&s, wbits);
  unsigned char *out = malloc(n ? n : 1);
  if (n) {
    s.next_in = comp; s.avail_in = (uInt)clen - 4; s.next_out = out; s.avail_out = (uInt)n;
    if (inflate(&s, Z_NO_FLUSH) != Z_OK) { printf("%s: inflate failed\n", name); failures++; }
  }
  uInt w = 1U << wbits, want = n < w ? (uInt)n : w;
  const unsigned char *expect = src + n - want;
  unsigned char *block = malloc(BLOCK);
  memset(block, GUARD, BLOCK);
  uInt len = 12345;
  inflateGetDictionary(&s, block, &len);
  check(name, block, len, expect, want);
  if (exact && want) {
    unsigned char *buf = malloc(want);
    inflateGetDictionary(&s, buf, &len);
    if (memcmp(buf, expect, want) != 0) { printf("%s: exact buffer WRONG\n", name); failures++; }
    free(buf);
  }
  inflateEnd(&s);
  free(block); free(out); free(comp); free(src);
}

static void deflate_case(const char *name, size_t n, int viaSetDictionary) {
  unsigned char *src = data(n);
  uLong bound = compressBound(n);
  unsigned char *comp = malloc(bound);
  z_stream d; memset(&d, 0, sizeof d);
  deflateInit(&d, Z_DEFAULT_COMPRESSION);
  if (viaSetDictionary) {
    deflateSetDictionary(&d, src, (uInt)n);
  } else if (n) {
    d.next_in = src; d.avail_in = (uInt)n; d.next_out = comp; d.avail_out = (uInt)bound;
    deflate(&d, Z_FINISH);
  }
  uInt want = n < 32768 ? (uInt)n : 32768;
  const unsigned char *expect = src + n - want;
  unsigned char *block = malloc(BLOCK);
  memset(block, GUARD, BLOCK);
  uInt len = 12345;
  deflateGetDictionary(&d, block, &len);
  check(name, block, len, expect, want);
  if (want) {
    unsigned char *buf = malloc(want);
    deflateGetDictionary(&d, buf, &len);
    if (memcmp(buf, expect, want) != 0) { printf("%s: exact buffer WRONG\n", name); failures++; }
    free(buf);
  }
  deflateEnd(&d);
  free(block); free(comp); free(src);
}

int main(void) {
  inflate_case("inflate n=100", 15, 100, 1);
  {
    unsigned char *src = data(100), comp[256];
    uLongf clen = sizeof comp;
    compress(comp, &clen, src, 100);
    unsigned char out[100];
    z_stream s; memset(&s, 0, sizeof s);
    inflateInit(&s);
    s.next_in = comp; s.avail_in = (uInt)clen - 4; s.next_out = out; s.avail_out = 100;
    inflate(&s, Z_NO_FLUSH);
    uInt len = 12345;
    int rc = inflateGetDictionary(&s, Z_NULL, &len);
    printf("inflate NULL: rc=%d len=%u\n", rc, len);
    if (rc != Z_OK || len != 100) failures++;
    inflateEnd(&s);
    free(src);
  }
  inflate_case("inflate fresh", 15, 0, 1);
  inflate_case("inflate n=40000 (wrapped window)", 15, 40000, 1);
  inflate_case("inflate windowBits=9 n=1000", 9, 1000, 1);
  deflate_case("deflate n=100", 100, 0);
  {
    unsigned char *src = data(100), comp[256];
    z_stream d; memset(&d, 0, sizeof d);
    deflateInit(&d, Z_DEFAULT_COMPRESSION);
    d.next_in = src; d.avail_in = 100; d.next_out = comp; d.avail_out = sizeof comp;
    deflate(&d, Z_FINISH);
    uInt len = 12345;
    int rc = deflateGetDictionary(&d, Z_NULL, &len);
    printf("deflate NULL: rc=%d len=%u\n", rc, len);
    if (rc != Z_OK || len != 100) failures++;
    deflateEnd(&d);
    free(src);
  }
  deflate_case("deflate fresh", 0, 0);
  deflate_case("deflate n=70000", 70000, 0);
  deflate_case("deflate setDictionary n=300", 300, 1);
  if (failures) { printf("%d failures\n", failures); return 1; }
  printf("all cases pass\n");
  return 0;
}
