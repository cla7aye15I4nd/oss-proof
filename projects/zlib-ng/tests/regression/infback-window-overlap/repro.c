/* Patch 0007 with inflateBack. inflateBack decodes into the caller's window and calls inflate_fast_safe with
 * next_out inside that window, so there inflate_fast's output IS the window (beg == window). A first version of
 * patch 0007 copied every match that reaches back into the window with memcpy(out, from, n), which assumes that
 * the window and the output are distinct objects (true for inflate, whose window is its own allocation). Here
 * from = window + wsize - op and out = window + k: when the match reaches into the previous pass of the window
 * and wsize - dist < n, the two ranges overlap, and memcpy with overlapping ranges is undefined (ISO C17
 * 7.24.2.1p2; AddressSanitizer reports memcpy-param-overlap; a copy onto itself, dist == wsize, is undefined as
 * well but not reported). Patch 0007 now copies with memcpy only when window != beg, and with upstream's
 * chunkcopy_safe, which handles the overlap, when window == beg. Upstream without patch 0007 is clean here too.
 *
 * Arguments: windowBits k dist len. The stream (fixed codes, one block): 2^windowBits literals (the window is
 * written out once), k more literals, a match of length len at distance dist (so op = dist - k bytes come from
 * the previous pass of the window), 40 literals, end of block. The output is checked against the expected
 * bytes. Output without a report: "back 1 <total> 1". Streams that zlib's deflate makes with the same window
 * never do this: their distances are at most wsize - 262. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "zlib.h"

static unsigned char *stream;
static size_t slen;
static unsigned long acc;
static int nacc;

static void put(unsigned v, int n) {
  acc |= (unsigned long)v << nacc; nacc += n;
  while (nacc >= 8) { stream[slen++] = (unsigned char)acc; acc >>= 8; nacc -= 8; }
}
static void huff(unsigned code, int n) { /* Huffman codes go most significant bit first */
  unsigned r = 0;
  for (int i = 0; i < n; i++) r = (r << 1) | ((code >> i) & 1);
  put(r, n);
}
static void lit(unsigned v) { /* fixed literal/length code */
  if (v < 144) huff(0x30 + v, 8);
  else if (v < 256) huff(0x190 + v - 144, 9);
  else if (v < 280) huff(v - 256, 7);
  else huff(0xc0 + v - 280, 8);
}
static void length(unsigned len) { /* 3..258 */
  static const unsigned base[] = {3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67,
                                  83, 99, 115, 131, 163, 195, 227, 258};
  static const int extra[] = {0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0};
  int c = 28;
  while (base[c] > len) c--;
  lit(257 + (unsigned)c);
  put(len - base[c], extra[c]);
}
static void distance(unsigned dist) { /* 1..32768 */
  static const unsigned base[] = {1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769,
                                  1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577};
  int c = 29;
  while (base[c] > dist) c--;
  huff((unsigned)c, 5);
  put(dist - base[c], c < 4 ? 0 : c / 2 - 1);
}

static unsigned char *expect, *got;
static size_t nexpect, ngot;
static unsigned in_cb(void *d, z_const unsigned char **buf) {
  int *done = d;
  if (*done) return 0;
  *done = 1;
  *buf = stream;
  return (unsigned)slen;
}
static int out_cb(void *d, unsigned char *buf, unsigned len) {
  (void)d;
  memcpy(got + ngot, buf, len);
  ngot += len;
  return 0;
}

int main(int argc, char **argv) {
  if (argc != 5) return 2;
  int wbits = atoi(argv[1]);
  unsigned k = (unsigned)atoi(argv[2]), dist = (unsigned)atoi(argv[3]), len = (unsigned)atoi(argv[4]);
  unsigned wsize = 1U << wbits;
  if (wbits < 8 || wbits > 15 || dist < 1 || dist > wsize || len < 3 || len > 258) return 2;
  size_t total = wsize + k + len + 40;
  stream = malloc(2 * total + 16);
  expect = malloc(total);
  got = malloc(total);
  if (stream == NULL || expect == NULL || got == NULL) return 2;
  put(1, 1); put(1, 2);                            /* last block, fixed codes */
  for (size_t i = 0; i < wsize + k; i++) {
    expect[nexpect] = (unsigned char)((i * 7 + i / 251) & 255);
    lit(expect[nexpect++]);
  }
  length(len); distance(dist);
  for (unsigned i = 0; i < len; i++, nexpect++) expect[nexpect] = expect[nexpect - dist];
  for (int i = 0; i < 40; i++) lit(expect[nexpect++] = 65);
  lit(256);
  if (nacc) stream[slen++] = (unsigned char)acc;
  unsigned char *window = malloc(wsize);
  if (window == NULL) return 2;
  z_stream s;
  memset(&s, 0, sizeof s);
  if (inflateBackInit(&s, wbits, window) != Z_OK) return 2;
  int done = 0;
  s.next_in = NULL;
  int ret = inflateBack(&s, in_cb, &done, out_cb, NULL);
  printf("back %d %zu %d\n", ret, ngot, ngot == nexpect && memcmp(got, expect, nexpect) == 0);
  inflateBackEnd(&s);
  free(window);
  free(stream);
  free(expect);
  free(got);
  return 0;
}
