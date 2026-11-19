/* Open defect of the verified source (patch 0007 with inflateBack). inflateBack decodes into the caller's window
 * and calls inflate_fast_safe with next_out inside that window, so inflate_fast's output IS the window. Patch 0007
 * made inflate_fast copy a match that reaches back into the window with memcpy(out, from, n), which assumes that
 * the window and the output are distinct objects. Here from = window + wsize - op and out = window + k: when the
 * match reaches into the previous pass of the window and dist + min(op, len) > wsize, the two ranges overlap, and
 * memcpy with overlapping ranges is undefined (ISO C17 7.24.2.1p2). Without patch 0007 the copy goes through
 * chunkcopy_safe, which handles the overlap. The stream: a 256-byte window (windowBits 8), 356 literals (the window
 * is written out once), then a match of length 150 at distance 200 at window offset 100: op = 100, the source is
 * window[156, 256) and the destination window[100, 200). AddressSanitizer reports memcpy-param-overlap. (A match
 * at distance exactly wsize copies a range onto itself, memcpy(p, p, n): also undefined, but AddressSanitizer does
 * not report a copy onto itself.) Streams that zlib's deflate makes with the same window never do this: their
 * distances are at most wsize - 262. Output without a report: "back 1 546". */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "zlib.h"

static unsigned char stream[1024];
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

static unsigned char *data;
static unsigned in_cb(void *d, z_const unsigned char **buf) {
  int *done = d;
  if (*done) return 0;
  *done = 1;
  *buf = data;
  return (unsigned)slen;
}
static unsigned long total;
static int out_cb(void *d, unsigned char *buf, unsigned len) { (void)d; (void)buf; total += len; return 0; }

int main(void) {
  put(1, 1); put(1, 2);                            /* last block, fixed codes */
  for (int i = 0; i < 256; i++) lit((unsigned)(i * 7) & 255);
  for (int i = 0; i < 100; i++) lit((unsigned)(i * 3 + 1) & 255);
  lit(257 + 24); put(150 - 131, 5);                /* length 150: code 281, base 131, 5 extra bits */
  huff(15, 5); put(200 - 193, 6);                  /* distance 200: code 15, base 193, 6 extra bits */
  for (int i = 0; i < 40; i++) lit(65);
  lit(256);
  if (nacc) stream[slen++] = (unsigned char)acc;
  data = malloc(slen);
  if (data == NULL) return 2;
  memcpy(data, stream, slen);
  unsigned char *window = malloc(256);
  if (window == NULL) return 2;
  z_stream s;
  memset(&s, 0, sizeof s);
  if (inflateBackInit(&s, 8, window) != Z_OK) return 2;
  int done = 0;
  s.next_in = NULL;
  int ret = inflateBack(&s, in_cb, &done, out_cb, NULL);
  printf("back %d %lu\n", ret, total);
  inflateBackEnd(&s);
  free(window);
  free(data);
  return 0;
}
