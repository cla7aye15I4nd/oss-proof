/* Patch 0018. fill_window lowers block_start by slide_len at every slide (deflate.c:1274); only a block flush
 * (FLUSH_BLOCK*, quick_end_block) raises it again. Two call sequences go 2^31 bytes without one, and take
 * block_start below INT_MIN (signed integer overflow, ISO C17 6.5p5):
 *   f: deflate_quick with strategy Z_FIXED (level 1) emits static-tree symbols into one block that stays open
 *      until a flush or the end of the stream: one Z_NO_FLUSH stream of 2^31 + 2^22 bytes (1 MiB chunks of
 *      low-entropy data), output discarded, then Z_FINISH;
 *   r: deflateResetKeep drops the tallied symbols but keeps strstart, block_start and the window, so rounds of
 *      fewer symbols than fill a block never flush one: level 6, raw, memLevel 9, 600 rounds of 4 MiB of zeros
 *      under Z_NO_FLUSH, each followed by deflateResetKeep.
 * Each run takes about 20 s under the sanitizers of run.sh; the runner runs `f` only (`r` prints
 * "resetkeep 600" with every patch and shows the same report without patch 0018). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "zlib.h"
int main(int argc, char **argv) {
  static unsigned char in[1 << 20], out[1 << 20];
  z_stream s;
  memset(&s, 0, sizeof s);
  if (argc > 1 && argv[1][0] == 'r') {
    unsigned char *zeros = calloc(4u << 20, 1);
    if (zeros == NULL) return 2;
    if (deflateInit2(&s, 6, Z_DEFLATED, -15, 9, Z_DEFAULT_STRATEGY) != Z_OK) return 2;
    int round;
    for (round = 0; round < 600; round++) {
      s.next_in = zeros; s.avail_in = 4u << 20;
      while (s.avail_in) {
        s.next_out = out; s.avail_out = sizeof out;
        if (deflate(&s, Z_NO_FLUSH) != Z_OK) return 3;
      }
      if (deflateResetKeep(&s) != Z_OK) return 4;
    }
    printf("resetkeep %d\n", round);
    deflateEnd(&s);
    free(zeros);
    return 0;
  }
  for (size_t k = 0; k < sizeof in; k++) in[k] = (unsigned char)(((k * 2654435761u) >> 24) & 3);
  if (deflateInit2(&s, 1, Z_DEFLATED, 15, 8, Z_FIXED) != Z_OK) return 2;
  unsigned long long total = (1ULL << 31) + (1ULL << 22), fed = 0;
  while (fed < total) {
    s.next_in = in; s.avail_in = sizeof in; fed += sizeof in;
    do {
      s.next_out = out; s.avail_out = sizeof out;
      if (deflate(&s, Z_NO_FLUSH) == Z_STREAM_ERROR) return 3;
    } while (s.avail_in != 0);
  }
  int r;
  do { s.next_out = out; s.avail_out = sizeof out; r = deflate(&s, Z_FINISH); } while (r == Z_OK);
  printf("deflate %d %llu\n", r, (unsigned long long)s.total_in);
  deflateEnd(&s);
  return 0;
}
