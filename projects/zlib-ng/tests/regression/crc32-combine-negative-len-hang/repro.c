/* Plain regression test (fixed upstream). In zlib-ng 2.3.3 crc32_combine_gen / crc32_combine with a
 * negative len2 looped forever in x2nmodp; the current upstream returns 0 for len2 < 0. Expected: each
 * returns 0. Argument: g (gen) or c (combine). The argument o (crc32_combine_op with op == 0) still does
 * not return: zlib.h only allows an op made by crc32_combine_gen from a non-negative length, which is
 * never 0, so it is not run. */
#include <stdio.h>
#include "zlib.h"
int main(int argc, char **argv) {
  if (argc != 2) return 2;
  if (argv[1][0] == 'g') printf("gen %lu\n", crc32_combine_gen(-1));
  if (argv[1][0] == 'o') printf("op %lu\n", crc32_combine_op(1, 2, 0));
  if (argv[1][0] == 'c') printf("comb %lu\n", crc32_combine(1, 2, -1));
  return 0;
}
