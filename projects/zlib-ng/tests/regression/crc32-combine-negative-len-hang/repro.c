/* Patch 0002. crc32_combine_gen / crc32_combine with a negative len2 loop forever in x2nmodp, and
 * crc32_combine_op with op == 0 loops forever in multmodp. Unpatched: the call does not return (the
 * runner stops it after a timeout). Patched: each returns 0. Argument: g (gen), o (op) or c (combine). */
#include <stdio.h>
#include "zlib.h"
int main(int argc, char **argv) {
  if (argc != 2) return 2;
  if (argv[1][0] == 'g') printf("gen %lu\n", crc32_combine_gen(-1));
  if (argv[1][0] == 'o') printf("op %lu\n", crc32_combine_op(1, 2, 0));
  if (argv[1][0] == 'c') printf("comb %lu\n", crc32_combine(1, 2, -1));
  return 0;
}
