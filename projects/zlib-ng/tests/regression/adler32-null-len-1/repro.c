/* Patch 0007. zlib.h documents that adler32 with a Z_NULL buffer returns the initial value 1, for any
 * length; adler32_c tests len == 1 before buf == NULL and reads buf[0] through NULL. Unpatched: an
 * AddressSanitizer report (a load through NULL). Patched: 1. Argument: the length. */
#include <stdio.h>
#include <stdlib.h>
#include "zlib.h"
int main(int argc, char **argv) {
  if (argc != 2) return 2;
  unsigned n = (unsigned)strtoul(argv[1], NULL, 10);
  printf("adler %lu\n", adler32(1, Z_NULL, n));
  printf("adler_z %lu\n", adler32_z(1, Z_NULL, n));
  return 0;
}
