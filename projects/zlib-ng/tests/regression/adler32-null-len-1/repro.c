/* Plain regression test (fixed upstream). zlib.h documents that adler32 with a Z_NULL buffer returns the
 * initial value 1, for any length. In zlib-ng 2.3.3 adler32_c tested len == 1 before buf == NULL and read
 * buf[0] through NULL; the current upstream tests buf == NULL in adler32 and adler32_z first. Expected:
 * 1 from both, no sanitizer report. Argument: the length. */
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
