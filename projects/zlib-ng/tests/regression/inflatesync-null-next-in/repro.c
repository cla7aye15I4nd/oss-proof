/* Patch 0005. With no input (next_in == NULL, avail_in == 0) but 16 bits primed by inflatePrime,
 * inflateSync runs strm->next_in += len with len == 0: NULL + 0 (ISO C17 6.5.6p8). No sanitizer reports
 * NULL + 0 in C, so this case cannot show the defect: it only checks that the call sequence runs and returns
 * the same values with and without the patch (prime 0, sync -3) and leaves next_in NULL. */
#include <stdio.h>
#include <string.h>
#include "zlib.h"
int main(void) {
  z_stream s;
  memset(&s, 0, sizeof s);
  if (inflateInit(&s) != Z_OK) return 2;
  printf("prime %d\n", inflatePrime(&s, 16, 0x1234));
  int r = inflateSync(&s);
  printf("sync %d %d\n", r, s.next_in == NULL);
  inflateEnd(&s);
  return 0;
}
