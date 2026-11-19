/* Open defect (no patch). A gzwrite of at least the buffer size takes the direct path of gz_write: it points
 * strm.next_in at the caller's buffer. When writing to the file fails, gz_comp returns with avail_in still nonzero,
 * so next_in keeps pointing into the caller's buffer after gzwrite has returned. After gzclearerr, the next small
 * gzwrite computes (next_in + avail_in) - state->in, a subtraction of pointers into different objects (ISO C17
 * §6.5.6p9), takes the result as the fill level of the input buffer and copies to state->in + that amount: a write
 * outside the buffer. The descriptor is opened read-only, so every write() fails (EBADF). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <fcntl.h>
#include "zlib.h"
int main(void) {
  int fd = open("/dev/null", O_RDONLY);
  gzFile f = gzdopen(fd, "wT");
  if (f == NULL) { printf("gzdopen failed\n"); return 2; }
  gzbuffer(f, 8);
  char *big = malloc(100);
  memset(big, 'a', 100);
  int r1 = gzwrite(f, big, 100);
  int err;
  gzerror(f, &err);
  gzclearerr(f);
  int r2 = gzwrite(f, "x", 1);
  printf("gzwrite %d %d %d\n", r1, err, r2);
  free(big);
  return 0;
}
