/* Open defect (no patch). The readers add to the signed 64-bit position x.pos without a bound. On a descriptor whose
 * lseek succeeds without moving and which always has data, such as Linux /dev/zero (lseek returns 0, read returns
 * zeros), a transparent read followed by gzseek(file, INT64_MAX, SEEK_SET) sets x.pos to INT64_MAX (the seek is
 * within the raw area, gzseek64 calls lseek and adds the offset); the next gzread adds the bytes it delivers:
 * signed overflow (ISO C17 §6.5p5) in gz_read. On a system whose /dev/zero lseek does not behave as Linux's, the
 * repro answers lseek on its descriptor as Linux does (returns 0); read is the system's. */
#include <stdio.h>
#include <stdint.h>
#include <fcntl.h>
#include <unistd.h>
#include "zlib.h"
#ifndef __linux__
#include <sys/syscall.h>
static int zfd = -1;
off_t lseek(int fd, off_t off, int whence) {
  if (fd == zfd) return 0;   /* Linux /dev/zero: zero_lseek */
  (void)off; (void)whence;
  return -1;
}
#endif
int main(void) {
  int fd = open("/dev/zero", O_RDONLY);
#ifndef __linux__
  zfd = fd;
#endif
  gzFile f = gzdopen(fd, "r");
  if (f == NULL) { printf("gzdopen failed\n"); return 2; }
  int c = gzgetc(f);
  long long s = (long long)gzseek(f, INT64_MAX, SEEK_SET);
  unsigned char buf[4];
  int r = gzread(f, buf, 4);
  printf("gzread %d %lld %d\n", c, s, r);
  gzclose(f);
  return 0;
}
