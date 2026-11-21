/* Patch 0013 on a build whose z_off64_t is 32 bits (-m32 -D_LARGEFILE64_SOURCE=0: zconf.h then makes z_off64_t the
 * 32-bit off_t, as on any system without large-file functions). The first version of patch 0013 (first-0013.patch)
 * bounded gz_read with (z_off64_t)n > GZ_OFF_MAX - x.pos: for n above INT_MAX the conversion gives a negative value,
 * so the bound was skipped and x.pos wrapped past GZ_OFF_MAX (unsigned arithmetic, then an implementation-defined
 * conversion). The current patch compares in 64 bits. Documented calls only: gzdopen of /dev/zero (its lseek
 * succeeds without moving; on other systems the repro answers lseek as Linux does), gzbuffer, gzgetc, gzseek to
 * GZ_OFF_MAX - 5, gzgetc, then the caller points the descriptor at /dev/null (dup2) so that no more data comes,
 * gzfread of 2^31 one-byte items into a 64-byte buffer (at most the bytes buffered reach it), gztell, gzerror.
 * Positions are printed as distances from GZ_OFF_MAX. Expected with the current patch on every build:
 * "pos32 seek max-5 fread 4 tell max-0 err -3", preceded by the widths "size_t <bytes> off <bytes>". With
 * first-0013.patch on the 32-bit build: x.pos wraps, gztell is negative ("tell max-" and a large number). */
#include <stdio.h>
#include <stdint.h>
#include <limits.h>
#include <fcntl.h>
#include <unistd.h>
#include "zlib.h"
#ifndef __linux__
static int zfd = -1;
off_t lseek(int fd, off_t off, int whence) {
  if (fd == zfd) return 0;   /* Linux /dev/zero: zero_lseek */
  (void)off; (void)whence;
  return -1;
}
#endif
int main(void) {
  printf("size_t %u off %u\n", (unsigned)sizeof(size_t), (unsigned)sizeof(z_off_t));
  int fd = open("/dev/zero", O_RDONLY);
#ifndef __linux__
  zfd = fd;
#endif
  gzFile f = gzdopen(fd, "r");
  if (f == NULL || gzbuffer(f, 8) != 0) { printf("gzdopen failed\n"); return 2; }
  (void)gzgetc(f);
  z_off_t target = sizeof(z_off_t) == 4 ? (z_off_t)(INT_MAX - 5) : (z_off_t)(INT64_MAX - 5);
  long long s = (long long)gzseek(f, target, SEEK_SET);
  (void)gzgetc(f);
  int nul = open("/dev/null", O_RDONLY);
  if (nul < 0 || dup2(nul, fd) < 0) { printf("dup2 failed\n"); return 2; }
  static unsigned char buf[64];
  size_t n = gzfread(buf, 1, (size_t)1 << (sizeof(size_t) * 8 - 1), f);
  long long t = (long long)gztell(f);
  int err;
  gzerror(f, &err);
  long long mx = sizeof(z_off_t) == 4 ? (long long)INT_MAX : (long long)INT64_MAX;
  printf("pos32 seek max-%lld fread %lu tell max-%lld err %d\n", mx - s, (unsigned long)n, mx - t, err);
  gzclose(f);
  return 0;
}
