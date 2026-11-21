/* Patch 0014 on a build whose size_t is 32 bits and whose file offsets are 64 bits (-m32 -D_FILE_OFFSET_BITS=64).
 * The first version of patch 0014 (first-0014.patch) compared len > (size_t)(GZ_OFF_MAX - x.pos): the conversion
 * to a 32-bit size_t keeps the low 32 bits of the remaining room, which are 0 at x.pos = 2^32 - 1, so a legal
 * one-byte write was refused with Z_DATA_ERROR. The current patch compares in 64 bits. Documented calls only:
 * gzdopen of /dev/null for transparent writing, gzbuffer, gzseek to 2^32 - 1 (the zeros are written to /dev/null
 * by the next write), gzwrite of one byte, gztell, gzerror.
 * Expected with the current patch on every build: "pos32 seek 4294967295 write 1 tell 4294967296 err 0", preceded
 * by the widths "size_t <bytes> off <bytes>". With first-0014.patch on the 32-bit build: "write 0 ... err -3". */
#include <stdio.h>
#include <stdint.h>
#include <fcntl.h>
#include <unistd.h>
#include "zlib.h"
int main(void) {
  int fd = open("/dev/null", O_WRONLY);
  gzFile f = gzdopen(fd, "wT");
  if (f == NULL || gzbuffer(f, 1 << 20) != 0) { printf("gzdopen failed\n"); return 2; }
  printf("size_t %u off %u\n", (unsigned)sizeof(size_t), (unsigned)sizeof(z_off_t));
  long long s = (long long)gzseek(f, (z_off_t)4294967295u, SEEK_SET);
  int w = gzwrite(f, "a", 1);
  long long t = (long long)gztell(f);
  int err;
  gzerror(f, &err);
  printf("pos32 seek %lld write %d tell %lld err %d\n", s, w, t, err);
  gzclose(f);
  return 0;
}
