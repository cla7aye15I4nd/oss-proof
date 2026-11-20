/* Patch 0016. The readers add the bytes they deliver to the signed 64-bit position x.pos; so does the gzgetc()
 * macro of zlib.h, which runs in the caller and takes bytes from the output buffer without any bound. Documented
 * calls only, on a descriptor whose lseek succeeds without moving and which always has data (Linux /dev/zero; on a
 * system whose /dev/zero lseek does not behave so, the repro answers lseek on its descriptor as Linux does):
 *   max:  gzdopen, gzgetc, gzseek(INT64_MAX - 2, SEEK_SET), gzread of 4 bytes, then the gzgetc() macro.
 *   near: gzdopen, gzgetc, gzseek(INT64_MAX - 12, SEEK_SET), gzread of 1 byte, then the gzgetc() macro 12 times.
 * Without patch 0016 gzread itself overflows x.pos (max). With the first version of the patch (first-0016.patch),
 * the readers stopped at GZ_OFF_MAX but left output buffered: the macro then overflows x.pos in the caller, at
 * GZ_OFF_MAX (max) or after taking the 11 bytes up to it (near). With the patch, gz_fetch produces no output past
 * GZ_OFF_MAX, so x.pos + x.have stays at most GZ_OFF_MAX: the macro takes the bytes up to GZ_OFF_MAX, then calls
 * gzgetc(), which reports Z_DATA_ERROR and returns -1. */
#include <stdio.h>
#include <stdint.h>
#include <string.h>
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
int main(int argc, char **argv) {
  int near = argc > 1 && strcmp(argv[1], "near") == 0;
  int fd = open("/dev/zero", O_RDONLY);
#ifndef __linux__
  zfd = fd;
#endif
  gzFile f = gzdopen(fd, "r");
  if (f == NULL) { printf("gzdopen failed\n"); return 2; }
  (void)gzgetc(f);
  (void)gzseek(f, near ? INT64_MAX - 12 : INT64_MAX - 2, SEEK_SET);
  unsigned char buf[4];
  int r = gzread(f, buf, near ? 1 : 4);
  printf("%s read %d have %u pos %lld\n", near ? "near" : "max", r, f->have, (long long)f->pos);
  fflush(stdout);
  int got = 0, c = 0;
  for (int i = 0; i < (near ? 12 : 1); i++) {
    c = gzgetc(f);   /* the macro of zlib.h */
    if (c >= 0) got++;
  }
  int err;
  gzerror(f, &err);
  printf("%s read %d macro %d last %d pos %lld err %d\n", near ? "near" : "max", r, got, c, (long long)f->pos, err);
  gzclose(f);
  return 0;
}
