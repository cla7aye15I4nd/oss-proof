/* local-0004: gzread at the largest position overflows x.pos.
 * gzdopen of /dev/zero for reading; gzread of one byte (not gzip: a transparent copy); gzseek to
 * INT64_MAX; gzread of 16 bytes. On Linux lseek on /dev/zero returns 0 without moving, so gzseek
 * accepts the target and sets x.pos to INT64_MAX. Without patch 0004 gz_read then adds 16 to
 * x.pos. Linux only. */
#include <fcntl.h>
#include <stdint.h>
#include <stdio.h>
#include "zlib.h"

int main(void) {
    char buf[16];
    int fd = open("/dev/zero", O_RDONLY), err;
    if (fd < 0) return 2;
    gzFile f = gzdopen(fd, "r");
    if (f == NULL) return 2;
    int r1 = gzread(f, buf, 1);
    long long s = (long long)gzseek(f, INT64_MAX, SEEK_SET);
    int r16 = gzread(f, buf, 16);
    gzerror(f, &err);
    int c = gzclose(f);
    printf("read1=%d seek=%lld read16=%d err=%d close=%d\n", r1, s, r16, err, c);
    return 0;
}
