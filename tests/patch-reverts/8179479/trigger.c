/* 8179479: inflateSync before any header, with windowBits 0, then reuse of the stream.
 * inflateInit2(0) takes the window size from the header. inflateSync finds 00 00 ff ff before any
 * header; the raw block after it decodes with wbits still 0, so inflate allocates a one-byte
 * window. inflateReset keeps it (wbits equals the requested 0). The zlib stream that follows sets
 * wbits to 15 from its header, and updatewindow() copies the 135 bytes of output into the one-byte
 * window. (The zlib stream is given without its four check bytes first: the call that passes the
 * check does not add its own output to the window.) The fix sets wbits to 15 in inflateSync when
 * no header was seen. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "zlib.h"

int main(void) {
    static const unsigned char first[] = {0x00, 0x00, 0xff, 0xff,
        0xcb, 0x48, 0xcd, 0xc9, 0xc9, 0x57, 0xc8, 0x40, 0x90, 0x00};
    static const unsigned char second[] = {
        0x78, 0x9c, 0x0b, 0xc9, 0x48, 0x55, 0x28, 0x2c, 0xcd, 0x4c, 0xce, 0x56, 0x48, 0x2a,
        0xca, 0x2f, 0xcf, 0x53, 0x48, 0xcb, 0xaf, 0x50, 0xc8, 0x2a, 0xcd, 0x2d, 0x28, 0x56,
        0xc8, 0x2f, 0x4b, 0x2d, 0x52, 0x28, 0x01, 0x4a, 0xe7, 0x24, 0x56, 0x55, 0x2a, 0xa4,
        0xe4, 0xa7, 0xeb, 0x29, 0x84, 0xd0, 0x4c, 0x31, 0x00, 0xf9, 0x3c, 0x30, 0x76};
    unsigned char out[200];
    z_stream s;
    memset(&s, 0, sizeof s);
    int rc = inflateInit2(&s, 0);
    s.next_in = (unsigned char *)first; s.avail_in = sizeof first;
    int sync = inflateSync(&s);
    s.next_out = out; s.avail_out = sizeof out;
    int r1 = inflate(&s, Z_NO_FLUSH);
    unsigned long o1 = s.total_out;
    int reset = inflateReset(&s);
    s.next_in = (unsigned char *)second; s.avail_in = sizeof second - 4;
    s.next_out = out; s.avail_out = sizeof out;
    int r2 = inflate(&s, Z_NO_FLUSH);
    unsigned long o2 = s.total_out;
    s.avail_in = 4;
    int r3 = inflate(&s, Z_NO_FLUSH);
    printf("init=%d sync=%d raw=%d,%lu reset=%d zlib=%d,%lu check=%d\n", rc, sync, r1, o1, reset,
           r2, o2, r3);
    inflateEnd(&s);
    return 0;
}
