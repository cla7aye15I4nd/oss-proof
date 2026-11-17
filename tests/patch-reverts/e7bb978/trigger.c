/* e7bb978: inflate_fast on a primed raw stream.
 * The raw stream has two fixed-code blocks: "a", then "bcdefghijklmnop" (final). Its first four bytes
 * are given by two inflatePrime(16, ...) calls; the other 15 bytes are the input, in a buffer of
 * exactly that size. inflate() takes the block type from the 32 primed bits and enters LEN with 15
 * bytes of input and 1000 bytes of room. Before the fix it calls inflate_fast with 29 bits in the
 * bit buffer. inflate_fast decodes "a" and the end of the block from those bits without reading
 * input, and then gives back the whole bytes it still holds: next_in moves before the input
 * buffer. The second block goes through inflate_fast again, which reads from there. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "zlib.h"

int main(void) {
    static const unsigned char stream[] = {0x4a, 0x04, 0x2c, 0x29, 0x39, 0x25, 0x35, 0x2d, 0x3d, 0x23,
                                           0x33, 0x2b, 0x3b, 0x27, 0x37, 0x2f, 0xbf, 0x00, 0x00};
    unsigned char *in = malloc(sizeof stream - 4), out[1000];
    memcpy(in, stream + 4, sizeof stream - 4);
    z_stream s;
    memset(&s, 0, sizeof s);
    int rc = inflateInit2(&s, -15);
    int p1 = inflatePrime(&s, 16, stream[0] | stream[1] << 8);
    int p2 = inflatePrime(&s, 16, stream[2] | stream[3] << 8);
    s.next_in = in; s.avail_in = sizeof stream - 4;
    s.next_out = out; s.avail_out = sizeof out;
    int r = inflate(&s, Z_NO_FLUSH);
    int ok = r == Z_STREAM_END && s.total_out == 16 && memcmp(out, "abcdefghijklmnop", 16) == 0;
    printf("init=%d prime=%d,%d inflate=%d out=%lu output %s\n", rc, p1, p2, r, s.total_out,
           ok ? "ok" : "WRONG");
    inflateEnd(&s);
    free(in);
    return ok ? 0 : 1;
}
