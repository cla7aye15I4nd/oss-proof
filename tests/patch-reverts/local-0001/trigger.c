/* local-0001: inflateCopy on a stream stopped inside a fixed-code block.
 * The stream is a zlib stream of 128 bytes 'A' compressed with Z_FIXED. inflate() runs with seven
 * bytes of output room, so it stops inside the fixed block, where state->lencode points to the
 * static table lenfix. inflateCopy() then copies the stream. Without patch 0001 it compares
 * state->lencode with state->codes by >= and <=: pointers into different objects.
 * The copy decodes the rest; the program prints the result of each call and checks the output. */
#include <stdio.h>
#include <string.h>
#include "zlib.h"

int main(void) {
    static const unsigned char in[] = {0x78, 0x01, 0x73, 0x74, 0x1c, 0x58, 0x00, 0x00,
                                       0x31, 0x38, 0x20, 0x81};
    unsigned char out[128];
    z_stream src, dst;
    memset(&src, 0, sizeof src);
    memset(&dst, 0, sizeof dst);
    int rc = inflateInit(&src);
    src.next_in = (unsigned char *)in; src.avail_in = sizeof in;
    src.next_out = out; src.avail_out = 7;
    int r1 = inflate(&src, Z_NO_FLUSH);
    int rcopy = inflateCopy(&dst, &src);
    inflateEnd(&src);
    dst.avail_out = sizeof out - 7;
    int r2 = inflate(&dst, Z_NO_FLUSH);
    int ok = r2 == Z_STREAM_END && dst.total_out == 128;
    for (int i = 0; i < 128; i++) ok = ok && out[i] == 'A';
    printf("init=%d inflate=%d copy=%d finish=%d output %s\n", rc, r1, rcopy, r2, ok ? "ok" : "WRONG");
    inflateEnd(&dst);
    return ok ? 0 : 1;
}
