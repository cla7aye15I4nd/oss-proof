/* 8a979f6: the flush rank of the first deflate call.
 * deflateInit sets last_flush to -2. The first deflate call with no input and nothing pending
 * compares RANK(flush) with RANK(last_flush). Before the fix RANK(f) is ((f) << 1) - ..., so
 * RANK(-2) shifts a negative value left. The fix multiplies by 2. */
#include <stdio.h>
#include <string.h>
#include "zlib.h"

int main(void) {
    unsigned char out[100];
    z_stream s;
    memset(&s, 0, sizeof s);
    int rc = deflateInit(&s, Z_DEFAULT_COMPRESSION);
    s.next_out = out; s.avail_out = sizeof out;
    int r1 = deflate(&s, Z_NO_FLUSH);
    s.next_in = (unsigned char *)"hello"; s.avail_in = 5;
    int r2 = deflate(&s, Z_FINISH);
    unsigned long n = s.total_out;
    int e = deflateEnd(&s);
    printf("init=%d first=%d finish=%d out=%lu end=%d\n", rc, r1, r2, n, e);
    return 0;
}
