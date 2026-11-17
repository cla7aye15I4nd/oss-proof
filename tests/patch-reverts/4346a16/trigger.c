/* 4346a16: deflatePrime with a negative number of bits.
 * deflatePrime(1, 1) leaves one bit buffered. deflatePrime(-1, 0) then passes the room check
 * (need = (1 + -1) >> 3 = 0). Before the fix nothing refuses a negative count: in the loop
 * put = Buf_size - bi_valid = 15 is above bits, so put becomes -1 and (1 << put) shifts by a negative
 * amount. The fix returns Z_BUF_ERROR for bits outside 0..16. */
#include <stdio.h>
#include <string.h>
#include "zlib.h"

int main(void) {
    z_stream s;
    memset(&s, 0, sizeof s);
    int rc = deflateInit(&s, Z_DEFAULT_COMPRESSION);
    int p1 = deflatePrime(&s, 1, 1);
    int p2 = deflatePrime(&s, -1, 0);
    int e = deflateEnd(&s);
    printf("init=%d prime1=%d prime-1=%d end=%d\n", rc, p1, p2, e);
    return 0;
}
