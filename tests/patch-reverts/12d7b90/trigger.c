/* 12d7b90: repeated deflatePrime with no deflate in between.
 * deflateInit2 with memLevel 1 gives a pending buffer of 512 bytes. Each deflatePrime(16, ...)
 * puts two bytes into it. Before the fix the only check compares sym_buf with pending_out + 2, and
 * pending_out does not move without deflate(), so 300 calls write past the end of pending_buf. */
#include <stdio.h>
#include <string.h>
#include "zlib.h"

int main(void) {
    z_stream s;
    memset(&s, 0, sizeof s);
    int rc = deflateInit2(&s, Z_DEFAULT_COMPRESSION, Z_DEFLATED, 15, 1, Z_DEFAULT_STRATEGY);
    int ok = 0, last = Z_OK;
    for (int i = 0; i < 300; i++) {
        last = deflatePrime(&s, 16, 0x1234);
        if (last != Z_OK) break;
        ok++;
    }
    int e = deflateEnd(&s);
    printf("init=%d primed=%d last=%d end=%d\n", rc, ok, last, e);
    return 0;
}
