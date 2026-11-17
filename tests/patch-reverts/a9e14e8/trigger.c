/* a9e14e8: windowBits INT_MIN.
 * inflateInit2(INT_MIN) and deflateInit2(..., INT_MIN, ...) each take the raw-deflate branch for a
 * negative windowBits and negate it. Before the fix nothing refuses a value below -15 first, so
 * -INT_MIN overflows int. The fix returns Z_STREAM_ERROR for such a value. The two calls run in
 * separate processes (inflateInit2 in a child), so that each site is reached. */
#include <limits.h>
#include <stdio.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>
#include "zlib.h"

int main(void) {
    z_stream s;
    memset(&s, 0, sizeof s);
    fflush(stdout);
    pid_t child = fork();
    if (child == 0) {
        printf("inflateInit2=%d\n", inflateInit2(&s, INT_MIN));
        return 0;
    }
    int status;
    waitpid(child, &status, 0);
    printf("deflateInit2=%d\n",
           deflateInit2(&s, Z_DEFAULT_COMPRESSION, Z_DEFLATED, INT_MIN, 8, Z_DEFAULT_STRATEGY));
    return WIFEXITED(status) && WEXITSTATUS(status) == 0 ? 0 : 1;
}
