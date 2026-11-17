/* 7dd6aa7: gzungetc right after gzopen.
 * gzopen for reading allocates no buffer: size is 0 and state->out is never written. Before the fix
 * gzungetc does not call gz_look first, so with no buffered byte it sets x.next to
 * state->out + (state->size << 1) - 1 and stores the byte there: through a pointer that was never
 * written, one byte before it. The fix sets up the buffers with gz_look first. */
#include <stdio.h>
#include <string.h>
#include "zlib.h"

int main(void) {
    char buf[8];
    FILE *raw = fopen("raw.dat", "wb");
    if (raw == NULL || fwrite("abc", 1, 3, raw) != 3 || fclose(raw) != 0) return 2;
    gzFile f = gzopen("raw.dat", "rb");
    if (f == NULL) return 2;
    int u = gzungetc('x', f);
    int g = gzgetc(f);
    memset(buf, 0, sizeof buf);
    int n = gzread(f, buf, sizeof buf - 1);
    int c = gzclose(f);
    printf("ungetc=%d getc=%d read=%d:%s close=%d\n", u, g, n, buf, c);
    return 0;
}
