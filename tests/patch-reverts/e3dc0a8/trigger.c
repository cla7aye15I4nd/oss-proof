/* e3dc0a8: gzprintf as the first write.
 * gzopen for writing allocates nothing; the first gzprintf calls gz_init, which sets next_in to
 * NULL, and then gz_vacate. Before the fix gz_vacate computes strm->next_in + strm->avail_in with
 * next_in NULL, and compares the result with state->in + state->size. The fix returns first when
 * next_in is NULL. */
#include <stdio.h>
#include "zlib.h"

int main(void) {
    gzFile f = gzopen("out.gz", "w");
    if (f == NULL) return 2;
    int p = gzprintf(f, "hello");
    int c = gzclose(f);
    gzFile r = gzopen("out.gz", "r");
    char buf[16] = {0};
    int n = r == NULL ? -1 : gzread(r, buf, sizeof buf - 1);
    if (r != NULL) gzclose(r);
    printf("printf=%d close=%d read=%d:%s\n", p, c, n, buf);
    return 0;
}
