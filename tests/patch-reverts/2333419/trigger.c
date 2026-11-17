/* 2333419: inflateBack with state->sane never set.
 * inflateBackInit allocates the state without zeroing it. Before the fix it never sets sane, so
 * sane holds whatever the allocation held; here the allocation is filled with zeros (ASan option
 * malloc_fill_byte=0, see run.sh), so sane is 0. The raw stream is one fixed-code block whose first
 * symbol is a match of length 3 at distance 1000, with nothing written yet; the window has 512
 * bytes (windowBits 9), so inflateBack takes inflate_fast. With sane 0, inflate_fast skips the
 * "invalid distance too far back" check and copies from window + (wsize - op), where the unsigned
 * wsize - op = 512 - 1000 wraps: a read about 4 GB past the window. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "zlib.h"

static unsigned char input[14] = {0x03, 0xe6, 0x73, 0x00};   /* then ten zero bytes */
static unsigned outs;

static unsigned in(void *desc, z_const unsigned char **buf) {
    int *given = desc;
    if (*given) return 0;
    *given = 1;
    *buf = input;
    return sizeof input;
}

static int out(void *desc, unsigned char *buf, unsigned len) {
    (void)desc; (void)buf;
    outs += len;
    return 0;
}

int main(void) {
    unsigned char *window = malloc(512);
    z_stream s;
    int given = 0;
    memset(&s, 0, sizeof s);
    int rc = inflateBackInit(&s, 9, window);
    int r = inflateBack(&s, in, &given, out, NULL);
    printf("init=%d back=%d out=%u msg=%s end=%d\n", rc, r, outs, s.msg ? s.msg : "-",
           inflateBackEnd(&s));
    free(window);
    return 0;
}
