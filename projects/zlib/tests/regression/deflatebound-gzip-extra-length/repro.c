/* deflateBound is too small for a gzip header whose extra length is 2^32 - 2 or 2^32 - 1.
 *
 * deflateBound_z adds 2 + s->gzhead->extra_len to the wrapper length. The sum is computed in
 * 32-bit unsigned arithmetic and wraps to 0 or 1 for these two lengths. deflate writes only the
 * low 16 bits of the extra length and that many bytes of extra (65534 or 65535), so the stream
 * is about 64 KiB longer than the bound.
 *
 * zlib.h: "If that first deflate() call is provided the sourceLen input bytes, an output buffer
 * allocated to the size returned by deflateBound(), and the flush value Z_FINISH, then deflate()
 * is guaranteed to return Z_STREAM_END."
 *
 * Build: cc repro.c -I<zlib> <zlib>/libz.a -o repro && ./repro
 * For each of the two lengths: the bound, the return code of one deflate(Z_FINISH) with exactly
 * the bound as room, and the size the stream needs. Exit 1 when some call does not return
 * Z_STREAM_END. No clock, no external input. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <zlib.h>

static int run(uLong extra_len, unsigned char *extra, unsigned char *in, uLong n) {
    z_stream s;
    gz_header h;
    memset(&s, 0, sizeof s);
    memset(&h, 0, sizeof h);
    if (deflateInit2(&s, Z_DEFAULT_COMPRESSION, Z_DEFLATED, 31, 8, Z_DEFAULT_STRATEGY) != Z_OK) return 2;
    h.extra = extra;
    h.extra_len = (uInt)extra_len;
    if (deflateSetHeader(&s, &h) != Z_OK) return 2;
    uLong bound = deflateBound(&s, n);
    unsigned char *out = malloc(bound + 1);
    unsigned char *big = malloc(2 * 65536 + 4 * n + 1024);
    if (!out || !big) return 2;
    s.next_in = in; s.avail_in = (uInt)n;
    s.next_out = out; s.avail_out = (uInt)bound;
    int ret = deflate(&s, Z_FINISH);
    deflateEnd(&s);
    /* the size the stream needs: the same call with ample room */
    z_stream t;
    memset(&t, 0, sizeof t);
    if (deflateInit2(&t, Z_DEFAULT_COMPRESSION, Z_DEFLATED, 31, 8, Z_DEFAULT_STRATEGY) != Z_OK) return 2;
    if (deflateSetHeader(&t, &h) != Z_OK) return 2;
    t.next_in = in; t.avail_in = (uInt)n;
    t.next_out = big; t.avail_out = 2 * 65536 + 4 * n + 1024;
    int full = deflate(&t, Z_FINISH);
    uLong need = t.total_out;
    deflateEnd(&t);
    printf("extra_len %lu: deflateBound %lu, deflate(Z_FINISH) with that room %s, the stream needs %lu%s\n",
           extra_len, bound, ret == Z_STREAM_END ? "Z_STREAM_END" : ret == Z_OK ? "Z_OK" : "error",
           need, full == Z_STREAM_END ? "" : " (?)");
    free(out); free(big);
    return ret == Z_STREAM_END ? 0 : 1;
}

int main(void) {
    static unsigned char extra[65535];
    unsigned char in[100];
    for (int i = 0; i < 65535; i++) extra[i] = (unsigned char)(i * 7);
    for (int i = 0; i < 100; i++) in[i] = (unsigned char)i;
    int a = run(0xfffffffeUL, extra, in, sizeof in);
    int b = run(0xffffffffUL, extra, in, sizeof in);
    if (a == 2 || b == 2) { puts("setup failed"); return 2; }
    return a || b;
}
