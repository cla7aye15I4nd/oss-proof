/* deflateBound is too small for Z_FIXED at levels 1 to 3 with the default windowBits and memLevel.
 *
 * Input: 64 KiB of pseudo-random bytes, then 3-byte copies, each from a pseudo-random distance in
 * (16384, 32000]. deflate_fast (levels 1 to 3) takes each copy as a match of length 3 (it has no
 * TOO_FAR test). With fixed codes such a match costs 7 + 5 + 13 = 25 bits for 3 bytes. A block of
 * 16383 symbols then spans about 49 KB, crosses a window slide, and FLUSH_BLOCK_ONLY passes
 * buf == NULL, so _tr_flush_block cannot fall back to a stored block. Z_FIXED forces the fixed
 * codes. The output grows by about 1/24 of the input, while the default-parameter bound of
 * deflateBound allows about 0.03%.
 *
 * zlib.h: "If that first deflate() call is provided the sourceLen input bytes, an output buffer
 * allocated to the size returned by deflateBound(), and the flush value Z_FINISH, then deflate()
 * is guaranteed to return Z_STREAM_END."
 *
 * Build: cc repro.c -I<zlib> <zlib>/libz.a -o repro && ./repro [n]
 * Prints, for levels 1 to 9, the bound, the return code of one deflate(Z_FINISH) with exactly the
 * bound as room, and the size the stream needs. Exit 1 when some level does not return
 * Z_STREAM_END. No clock, no external input. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <zlib.h>

static uint64_t rs = 88172645463325252ull;
static unsigned rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return (unsigned)rs; }

int main(int argc, char **argv) {
    size_t n = argc > 1 ? strtoull(argv[1], 0, 10) : 1000000, i = 0;
    unsigned char *in = malloc(n);
    for (; i < n && i < 65536; i++) in[i] = (unsigned char)rnd();
    while (i < n) {
        size_t d = 16385 + rnd() % (32000 - 16385);
        for (int k = 0; k < 3 && i < n; k++, i++) in[i] = in[i - d];
    }
    int bad = 0;
    printf("zlib %s, n = %zu, windowBits 15, memLevel 8, strategy Z_FIXED\n", zlibVersion(), n);
    for (int level = 1; level <= 9; level++) {
        z_stream s, t;
        memset(&s, 0, sizeof s);
        memset(&t, 0, sizeof t);
        if (deflateInit2(&s, level, Z_DEFLATED, 15, 8, Z_FIXED) != Z_OK) return 2;
        uLong bound = deflateBound(&s, n);
        unsigned char *out = malloc(bound);
        s.next_in = in; s.avail_in = (uInt)n; s.next_out = out; s.avail_out = (uInt)bound;
        int rc = deflate(&s, Z_FINISH);
        /* The size of the whole stream, with ample room. */
        size_t big = 2 * n + 1024;
        unsigned char *o2 = malloc(big);
        if (deflateInit2(&t, level, Z_DEFLATED, 15, 8, Z_FIXED) != Z_OK) return 2;
        t.next_in = in; t.avail_in = (uInt)n; t.next_out = o2; t.avail_out = (uInt)big;
        deflate(&t, Z_FINISH);
        printf("level %d: deflateBound %lu, deflate(Z_FINISH) with that room returns %d (%s), stream needs %lu\n",
               level, bound, rc, rc == Z_STREAM_END ? "Z_STREAM_END" : "not Z_STREAM_END", t.total_out);
        if (rc != Z_STREAM_END) bad = 1;
        deflateEnd(&s); deflateEnd(&t); free(out); free(o2);
    }
    free(in);
    return bad;
}
