/* Statement test for the deflate completion goals on the REAL libz.a (pinned zlib plus patches):
 * DeflateCompletes, the deflateBound promise of zlib.h and the compressBound promise.
 *
 *   single   after init (and optional dictionary or gzip header), deflateBound(n) as avail_out, one
 *            deflate(Z_FINISH) with all n bytes: must return Z_STREAM_END (zlib.h, deflateBound).
 *            The output buffer is exactly the bound, so a sanitizer build sees any overrun.
 *            Also records the slack bound - produced, and whether room = produced suffices.
 *   multi    random Z_FINISH calls (FINISH) or Z_NO_FLUSH calls then Z_FINISH (MIXED), random input
 *            and output chunks, then one Z_FINISH call with the rest of the input and
 *            max(1, bound - produced) bytes of room: must return Z_STREAM_END (DeflateCompletes
 *            for FINISH; the zlib.h reading that Z_NO_FLUSH keeps the bound, for MIXED).
 *   compress compress2 at every level with destLen = compressBound(n): must return Z_OK.
 *   extra    gzip header with extra_len near 2^32 (the C reads extra_len & 0xffff bytes).
 *
 *   sweep    every length below COUNT, single call, one wrapper and window per SEED (0 .. 23).
 *   far      far 3- to 5-byte copies, n = COUNT, windowBits SEED (9 .. 15), single call (see far()).
 *
 * Usage: bound MODE SEED COUNT, MODE one of grid, sweep, compress, extra, far.
 * Output: one line per failure ("FAIL ..." with every parameter), then summary lines
 * ("SLACK class min count", "EXACT class ok fail"). Exit 1 on any failure.
 * All randomness comes from SEED; no clock. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <zlib.h>

static uint64_t rs;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static size_t rn(size_t n) { return n ? (size_t)(rnd() % n) : 0; }

static int failures;

/* Input classes. 0 random (incompressible), 1 zeros, 2 words, 3 random with far 3-byte repeats,
 * 4 random runs and long runs (blocks that span a window slide), 5 short period, 6 random with
 * 258-byte copies at the window distance, 7 random bytes >= 144 (9-bit fixed literals). */
#define KINDS 8
static void data(unsigned char *b, size_t n, unsigned kind, size_t wsize) {
    static const char *W[] = {"the ", "quick ", "brown ", "fox ", "zlib ", "deflate ", "window ", "huffman "};
    size_t i = 0;
    switch (kind) {
    case 0: for (; i < n; i++) b[i] = (unsigned char)rnd(); break;
    case 1: memset(b, 0, n); break;
    case 2: while (i < n) { const char *w = W[rn(8)]; for (size_t k = 0; w[k] && i < n; k++) b[i++] = (unsigned char)w[k]; } break;
    case 3:
        for (; i < n; i++) {
            if (i > 3 && rn(3) == 0) { size_t d = 1 + rn(i - 3 < wsize - 3 ? i - 3 : wsize - 3);
                for (int k = 0; k < 3 && i < n; k++, i++) b[i] = b[i - d]; i--; }
            else b[i] = (unsigned char)rnd();
        }
        break;
    case 4:
        while (i < n) { size_t r = rn(2) ? 1 + rn(3000) : 1 + rn(40);
            unsigned char c = (unsigned char)rnd(); int run = rn(2);
            for (size_t k = 0; k < r && i < n; k++) b[i++] = run ? c : (unsigned char)rnd(); }
        break;
    case 5: { unsigned char p[3]; for (int k = 0; k < 3; k++) p[k] = (unsigned char)rnd(); for (; i < n; i++) b[i] = p[i % (1 + (i / 997) % 3)]; } break;
    case 6:
        for (; i < n; i++) {
            if (i >= wsize && rn(64) == 0) { for (int k = 0; k < 258 && i < n; k++, i++) b[i] = b[i - wsize + 1]; i--; }
            else b[i] = (unsigned char)rnd();
        }
        break;
    default: for (; i < n; i++) b[i] = (unsigned char)(144 + rn(112)); break;
    }
}

typedef struct {
    int level, wbits, mem, strategy;   /* wbits as given to deflateInit2 (sign and +16 select the wrapper) */
    size_t dict;                       /* preset dictionary length, 0: none */
    int head;                          /* gzip: 0 none, 1 name+comment+hcrc, 2 extra 300, 3 extra 65535, 4 extra 70000 */
} Cfg;

static unsigned char dictbuf[40000];
static unsigned char extrabuf[70000];

static int setup(z_stream *s, const Cfg *c, gz_header *gh) {
    memset(s, 0, sizeof *s);
    if (deflateInit2(s, c->level, Z_DEFLATED, c->wbits, c->mem, c->strategy) != Z_OK) return 0;
    if (c->dict && deflateSetDictionary(s, dictbuf, (uInt)c->dict) != Z_OK) { deflateEnd(s); return 0; }
    if (c->head) {
        memset(gh, 0, sizeof *gh);
        gh->time = 0x12345678; gh->os = 3;
        if (c->head == 1) { gh->name = (Bytef *)"name.txt"; gh->comment = (Bytef *)"a comment"; gh->hcrc = 1; }
        else { gh->extra = extrabuf; gh->extra_len = c->head == 2 ? 300 : c->head == 3 ? 65535 : 70000; }
        if (deflateSetHeader(s, gh) != Z_OK) { deflateEnd(s); return 0; }
    }
    return 1;
}

static void cfgstr(char *o, size_t on, const Cfg *c) {
    snprintf(o, on, "level=%d wbits=%d mem=%d strategy=%d dict=%zu head=%d", c->level, c->wbits, c->mem,
             c->strategy, c->dict, c->head);
}

/* Slack statistics per class (wrapper x default-or-not x level-zero-or-not). */
static long long minslack[3][2][2];
static long long nslack[3][2][2];
static long exactok, exactfail;
static int wrapof(int wbits) { return wbits < 0 ? 0 : wbits > 15 ? 2 : 1; }

static void single(const Cfg *c, const unsigned char *in, size_t n, unsigned kind) {
    z_stream s; gz_header gh; char cs[200];
    if (!setup(&s, c, &gh)) return;
    uLong bound = deflateBound(&s, n);
    if (deflateBound_z(&s, n) != bound) { cfgstr(cs, sizeof cs, c); printf("FAIL bound_z %s n=%zu\n", cs, n); failures++; }
    unsigned char *out = malloc(bound ? bound : 1);
    s.next_in = (Bytef *)in; s.avail_in = (uInt)n; s.next_out = out; s.avail_out = (uInt)bound;
    int rc = deflate(&s, Z_FINISH);
    size_t produced = s.total_out;
    deflateEnd(&s);
    free(out);
    cfgstr(cs, sizeof cs, c);
    if (rc != Z_STREAM_END) {
        printf("FAIL single %s kind=%u n=%zu bound=%lu rc=%d produced=%zu\n", cs, kind, n, bound, rc, produced);
        failures++;
        return;
    }
    int wb = c->wbits < 0 ? -c->wbits : c->wbits > 15 ? c->wbits - 16 : c->wbits;
    int w = wrapof(c->wbits), def = wb == 15 && c->mem == 8;
    long long sl = (long long)bound - (long long)produced;
    int lz = c->level == 0;
    if (nslack[w][def][lz] == 0 || sl < minslack[w][def][lz]) {
        minslack[w][def][lz] = sl;
        printf("MIN wrap=%d default=%d level0=%d slack=%lld %s kind=%u n=%zu\n", w, def, lz, sl, cs, kind, n);
    }
    nslack[w][def][lz]++;
    /* room = produced exactly: is the actual size alone enough room? (Not promised; informs the proof.) */
    if (setup(&s, c, &gh)) {
        unsigned char *o2 = malloc(produced ? produced : 1);
        s.next_in = (Bytef *)in; s.avail_in = (uInt)n; s.next_out = o2; s.avail_out = (uInt)produced;
        int rc2 = deflate(&s, Z_FINISH);
        if (rc2 == Z_STREAM_END) exactok++;
        else { exactfail++; if (exactfail <= 20) printf("INFO exact-room-not-enough %s kind=%u n=%zu produced=%zu rc=%d\n", cs, kind, n, produced, rc2); }
        deflateEnd(&s);
        free(o2);
    }
}

static void multi(const Cfg *c, const unsigned char *in, size_t n, unsigned kind, int mixed) {
    z_stream s; gz_header gh; char cs[200];
    if (!setup(&s, c, &gh)) return;
    uLong bound = deflateBound(&s, n);
    unsigned char *out = malloc(bound + 70000);
    size_t pos = 0;
    int calls = 1 + (int)rn(12), rc = Z_OK;
    size_t maxchunk = 1 + rn(rn(2) ? 64 : 5000);
    int fin = 0;
    for (int k = 0; k < calls && rc != Z_STREAM_END; k++) {
        size_t produced = s.total_out;
        size_t ain = rn(2) ? rn(n - pos + 1) : (n - pos < 300 ? rn(n - pos + 1) : rn(300));
        size_t aout = 1 + rn(maxchunk);
        int flush = Z_FINISH;
        if (mixed && !fin) flush = rn(3) ? Z_NO_FLUSH : Z_FINISH;
        if (flush == Z_FINISH) fin = 1;
        s.next_in = (Bytef *)in + pos; s.avail_in = (uInt)ain; s.next_out = out + produced; s.avail_out = (uInt)aout;
        rc = deflate(&s, flush);
        pos += ain - s.avail_in;
        if (rc == Z_STREAM_END && pos < n) break;   /* finished early: the rest is not part of this stream */
    }
    cfgstr(cs, sizeof cs, c);
    if (rc != Z_STREAM_END) {
        size_t produced = s.total_out;
        size_t room = bound > produced ? bound - produced : 1;
        s.next_in = (Bytef *)in + pos; s.avail_in = (uInt)(n - pos); s.next_out = out + produced; s.avail_out = (uInt)room;
        /* DeflateCompletes needs FINISH_STATE -> avail_in = 0 and room within the buffer. */
        rc = deflate(&s, Z_FINISH);
        if (rc != Z_STREAM_END && !(rc == Z_BUF_ERROR && pos < n && s.avail_in == n - pos)) {
            printf("FAIL multi%s %s kind=%u n=%zu bound=%lu before=%zu room=%zu rc=%d after=%lu left_in=%u\n",
                   mixed ? "-mixed" : "", cs, kind, n, bound, produced, room, rc, s.total_out, s.avail_in);
            failures++;
        }
    }
    if (rc == Z_STREAM_END && s.total_in == n && s.total_out > bound) {
        printf("FAIL multi-total%s %s kind=%u n=%zu bound=%lu total=%lu\n", mixed ? "-mixed" : "", cs, kind, n, bound, s.total_out);
        failures++;
    }
    deflateEnd(&s);
    free(out);
}

static const size_t SIZES[] = {0, 1, 2, 3, 4, 7, 100, 127, 128, 255, 256, 511, 512, 1000, 4095, 4096, 16383, 16384,
                               16385, 32767, 32768, 32769, 65535, 65536, 65537, 100000};
#define NSIZES (sizeof SIZES / sizeof SIZES[0])

static void grid(size_t count) {
    static const int WB[] = {8, 9, 10, 11, 12, 13, 14, 15};
    size_t maxn = 100000;
    unsigned char *in = malloc(maxn + 1);
    for (int wrap = 0; wrap < 3; wrap++)
    for (int wi = 0; wi < 8; wi++)
    for (int mem = 1; mem <= 9; mem++)
    for (int level = 0; level <= 9; level++)
    for (int strategy = 0; strategy <= 4; strategy++) {
        Cfg c = {level, wrap == 0 ? -WB[wi] : wrap == 1 ? WB[wi] : WB[wi] + 16, mem, strategy, 0, 0};
        if (wrap == 0 && WB[wi] == 8) continue;            /* refused by deflateInit2 */
        size_t wsize = (size_t)1 << (WB[wi] == 8 ? 9 : WB[wi]);
        for (size_t t = 0; t < count; t++) {
            size_t n = rn(4) ? SIZES[rn(NSIZES)] : rn(maxn);
            if (n > 20000 && rn(3)) n = rn(20000);
            unsigned kind = (unsigned)rn(KINDS);
            if (wrap == 1 && rn(4) == 0) { size_t d = rn(3); c.dict = d == 0 ? 1 : d == 1 ? 100 : 40000; } else c.dict = 0;
            if (wrap == 0 && rn(8) == 0) c.dict = 1 + rn(1000);
            c.head = wrap == 2 && rn(3) == 0 ? 1 + (int)rn(4) : 0;
            data(in, n, kind, wsize);
            single(&c, in, n, kind);
            multi(&c, in, n, kind, 0);
            multi(&c, in, n, kind, 1);
        }
    }
    free(in);
}

/* Every length 0 .. COUNT-1 in one parameter slice (SEED selects the wrapper and window), single
 * call only, for the input classes that cost most per byte: random, bytes >= 144, zeros. */
static void sweep(int slice, size_t count) {
    static const int WB[] = {8, 9, 10, 11, 12, 13, 14, 15};
    int wrap = slice / 8 % 3, wi = slice % 8;
    if (wrap == 0 && WB[wi] == 8) return;
    unsigned char *in = malloc(count + 1);
    size_t wsize = (size_t)1 << (WB[wi] == 8 ? 9 : WB[wi]);
    for (int mem = 1; mem <= 9; mem++)
    for (int level = 0; level <= 9; level++)
    for (int strategy = 0; strategy <= 4; strategy++) {
        Cfg c = {level, wrap == 0 ? -WB[wi] : wrap == 1 ? WB[wi] : WB[wi] + 16, mem, strategy, 0, 0};
        static const unsigned K[] = {0, 7, 1};
        for (int k = 0; k < 3; k++)
            for (size_t n = 0; n < count; n++) { data(in, n, K[k], wsize); single(&c, in, n, K[k]); }
    }
    free(in);
}

/* The far-match search (docs/findings/deflatebound-fixed-far-matches): random bytes, then copies
 * of length L from a random distance in the far half of the window (the upper half of the usable
 * distances for windowBits 9), with literals at a rate of
 * R percent between them. Every window (SEED selects one: 9 .. 15), memLevel, level 1 .. 9 and
 * strategy, L in 3 .. 5, R in {0, 10, 25, 50}, zlib wrapper, one deflate(Z_FINISH) with room
 * deflateBound(n), n = COUNT. Before patch 0007 the case windowBits 15, memLevel 8, Z_FIXED,
 * levels 1 to 3 fails here. */
static void far(int wb, size_t n) {
    size_t wsize = (size_t)1 << wb, hi = wsize - 262, lo = wsize / 2 + 1 <= hi ? wsize / 2 + 1 : hi / 2 + 1;
    unsigned char *in = malloc(n + 1), *out = malloc(2 * n + 1024);
    static const int RATE[] = {0, 10, 25, 50};
    for (int len = 3; len <= 5; len++)
    for (int ri = 0; ri < 4; ri++) {
        size_t i = 0;
        for (; i < n && i < 2 * wsize; i++) in[i] = (unsigned char)rnd();
        while (i < n) {
            if ((int)rn(100) < RATE[ri]) { in[i++] = (unsigned char)rnd(); continue; }
            size_t d = lo + rn(hi - lo + 1);
            for (int k = 0; k < len && i < n; k++, i++) in[i] = in[i - d];
        }
        for (int mem = 1; mem <= 9; mem++)
        for (int level = 1; level <= 9; level++)
        for (int strategy = 0; strategy <= 4; strategy++) {
            z_stream s; memset(&s, 0, sizeof s);
            if (deflateInit2(&s, level, Z_DEFLATED, wb, mem, strategy) != Z_OK) continue;
            uLong bound = deflateBound(&s, n);
            s.next_in = in; s.avail_in = (uInt)n; s.next_out = out; s.avail_out = (uInt)bound;
            int rc = deflate(&s, Z_FINISH);
            if (rc != Z_STREAM_END) {
                printf("FAIL far level=%d wbits=%d mem=%d strategy=%d len=%d rate=%d n=%zu bound=%lu rc=%d\n",
                       level, wb, mem, strategy, len, RATE[ri], n, bound, rc);
                failures++;
            }
            deflateEnd(&s);
        }
    }
    printf("FAR wbits=%d n=%zu done\n", wb, n);
    free(in); free(out);
}

/* compressBound: compress2 at every level and compress, room exactly compressBound(n). */
static void compress_test(size_t count) {
    size_t maxn = 300000;
    unsigned char *in = malloc(maxn + 1);
    for (size_t t = 0; t < count; t++) {
        size_t n = rn(3) ? SIZES[rn(NSIZES)] : rn(maxn);
        unsigned kind = (unsigned)rn(KINDS);
        data(in, n, kind, 32768);
        uLong cb = compressBound(n);
        if (compressBound_z(n) != cb) { printf("FAIL compressBound_z n=%zu\n", n); failures++; }
        unsigned char *out = malloc(cb);
        for (int level = -1; level <= 9; level++) {
            uLongf dl = cb;
            int rc = compress2(out, &dl, in, n, level);
            if (rc != Z_OK) { printf("FAIL compress2 level=%d kind=%u n=%zu bound=%lu rc=%d\n", level, kind, n, cb, rc); failures++; }
        }
        uLongf dl = cb;
        int rc = compress(out, &dl, in, n);
        if (rc != Z_OK) { printf("FAIL compress kind=%u n=%zu bound=%lu rc=%d\n", kind, n, cb, rc); failures++; }
        free(out);
    }
    free(in);
}

/* The gzip extra length: deflateBound adds 2 + extra_len at unsigned int width; deflate writes
 * extra_len & 0xffff bytes. */
static void extra_test(void) {
    static const uInt LENS[] = {0xffffffffu, 0xfffffffeu, 0xfffffffdu, 0x10000u, 0xffffu};
    unsigned char in[100];
    for (size_t i = 0; i < sizeof in; i++) in[i] = (unsigned char)rnd();
    for (size_t k = 0; k < sizeof LENS / sizeof LENS[0]; k++) {
        z_stream s; gz_header gh;
        memset(&s, 0, sizeof s); memset(&gh, 0, sizeof gh);
        if (deflateInit2(&s, 6, Z_DEFLATED, 31, 8, 0) != Z_OK) return;
        gh.extra = extrabuf; gh.extra_len = LENS[k];
        deflateSetHeader(&s, &gh);
        uLong bound = deflateBound(&s, sizeof in);
        if (bound > 0xffffffffu) {   /* no single avail_out can hold it: the promise is vacuous here */
            printf("N/A  extra_len=%u bound=%lu exceeds avail_out\n", LENS[k], bound);
            deflateEnd(&s);
            continue;
        }
        unsigned char *out = malloc(bound);
        s.next_in = in; s.avail_in = sizeof in; s.next_out = out; s.avail_out = (uInt)bound;
        int rc = deflate(&s, Z_FINISH);
        printf("%s extra_len=%u bound=%lu rc=%d produced=%lu\n", rc == Z_STREAM_END ? "OK  " : "FAIL", LENS[k], bound, rc,
               s.total_out);
        if (rc != Z_STREAM_END) failures++;
        deflateEnd(&s);
        free(out);
    }
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: bound grid|compress|extra SEED COUNT\n"); return 2; }
    rs = strtoull(argv[2], 0, 10) * 0x9E3779B97F4A7C15ull + 1;
    size_t count = strtoull(argv[3], 0, 10);
    for (size_t i = 0; i < sizeof dictbuf; i++) dictbuf[i] = (unsigned char)rnd();
    for (size_t i = 0; i < sizeof extrabuf; i++) extrabuf[i] = (unsigned char)rnd();
    if (!strcmp(argv[1], "grid")) grid(count);
    else if (!strcmp(argv[1], "compress")) compress_test(count);
    else if (!strcmp(argv[1], "sweep")) sweep((int)strtol(argv[2], 0, 10), count);
    else if (!strcmp(argv[1], "extra")) extra_test();
    else if (!strcmp(argv[1], "far")) far((int)strtol(argv[2], 0, 10), count);
    else { fprintf(stderr, "unknown mode\n"); return 2; }
    for (int w = 0; w < 3; w++) for (int d = 0; d < 2; d++) for (int l = 0; l < 2; l++)
        if (nslack[w][d][l]) printf("SLACK wrap=%d default=%d level0=%d min=%lld runs=%lld\n", w, d, l, minslack[w][d][l], nslack[w][d][l]);
    printf("EXACT room=produced ends=%ld does-not-end=%ld\n", exactok, exactfail);
    printf("FAILURES %d\n", failures);
    return failures != 0;
}
