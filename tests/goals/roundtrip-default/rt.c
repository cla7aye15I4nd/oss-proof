/* Statement test of the default-stream round trip on the REAL libz.a (pinned zlib plus patches).
 * Default stream: deflateInit(Z_DEFAULT_COMPRESSION) (level 6, zlib wrapper, windowBits 15,
 * memLevel 8, default strategy) and inflateInit. Each input is checked against five claims.
 *
 *   one      after deflateInit, one deflate(Z_FINISH) with all n bytes and room deflateBound(n)
 *            returns Z_STREAM_END, and deflateBound(n) = compressBound(n) for this configuration.
 *   rest     a random history of Z_NO_FLUSH and Z_FINISH calls (random input and output chunks,
 *            some with no room), then one Z_FINISH call with the rest of the input and room
 *            max(1, deflateBound(n) - produced) returns Z_STREAM_END (DeflateCompletes, default). A Z_FINISH call
 *            may offer part of the input and later calls more; if the final block was begun first, the stream
 *            ends without the rest, and its output must still be at most compressBound of what it accepted.
 *   live     repeated deflate(Z_FINISH) calls with all remaining input and 1 to 64 bytes of room
 *            end with Z_STREAM_END having consumed all input, within total_out + 2 calls.
 *   stream   the encoder output of `rest`, fed to inflate: a random history of calls (flush
 *            Z_NO_FLUSH, Z_SYNC_FLUSH or Z_FINISH, random chunks), then one call with the rest of the
 *            stream and room n - written returns Z_STREAM_END, with output = input and every
 *            stream byte consumed (InflateCompletes on a default stream; the unconditional round trip).
 *   compress compress with destLen = compressBound(n) returns Z_OK; uncompress with destLen = n
 *            returns Z_OK, destLen = n and the input; uncompress2 consumes exactly the stream.
 *
 * Input classes: 0 random, 1 zeros, 2 words, 3 random with near 3-byte repeats, 4 runs, 5 short
 * period, 6 random with 258-byte copies at the window distance, 7 bytes >= 144, 8 random with 3-byte
 * copies from the far half of the window (lazy matching at level 6 keeps them), 9 a random block
 * repeated at distance 32768 - 262 (the largest usable distance).
 * Sizes: every length below 600, lengths at k * 16383 + {-1, 0, 1} and k * 32768 + {-262, -1, 0, 1,
 * 262} for small k, 65535 .. 65537, 2^17, 2^20, 2^22, and random lengths up to 300000.
 * Usage: rt SEED COUNT. Output: "FAIL ..." per failure, then a summary. Exit 1 on any failure. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <zlib.h>

static uint64_t rs;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static size_t rn(size_t n) { return n ? (size_t)(rnd() % n) : 0; }
static int failures;
static long checked[5], early;

#define KINDS 10
#define WSIZE 32768
static void data(unsigned char *b, size_t n, unsigned kind) {
    static const char *W[] = {"the ", "quick ", "brown ", "fox ", "zlib ", "deflate ", "window ", "huffman "};
    size_t i = 0;
    switch (kind) {
    case 0: for (; i < n; i++) b[i] = (unsigned char)rnd(); break;
    case 1: memset(b, 0, n); break;
    case 2: while (i < n) { const char *w = W[rn(8)]; for (size_t k = 0; w[k] && i < n; k++) b[i++] = (unsigned char)w[k]; } break;
    case 3:
        for (; i < n; i++) {
            if (i > 3 && rn(3) == 0) { size_t d = 1 + rn(i - 3 < 4096 ? i - 3 : 4096);
                for (int k = 0; k < 3 && i < n; k++, i++) b[i] = b[i - d]; i--; }
            else b[i] = (unsigned char)rnd();
        }
        break;
    case 4:
        while (i < n) { size_t r = rn(2) ? 1 + rn(3000) : 1 + rn(40);
            unsigned char c = (unsigned char)rnd(); int run = (int)rn(2);
            for (size_t k = 0; k < r && i < n; k++) b[i++] = run ? c : (unsigned char)rnd(); }
        break;
    case 5: { unsigned char p[3]; for (int k = 0; k < 3; k++) p[k] = (unsigned char)rnd(); for (; i < n; i++) b[i] = p[i % (1 + (i / 997) % 3)]; } break;
    case 6:
        for (; i < n; i++) {
            if (i >= WSIZE && rn(64) == 0) { for (int k = 0; k < 258 && i < n; k++, i++) b[i] = b[i - WSIZE + 262]; i--; }
            else b[i] = (unsigned char)rnd();
        }
        break;
    case 7: for (; i < n; i++) b[i] = (unsigned char)(144 + rn(112)); break;
    case 8: {
        size_t hi = WSIZE - 262, lo = WSIZE / 2 + 1;
        for (; i < n && i < 2 * WSIZE; i++) b[i] = (unsigned char)rnd();
        while (i < n) {
            if (rn(10) == 0) { b[i++] = (unsigned char)rnd(); continue; }
            size_t d = lo + rn(hi - lo + 1);
            for (int k = 0; k < 3 && i < n; k++, i++) b[i] = b[i - d];
        }
        break;
    }
    default:
        for (; i < n; i++) b[i] = i < WSIZE - 262 ? (unsigned char)rnd() : b[i - (WSIZE - 262)];
        break;
    }
}

static unsigned char *enc, *dec;
static size_t encn;

static void one(const unsigned char *in, size_t n, unsigned kind) {
    z_stream s; memset(&s, 0, sizeof s);
    if (deflateInit(&s, Z_DEFAULT_COMPRESSION) != Z_OK) { printf("FAIL init\n"); failures++; return; }
    uLong bound = deflateBound(&s, n);
    if (bound != compressBound(n)) { printf("FAIL bound-ne-compressBound n=%zu bound=%lu cb=%lu\n", n, bound, compressBound(n)); failures++; }
    unsigned char *out = malloc(bound);
    s.next_in = (Bytef *)in; s.avail_in = (uInt)n; s.next_out = out; s.avail_out = (uInt)bound;
    int rc = deflate(&s, Z_FINISH);
    if (rc != Z_STREAM_END || s.total_in != n)
        { printf("FAIL one kind=%u n=%zu bound=%lu rc=%d out=%lu\n", kind, n, bound, rc, s.total_out); failures++; }
    deflateEnd(&s); free(out); checked[0]++;
}

/* unfinished_output_lt, checked after every call of a clean history that did not end it: the output
 * so far is below compressBound of the accepted input; and the stronger form the proof carries,
 * with the pending bytes and the held bits counted as written. */
static long ledgers, ledgermin = -1;
static void ledger(z_stream *s, unsigned kind, size_t n) {
    unsigned pend; int bits;
    if (deflatePending(s, &pend, &bits) != Z_OK) return;
    uLong cb = compressBound(s->total_in);
    if (s->total_out >= cb) { printf("FAIL ledger kind=%u n=%zu in=%lu out=%lu cb=%lu\n", kind, n, s->total_in, s->total_out, cb); failures++; }
    unsigned long held = s->total_out + pend + (bits + 7) / 8;
    if (held >= cb) { printf("FAIL ledger-pending kind=%u n=%zu in=%lu out=%lu pending=%u bits=%d cb=%lu\n", kind, n, s->total_in, s->total_out, pend, bits, cb); failures++; }
    long slack = (long)cb - (long)held;
    if (ledgermin < 0 || slack < ledgermin) ledgermin = slack;
    ledgers++;
}

static void rest(const unsigned char *in, size_t n, unsigned kind) {
    z_stream s; memset(&s, 0, sizeof s);
    if (deflateInit(&s, Z_DEFAULT_COMPRESSION) != Z_OK) { failures++; return; }
    uLong bound = deflateBound(&s, n);
    size_t pos = 0; int rc = Z_OK, fin = 0, calls = (int)rn(16);
    size_t maxchunk = 1 + rn(rn(2) ? 64 : 20000);
    for (int k = 0; k < calls && rc != Z_STREAM_END; k++) {
        size_t produced = s.total_out;
        size_t ain = fin && rn(2) ? 0 : (rn(2) ? rn(n - pos + 1) : rn((n - pos < 3000 ? n - pos : 3000) + 1));
        size_t aout = rn(8) ? 1 + rn(maxchunk) : 0;
        if (produced + aout > bound + 64) aout = 0;
        int flush = fin ? Z_FINISH : (rn(4) ? Z_NO_FLUSH : Z_FINISH);
        if (flush == Z_FINISH && rn(2)) ain = n - pos;   /* Z_FINISH with all remaining input, or a part of it */
        if (flush == Z_FINISH) fin = 1;
        s.next_in = (Bytef *)in + pos; s.avail_in = (uInt)ain; s.next_out = enc + produced; s.avail_out = (uInt)aout;
        rc = deflate(&s, flush);
        pos += ain - s.avail_in;
        if (rc != Z_STREAM_END) ledger(&s, kind, n);
    }
    if (rc != Z_STREAM_END) {
        size_t produced = s.total_out, room = bound > produced ? bound - produced : 1;
        s.next_in = (Bytef *)in + pos; s.avail_in = (uInt)(n - pos); s.next_out = enc + produced; s.avail_out = (uInt)room;
        rc = deflate(&s, Z_FINISH);
        if (rc == Z_BUF_ERROR && s.avail_in == n - pos) {
            /* The final block was begun under an earlier Z_FINISH with part of the input: the stream
             * takes no new input (zlib.h); the call delivers pending output and refuses. The goal's
             * premise (FINISH_STATE -> no input offered) excludes this call; with no input it ends. */
            s.avail_in = 0;
            rc = deflate(&s, Z_FINISH);
            if (rc != Z_STREAM_END || s.total_out > compressBound(s.total_in)) {
                printf("FAIL rest-early kind=%u n=%zu in=%lu rc=%d out=%lu\n", kind, n, s.total_in, rc, s.total_out);
                failures++;
            }
            early++; deflateEnd(&s); encn = 0; return;
        }
        if (rc != Z_STREAM_END || s.total_in != n) {
            printf("FAIL rest kind=%u n=%zu bound=%lu before=%zu room=%zu rc=%d after=%lu\n", kind, n, bound, produced, room, rc, s.total_out);
            failures++; deflateEnd(&s); encn = 0; return;
        }
    }
    if (s.total_out > compressBound(s.total_in)) { printf("FAIL rest-total kind=%u n=%zu in=%lu total=%lu\n", kind, n, s.total_in, s.total_out); failures++; }
    if (s.total_in != n) { early++; deflateEnd(&s); encn = 0; checked[1]++; return; }   /* ended under an early Z_FINISH */
    encn = s.total_out;
    deflateEnd(&s); checked[1]++;
}

static void live(const unsigned char *in, size_t n, unsigned kind) {
    z_stream s; memset(&s, 0, sizeof s);
    if (deflateInit(&s, Z_DEFAULT_COMPRESSION) != Z_OK) { failures++; return; }
    uLong bound = deflateBound(&s, n);
    unsigned char *out = malloc(bound + 64);
    s.next_in = (Bytef *)in; s.avail_in = (uInt)n;
    int rc = Z_OK; size_t calls = 0, room = 1 + rn(64);
    while (rc != Z_STREAM_END && calls <= bound + 2) {
        s.next_out = out + s.total_out; s.avail_out = (uInt)room;
        rc = deflate(&s, Z_FINISH); calls++;
        if (rc != Z_OK && rc != Z_STREAM_END) break;
    }
    if (rc != Z_STREAM_END || s.total_in != n || calls > s.total_out + 2)
        { printf("FAIL live kind=%u n=%zu room=%zu rc=%d calls=%zu out=%lu in=%lu\n", kind, n, room, rc, calls, s.total_out, s.total_in); failures++; }
    deflateEnd(&s); free(out); checked[2]++;
}

static void stream(const unsigned char *in, size_t n, unsigned kind) {
    if (!encn) return;
    z_stream s; memset(&s, 0, sizeof s);
    if (inflateInit(&s) != Z_OK) { failures++; return; }
    size_t pin = 0; int rc = Z_OK, calls = (int)rn(16);
    for (int k = 0; k < calls && rc != Z_STREAM_END; k++) {
        size_t ain = rn(2) ? rn(encn - pin + 1) : rn((encn - pin < 64 ? encn - pin : 64) + 1);
        size_t aout = rn(8) ? rn(n - s.total_out + 1) : 0;
        int fl = rn(3) == 0 ? Z_NO_FLUSH : rn(2) ? Z_SYNC_FLUSH : Z_FINISH;
        s.next_in = enc + pin; s.avail_in = (uInt)ain; s.next_out = dec + s.total_out; s.avail_out = (uInt)aout;
        rc = inflate(&s, fl);
        pin += ain - s.avail_in;
        if (rc != Z_OK && rc != Z_BUF_ERROR && rc != Z_STREAM_END) break;
    }
    if (rc != Z_STREAM_END) {
        int fl = rn(3) == 0 ? Z_NO_FLUSH : rn(2) ? Z_SYNC_FLUSH : Z_FINISH;
        size_t room = n - s.total_out;
        unsigned char spare;
        s.next_in = enc + pin; s.avail_in = (uInt)(encn - pin); s.next_out = room ? dec + s.total_out : &spare; s.avail_out = (uInt)room;
        rc = inflate(&s, fl);
    }
    if (rc != Z_STREAM_END || s.total_out != n || s.total_in != encn || memcmp(dec, in, n))
        { printf("FAIL stream kind=%u n=%zu enc=%zu rc=%d out=%lu in=%lu\n", kind, n, encn, rc, s.total_out, s.total_in); failures++; }
    inflateEnd(&s); checked[3]++;
}

static void compress_rt(const unsigned char *in, size_t n, unsigned kind) {
    uLongf cl = compressBound(n);
    unsigned char *c = malloc(cl);
    int rc = compress(c, &cl, in, n);
    if (rc != Z_OK) { printf("FAIL compress kind=%u n=%zu rc=%d\n", kind, n, rc); failures++; free(c); return; }
    uLongf dl = n; unsigned char spare;
    rc = uncompress(n ? dec : &spare, &dl, c, cl);
    if (rc != Z_OK || dl != n || memcmp(dec, in, n)) { printf("FAIL uncompress kind=%u n=%zu rc=%d dl=%lu\n", kind, n, rc, dl); failures++; }
    uLong sl = cl; dl = n;
    rc = uncompress2(n ? dec : &spare, &dl, c, &sl);
    if (rc != Z_OK || dl != n || sl != cl) { printf("FAIL uncompress2 kind=%u n=%zu rc=%d sl=%lu cl=%lu\n", kind, n, rc, sl, cl); failures++; }
    free(c); checked[4]++;
}

static void all(unsigned char *in, size_t n, unsigned kind) {
    data(in, n, kind);
    one(in, n, kind); rest(in, n, kind); live(in, n, kind); stream(in, n, kind); compress_rt(in, n, kind);
}

/* Negative control (mode `flushes`): flushes other than Z_NO_FLUSH and Z_FINISH cost output without input,
 * so the bound promise does not cover them (zlib.h) and the clean histories of the bound goals exclude them.
 * After deflateInit, COUNT single bytes each with Z_SYNC_FLUSH (or Z_FULL_FLUSH, or Z_PARTIAL_FLUSH), then one
 * Z_FINISH call with room max(1, compressBound(COUNT) - produced): this must fail to end. Exit 0 when all three
 * fail as expected. */
static int flushes(size_t count) {
    static const int F[] = {Z_SYNC_FLUSH, Z_FULL_FLUSH, Z_PARTIAL_FLUSH};
    static const char *N[] = {"sync", "full", "partial"};
    int expected = 0;
    unsigned char in[1] = {'a'}, *out = malloc(64 * count + 64);
    for (int f = 0; f < 3; f++) {
        z_stream s; memset(&s, 0, sizeof s);
        if (deflateInit(&s, Z_DEFAULT_COMPRESSION) != Z_OK) return 2;
        for (size_t i = 0; i < count; i++) {
            s.next_in = in; s.avail_in = 1; s.next_out = out + s.total_out; s.avail_out = 64;
            deflate(&s, F[f]);
        }
        size_t produced = s.total_out, bound = compressBound(count);
        size_t room = bound > produced ? bound - produced : 1;
        s.next_in = in; s.avail_in = 0; s.next_out = out + produced; s.avail_out = (uInt)room;
        int rc = deflate(&s, Z_FINISH);
        printf("CONTROL %s count=%zu produced_before=%zu bound=%zu room=%zu rc=%d %s\n", N[f], count, produced,
               bound, room, rc, rc == Z_STREAM_END ? "ENDED (unexpected)" : "did not end (expected)");
        if (rc != Z_STREAM_END) expected++;
        deflateEnd(&s);
    }
    free(out);
    return expected == 3 ? 0 : 1;
}

int main(int argc, char **argv) {
    if (argc == 3 && !strcmp(argv[1], "flushes")) return flushes(strtoull(argv[2], 0, 10));
    if (argc < 3) { fprintf(stderr, "usage: rt SEED COUNT | rt flushes COUNT\n"); return 2; }
    rs = strtoull(argv[1], 0, 10) * 0x9E3779B97F4A7C15ull + 1;
    size_t count = strtoull(argv[2], 0, 10), maxn = (size_t)1 << 22;
    unsigned char *in = malloc(maxn + 1);
    enc = malloc(compressBound(maxn) + 128); dec = malloc(maxn + 1);
    size_t sizes[200], ns = 0;
    for (int k = 1; k <= 8; k++) for (int d = -1; d <= 1; d++) sizes[ns++] = (size_t)(k * 16383 + d);
    for (int k = 1; k <= 6; k++) { static const int D[] = {-262, -1, 0, 1, 262}; for (int j = 0; j < 5; j++) sizes[ns++] = (size_t)(k * 32768 + D[j]); }
    sizes[ns++] = 65535; sizes[ns++] = 65536; sizes[ns++] = 65537; sizes[ns++] = 1 << 17; sizes[ns++] = 1 << 20;
    for (unsigned kind = 0; kind < KINDS; kind++) {
        for (size_t n = 0; n < 600; n++) all(in, n, kind);
        for (size_t j = 0; j < ns; j++) all(in, sizes[j], kind);
    }
    for (unsigned kind = 0; kind < KINDS; kind++) all(in, (size_t)1 << 22, kind);
    for (size_t t = 0; t < count; t++) all(in, rn(300001), (unsigned)rn(KINDS));
    printf("CHECKED one=%ld rest=%ld (early end %ld) live=%ld stream=%ld compress=%ld ledger=%ld (min slack %ld)\nFAILURES %d\n",
           checked[0], checked[1], early, checked[2], checked[3], checked[4], ledgers, ledgermin, failures);
    return failures != 0;
}
