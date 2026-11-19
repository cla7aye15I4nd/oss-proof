/* C side of the differential test for deflate.c (with trees.c, the strategies, insert_string.c, the generic
 * compare256 / longest_match / slide_hash) and compress.c: links the REAL patched zlib-ng (verified configuration).
 * Two kinds of lines:
 *
 *   def <level> <method> <windowBits> <memLevel> <strategy> <data> <dict> <hdr> <outcap> <script>
 *
 * deflateInit2_ on a fresh stream, then a script of calls on it (comma-separated, never empty; "-" is none):
 *   i<k>  avail_in = min(k, input left)         o<k>  avail_out = min(k, output space left)
 *   f<n>  deflate(n)                            L<n>/<ic>/<oc>  loop: avail_in = min(ic, left), avail_out =
 *         min(oc, space left), deflate(n), until a call does not return Z_OK or makes no progress (200000 calls)
 *   P<bits>/<value> deflatePrime   Q<level>/<strategy> deflateParams   T<good>/<lazy>/<nice>/<chain> deflateTune
 *   C     deflateCopy to a new stream, deflateEnd of the old one, go on with the copy
 *   D     deflateSetDictionary(dict)            d  deflateSetDictionary(NULL, 0)
 *   G<n>  deflateGetDictionary into an n-byte buffer (0: NULL) and a length cell; g: (NULL, NULL)
 *   p     deflatePending(&pending, &bits)       q  deflatePending(NULL, NULL)
 *   u     deflateUsed(&bits)                    B<n>  deflateBound(strm, n)    b<n>  deflateBound_z(strm, n)
 *   R / K deflateReset / deflateResetKeep       H  deflateSetHeader(header)   E  deflateEnd
 * Each call prints "<ret>" plus the stream fields ":in_off:avail_in:out_off:avail_out:total_in:total_out:adler:
 * data_type:msg" (for deflate: always; for the others: the values they return). At the end: the output bytes and
 * the result of a final deflateEnd (unless the script ended the stream).
 *
 *   cmp <fn> <level> <data> <outcap|N> <destLen|N>
 *
 * compress / compress2 / compress_z / compress2_z (<fn> = c, c2, cz, c2z; <level> ignored by c / cz) with a
 * destination of outcap bytes (N: NULL) and a length cell holding destLen (N: a NULL cell). Prints the result,
 * the cell and the output bytes.
 *
 * <data>, <dict>: "-" (empty), "null" (NULL pointer, no bytes), "hex:<digits>" or "gen:<kind>:<len>:<seed>" (see
 * gen_data). <hdr>: "-" (no header object) or "<text>/<time>/<xflags>/<os>/<extra>/<name>/<comment>/<hcrc>" where
 * <extra>, <name>, <comment> are -1 (NULL) or a length (extra: extra_len bytes; name, comment: that many non-zero
 * characters and a NUL). */
#include "common.h"
#include <stdint.h>
#include "zlib.h"

static void hex_out(const unsigned char *p, size_t n) {
    if (n == 0) { fputs("-", stdout); return; }
    for (size_t i = 0; i < n; i++) printf("%02x", p[i]);
}

/* Test data, identical in tests/lean/Driver/Deflate.lean: xorshift32 from seed | 1. */
static unsigned char *gen_data(const char *s, size_t *len, int *isnull) {
    *isnull = 0;
    if (strcmp(s, "-") == 0) { *len = 0; return malloc(1); }
    if (strcmp(s, "null") == 0) { *len = 0; *isnull = 1; return NULL; }
    if (strncmp(s, "hex:", 4) == 0) {
        s += 4;
        size_t n = strlen(s);
        if (n % 2) { fprintf(stderr, "odd hex\n"); exit(2); }
        *len = n / 2;
        unsigned char *b = malloc(*len ? *len : 1);
        for (size_t i = 0; i < *len; i++) b[i] = (unsigned char)(hexval(s[2 * i]) * 16 + hexval(s[2 * i + 1]));
        return b;
    }
    char kind; unsigned long long n, seed;
    if (sscanf(s, "gen:%c:%llu:%llu", &kind, &n, &seed) != 3) { fprintf(stderr, "bad data %s\n", s); exit(2); }
    *len = (size_t)n;
    unsigned char *b = malloc(n ? n : 1);
    uint32_t x = (uint32_t)seed | 1u;
    static const char alpha[] = "etaoin shrdlu\n";
    for (size_t i = 0; i < n; i++) {
        x ^= x << 13; x ^= x >> 17; x ^= x << 5;
        char k = kind;
        if (k == 'm') { static const char ks[] = "rtpz"; k = ks[(i / 1000) % 4]; }
        unsigned char v;
        switch (k) {
        case 'z': v = 0; break;
        case 'r': v = (unsigned char)(x & 0xff); break;
        case 't': v = (unsigned char)alpha[x % 14]; break;
        case 'p': v = (unsigned char)((i % (1 + seed % 61)) * 7 + 3); break;
        case 'b': v = (unsigned char)(x % 4); break;
        default: fprintf(stderr, "bad kind\n"); exit(2);
        }
        b[i] = v;
    }
    return b;
}

static void fields(z_stream *s, unsigned char *in, unsigned char *out) {
    printf(":%zu:%u:%zu:%u:%lu:%lu:%lu:%d:%s", s->next_in ? (size_t)(s->next_in - in) : 0, s->avail_in,
           s->next_out ? (size_t)(s->next_out - out) : 0, s->avail_out, s->total_in, s->total_out, s->adler,
           s->data_type, s->msg ? s->msg : "-");
}

static void run_def(char **tok, int nt) {
    if (nt != 11) { printf("BADINPUT\n"); return; }
    int level = (int)parse_i(tok[1]), method = (int)parse_i(tok[2]), wbits = (int)parse_i(tok[3]);
    int memlevel = (int)parse_i(tok[4]), strategy = (int)parse_i(tok[5]);
    size_t inlen, dictlen; int innull, dictnull;
    unsigned char *in = gen_data(tok[6], &inlen, &innull);
    unsigned char *dict = gen_data(tok[7], &dictlen, &dictnull);
    size_t outcap = (size_t)parse_u(tok[9]);
    unsigned char *out = malloc(outcap ? outcap : 1);
    gz_header hdr; memset(&hdr, 0, sizeof hdr);
    unsigned char *hx = NULL, *hn = NULL, *hc = NULL;
    int havehdr = strcmp(tok[8], "-") != 0;
    if (havehdr) {
        long long t, tm, xf, os, ex, nm, cm, hc_;
        if (sscanf(tok[8], "%lld/%lld/%lld/%lld/%lld/%lld/%lld/%lld", &t, &tm, &xf, &os, &ex, &nm, &cm, &hc_) != 8) {
            printf("BADINPUT\n"); return;
        }
        hdr.text = (int)t; hdr.time = (uLong)tm; hdr.xflags = (int)xf; hdr.os = (int)os; hdr.hcrc = (int)hc_;
        if (ex >= 0) { hx = malloc(ex ? (size_t)ex : 1); for (long long i = 0; i < ex; i++) hx[i] = (unsigned char)(i * 7 + 1);
                       hdr.extra = hx; hdr.extra_len = (uInt)ex; hdr.extra_max = (uInt)ex; }
        if (nm >= 0) { hn = malloc((size_t)nm + 1); for (long long i = 0; i < nm; i++) hn[i] = (unsigned char)('a' + i % 26);
                       hn[nm] = 0; hdr.name = hn; hdr.name_max = (uInt)nm + 1; }
        if (cm >= 0) { hc = malloc((size_t)cm + 1); for (long long i = 0; i < cm; i++) hc[i] = (unsigned char)('A' + i % 26);
                       hc[cm] = 0; hdr.comment = hc; hdr.comm_max = (uInt)cm + 1; }
    }
    z_stream s1, s2; memset(&s1, 0, sizeof s1); memset(&s2, 0, sizeof s2);
    z_stream *s = &s1;
    int r = deflateInit2_(s, level, method, wbits, memlevel, strategy, ZLIB_VERSION, (int)sizeof(z_stream));
    printf("init:%d", r);
    fields(s, in, out);
    int live = r == Z_OK;
    s->next_in = innull ? NULL : in;
    s->next_out = out;
    char *save;
    for (char *op = strtok_r(tok[10], ",", &save); op && live; op = strtok_r(NULL, ",", &save)) {
        char c = op[0];
        const char *a = op + 1;
        if (c == '-') continue;
        if (c == 'i') {
            size_t k = (size_t)parse_u(a), left = inlen - (s->next_in ? (size_t)(s->next_in - in) : 0);
            s->avail_in = (uInt)(left < k ? left : k);
        } else if (c == 'o') {
            size_t k = (size_t)parse_u(a), left = outcap - (size_t)(s->next_out - out);
            s->avail_out = (uInt)(left < k ? left : k);
        } else if (c == 'f') {
            r = deflate(s, (int)parse_i(a));
            printf(" f%d", r); fields(s, in, out);
        } else if (c == 'L') {
            int n; unsigned long ic, oc;
            if (sscanf(a, "%d/%lu/%lu", &n, &ic, &oc) != 3) { printf(" BADOP"); break; }
            printf(" L");
            int calls;
            for (calls = 0; calls < 200000; calls++) {
                size_t inleft = inlen - (s->next_in ? (size_t)(s->next_in - in) : 0);
                size_t outleft = outcap - (size_t)(s->next_out - out);
                s->avail_in = (uInt)(inleft < ic ? inleft : ic);
                s->avail_out = (uInt)(outleft < oc ? outleft : oc);
                const unsigned char *ni = s->next_in; unsigned char *no = s->next_out;
                r = deflate(s, n);
                printf(" %d", r); fields(s, in, out);
                if (r != Z_OK) break;
                if (s->next_in == ni && s->next_out == no) break;
            }
            if (calls == 200000) printf(" LIMIT");
        } else if (c == 'P') {
            int bits, value;
            if (sscanf(a, "%d/%d", &bits, &value) != 2) { printf(" BADOP"); break; }
            printf(" P%d", deflatePrime(s, bits, value));
        } else if (c == 'Q') {
            int lv, st;
            if (sscanf(a, "%d/%d", &lv, &st) != 2) { printf(" BADOP"); break; }
            r = deflateParams(s, lv, st);
            printf(" Q%d", r); fields(s, in, out);
        } else if (c == 'T') {
            int g, l, n, ch;
            if (sscanf(a, "%d/%d/%d/%d", &g, &l, &n, &ch) != 4) { printf(" BADOP"); break; }
            printf(" T%d", deflateTune(s, g, l, n, ch));
        } else if (c == 'C') {
            z_stream *d = s == &s1 ? &s2 : &s1;
            r = deflateCopy(d, s);
            printf(" C%d", r);
            if (r == Z_OK) { printf(":%d", deflateEnd(s)); s = d; }
        } else if (c == 'D') {
            printf(" D%d", deflateSetDictionary(s, dictnull ? NULL : dict, (uInt)dictlen));
            fields(s, in, out);
        } else if (c == 'd') {
            printf(" d%d", deflateSetDictionary(s, NULL, 0));
        } else if (c == 'G') {
            size_t n = (size_t)parse_u(a);
            unsigned char *buf = n ? malloc(n) : NULL;
            uInt len = 7777;
            r = deflateGetDictionary(s, buf, &len);
            printf(" G%d:%u:", r, len);
            if (buf) hex_out(buf, r == Z_OK && len <= n ? len : 0); else fputs("-", stdout);
            free(buf);
        } else if (c == 'g') {
            printf(" g%d", deflateGetDictionary(s, NULL, NULL));
        } else if (c == 'p') {
            unsigned pend = 7777; int bits = 7777;
            r = deflatePending(s, &pend, &bits);
            printf(" p%d:%u:%d", r, pend, bits);
        } else if (c == 'q') {
            printf(" q%d", deflatePending(s, NULL, NULL));
        } else if (c == 'u') {
            int bits = 7777;
            r = deflateUsed(s, &bits);
            printf(" u%d:%d", r, bits);
        } else if (c == 'B') {
            printf(" B%lu", deflateBound(s, (uLong)parse_u(a)));
        } else if (c == 'b') {
            printf(" b%zu", deflateBound_z(s, (size_t)parse_u(a)));
        } else if (c == 'R') {
            r = deflateReset(s);
            printf(" R%d", r); fields(s, in, out);
        } else if (c == 'K') {
            r = deflateResetKeep(s);
            printf(" K%d", r); fields(s, in, out);
        } else if (c == 'H') {
            printf(" H%d", deflateSetHeader(s, havehdr ? &hdr : NULL));
        } else if (c == 'E') {
            r = deflateEnd(s);
            printf(" E%d", r);
            live = 0;
        } else { printf(" BADOP"); break; }
    }
    printf(" out:");
    hex_out(out, (size_t)(s->next_out - out));
    if (live) printf(" end:%d", deflateEnd(s));
    if (havehdr) printf(" hdr:%d:%lu", hdr.done, hdr.time);
    printf("\n");
    free(in); free(dict); free(out); free(hx); free(hn); free(hc);
}

static void run_cmp(char **tok, int nt) {
    if (nt != 6) { printf("BADINPUT\n"); return; }
    const char *fn = tok[1];
    int level = (int)parse_i(tok[2]);
    size_t inlen; int innull;
    unsigned char *in = gen_data(tok[3], &inlen, &innull);
    int outnull = strcmp(tok[4], "N") == 0, cellnull = strcmp(tok[5], "N") == 0;
    size_t outcap = outnull ? 0 : (size_t)parse_u(tok[4]);
    unsigned char *out = outnull ? NULL : malloc(outcap ? outcap : 1);
    unsigned long long cell = cellnull ? 0 : parse_u(tok[5]);
    const unsigned char *src = innull ? NULL : in;
    int r;
    unsigned long ul = (unsigned long)cell; size_t sz = (size_t)cell;
    if (strcmp(fn, "c") == 0) { r = compress(out, cellnull ? NULL : &ul, src, (uLong)inlen); cell = ul; }
    else if (strcmp(fn, "c2") == 0) { r = compress2(out, cellnull ? NULL : &ul, src, (uLong)inlen, level); cell = ul; }
    else if (strcmp(fn, "cz") == 0) { r = compress_z(out, cellnull ? NULL : &sz, src, inlen); cell = sz; }
    else if (strcmp(fn, "c2z") == 0) { r = compress2_z(out, cellnull ? NULL : &sz, src, inlen, level); cell = sz; }
    else { printf("BADINPUT\n"); free(in); free(out); return; }
    printf("%d:", r);
    if (cellnull) printf("N"); else printf("%llu", cell);
    printf(":");
    if (out && r == Z_OK) hex_out(out, (size_t)cell); else fputs("-", stdout);
    printf("\n");
    free(in); free(out);
}

int main(void) {
    char *line = NULL; size_t cap = 0;
    while (getline(&line, &cap, stdin) >= 0) {
        char *tok[12]; int nt = 0; char *save;
        for (char *t = strtok_r(line, " \t\r\n", &save); t && nt < 12; t = strtok_r(NULL, " \t\r\n", &save))
            tok[nt++] = t;
        if (nt == 0) continue;
        if (strcmp(tok[0], "def") == 0) run_def(tok, nt);
        else if (strcmp(tok[0], "cmp") == 0) run_cmp(tok, nt);
        else printf("BADINPUT\n");
        fflush(stdout);
    }
    free(line);
    return 0;
}
