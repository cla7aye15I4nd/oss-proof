/* C side of the differential test for inflate.c: links the REAL patched zlib-ng (verified configuration).
 * One test per line:
 *   inf <windowBits> <flush> <inchunk> <outchunk> <outcap> <data> <dict> <hdr> <reset>
 * <data>, <dict>: hex digits ("-" for an empty input / no dictionary).
 * <hdr>: "-" or "<extra_max>,<name_max>,<comm_max>": call inflateGetHeader with a gz_header whose buffers have
 *   these sizes (0 = NULL pointer), filled with 0xAA.
 * <reset>: "-", "R" (inflateReset), "K" (inflateResetKeep) or "W<bits>" (inflateReset2): after the first decode,
 *   reset the stream and decode the same data again into a fresh output buffer.
 * A decode calls inflate(flush) with avail_in = min(inchunk, input left) and avail_out = min(outchunk, output space
 * left) until a call returns neither Z_OK nor Z_BUF_ERROR (Z_NEED_DICT with a dictionary: inflateSetDictionary,
 * then go on), or makes no progress, or 20000 calls. Output (one line): the init result, then per call
 * "ret:in_off:avail_in:out_off:avail_out:total_in:total_out:adler:data_type:msg", then the produced bytes, the
 * header fields and buffers, and the inflateEnd result. */
#include "common.h"
#include <stdint.h>
#include "zlib.h"

static void hex_out(const unsigned char *p, size_t n) {
    if (n == 0) { fputs("-", stdout); return; }
    for (size_t i = 0; i < n; i++) printf("%02x", p[i]);
}

static unsigned char *parse_hex(const char *s, size_t *len) {
    if (strcmp(s, "-") == 0) { *len = 0; unsigned char *b = malloc(1); return b; }
    size_t n = strlen(s);
    if (n % 2) { fprintf(stderr, "odd hex\n"); exit(2); }
    *len = n / 2;
    unsigned char *b = malloc(*len ? *len : 1);
    for (size_t i = 0; i < *len; i++) b[i] = (unsigned char)(hexval(s[2 * i]) * 16 + hexval(s[2 * i + 1]));
    return b;
}

static void decode(z_stream *s, unsigned char *in, size_t inlen, unsigned char *out, size_t outcap, int flush,
                   size_t inchunk, size_t outchunk, unsigned char *dict, size_t dictlen, int havedict) {
    s->next_in = in;
    s->next_out = out;
    for (int calls = 0; calls < 20000; calls++) {
        size_t inleft = inlen - (size_t)(s->next_in - in);
        size_t outleft = outcap - (size_t)(s->next_out - out);
        s->avail_in = (uInt)(inleft < inchunk ? inleft : inchunk);
        s->avail_out = (uInt)(outleft < outchunk ? outleft : outchunk);
        unsigned char *ni = s->next_in, *no = s->next_out;
        int r = inflate(s, flush);
        printf(" %d:%zu:%u:%zu:%u:%lu:%lu:%lu:%d:%s", r, (size_t)(s->next_in - in), s->avail_in,
               (size_t)(s->next_out - out), s->avail_out, s->total_in, s->total_out, s->adler, s->data_type,
               s->msg ? s->msg : "-");
        if (r == Z_NEED_DICT && havedict) {
            printf(" setdict:%d", inflateSetDictionary(s, dict, (uInt)dictlen));
            havedict = 0;
            continue;
        }
        if (r != Z_OK && r != Z_BUF_ERROR) return;
        if (s->next_in == ni && s->next_out == no) return;
    }
    printf(" LIMIT");
}

static void fields(z_stream *s, unsigned char *in, unsigned char *out) {
    printf(":%zu:%u:%zu:%u:%lu:%lu:%lu:%d:%s", (size_t)(s->next_in - in), s->avail_in, (size_t)(s->next_out - out),
           s->avail_out, s->total_in, s->total_out, s->adler, s->data_type, s->msg ? s->msg : "-");
}

/* ops <windowBits> <outcap> <data> <dict> <script>: a script of calls on one stream, comma-separated:
 * i<k> avail_in = min(k, input left); o<k> avail_out = min(k, space left); f<n> inflate(n); P<bits>/<value>
 * inflatePrime; S inflateSync; Y inflateSyncPoint; C inflateCopy to a new stream, inflateEnd of the old one, go on
 * with the copy; G<n> inflateGetDictionary into an n-byte buffer (0: NULL); g inflateGetDictionary(NULL, NULL);
 * d inflateSetDictionary(dict); n inflateSetDictionary(NULL, 0); U<v> inflateUndermine; V<v> inflateValidate;
 * M inflateMark; N inflateCodesUsed; R / K / W<bits> the resets; E inflateEnd. */
static void run_ops(char **tok) {
    int wbits = (int)parse_i(tok[1]);
    size_t outcap = (size_t)parse_u(tok[2]);
    size_t inlen, dictlen;
    unsigned char *in = parse_hex(tok[3], &inlen);
    unsigned char *dict = parse_hex(tok[4], &dictlen);
    unsigned char *out = malloc(outcap ? outcap : 1);
    z_stream s1, s2; memset(&s1, 0, sizeof s1); memset(&s2, 0, sizeof s2);
    z_stream *s = &s1;
    int r = inflateInit2_(s, wbits, ZLIB_VERSION, (int)sizeof(z_stream));
    printf("init:%d", r);
    if (r != Z_OK) { printf("\n"); free(in); free(dict); free(out); return; }
    s->next_in = in; s->next_out = out;
    char *save;
    for (char *op = strtok_r(tok[5], ",", &save); op; op = strtok_r(NULL, ",", &save)) {
        char c = op[0];
        if (c == 'i') { size_t k = (size_t)parse_u(op + 1), left = inlen - (size_t)(s->next_in - in);
                        s->avail_in = (uInt)(left < k ? left : k); continue; }
        if (c == 'o') { size_t k = (size_t)parse_u(op + 1), left = outcap - (size_t)(s->next_out - out);
                        s->avail_out = (uInt)(left < k ? left : k); continue; }
        printf(" %s", op);
        if (c == 'f') { r = inflate(s, (int)parse_i(op + 1)); printf("=%d", r); fields(s, in, out); }
        else if (c == 'P') { char *sl = strchr(op, '/'); *sl = 0;
                             printf("=%d", inflatePrime(s, (int)parse_i(op + 1), (int)parse_i(sl + 1))); }
        else if (c == 'S') { printf("=%d", inflateSync(s)); fields(s, in, out); }
        else if (c == 'Y') printf("=%d", inflateSyncPoint(s));
        else if (c == 'C') { r = inflateCopy(&s2, s); printf("=%d", r);
                             if (r == Z_OK) { printf(":%d", inflateEnd(s)); s = &s2; } }
        else if (c == 'G') { size_t n = (size_t)parse_u(op + 1); unsigned char *b = n ? malloc(n) : NULL;
                             if (b) memset(b, 0xaa, n); uInt len = 12345;
                             printf("=%d:%u:", inflateGetDictionary(s, b, &len), len);
                             if (b) hex_out(b, n); else printf("-"); free(b); }
        else if (c == 'g') printf("=%d", inflateGetDictionary(s, NULL, NULL));
        else if (c == 'd') printf("=%d", inflateSetDictionary(s, dict, (uInt)dictlen));
        else if (c == 'n') printf("=%d", inflateSetDictionary(s, NULL, 0));
        else if (c == 'U') printf("=%d", inflateUndermine(s, (int)parse_i(op + 1)));
        else if (c == 'V') printf("=%d", inflateValidate(s, (int)parse_i(op + 1)));
        else if (c == 'M') printf("=%ld", inflateMark(s));
        else if (c == 'N') printf("=%lu", inflateCodesUsed(s));
        else if (c == 'R') printf("=%d", inflateReset(s));
        else if (c == 'K') printf("=%d", inflateResetKeep(s));
        else if (c == 'W') printf("=%d", inflateReset2(s, (int)parse_i(op + 1)));
        else if (c == 'E') printf("=%d", inflateEnd(s));
        else { fprintf(stderr, "bad op %s\n", op); exit(2); }
    }
    printf(" out:"); hex_out(out, (size_t)(s->next_out - out));
    printf(" end:%d\n", inflateEnd(s));
    if (s != &s1) inflateEnd(&s1);
    free(in); free(dict); free(out);
}

/* unc <variant u|u2|uz|u2z> <dest: size|null> <destLen: value|null> <sourceLen: value|null> <source: hex|null> */
static void run_unc(char **tok) {
    const char *v = tok[1];
    int dnull = strcmp(tok[2], "null") == 0, dlnull = strcmp(tok[3], "null") == 0;
    int slnull = strcmp(tok[4], "null") == 0, snull = strcmp(tok[5], "null") == 0;
    size_t dsize = dnull ? 0 : (size_t)parse_u(tok[2]);
    unsigned char *dest = dnull ? NULL : malloc(dsize ? dsize : 1);
    if (dest) memset(dest, 0xaa, dsize ? dsize : 1);
    size_t slen; unsigned char *src = snull ? NULL : parse_hex(tok[6], &slen);
    unsigned long dl = dlnull ? 0 : (unsigned long)parse_u(tok[3]);
    unsigned long sl = slnull ? 0 : (unsigned long)parse_u(tok[4]);
    int r;
    if (strcmp(v, "u") == 0) r = uncompress(dest, dlnull ? NULL : &dl, src, sl);
    else if (strcmp(v, "u2") == 0) r = uncompress2(dest, dlnull ? NULL : &dl, src, slnull ? NULL : &sl);
    else if (strcmp(v, "uz") == 0) { size_t d = dl; r = uncompress_z(dest, dlnull ? NULL : &d, src, sl); dl = d; }
    else { size_t d = dl, s2 = sl; r = uncompress2_z(dest, dlnull ? NULL : &d, src, slnull ? NULL : &s2); dl = d; sl = s2; }
    printf("%d:%lu:%lu:", r, dl, sl);
    if (dest) hex_out(dest, dsize); else printf("-");
    printf("\n");
    free(dest); free(src);
}

/* ver <version: string|null> <stream_size> <windowBits|->: inflateInit_ / inflateInit2_ with that version. */
static void run_ver(char **tok) {
    const char *ver = strcmp(tok[1], "null") == 0 ? NULL : tok[1];
    int size = (int)parse_i(tok[2]);
    z_stream s; memset(&s, 0, sizeof s);
    int r = strcmp(tok[3], "-") == 0 ? inflateInit_(&s, ver, size) : inflateInit2_(&s, (int)parse_i(tok[3]), ver, size);
    printf("init:%d end:%d\n", r, r == Z_OK ? inflateEnd(&s) : 99);
}

int main(void) {
    char *line = NULL; size_t cap = 0;
    while (getline(&line, &cap, stdin) >= 0) {
        char *tok[16]; int nt = 0; char *save;
        for (char *t = strtok_r(line, " \t\r\n", &save); t && nt < 16; t = strtok_r(NULL, " \t\r\n", &save))
            tok[nt++] = t;
        if (nt == 0) continue;
        if (strcmp(tok[0], "ops") == 0 && nt == 6) { run_ops(tok); continue; }
        if (strcmp(tok[0], "unc") == 0 && nt == 7) { run_unc(tok); continue; }
        if (strcmp(tok[0], "ver") == 0 && nt == 4) { run_ver(tok); continue; }
        if (strcmp(tok[0], "inf") != 0 || nt != 10) { printf("BADINPUT\n"); continue; }
        int wbits = (int)parse_i(tok[1]);
        int flush = (int)parse_i(tok[2]);
        size_t inchunk = (size_t)parse_u(tok[3]), outchunk = (size_t)parse_u(tok[4]);
        size_t outcap = (size_t)parse_u(tok[5]);
        size_t inlen, dictlen;
        unsigned char *in = parse_hex(tok[6], &inlen);
        unsigned char *dict = parse_hex(tok[7], &dictlen);
        int havedict = strcmp(tok[7], "-") != 0;
        z_stream s; memset(&s, 0, sizeof s);
        int r = inflateInit2_(&s, wbits, ZLIB_VERSION, (int)sizeof(z_stream));
        printf("init:%d", r);
        if (r != Z_OK) { printf("\n"); free(in); free(dict); continue; }
        gz_header h; memset(&h, 0, sizeof h);
        unsigned extra_max = 0, name_max = 0, comm_max = 0;
        int hdr = strcmp(tok[8], "-") != 0;
        if (hdr) {
            if (sscanf(tok[8], "%u,%u,%u", &extra_max, &name_max, &comm_max) != 3) { fprintf(stderr, "bad hdr\n"); exit(2); }
            h.extra = extra_max ? malloc(extra_max) : NULL;
            h.name = name_max ? malloc(name_max) : NULL;
            h.comment = comm_max ? malloc(comm_max) : NULL;
            if (h.extra) memset(h.extra, 0xaa, extra_max);
            if (h.name) memset(h.name, 0xaa, name_max);
            if (h.comment) memset(h.comment, 0xaa, comm_max);
            h.extra_max = extra_max; h.name_max = name_max; h.comm_max = comm_max;
            h.text = 7; h.time = 7; h.xflags = 7; h.os = 7; h.extra_len = 7; h.hcrc = 7; h.done = 7;
            printf(" gethdr:%d", inflateGetHeader(&s, &h));
        }
        unsigned char *out = malloc(outcap ? outcap : 1);
        decode(&s, in, inlen, out, outcap, flush, inchunk, outchunk, dict, dictlen, havedict);
        printf(" out:"); hex_out(out, (size_t)(s.next_out - out));
        if (hdr) {
            printf(" hdr:%d:%lu:%d:%d:%u:%d:%d:", h.text, h.time, h.xflags, h.os, h.extra_len, h.hcrc, h.done);
            printf("%s:%s:%s:", h.extra ? "p" : "n", h.name ? "p" : "n", h.comment ? "p" : "n");
            if (h.extra) hex_out(h.extra, extra_max); else printf("-");
            printf(":"); if (h.name) hex_out(h.name, name_max); else printf("-");
            printf(":"); if (h.comment) hex_out(h.comment, comm_max); else printf("-");
        }
        if (strcmp(tok[9], "-") != 0) {
            if (tok[9][0] == 'R') r = inflateReset(&s);
            else if (tok[9][0] == 'K') r = inflateResetKeep(&s);
            else r = inflateReset2(&s, (int)parse_i(tok[9] + 1));
            printf(" reset:%d", r);
            unsigned char *out2 = malloc(outcap ? outcap : 1);
            decode(&s, in, inlen, out2, outcap, flush, inchunk, outchunk, dict, dictlen, havedict);
            printf(" out:"); hex_out(out2, (size_t)(s.next_out - out2));
            free(out2);
        }
        printf(" end:%d\n", inflateEnd(&s));
        free(out); free(in); free(dict);
        if (hdr) { free(h.extra); free(h.name); free(h.comment); }
    }
    free(line);
    return 0;
}
