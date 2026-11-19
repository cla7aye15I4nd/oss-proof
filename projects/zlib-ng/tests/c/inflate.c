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

int main(void) {
    char *line = NULL; size_t cap = 0;
    while (getline(&line, &cap, stdin) >= 0) {
        char *tok[16]; int nt = 0; char *save;
        for (char *t = strtok_r(line, " \t\r\n", &save); t && nt < 16; t = strtok_r(NULL, " \t\r\n", &save))
            tok[nt++] = t;
        if (nt == 0) continue;
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
