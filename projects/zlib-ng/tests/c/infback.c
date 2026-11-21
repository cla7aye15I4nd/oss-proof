/* C side of the differential test for infback.c: links the REAL patched zlib-ng (verified configuration).
 * One test per line:
 *   back <windowBits> <first> <chunks> <limit> <abort> <calls> <data>
 *     inflateBackInit_ with a malloc'ed window of exactly 1 << windowBits bytes, then <calls> inflateBack calls
 *     (each starts again from the first input byte), then inflateBackEnd.
 *     <first>: "null" (next_in = NULL), "z" (next_in = a 1-byte block, avail_in = 0), or k: the first k bytes are
 *       given in next_in / avail_in (a block of exactly k bytes, at least 1).
 *     <chunks>: comma-separated sizes cycled by in(): each call hands out the next bytes in a fresh block of
 *       exactly that many bytes (the previous block is freed then); "-" = everything left at once.
 *     <limit>: in() returns 0 once this many bytes were handed out in all (counting <first>), "-" = at the end.
 *     <abort>: "-", or n: the n-th call of out() returns 1 (0 otherwise).
 *     <data>: hex digits, "-" for none.
 *   Output: "init:<r>", per call " back:<ret>:<next_in>:<avail_in>:<msg>:<in calls>:<out lengths>:<out bytes>"
 *   (<next_in>: "N" for NULL, "f+<offset>" into the first buffer, "c<i>+<offset>" into the i-th in() block),
 *   then " end:<r>".
 *   init <windowBits> <window: w|null> <version: string|null> <stream_size>: inflateBackInit_ alone, then
 *     inflateBackEnd when it succeeded.
 *   misc: inflateBack(NULL, ...), inflateBackEnd(NULL), and both on a z_stream whose state is NULL. */
#include "common.h"
#include <stdint.h>
#include "zlib.h"

struct indesc {
    const unsigned char *data; size_t len, pos, limit;
    size_t *chunks; int nchunks, ci;
    unsigned char *cur; int calls;
};

struct outdesc {
    unsigned char *acc; size_t accn, acccap;
    int calls, abort_at;
    char lens[8192]; size_t lensn;
};

static unsigned in_cb(void *d, z_const unsigned char **buf) {
    struct indesc *s = d;
    s->calls++;
    free(s->cur); s->cur = NULL;
    size_t end = s->limit < s->len ? s->limit : s->len;
    if (s->pos >= end) return 0;
    size_t n = end - s->pos;
    if (s->nchunks) { size_t k = s->chunks[s->ci % s->nchunks]; s->ci++; if (k < n) n = k; }
    s->cur = malloc(n);
    memcpy(s->cur, s->data + s->pos, n);
    s->pos += n;
    *buf = s->cur;
    return (unsigned)n;
}

static int out_cb(void *d, unsigned char *buf, unsigned len) {
    struct outdesc *o = d;
    o->calls++;
    if (o->lensn < sizeof o->lens - 16)
        o->lensn += (size_t)snprintf(o->lens + o->lensn, sizeof o->lens - o->lensn, "%s%u", o->lensn ? "," : "", len);
    if (o->accn + len > o->acccap) {
        o->acccap = (o->accn + len) * 2;
        o->acc = realloc(o->acc, o->acccap);
    }
    memcpy(o->acc + o->accn, buf, len);
    o->accn += len;
    return o->calls == o->abort_at;
}

static void hex_out(const unsigned char *p, size_t n) {
    if (n == 0) { fputs("-", stdout); return; }
    for (size_t i = 0; i < n; i++) printf("%02x", p[i]);
}

static unsigned char *parse_hex(const char *s, size_t *len) {
    if (strcmp(s, "-") == 0) { *len = 0; return malloc(1); }
    size_t n = strlen(s);
    if (n % 2) { fprintf(stderr, "odd hex\n"); exit(2); }
    *len = n / 2;
    unsigned char *b = malloc(*len ? *len : 1);
    for (size_t i = 0; i < *len; i++) b[i] = (unsigned char)(hexval(s[2 * i]) * 16 + hexval(s[2 * i + 1]));
    return b;
}

static void run_back(char **tok) {
    int wbits = (int)parse_i(tok[1]);
    const char *first = tok[2];
    size_t chunks[64]; int nchunks = 0;
    if (strcmp(tok[3], "-") != 0) {
        char *save;
        for (char *t = strtok_r(tok[3], ",", &save); t && nchunks < 64; t = strtok_r(NULL, ",", &save))
            chunks[nchunks++] = (size_t)parse_u(t);
    }
    size_t datalen;
    unsigned char *data = parse_hex(tok[7], &datalen);
    size_t limit = strcmp(tok[4], "-") == 0 ? datalen : (size_t)parse_u(tok[4]);
    int abort_at = strcmp(tok[5], "-") == 0 ? -1 : (int)parse_i(tok[5]);
    int calls = (int)parse_i(tok[6]);
    unsigned char *window = malloc((size_t)1 << wbits);
    z_stream s; memset(&s, 0, sizeof s);
    int r = inflateBackInit_(&s, wbits, window, ZLIB_VERSION, (int)sizeof(z_stream));
    printf("init:%d", r);
    if (r != Z_OK) { printf("\n"); free(window); free(data); return; }
    for (int k = 0; k < calls; k++) {
        struct indesc in; memset(&in, 0, sizeof in);
        in.data = data; in.len = datalen; in.limit = limit; in.chunks = chunks; in.nchunks = nchunks;
        struct outdesc o; memset(&o, 0, sizeof o);
        o.abort_at = abort_at;
        unsigned char *fb = NULL;
        if (strcmp(first, "null") == 0) { s.next_in = NULL; s.avail_in = 12345; }
        else if (strcmp(first, "z") == 0) { fb = malloc(1); fb[0] = 0; s.next_in = fb; s.avail_in = 0; }
        else {
            size_t f = (size_t)parse_u(first);
            if (f > datalen) f = datalen;
            if (f > limit) f = limit;
            fb = malloc(f ? f : 1);
            if (f) memcpy(fb, data, f);
            s.next_in = fb; s.avail_in = (unsigned)f;
            in.pos = f;
        }
        r = inflateBack(&s, in_cb, &in, out_cb, &o);
        printf(" back:%d:", r);
        if (s.next_in == NULL) printf("N");
        else if (in.cur != NULL) printf("c%d+%zu", in.calls, (size_t)(s.next_in - in.cur));
        else printf("f+%zu", (size_t)(s.next_in - fb));
        printf(":%u:%s:%d:%s:", s.avail_in, s.msg ? s.msg : "-", in.calls, o.lensn ? o.lens : "-");
        hex_out(o.acc, o.accn);
        free(in.cur); free(fb); free(o.acc);
    }
    printf(" end:%d\n", inflateBackEnd(&s));
    free(window); free(data);
}

static void run_init(char **tok) {
    int wbits = (int)parse_i(tok[1]);
    int wnull = strcmp(tok[2], "null") == 0;
    const char *ver = strcmp(tok[3], "null") == 0 ? NULL : tok[3];
    int size = (int)parse_i(tok[4]);
    unsigned char *window = wnull ? NULL : malloc(1 << 15);
    z_stream s; memset(&s, 0, sizeof s);
    int r = inflateBackInit_(&s, wbits, window, ver, size);
    printf("init:%d end:%d\n", r, r == Z_OK ? inflateBackEnd(&s) : 99);
    free(window);
}

static unsigned in_none(void *d, z_const unsigned char **buf) { (void)d; (void)buf; return 0; }
static int out_none(void *d, unsigned char *buf, unsigned len) { (void)d; (void)buf; (void)len; return 0; }

static void run_misc(void) {
    z_stream s; memset(&s, 0, sizeof s);
    int a = inflateBack(NULL, in_none, NULL, out_none, NULL);
    int b = inflateBackEnd(NULL);
    int c = inflateBack(&s, in_none, NULL, out_none, NULL);
    int d = inflateBackEnd(&s);
    printf("misc:%d:%d:%d:%d\n", a, b, c, d);
}

int main(void) {
    char *line = NULL; size_t cap = 0;
    while (getline(&line, &cap, stdin) >= 0) {
        char *tok[16]; int nt = 0; char *save;
        for (char *t = strtok_r(line, " \t\r\n", &save); t && nt < 16; t = strtok_r(NULL, " \t\r\n", &save))
            tok[nt++] = t;
        if (nt == 0) continue;
        if (strcmp(tok[0], "back") == 0 && nt == 8) { run_back(tok); continue; }
        if (strcmp(tok[0], "init") == 0 && nt == 5) { run_init(tok); continue; }
        if (strcmp(tok[0], "misc") == 0 && nt == 1) { run_misc(); continue; }
        printf("BADINPUT\n");
    }
    free(line);
    return 0;
}
