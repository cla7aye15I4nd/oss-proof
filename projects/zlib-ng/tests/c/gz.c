/* Differential test driver for gzlib.c, gzread.c and gzwrite.c (the real C library side).
 *
 * The library's calls of open, read, write, lseek, lseek64, close and strerror are answered by the file-system model
 * below, which mirrors ZlibNgF/Runtime/Fs.lean (regular files in memory, x86_64 Linux open flags and errno values,
 * glibc's strerror texts) and follows the same per-call schedule as the Lean side. The definitions in this file take
 * precedence over the C library's for the statically linked libz.a, so the real library code runs unchanged against
 * a world that both sides reproduce exactly, including short reads, short writes, failures and lseek results that a
 * regular file never gives. The C library's own malloc, free, snprintf, vsnprintf, strlen, memcpy, memchr and
 * memmove are used.
 *
 * Input: one test per line:  gz <file f: hex or -> <schedule or -> <op> <op> ...
 * schedule: comma-separated <n>:<choice> for OS call number n (0-based, counting open/read/write/lseek/close):
 *   F<e>  fail with errno e      S<k>  read: regular read of at most k bytes; write: write the first k bytes
 *   B<hex> read: deliver these bytes (device data)      V<v>  lseek: return v without moving
 * ops: see gen/gz.py. Output: one line per test, the result of each op separated by spaces, then the final length
 * and FNV-1a hash of file f, and the descriptors still open.
 */
#define _GNU_SOURCE 1
#define _LARGEFILE64_SOURCE 1
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <fcntl.h>
#include <unistd.h>
#include <stdarg.h>
#include <stdint.h>
#include <sys/types.h>
#include "zlib.h"

/* ---------- the file-system model (Runtime/Fs.lean) ---------- */
#define L_O_WRONLY 1
#define L_O_CREAT 64
#define L_O_EXCL 128
#define L_O_TRUNC 512
#define L_O_APPEND 1024
#define L_O_CLOEXEC 524288
#define L_ENOENT 2
#define L_EIO 5
#define L_EBADF 9
#define L_EEXIST 17
#define L_EINVAL 22
#define L_EOVERFLOW 75

#define NNODES 8
#define NFDS 64
#define NSCHED 64
struct node { char name[64]; unsigned char *data; size_t len; };
struct ofile { int used, node, rd, wr, app, oflag; size_t pos; };
struct sched { long n; char kind; long long val; unsigned char *bytes; size_t nbytes; };
static struct node nodes[NNODES];
static int nnodes;
static struct ofile fds[NFDS];
static struct sched sch[NSCHED];
static int nsch;
static long ncall;
static size_t budget;
static int last_oflag;

static struct sched *choice(long n) {
    for (int i = 0; i < nsch; i++) if (sch[i].n == n) return &sch[i];
    return NULL;
}
static int fail_errno(long long e) { return e == 0 ? L_EIO : (int)e; }
static int lookup(const char *p) {
    for (int i = 0; i < nnodes; i++) if (strcmp(nodes[i].name, p) == 0) return i;
    return -1;
}
static int lowest_fd(void) {
    for (int i = 3; i < NFDS; i++) if (!fds[i].used) return i;
    fprintf(stderr, "gz driver: out of descriptors\n"); exit(2);
}
static struct ofile *ofile(int fd) { return fd >= 0 && fd < NFDS && fds[fd].used ? &fds[fd] : NULL; }

/* open with Linux flag values */
static int model_open(const char *path, int oflag) {
    struct sched *c = choice(ncall++);
    if (c && c->kind == 'F') { errno = fail_errno(c->val); return -1; }
    int wr = (oflag & 3) == L_O_WRONLY, creat = !!(oflag & L_O_CREAT), excl = !!(oflag & L_O_EXCL);
    int trunc = !!(oflag & L_O_TRUNC), app = !!(oflag & L_O_APPEND);
    int n = lookup(path);
    if (n >= 0) {
        if (creat && excl) { errno = L_EEXIST; return -1; }
        if (trunc && wr) nodes[n].len = 0;
    } else {
        if (!creat) { errno = L_ENOENT; return -1; }
        if (nnodes == NNODES || strlen(path) >= 64) { fprintf(stderr, "gz driver: too many files\n"); exit(2); }
        n = nnodes++;
        strcpy(nodes[n].name, path); nodes[n].data = NULL; nodes[n].len = 0;
    }
    int fd = lowest_fd();
    fds[fd] = (struct ofile){ 1, n, !wr, wr, app, oflag, 0 };
    last_oflag = oflag;
    return fd;
}
static int host_to_linux(int f) {
    int l = (f & O_ACCMODE) == O_WRONLY ? L_O_WRONLY : (f & O_ACCMODE) == O_RDWR ? 2 : 0;
    if (f & O_CREAT) l |= L_O_CREAT;
    if (f & O_EXCL) l |= L_O_EXCL;
    if (f & O_TRUNC) l |= L_O_TRUNC;
    if (f & O_APPEND) l |= L_O_APPEND;
    if (f & O_CLOEXEC) l |= L_O_CLOEXEC;
    int known = O_ACCMODE | O_CREAT | O_EXCL | O_TRUNC | O_APPEND | O_CLOEXEC;
#ifdef O_LARGEFILE
    known |= O_LARGEFILE;   /* 0 in user space on x86_64 glibc */
#endif
    if (f & ~known) { fprintf(stderr, "gz driver: unexpected open flags %#x\n", f); exit(2); }
    return l;
}
int open(const char *path, int flags, ...) { return model_open(path, host_to_linux(flags)); }
int open64(const char *path, int flags, ...) { return model_open(path, host_to_linux(flags)); }

static void write_at(struct node *nd, size_t pos, const unsigned char *b, size_t k) {
    size_t end = pos + k > nd->len ? pos + k : nd->len;
    if (end > nd->len) {
        nd->data = realloc(nd->data, end ? end : 1);
        if (!nd->data) { fprintf(stderr, "gz driver: out of memory\n"); exit(2); }
        memset(nd->data + nd->len, 0, end - nd->len);
        nd->len = end;
    }
    if (k) memcpy(nd->data + pos, b, k);
}
ssize_t read(int fd, void *buf, size_t n) {
    struct sched *c = choice(ncall++);
    size_t cap = n;
    if (c && c->kind == 'F') { errno = fail_errno(c->val); return -1; }
    if (c && c->kind == 'B') {
        size_t k = c->nbytes < n ? c->nbytes : n;
        if (k > budget) k = budget;
        if (k) memcpy(buf, c->bytes, k);
        budget -= k;
        return (ssize_t)k;
    }
    if (c && c->kind == 'S' && (size_t)c->val < cap) cap = (size_t)c->val;
    struct ofile *o = ofile(fd);
    if (!o || !o->rd) { errno = L_EBADF; return -1; }
    struct node *nd = &nodes[o->node];
    size_t avail = o->pos < nd->len ? nd->len - o->pos : 0;
    size_t k = cap < avail ? cap : avail;
    if (k) memcpy(buf, nd->data + o->pos, k);
    o->pos += k;
    return (ssize_t)k;
}
ssize_t write(int fd, const void *buf, size_t n) {
    struct sched *c = choice(ncall++);
    if (c && c->kind == 'F') { errno = fail_errno(c->val); return -1; }
    if (c && c->kind == 'S' && (size_t)c->val < n) n = (size_t)c->val;
    struct ofile *o = ofile(fd);
    if (!o || !o->wr) { errno = L_EBADF; return -1; }
    struct node *nd = &nodes[o->node];
    size_t pos = o->app ? nd->len : o->pos;
    write_at(nd, pos, buf, n);
    o->pos = pos + n;
    return (ssize_t)n;
}
static off_t model_lseek(int fd, off_t off, int whence) {
    struct sched *c = choice(ncall++);
    if (c && c->kind == 'F') { errno = fail_errno(c->val); return -1; }
    if (c && c->kind == 'V') return (off_t)c->val;
    struct ofile *o = ofile(fd);
    if (!o) { errno = L_EBADF; return -1; }
    __int128 base;
    if (whence == SEEK_SET) base = 0;
    else if (whence == SEEK_CUR) base = (__int128)o->pos;
    else if (whence == SEEK_END) base = (__int128)nodes[o->node].len;
    else { errno = L_EINVAL; return -1; }
    __int128 np = base + off;
    if (np < 0) { errno = L_EINVAL; return -1; }
    if (np > (__int128)INT64_MAX) { errno = L_EOVERFLOW; return -1; }
    o->pos = (size_t)np;
    return (off_t)np;
}
off_t lseek(int fd, off_t off, int whence) { return model_lseek(fd, off, whence); }
#ifdef __linux__
off64_t lseek64(int fd, off64_t off, int whence) { return model_lseek(fd, off, whence); }
#endif
int close(int fd) {
    struct sched *c = choice(ncall++);
    struct ofile *o = ofile(fd);
    if (!o) { errno = L_EBADF; return -1; }
    o->used = 0;
    if (c && c->kind == 'F') { errno = fail_errno(c->val); return -1; }
    return 0;
}
char *strerror(int e) {
    static char unk[64];
    switch (e) {
    case 0: return "Success";
    case 2: return "No such file or directory";
    case 4: return "Interrupted system call";
    case 5: return "Input/output error";
    case 9: return "Bad file descriptor";
    case 11: return "Resource temporarily unavailable";
    case 13: return "Permission denied";
    case 17: return "File exists";
    case 22: return "Invalid argument";
    case 28: return "No space left on device";
    case 29: return "Illegal seek";
    case 32: return "Broken pipe";
    case 75: return "Value too large for defined data type";
    default: snprintf(unk, sizeof unk, "Unknown error %d", e); return unk;
    }
}

/* ---------- parsing ---------- */
static int hexv(int c) {
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    return -1;
}
static unsigned char *unhex(const char *s, size_t *len) {
    size_t n = strlen(s);
    if (strcmp(s, "-") == 0) n = 0;
    if (n % 2) { fprintf(stderr, "odd hex\n"); exit(2); }
    unsigned char *b = malloc(n / 2 + 1);
    for (size_t i = 0; i < n / 2; i++) {
        int h = hexv(s[2 * i]), l = hexv(s[2 * i + 1]);
        if (h < 0 || l < 0) { fprintf(stderr, "bad hex\n"); exit(2); }
        b[i] = (unsigned char)(h * 16 + l);
    }
    b[n / 2] = 0;
    *len = n / 2;
    return b;
}
static long long num(const char *s) {
    char *e; errno = 0;
    long long v = strtoll(s, &e, 10);
    if (*s == 0 || (*e != 0 && *e != ':') || errno) { fprintf(stderr, "bad number %s\n", s); exit(2); }
    return v;
}
static unsigned long long unum(const char *s) {
    char *e; errno = 0;
    unsigned long long v = strtoull(s, &e, 10);
    if (*s == 0 || (*e != 0 && *e != ':') || errno) { fprintf(stderr, "bad number %s\n", s); exit(2); }
    return v;
}
/* the i-th ':'-separated field of op (0 is the name) */
static const char *field(const char *op, int i) {
    while (i-- > 0) { op = strchr(op, ':'); if (!op) { fprintf(stderr, "missing field\n"); exit(2); } op++; }
    return op;
}
static void fieldcpy(char *dst, size_t cap, const char *f) {
    size_t n = strcspn(f, ":");
    if (n >= cap) { fprintf(stderr, "field too long\n"); exit(2); }
    memcpy(dst, f, n); dst[n] = 0;
}

/* ---------- output ---------- */
static char out[1 << 20];
static size_t outn;
static void emit(const char *fmt, ...) {
    va_list va; va_start(va, fmt);
    if (outn) out[outn++] = ' ';
    int k = vsnprintf(out + outn, sizeof out - outn, fmt, va);
    va_end(va);
    if (k < 0 || (size_t)k >= sizeof out - outn) { fprintf(stderr, "output too long\n"); exit(2); }
    outn += (size_t)k;
}
static void hexs(char *dst, const unsigned char *b, size_t n) {
    static const char d[] = "0123456789abcdef";
    if (n == 0) { strcpy(dst, "-"); return; }
    for (size_t i = 0; i < n; i++) { dst[2 * i] = d[b[i] >> 4]; dst[2 * i + 1] = d[b[i] & 15]; }
    dst[2 * n] = 0;
}
static char hx[1 << 19];
static uint64_t fnv(const unsigned char *b, size_t n) {
    uint64_t h = 1469598103934665603ULL;
    for (size_t i = 0; i < n; i++) { h ^= b[i]; h *= 1099511628211ULL; }
    return h;
}

/* ---------- ops ---------- */
static gzFile file;
static void op_error(const char *name) {
    int en = 12345;
    const char *m = gzerror(file, &en);
    if (!m) { emit("%s:null", name); return; }
    hexs(hx, (const unsigned char *)m, strlen(m));
    emit("%s:%d:%s", name, en, hx);
}
static void run(char *line) {
    char *save;
    char *t = strtok_r(line, " \n", &save);
    if (!t) return;
    if (strcmp(t, "gz") != 0) { fprintf(stderr, "bad line\n"); exit(2); }
    /* reset the world */
    for (int i = 0; i < nnodes; i++) free(nodes[i].data);
    nnodes = 0; memset(fds, 0, sizeof fds);
    for (int i = 0; i < nsch; i++) free(sch[i].bytes);
    nsch = 0; ncall = 0; budget = 1 << 30; last_oflag = 0; errno = 0;
    file = NULL;
    char *fhex = strtok_r(NULL, " \n", &save);
    if (strcmp(fhex, "none") != 0) {
        size_t n; unsigned char *b = unhex(fhex, &n);
        strcpy(nodes[0].name, "f"); nodes[0].data = b; nodes[0].len = n; nnodes = 1;
    }
    char *sc = strtok_r(NULL, " \n", &save);
    if (strcmp(sc, "-") != 0) {
        char *s2;
        for (char *e = strtok_r(sc, ",", &s2); e; e = strtok_r(NULL, ",", &s2)) {
            if (nsch == NSCHED) { fprintf(stderr, "schedule too long\n"); exit(2); }
            struct sched *c = &sch[nsch++];
            c->n = (long)num(e);
            char *k = strchr(e, ':') + 1;
            c->kind = *k; c->bytes = NULL; c->nbytes = 0; c->val = 0;
            if (*k == 'B') c->bytes = unhex(k + 1, &c->nbytes);
            else c->val = num(k + 1);
        }
    }
    outn = 0;
    for (char *op = strtok_r(NULL, " \n", &save); op; op = strtok_r(NULL, " \n", &save)) {
        char name[32]; fieldcpy(name, sizeof name, op);
        if (!strcmp(name, "open") || !strcmp(name, "openg")) {
            char mode[64]; fieldcpy(mode, sizeof mode, field(op, 1));
            file = gzopen(name[4] ? "g" : "f", mode);
            emit("open:%d:%d", file != NULL, last_oflag);
        } else if (!strcmp(name, "dopen")) {
            int fl = (int)num(field(op, 1));
            char mode[64]; fieldcpy(mode, sizeof mode, field(op, 2));
            int fd = model_open("f", fl);
            file = gzdopen(fd, mode);
            emit("dopen:%d:%d", fd, file != NULL);
        } else if (!strcmp(name, "dopenfd")) {
            int fd = (int)num(field(op, 1));
            char mode[64]; fieldcpy(mode, sizeof mode, field(op, 2));
            file = gzdopen(fd, mode);
            emit("dopenfd:%d", file != NULL);
        } else if (!strcmp(name, "buffer")) {
            emit("%d", gzbuffer(file, (unsigned)unum(field(op, 1))));
        } else if (!strcmp(name, "read")) {
            unsigned n = (unsigned)unum(field(op, 1));
            unsigned char *b = malloc(n && n <= (1u << 20) ? n : 1);
            int r = gzread(file, b, n);
            hexs(hx, b, r > 0 ? (size_t)r : 0);
            emit("%d:%s", r, hx);
            free(b);
        } else if (!strcmp(name, "fread")) {
            size_t sz = (size_t)unum(field(op, 1)), ni = (size_t)unum(field(op, 2));
            size_t cap = (sz && ni <= SIZE_MAX / sz) ? sz * ni : 1;
            if (cap > (1u << 20)) cap = 1;
            unsigned char *b = malloc(cap ? cap : 1);
            size_t r = gzfread(b, sz, ni, file);
            hexs(hx, b, r * sz <= cap ? r * sz : 0);
            emit("%zu:%s", r, hx);
            free(b);
        } else if (!strcmp(name, "getc")) {
            emit("%d", (gzgetc)(file));
        } else if (!strcmp(name, "getc_")) {
            emit("%d", gzgetc_(file));
        } else if (!strcmp(name, "ungetc")) {
            emit("%d", gzungetc((int)num(field(op, 1)), file));
        } else if (!strcmp(name, "gets")) {
            int n = (int)num(field(op, 1));
            char *b = malloc(n > 0 ? (size_t)n : 1);
            char *r = gzgets(file, b, n);
            if (!r) emit("null");
            else { hexs(hx, (unsigned char *)r, strlen(r)); emit("%d:%s", (int)(r - b), hx); }
            free(b);
        } else if (!strcmp(name, "eof")) {
            emit("%d", gzeof(file));
        } else if (!strcmp(name, "direct")) {
            emit("%d", gzdirect(file));
        } else if (!strcmp(name, "error")) {
            op_error("err");
        } else if (!strcmp(name, "clearerr")) {
            gzclearerr(file); emit("ok");
        } else if (!strcmp(name, "tell")) {
            emit("%lld", (long long)gztell(file));
        } else if (!strcmp(name, "offset")) {
            emit("%lld", (long long)gzoffset(file));
        } else if (!strcmp(name, "seek")) {
            long long off = num(field(op, 1));
            int wh = (int)num(field(op, 2));
            emit("%lld", (long long)gzseek(file, (z_off64_t)off, wh));
        } else if (!strcmp(name, "rewind")) {
            emit("%d", gzrewind(file));
        } else if (!strcmp(name, "write")) {
            size_t n; unsigned char *b = unhex(field(op, 1), &n);
            unsigned char *c = malloc(n ? n : 1);
            if (n) memcpy(c, b, n);
            emit("%d", gzwrite(file, c, (unsigned)n));
            free(c); free(b);
        } else if (!strcmp(name, "writen")) {
            size_t n = (size_t)unum(field(op, 1));
            int v = (int)num(field(op, 2));
            unsigned char *c = malloc(n ? n : 1);
            for (size_t i = 0; i < n; i++) c[i] = (unsigned char)(v < 0 ? (i * 7 + i / 3) & 255 : v);
            emit("%d", gzwrite(file, c, (unsigned)n));
            free(c);
        } else if (!strcmp(name, "fwrite")) {
            size_t sz = (size_t)unum(field(op, 1)), ni = (size_t)unum(field(op, 2));
            size_t n; unsigned char *b = unhex(field(op, 3), &n);
            unsigned char *c = malloc(n ? n : 1);
            if (n) memcpy(c, b, n);
            emit("%zu", gzfwrite(c, sz, ni, file));
            free(c); free(b);
        } else if (!strcmp(name, "putc")) {
            emit("%d", gzputc(file, (int)num(field(op, 1))));
        } else if (!strcmp(name, "puts")) {
            size_t n; unsigned char *b = unhex(field(op, 1), &n);
            emit("%d", gzputs(file, (char *)b));
            free(b);
        } else if (!strcmp(name, "printf")) {
            char k = *field(op, 1);
            if (k == 's') {
                size_t n; unsigned char *b = unhex(field(op, 2), &n);
                emit("%d", gzprintf(file, "%s", (char *)b));
                free(b);
            } else if (k == 'd') {
                emit("%d", gzprintf(file, "%d", (int)num(field(op, 2))));
            } else if (k == 'e') {
                emit("%d", gzprintf(file, "%s", ""));
            } else { fprintf(stderr, "bad printf kind\n"); exit(2); }
        } else if (!strcmp(name, "flush")) {
            emit("%d", gzflush(file, (int)num(field(op, 1))));
        } else if (!strcmp(name, "params")) {
            emit("%d", gzsetparams(file, (int)num(field(op, 1)), (int)num(field(op, 2))));
        } else if (!strcmp(name, "close") || !strcmp(name, "closer") || !strcmp(name, "closew")) {
            int r = !strcmp(name, "close") ? gzclose(file) : !strcmp(name, "closer") ? gzclose_r(file) : gzclose_w(file);
            emit("%d", r);
            if (r != Z_STREAM_ERROR) file = NULL;
        } else if (!strcmp(name, "null")) {
            /* every function on a NULL handle */
            gzFile z = NULL; int en = 7; unsigned char b[4];
            emit("null:%d:%d:%zu:%d:%zu:%d:%d:%d:%d:%d:%d:%d:%d:%d:%d:%lld:%lld:%lld:%d:%d:%d:%d:%d",
                 gzbuffer(z, 64), gzread(z, b, 1), gzfread(b, 1, 1, z), gzwrite(z, b, 1), gzfwrite(b, 1, 1, z),
                 gzputc(z, 1), gzputs(z, "a"), gzprintf(z, "%d", 1), (gzgetc)(z), gzungetc(1, z),
                 gzgets(z, (char *)b, 4) == NULL, gzflush(z, 0), gzsetparams(z, 1, 0), gzrewind(z), gzeof(z),
                 (long long)gzseek(z, 0, 0), (long long)gztell(z), (long long)gzoffset(z),
                 gzerror(z, &en) == NULL, gzdirect(z), gzclose(z), gzclose_r(z), gzclose_w(z));
            gzclearerr(z);
        } else { fprintf(stderr, "bad op %s\n", name); exit(2); }
    }
    if (file) { emit("autoclose:%d", gzclose(file)); file = NULL; }
    int fi = lookup("f");
    if (fi >= 0) emit("F:%zu:%016llx", nodes[fi].len, (unsigned long long)fnv(nodes[fi].data, nodes[fi].len));
    else emit("F:none");
    int fg = lookup("g");
    if (fg >= 0) emit("G:%zu:%016llx", nodes[fg].len, (unsigned long long)fnv(nodes[fg].data, nodes[fg].len));
    int nopen = 0;
    for (int i = 0; i < NFDS; i++) nopen += fds[i].used;
    emit("fds:%d", nopen);
    puts(out);
}

int main(void) {
    char *line = NULL; size_t cap = 0;
    while (getline(&line, &cap, stdin) > 0) {
        if (line[0] == '\n' || line[0] == 0) continue;
        run(line);
    }
    free(line);
    for (int i = 0; i < nnodes; i++) free(nodes[i].data);
    for (int i = 0; i < nsch; i++) free(sch[i].bytes);
    return 0;
}
