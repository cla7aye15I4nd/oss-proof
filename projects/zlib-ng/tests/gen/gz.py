#!/usr/bin/env python3
"""Inputs for the gz* differential test (gzlib.c, gzread.c, gzwrite.c), written to stdout. Deterministic.

Line: gz <file f: hex, - (empty) or none> <schedule or -> <op> <op> ...  (format: tests/c/gz.c)
Ops: open:<mode> (path "f"), openg:<mode> (path "g", absent at the start), dopen:<linux oflag>:<mode> (open "f"
with that flag, then gzdopen the descriptor), dopenfd:<fd>:<mode>, buffer:<n>, read:<n>, fread:<size>:<nitems>,
getc, getc_, ungetc:<c>, gets:<len>, eof, direct, error, clearerr, tell, offset, seek:<off>:<whence>, rewind,
write:<hex>, writen:<n>:<byte, or -1 for a pattern>, fwrite:<size>:<nitems>:<hex>, putc:<c>, puts:<hex>,
printf:s:<hex> ("%s"), printf:d:<int> ("%d"), printf:e ("%s" of ""), flush:<f>, params:<level>:<strategy>, close,
closer, closew, null (every function on a NULL handle). A handle still open at the end is closed with gzclose.

The schedule numbers the OS calls (open, read, write, lseek, close) of the line from 0 and chooses, for some of
them, a failure (F<errno>), a short read or write (S<k>), device data for a read (B<hex>) or an lseek result
(V<value>); see tests/c/gz.c.

A schedule entry A<k> makes the library's malloc call number k of the line (0-based) return NULL.

Every input on which the C ran into undefined behaviour before patches 0014-0016 is generated: write errors on the
direct path of gz_write followed by further writes, flushes and closes, gzclearerr after write errors, allocation
failures (gz_state, path, buffers, inflate and deflate state, error message), reads after gzseek to near 2^63,
gzdirect while a seek is pending (patch 0020), and gzgets while a seek is pending at the end of a file that grows
(patch 0021).
Patch 0017 refuses a write past GZ_OFF_MAX before it reads the buffer: gzfwrite lengths above it are generated with
a one-byte buffer (nothing else can reach that position in a test's time).
"""
import random
import zlib

rng = random.Random(20261119)
out = []


def hx(b):
    return b.hex() if b else "-"


def gz(data, level=6, extra_members=()):
    c = zlib.compressobj(level, zlib.DEFLATED, 31)
    r = c.compress(data) + c.flush()
    for m in extra_members:
        c = zlib.compressobj(level, zlib.DEFLATED, 31)
        r += c.compress(m) + c.flush()
    return r


def text(n):
    words = [b"alpha", b"beta", b"gamma", b"\n", b"delta", b"x", b"\n\n", b"0123456789"]
    r = b""
    while len(r) < n:
        r += rng.choice(words) + b" "
    return r[:n]


def rnd(n):
    return bytes(rng.randrange(256) for _ in range(n))


def line(file, sched, ops):
    f = "none" if file is None else hx(file)
    s = ",".join(sched) if sched else "-"
    out.append("gz %s %s %s" % (f, s, " ".join(ops)))


# ---- open modes ----
modes = ["r", "rb", "w", "wb", "a", "ab", "w9", "w0", "w1", "wb6", "wf", "wh", "wR", "wF", "wT", "aT", "rT", "rG", "wG",
         "r+", "w+", "", "b", "zz", "re", "we", "wx", "rx", "ax", "w5h", "w95", "rw", "wr", "T", "G", "wTG", "rGT"]
for m in modes:
    for file in (None, b"", gz(b"hello\n")):
        line(file, [], ["open:" + m, "direct", "error", "tell", "offset", "eof"])
        line(file, [], ["openg:" + m, "write:616263", "read:4", "close"])
for m in ("r", "w", "a", "wT", "rG", "zz"):
    line(gz(b"abc"), [], ["dopen:0:" + m, "read:10", "write:41", "error", "close"])
    line(b"plain data", [], ["dopen:577:" + m, "write:4142", "read:3", "close"])
for fd in (-1, -2, -5, 0, 2, 3, 50):
    line(gz(b"abc"), [], ["dopenfd:%d:r" % fd, "read:5", "error", "close"])
    line(gz(b"abc"), [], ["dopenfd:%d:w" % fd, "write:41", "error", "close"])
# open failures, lseek failures at open
line(gz(b"abc"), ["0:F13"], ["open:r", "read:3"])
line(None, ["0:F28"], ["openg:w", "write:41"])
line(gz(b"abc"), ["1:F29"], ["open:r", "read:3", "tell", "offset", "rewind", "close"])
line(gz(b"abc"), ["1:V-7"], ["open:r", "read:3", "rewind", "close"])
line(b"xyz", ["1:V123"], ["open:a", "write:41", "offset", "close"])

# ---- reading ----
datas = [b"", b"a", b"hello world\n", text(300), rnd(200), text(3000), rnd(70000) if False else rnd(1500)]
bufs = [None, 8, 9, 16, 33, 64, 1000]
for d in datas:
    for lvl in (0, 1, 6, 9):
        g = gz(d, lvl)
        for b in bufs:
            pre = [] if b is None else ["buffer:%d" % b]
            if b is None and len(d) > 400:
                continue
            ops = ["open:r"] + pre + ["read:%d" % rng.choice([1, 5, 17, 100, 1000, 5000]), "tell", "offset", "eof",
                                      "read:%d" % rng.choice([0, 3, 64, 4096]), "getc", "gets:%d" % rng.choice([1, 2, 7, 80]),
                                      "eof", "error", "close"]
            line(g, [], ops)
# transparent, concatenated, garbage, truncated, corrupted
cases = [
    b"", b"\x1f", b"\x1f\x8b", b"plain text file\nsecond line\n", rnd(500),
    gz(b"first ", 6, [b"second ", b"", b"third"]),
    gz(text(100)) + b"trailing garbage",
    gz(text(100)) + b"\x1f\x8b",
    gz(text(400))[:-3], gz(text(400))[:-9], gz(text(400))[:15], gz(b"")[:10],
]
g = bytearray(gz(text(400)))
g[30] ^= 0x55
cases.append(bytes(g))
g = bytearray(gz(text(400)))
g[-6] ^= 1
cases.append(bytes(g))
g = bytearray(gz(text(50)))
g[3] = 0xe0  # reserved flags
cases.append(bytes(g))
g = bytearray(gz(text(50)))
g[2] = 7  # bad method
cases.append(bytes(g))
for c in cases:
    for b in (8, 16, 100, None):
        pre = [] if b is None else ["buffer:%d" % b]
        line(c, [], ["open:r"] + pre + ["direct", "read:7", "read:2000", "eof", "error", "tell", "offset", "read:5",
                                        "eof", "clearerr", "eof", "error", "close"])
        line(c, [], ["open:r"] + pre + ["gets:5", "gets:100", "getc", "getc_", "ungetc:65", "getc", "gets:3", "close"])
        line(c, [], ["open:rG"] + pre + ["read:100", "error", "direct", "close"])
# gzgets with small buffers and long lines
t = b"line one\nline two is longer than the others\n\nlast"
for c in (gz(t), t, gz(t * 20)):
    for b in (8, 9, 12, None):
        pre = [] if b is None else ["buffer:%d" % b]
        line(c, [], ["open:r"] + pre + ["gets:%d" % n for n in (1, 2, 3, 0, -1, 4, 10, 100, 5, 1000, 7)] + ["eof", "close"])
# getc / ungetc interleavings
for c in (gz(b"abcdefghij" * 5), b"abcdefghij" * 5, gz(b""), b""):
    for b in (8, None):
        pre = [] if b is None else ["buffer:%d" % b]
        line(c, [], ["open:r"] + pre + ["ungetc:66", "getc", "getc", "ungetc:-1", "ungetc:300", "getc", "tell",
                                        "read:3", "ungetc:1", "ungetc:2", "read:4", "tell", "close"])
        line(c, [], ["open:r"] + pre + ["ungetc:%d" % i for i in range(20)] + ["error", "read:30", "tell", "close"])
        line(c, [], ["open:r"] + pre + ["getc"] * 12 + ["ungetc:%d" % i for i in range(5)] + ["read:40", "close"])
# gzfread
for c in (gz(text(300)), text(300)):
    for sz, ni in ((1, 10), (3, 7), (0, 5), (5, 0), (7, 100), (2, 9223372036854775808), (18446744073709551615, 2),
                   (1000, 1), (4294967296, 4294967296)):
        line(c, [], ["open:r", "buffer:16", "fread:%d:%d" % (sz, ni), "fread:2:3", "error", "tell", "close"])
# seeking in read mode
for c in (gz(text(2000)), text(2000), gz(b"short")):
    for b in (8, 64, None):
        pre = [] if b is None else ["buffer:%d" % b]
        for sk in (["seek:10:0", "read:5", "tell"], ["seek:100:1", "seek:5:1", "getc", "tell"],
                   ["read:50", "seek:10:0", "read:5", "tell"], ["read:50", "seek:-20:1", "read:5", "tell"],
                   ["seek:-1:0"], ["seek:5:2"], ["read:5", "seek:-6:1", "tell"], ["seek:1000000:0", "read:5", "eof", "tell"],
                   ["rewind", "read:3", "rewind", "read:3", "tell"], ["ungetc:65", "seek:0:1", "tell", "seek:3:0", "tell"],
                   ["seek:9223372036854775807:0", "tell", "seek:1:1", "tell"], ["seek:9223372036854775807:1"],
                   ["read:10", "seek:-9223372036854775807:1"], ["gets:20", "seek:0:0", "gets:20", "offset"],
                   ["seek:7:0", "ungetc:66", "read:4", "tell"]):
            line(c, [], ["open:r"] + pre + sk + ["error", "close"])

# ---- writing ----
wdatas = [b"", b"a", text(50), rnd(300), text(5000)]
for m in ("w", "w0", "w1", "w9", "wf", "wh", "wR", "wF", "wT", "a", "aT"):
    for d in wdatas:
        for b in (8, 10, 64, 4096):
            if m.startswith("w") and len(d) > 1000 and b < 64:
                continue
            ops = ["openg:" + m, "buffer:%d" % b, "write:" + hx(d[: len(d) // 2]), "tell", "write:" + hx(d[len(d) // 2:]),
                   "putc:%d" % rng.randrange(-300, 300), "puts:" + hx(text(rng.randrange(0, 40)).replace(b"\0", b"")),
                   "tell", "flush:%d" % rng.choice([0, 1, 2, 3, 4, 5, 6, -1]), "offset", "close"]
            line(b"existing", [], ops)
for m in ("w", "wT", "w1"):
    for n in (0, 1, 7, 8, 9, 15, 16, 17, 100, 3000):
        line(None, [], ["openg:" + m, "buffer:8", "writen:%d:-1" % n, "writen:%d:0" % n, "tell", "close"])
    for k in ("e", "s:" + hx(b"x" * 3), "s:" + hx(b"y" * 7), "s:" + hx(b"z" * 8), "s:" + hx(b"w" * 15), "s:" + hx(b"v" * 16),
              "s:" + hx(b"u" * 17), "d:-2147483648", "d:0", "d:42"):
        line(None, [], ["openg:" + m, "buffer:16", "printf:" + k, "printf:" + k, "write:6162", "printf:" + k, "tell",
                        "close"])
    line(None, [], ["openg:" + m, "printf:s:" + hx(text(500)), "printf:d:7", "close"])
    line(None, [], ["openg:" + m, "buffer:8", "putc:1"] + ["putc:%d" % i for i in range(40)] + ["tell", "close"])
    line(None, [], ["openg:" + m, "fwrite:3:4:" + hx(rnd(12)), "fwrite:0:4:41", "fwrite:4:0:41",
                    "fwrite:2:9223372036854775808:41", "error", "fwrite:1:2:4142", "close"])
# gzsetparams mid-stream
for m in ("w", "wT", "w0", "wh"):
    for l, s in ((1, 0), (9, 0), (0, 0), (-1, 0), (-2, 0), (10, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, -1), (5, 3)):
        line(None, [], ["openg:" + m, "buffer:64", "params:%d:%d" % (l, s), "write:" + hx(text(200)),
                        "params:%d:%d" % (l, s), "write:" + hx(rnd(150)), "params:1:2", "puts:" + hx(text(30)),
                        "error", "close"])
# seeking in write mode
for m in ("w", "wT"):
    for sk in (["seek:10:0", "write:41", "tell"], ["write:4142", "seek:5:1", "putc:66", "tell"],
               ["write:4142", "seek:1:0", "tell"], ["seek:-1:1"], ["seek:3:2"], ["seek:20:0", "seek:30:0", "flush:2", "tell"],
               ["seek:100:0", "printf:d:5", "tell"], ["seek:100:0", "puts:4142", "tell"], ["seek:40:0", "params:1:0", "tell"],
               ["seek:20:0", "closew"], ["rewind"]):
        line(None, [], ["openg:" + m, "buffer:16"] + sk + ["error", "close"])

# ---- wrong mode, NULL handle, errors, close variants ----
line(gz(b"abc"), [], ["open:r", "write:41", "putc:1", "puts:41", "printf:d:1", "flush:0", "params:1:0", "fwrite:1:1:41",
                      "closew", "error", "close"])
line(None, [], ["openg:w", "read:3", "getc", "ungetc:1", "gets:4", "fread:1:1", "rewind", "eof", "direct", "closer",
                "error", "close"])
line(None, [], ["null"])
line(gz(b"abc"), [], ["open:r", "buffer:100", "read:2", "buffer:100", "close"])
line(None, [], ["openg:w", "write:41", "buffer:100", "close"])
for b in (0, 1, 7, 8, 1073741824, 1073741825, 4294967295):
    line(gz(b"abc"), [], ["open:r", "buffer:%d" % b, "read:1", "close"]) if b <= 1000 else \
        line(gz(b"abc"), [], ["open:r", "buffer:%d" % b, "close"])
line(gz(b"abc"), [], ["open:r", "read:2147483648", "error", "read:3", "close"])
line(None, [], ["openg:w", "write:41", "error", "close"])

# ---- OS-call schedules ----
# reading: short reads, failures, device data
g = gz(text(800))
for sched in (["1:S1", "2:S1", "3:S2"], ["2:S5", "3:F5"], ["2:F4"], ["2:F0"], ["3:F11", "4:S3"], ["2:B" + hx(b"\x1f\x8b")],
              ["2:B" + hx(rnd(30))], ["2:S0"], ["2:S1", "3:S0"], ["4:F9", "5:S2"], ["6:F5"], ["10:F5"]):
    for b in (8, 64):
        line(g, sched, ["open:r", "buffer:%d" % b, "read:200", "error", "read:200", "error", "clearerr", "read:2000",
                        "tell", "close"])
        line(text(500), sched, ["open:r", "buffer:%d" % b, "read:20", "getc", "error", "read:3000", "error", "close"])
# close failure, lseek failures and odd values
for sched in (["3:F5"], ["4:F5"], ["5:F28"]):
    line(gz(b"abc"), sched, ["open:r", "read:5", "close"])
    line(None, sched, ["openg:w", "write:41", "close"])
for v in ("V0", "V-1", "V-2", "V9223372036854775807", "V-9223372036854775808", "F29"):
    line(text(300), ["2:" + v], ["open:r", "buffer:8", "read:3", "offset", "read:3", "close"])
    line(text(300), ["3:" + v], ["open:r", "buffer:8", "read:3", "offset", "seek:2:1", "tell", "read:3", "close"])
    line(text(300), ["1:" + v], ["open:r", "buffer:8", "read:3", "rewind", "read:3", "close"])
    line(gz(text(300)), ["1:" + v], ["open:r", "buffer:8", "read:30", "seek:1:0", "read:3", "close"])
# writing: short writes and failures, small writes only (see the module doc)
for m in ("w", "wT"):
    for sched in (["1:S3"], ["1:F28"], ["1:S0"], ["2:F5"], ["1:F0"]):
        line(None, sched, ["openg:" + m, "buffer:64", "write:" + hx(text(20)), "flush:2", "error", "write:41", "error",
                           "close"])
        line(None, sched, ["openg:" + m, "buffer:64", "puts:" + hx(text(30)), "printf:d:5", "close", "error"])

# ---- write errors on the direct path (patch 0014), then more writes, gzclearerr, flushes and closes ----
for m in ("w", "wT", "w1", "w0"):
    for sched in (["1:F28"], ["1:S3"], ["2:F5"], ["1:F11"], ["1:S0"], ["3:F5"]):
        line(None, sched, ["openg:" + m, "buffer:8", "writen:100:-1", "error", "clearerr", "write:41", "putc:66",
                           "printf:d:7", "params:1:0", "writen:20:5", "flush:2", "error", "close"])
        line(None, sched, ["openg:" + m, "buffer:8", "writen:100:-1", "error", "close"])
        line(None, sched, ["openg:" + m, "buffer:8", "write:41", "writen:100:-1", "clearerr", "writen:50:3", "tell",
                           "close"])
        line(None, sched, ["openg:" + m, "buffer:8", "writen:100:-1", "clearerr", "printf:s:" + hx(b"abcdefg"),
                           "seek:20:1", "flush:4", "closew"])

# ---- allocation failures ----
for k in range(9):
    A = ["A%d" % k]
    line(gz(text(300)), A, ["open:r", "buffer:16", "read:20", "gets:10", "error", "read:4000", "error", "close"])
    line(text(300), A, ["open:r", "buffer:16", "read:20", "getc", "ungetc:65", "error", "close"])
    line(gz(text(50))[:-5], A, ["open:r", "read:200", "error", "clearerr", "error", "read:5", "error", "close"])
    line(gz(b"abc"), A, ["dopen:0:r", "direct", "read:10", "error", "close"])
    line(gz(b"abc"), A, ["open:r", "seek:2:0", "read:5", "error", "close"])
    line(None, A, ["openg:zz", "error"])
    for m in ("w", "wT", "w9", "a"):
        line(None, A, ["openg:" + m, "buffer:16", "write:" + hx(text(40)), "error", "printf:d:5", "flush:2", "close"])
        line(None, A, ["openg:" + m, "write:41", "error", "clearerr", "putc:1", "puts:4142", "error", "close"])
        line(None, A, ["openg:" + m, "seek:30:0", "params:2:0", "error", "close"])
    line(None, A, ["openg:w", "buffer:8", "writen:100:-1", "error", "close"])
    line(None, ["0:F13"] + A, ["openg:r", "error", "open:r", "error"])
for a, b in ((0, 1), (1, 2), (2, 3), (3, 4), (2, 4), (4, 5), (1, 3)):
    A = ["A%d" % a, "A%d" % b]
    line(gz(text(300)), A, ["open:r", "read:20", "error", "read:20", "error", "close"])
    line(None, A, ["openg:w", "write:41", "error", "write:42", "error", "close"])
    line(None, ["1:F5"] + A, ["openg:w", "buffer:8", "writen:30:-1", "error", "close", "error"])

# ---- reads after gzseek to near 2^63 (patch 0016): device data from a descriptor whose lseek moves freely ----
t = text(300)
dev = ["%d:B%s" % (i, hx(rnd(25))) for i in range(3, 16)]
for b in (8, 64):
    for ops in (["read:3", "seek:9223372036854775807:0", "tell", "read:5", "tell", "getc", "getc_", "gets:10", "read:5",
                 "eof", "tell"],
                ["read:3", "seek:9223372036854775800:0", "read:5", "tell", "read:5", "tell", "getc", "tell", "read:3",
                 "gets:4", "getc", "ungetc:65", "getc", "tell"],
                ["getc", "seek:9223372036854775806:0", "getc", "getc", "getc", "tell", "ungetc:66", "getc", "getc",
                 "tell"],
                ["read:3", "seek:9223372036854775790:0", "gets:30", "gets:30", "tell", "read:100", "tell"],
                ["read:3", "seek:9223372036854775797:0", "fread:3:4", "tell", "fread:1:5", "tell"],
                ["read:3", "seek:9223372036854775800:0", "ungetc:65", "ungetc:66", "tell", "read:20", "tell", "getc"]):
        line(t, dev, ["open:r", "buffer:%d" % b] + ops + ["error", "close"])
for c in (gz(text(2000)), gz(b"short")):
    line(c, [], ["open:r", "buffer:8", "seek:9223372036854775807:0", "read:5", "tell", "getc", "gets:5", "eof", "error",
                 "close"])

# ---- gzdirect while a seek is pending (patch 0020): the output gz_look buffers is skipped first ----
for c in (text(300), b"hello, world\n", gz(text(300))):
    for b in (8, 64, None):
        pre = [] if b is None else ["buffer:%d" % b]
        for ops in (["seek:9223372036854775807:0", "direct", "getc", "tell", "getc_", "tell", "read:5", "eof"],
                    ["seek:5:0", "direct", "getc", "tell", "gets:10", "tell"],
                    ["seek:200:0", "direct", "getc", "tell", "ungetc:65", "getc", "tell"],
                    ["read:3", "seek:2:0", "direct", "getc", "tell", "read:4"],
                    ["seek:3:1", "direct", "seek:4:1", "direct", "getc", "tell"]):
            line(c, [], ["open:r"] + pre + ops + ["error", "close"])

# ---- gzgets while a seek is pending after the end of file (patch 0021): the file has grown (device data for the
# read after the one that returned 0); gzgets does not fetch before the skip is done ----
for sk in ("9223372036854775807", "5", "2"):
    for ops in (["seek:%s:0" % sk, "direct", "gets:16", "tell", "gets:16", "tell"],
                ["seek:%s:0" % sk, "read:1", "gets:16", "ungetc:65", "tell", "getc", "tell"],
                ["seek:%s:0" % sk, "direct", "ungetc:66", "gets:16", "tell", "read:4", "tell"]):
        for sched in ([], ["4:B64650a"], ["4:B64650a", "5:B7879"]):
            line(b"abc", sched, ["open:r"] + ops + ["eof", "error", "close"])
# the same reads with no skip pending: gzgets still reads after the end of file
for sched in ([], ["4:B64650a"]):
    line(b"abc", sched, ["open:r", "read:8", "gets:16", "tell", "eof", "close"])
    line(b"abc", sched, ["open:r", "direct", "gets:16", "tell", "eof", "close"])

# ---- a write that would move the position past GZ_OFF_MAX is refused (patch 0017); the driver's buffer is not read ----
for m in ("w", "wT"):
    for ops in (["fwrite:1:9223372036854775808:41"], ["fwrite:3:3074457345618258603:41"],
                ["write:4142", "fwrite:1:9223372036854775806:41"], ["seek:5:0", "fwrite:1:9223372036854775803:41"]):
        line(None, [], ["openg:" + m, "buffer:16"] + ops + ["error", "tell", "write:41", "clearerr", "putc:65",
                                                             "printf:d:3", "tell", "close"])

for l in out:
    print(l)
