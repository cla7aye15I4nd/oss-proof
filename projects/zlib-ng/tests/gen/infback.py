#!/usr/bin/env python3
"""Inputs for the infback.c differential test, written to stdout. Deterministic (fixed seed).
Lines: back <windowBits> <first> <chunks> <limit> <abort> <calls> <data>; init <windowBits> <window> <version>
<stream_size>; misc  (see tests/c/infback.c).

Classes: raw deflate streams of every block type (stored: level 0; fixed: Z_FIXED; dynamic: the other strategies,
and hand-built fixed-code streams), every windowBits 8..15 with a window of exactly 1 << windowBits bytes, input from
next_in or from in() in 1-byte, odd-sized and whole chunks, in() running out early (Z_BUF_ERROR, next_in NULL), out()
failing at its first, second and later call, corrupted and truncated streams, long matches that wrap the window,
inflateBack called twice on one state, inflateBackInit_ argument errors (NULL window, windowBits outside 8..15,
wrong version or stream_size) and NULL / stateless streams.

Not generated: streams where a match reaches back into the previous pass of the window so that the source of
inflate_fast's window copy, window + wsize - op, overlaps its destination (distance + min(op, length) > wsize, op the
part of the distance before the current pass). With patch 0007 that copy is a memcpy, and such a stream is undefined
behaviour of the verified source (open-defect case tests/regression/infback-window-overlap). `unsafe` below decodes
the structure of each stream (lengths and distances only) with zlib's rules, continuing past distances that only the
fast path accepts, and drops a line when any match could reach that copy.
"""
import random
import zlib

rng = random.Random(20261119)
out = []

# ---------------------------------------------------------------- structural decoder (filter)

class Bad(Exception):
    pass

class Bits:
    def __init__(self, data):
        self.data = data; self.pos = 0; self.bit = 0
    def get(self, n):
        v = 0
        for i in range(n):
            if self.pos >= len(self.data):
                raise Bad("eof")
            v |= ((self.data[self.pos] >> self.bit) & 1) << i
            self.bit += 1
            if self.bit == 8:
                self.bit = 0; self.pos += 1
        return v
    def align(self):
        if self.bit:
            self.bit = 0; self.pos += 1

def build(lens, kind):
    """zlib's inflate_table rules. Returns a decode map {(len, code): sym} or None (no symbols: every code invalid)."""
    mx = max(lens) if lens else 0
    if mx == 0:
        return None
    count = [0] * 16
    for l in lens:
        count[l] += 1
    left = 1
    for l in range(1, 16):
        left = left * 2 - count[l]
        if left < 0:
            raise Bad("over-subscribed")
    if left > 0 and (kind == "codes" or mx != 1):
        raise Bad("incomplete")
    count[0] = 0
    code = 0; nxt = [0] * 16
    for l in range(1, 16):
        code = (code + count[l - 1]) << 1
        nxt[l] = code
    m = {}
    for s, l in enumerate(lens):
        if l:
            m[(l, nxt[l])] = s; nxt[l] += 1
    return m

def decode(br, m, kind):
    if m is None:
        if kind == "codes":
            br.get(1); return 0
        raise Bad("invalid code")
    code = 0
    for l in range(1, 16):
        code = (code << 1) | br.get(1)
        if (l, code) in m:
            return m[(l, code)]
    raise Bad("invalid code")

LB = [3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258]
LE = [0] * 8 + [1] * 4 + [2] * 4 + [3] * 4 + [4] * 4 + [5] * 4 + [0]
DB = [1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097,
      6145, 8193, 12289, 16385, 24577]
DE = [0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13]
ORDER = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15]
FIXL = build([8] * 144 + [9] * 112 + [7] * 24 + [8] * 8, "lens")
FIXD = build([5] * 30 + [5] * 2, "dists")

def unsafe(data, wbits):
    """True when some match of the stream could make inflate_fast's window copy overlap its destination."""
    wsize = 1 << wbits
    br = Bits(data); pos = 0
    try:
        last = 0
        while not last:
            last = br.get(1); t = br.get(2)
            if t == 0:
                br.align(); n = br.get(16); nn = br.get(16)
                if n != (nn ^ 0xffff):
                    return False
                if br.pos + n > len(br.data):
                    return False
                br.pos += n
                pos += n
                continue
            if t == 3:
                return False
            if t == 1:
                lm, dm = FIXL, FIXD
            else:
                nlen = br.get(5) + 257; ndist = br.get(5) + 1; ncode = br.get(4) + 4
                if nlen > 286 or ndist > 30:
                    return False
                cl = [0] * 19
                for i in range(ncode):
                    cl[ORDER[i]] = br.get(3)
                cm = build(cl, "codes")
                lens = []
                while len(lens) < nlen + ndist:
                    s = decode(br, cm, "codes")
                    if s < 16:
                        lens.append(s)
                    elif s == 16:
                        if not lens:
                            return False
                        lens += [lens[-1]] * (3 + br.get(2))
                    elif s == 17:
                        lens += [0] * (3 + br.get(3))
                    else:
                        lens += [0] * (11 + br.get(7))
                    if len(lens) > nlen + ndist:
                        return False
                if lens[256] == 0:
                    return False
                lm = build(lens[:nlen], "lens"); dm = build(lens[nlen:], "dists")
            while True:
                s = decode(br, lm, "lens")
                if s < 256:
                    pos += 1; continue
                if s == 256:
                    break
                if s > 285:
                    return False
                ln = LB[s - 257] + br.get(LE[s - 257])
                d = decode(br, dm, "dists")
                if d > 29:
                    return False
                dist = DB[d] + br.get(DE[d])
                off = pos % wsize
                whave = wsize if pos >= wsize else 0
                if dist > off + whave:
                    return False
                if dist > off and dist + min(dist - off, ln) > wsize:
                    return True
                pos += ln
    except Bad:
        return False
    return False

# ---------------------------------------------------------------- emitters

def hx(b):
    return b.hex() if b else "-"

def emit(wbits, data, first="null", chunks="-", limit="-", abort="-", calls=1):
    if unsafe(data, wbits):
        return
    out.append(f"back {wbits} {first} {chunks} {limit} {abort} {calls} {hx(data)}")

def comp(data, level=6, wbits=15, strategy=zlib.Z_DEFAULT_STRATEGY):
    c = zlib.compressobj(level, zlib.DEFLATED, -wbits, 8, strategy)
    return c.compress(data) + c.flush()

def text(n):
    words = [b"inflate", b"back", b"window", b"zlib", b"the", b"of", b"lean", b"proof", b"\n", b"  "]
    s = b""
    while len(s) < n:
        s += rng.choice(words) + b" "
    return s[:n]

def rnd(n):
    return bytes(rng.randrange(256) for _ in range(n))

def periodic(n, d):
    pat = rnd(d)
    return (pat * (n // d + 1))[:n]

class BW:
    def __init__(self):
        self.acc = 0; self.n = 0; self.out = bytearray()
    def put(self, v, n):
        self.acc |= v << self.n; self.n += n
        while self.n >= 8:
            self.out.append(self.acc & 255); self.acc >>= 8; self.n -= 8
    def huff(self, code, n):
        r = 0
        for i in range(n):
            r = (r << 1) | ((code >> i) & 1)
        self.put(r, n)
    def flush(self):
        if self.n:
            self.out.append(self.acc & 255); self.acc = 0; self.n = 0
        return bytes(self.out)

def lit(w, v):
    if v < 144: w.huff(0x30 + v, 8)
    elif v < 256: w.huff(0x190 + v - 144, 9)
    elif v < 280: w.huff(v - 256, 7)
    else: w.huff(0xc0 + v - 280, 8)

def fixed(syms):
    """A last fixed-code block of literals (ints) and (length, distance) matches."""
    w = BW(); w.put(1, 1); w.put(1, 2)
    for s in syms:
        if isinstance(s, int):
            lit(w, s)
        else:
            l, d = s
            i = max(k for k in range(29) if LB[k] <= l)
            lit(w, 257 + i); w.put(l - LB[i], LE[i])
            j = max(k for k in range(30) if DB[k] <= d)
            w.huff(j, 5); w.put(d - DB[j], DE[j])
    lit(w, 256)
    return w.flush()

DATAS = [b"", b"a", b"hello, hello, hello world", text(300), rnd(200), bytes(1000), periodic(1500, 3), text(5000),
         periodic(20000, 37)]
STRATS = [zlib.Z_DEFAULT_STRATEGY, zlib.Z_FILTERED, zlib.Z_HUFFMAN_ONLY, zlib.Z_RLE, zlib.Z_FIXED]

# 1. Block types, levels, strategies; whole input at once from next_in and from in().
for d in DATAS:
    for level in (0, 1, 6, 9):
        for st in (STRATS if level else [zlib.Z_DEFAULT_STRATEGY]):
            c = comp(d, level, 15, st)
            emit(15, c)
            emit(15, c, str(len(c)))
            if len(d) <= 5000:
                emit(15, c, "null", rng.choice(["1", "3,5,7", "13", "64", "2,1000"]))

# 2. Every windowBits with a window of exactly that size; streams made with that window (9 for 8: raw deflate
#    refuses windowBits 8), so matches wrap the window many times.
for wb in range(8, 16):
    for d in (text(3000), periodic(5000, 300), periodic(9000, 250), rnd(700) * 6, text(40000)):
        c = comp(d, 9, max(wb, 9))
        emit(wb, c)
        emit(wb, c, "null", "1")
        emit(wb, c, "7", "11,3")
        emit(wb, c, "null", "-", "-", "-", 2)

# 3. Input chunk sizes 1..20 and around inflate_fast's need of 15 bytes, first chunk from next_in of every size.
d = text(6000)
c = comp(d, 9, 12)
for ch in range(1, 21):
    emit(12, c, "null", str(ch))
for f in (0, 1, 2, 14, 15, 16, len(c) // 2, len(c)):
    emit(12, c, str(f), "17")
emit(12, c, "z", "-")

# 4. in() running out: every truncation class.
for lim in (0, 1, 2, 3, 5, 10, len(c) // 3, len(c) - 1):
    emit(12, c, "null", "-", str(lim))
    emit(12, c, "null", "4", str(lim))
    emit(12, c, str(min(lim, 3)), "1", str(lim))

# 5. out() failing at its first, second and later calls, with output that fills the window several times.
for wb in (8, 10, 15):
    d = text(9000)
    c = comp(d, 6, max(wb, 9))
    for ab in (1, 2, 3, 7, 1000):
        emit(wb, c, "null", "-", "-", str(ab))
        emit(wb, c, "null", "5", "-", str(ab), 2)

# 6. Hand-built fixed-code streams: long matches wrapping the window, distances 1..258 at every phase of a 256-byte
#    window, lengths 3..258.
for wb in (8, 9):
    ws = 1 << wb
    for start in (0, 1, 100, ws - 3, ws - 1, ws, ws + 1, 2 * ws - 10):
        for dist in (1, 2, 3, 7, 64, 100, 200, ws - 10, ws):
            for ln in (3, 10, 100, 258):
                if dist > start:
                    continue
                syms = [rng.randrange(256) for _ in range(start)] + [(ln, dist)] + [65] * 20
                s = fixed(syms)
                emit(wb, s)
                emit(wb, s, "null", "1")
    long_ = [rng.randrange(256) for _ in range(40)] + [(258, 40)] * 30 + [(258, 1)] * 10 + [7] * 30
    emit(wb, fixed(long_))
    emit(wb, fixed(long_), "null", "3")

# 7. Corrupted streams: bit flips, bad block type, bad stored lengths, distances too far back, bad codes.
for _ in range(150):
    d = rng.choice([text(2000), periodic(3000, 11), rnd(300), text(400)])
    level = rng.choice([0, 1, 6, 9]); st = rng.choice(STRATS)
    wb = rng.choice([8, 9, 12, 15])
    c = bytearray(comp(d, level, max(wb, 9), st))
    for _ in range(rng.choice([1, 1, 2, 5])):
        i = rng.randrange(len(c)); c[i] ^= 1 << rng.randrange(8)
    emit(wb, bytes(c), rng.choice(["null", "5"]), rng.choice(["-", "1", "9"]))
emit(15, bytes([0x07]))                          # block type 3
emit(15, bytes([0x01, 0x05, 0x00, 0xfa, 0xfe]))  # stored length check fails
emit(15, bytes([0x01, 0x00, 0x00, 0xff, 0xff]))  # empty stored block
emit(15, fixed([1, 2, (10, 3)]))                 # distance beyond the output
emit(15, fixed([(3, 1)]))                        # distance 1 at the start
emit(8, fixed([5] * 20 + [(258, 300)]))          # distance beyond a 256-byte window
emit(15, bytes([0x05, 0xe0, 0xff, 0x07]))        # dynamic header with too many symbols
emit(15, bytes([0x0d, 0x00, 0x00]))              # dynamic header, all code lengths 0
for k in range(1, 40):
    emit(15, comp(text(500), 9)[:k])             # truncated at every early byte

# 8. A stream followed by trailing bytes (next_in and avail_in on return), two streams back to back.
c = comp(text(800), 6)
emit(15, c + b"TRAILING DATA")
emit(15, c + b"TRAILING DATA", str(len(c) + 13))
emit(15, c + c, "null", "-", "-", "-", 2)

# 9. inflateBackInit_ arguments and NULL streams.
for wb in (-1, 0, 7, 8, 9, 15, 16, 31, -15, 2147483647, -2147483648):
    out.append(f"init {wb} w 1.3.2.zlib-ng 112")
out.append("init 15 null 1.3.2.zlib-ng 112")
out.append("init 7 null 1.3.2.zlib-ng 112")
for ver, size in (("null", 112), ("2.0.0", 112), ("1.2.3", 112), ("1.3.2.zlib-ng", 111), ("1.3.2.zlib-ng", 88),
                  ("1", 112)):
    out.append(f"init 15 w {ver} {size}")
    out.append(f"init 15 null {ver} {size}")
out.append("misc")

print("\n".join(out))
