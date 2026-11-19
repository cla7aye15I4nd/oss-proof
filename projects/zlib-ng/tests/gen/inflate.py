#!/usr/bin/env python3
"""Inputs for the inflate.c differential test, written to stdout. Deterministic (fixed seed).
Line: inf <windowBits> <flush> <inchunk> <outchunk> <outcap> <data> <dict> <hdr> <reset>  (see tests/c/inflate.c).

Classes: zlib, gzip and raw streams of every block type (stored: level 0; fixed: Z_FIXED; dynamic: the other
strategies), every windowBits value accepted or refused by inflateInit2 (including streams made with a smaller
window, and a header window larger than the requested one), dictionaries (right, wrong, missing), gzip headers with
extra / name / comment / header CRC and header buffers of every size class, every flush mode, input and output split
at small and odd sizes (1 byte, 7, 259/260/261 around inflate_fast's limit), truncated and corrupted streams (bit
flips, bad header check, bad block type, bad stored lengths, distances too far back, bad check values), matches
crossing the window (data longer than the window, output in pieces), match distances 1..64, and
inflateReset / inflateResetKeep / inflateReset2 between two decodes.
"""
import random
import struct
import zlib

rng = random.Random(20261118)
out = []

def hx(b):
    return b.hex() if b else "-"

def emit(wbits, flush, inchunk, outchunk, outcap, data, dict_="-", hdr="-", reset="-"):
    out.append(f"inf {wbits} {flush} {inchunk} {outchunk} {outcap} {hx(data)} {dict_} {hdr} {reset}")

def comp(data, level=6, wbits=15, strategy=zlib.Z_DEFAULT_STRATEGY, memlevel=8, zdict=None):
    if zdict is not None:
        c = zlib.compressobj(level, zlib.DEFLATED, wbits, memlevel, strategy, zdict)
    else:
        c = zlib.compressobj(level, zlib.DEFLATED, wbits, memlevel, strategy)
    return c.compress(data) + c.flush()

def text(n):
    words = [b"inflate", b"window", b"zlib", b"deflate", b"the", b"of", b"lean", b"proof", b"\n", b"  "]
    s = b""
    while len(s) < n:
        s += rng.choice(words) + b" "
    return s[:n]

def rnd(n):
    return bytes(rng.randrange(256) for _ in range(n))

def periodic(n, d):
    pat = rnd(d)
    return (pat * (n // d + 1))[:n]

DATAS = [b"", b"a", b"hello, hello, hello world", text(300), rnd(200), bytes(1000), periodic(1500, 3), text(4000)]
STRATS = [zlib.Z_DEFAULT_STRATEGY, zlib.Z_FILTERED, zlib.Z_HUFFMAN_ONLY, zlib.Z_RLE, zlib.Z_FIXED]

# 1. zlib streams: block types, levels, strategies, whole buffers and small pieces.
for d in DATAS:
    for level in (0, 1, 6, 9):
        for st in (STRATS if level else [zlib.Z_DEFAULT_STRATEGY]):
            c = comp(d, level, 15, st)
            emit(15, 0, 1 << 20, 1 << 20, len(d) + 10, c)
            if len(d) <= 1500:
                emit(15, 0, rng.choice([1, 2, 3, 7, 16]), rng.choice([1, 7, 64, 259, 260, 261, 1000]), len(d) + 5, c)

# 2. Split points: every input chunk size 1..20 and output sizes around 258/260 on one dynamic stream.
d = text(2000)
c = comp(d, 9)
for ic in range(1, 21):
    emit(15, 0, ic, 1 << 20, len(d), c)
for oc in (1, 2, 3, 4, 5, 8, 15, 16, 17, 257, 258, 259, 260, 261, 262, 300, 511):
    emit(15, 0, 1 << 20, oc, len(d), c)
    emit(15, 0, 13, oc, len(d), c)

# 3. Flush modes.
for flush in (0, 2, 4, 5, 6):
    for d in (text(500), periodic(800, 7), b"x"):
        c = comp(d, 6)
        emit(15, flush, 1 << 20, 1 << 20, len(d) + 3, c)
        emit(15, flush, 5, 100, len(d) + 3, c)
        emit(15, flush, 1 << 20, 1 << 20, max(1, len(d) // 2), c)   # Z_FINISH with too little output

# 4. windowBits: compression windows 9..15, every inflate windowBits.
d = text(3000) + periodic(3000, 300)
for cw in (9, 10, 12, 15):
    for wrap, off in (("zlib", 0), ("gzip", 16), ("raw", None)):
        if wrap == "raw":
            c = comp(d, 6, -cw)
            for iw in range(-15, -7):
                emit(iw, 0, 1 << 20, 1 << 20, len(d), c)
            emit(-cw, 0, 97, 333, len(d), c)
        else:
            c = comp(d, 6, cw + off)
            for iw in [0, 8, 9, 10, 11, 12, 13, 14, 15, 24, 31, 32, 39, 40, 47]:
                emit(iw, 0, 1 << 20, 1 << 20, len(d), c)
for iw in (1, 7, 16, 17, 23, 48, 64, -1, -7, -16, -100, 2147483647, -2147483648):
    emit(iw, 0, 16, 16, 16, comp(b"abc"))

# 5. Dictionaries.
dic = text(400)
for d in (text(600), dic[:100] + text(100)):
    c = comp(d, 6, 15, zdict=dic)
    emit(15, 0, 1 << 20, 1 << 20, len(d), c, dic.hex())
    emit(15, 0, 7, 50, len(d), c, dic.hex())
    emit(15, 0, 1 << 20, 1 << 20, len(d), c, text(400).hex())   # wrong dictionary
    emit(15, 0, 1 << 20, 1 << 20, len(d), c)                    # no dictionary: Z_NEED_DICT
    craw = comp(d, 6, -15, zdict=dic)
    emit(-15, 0, 1 << 20, 1 << 20, len(d), craw)                # raw without dictionary: too far back
    emit(-15, 0, 1 << 20, 1 << 20, len(d), craw, rnd(1).hex())  # raw dictionary through Z_NEED_DICT? (no: raw never asks)

# 6. gzip headers.
def gz_member(data, extra=None, name=None, comment=None, hcrc=False, mtime=0x12345678, xfl=2, os_=3, text_=0):
    flg = (1 if text_ else 0) | (2 if hcrc else 0) | (4 if extra is not None else 0) | \
          (8 if name is not None else 0) | (16 if comment is not None else 0)
    h = bytes([0x1f, 0x8b, 8, flg]) + struct.pack("<I", mtime) + bytes([xfl, os_])
    if extra is not None:
        h += struct.pack("<H", len(extra)) + extra
    if name is not None:
        h += name + b"\0"
    if comment is not None:
        h += comment + b"\0"
    if hcrc:
        h += struct.pack("<H", zlib.crc32(h) & 0xffff)
    body = comp(data, 6, -15)
    return h + body + struct.pack("<II", zlib.crc32(data), len(data) & 0xffffffff)

d = text(700)
variants = [
    dict(),
    dict(extra=rnd(10)),
    dict(extra=b""),
    dict(name=b"file.txt"),
    dict(comment=b"a comment here"),
    dict(extra=rnd(30), name=b"n", comment=b"c", hcrc=True, text_=1),
    dict(name=b"", comment=b"", hcrc=True),
    dict(extra=rnd(300), name=b"x" * 40, comment=b"y" * 40),
]
for v in variants:
    m = gz_member(d, **v)
    for hdr in ("-", "0,0,0", "4,4,4", "64,64,64", "512,64,64", "1,1,1"):
        emit(31, 0, 1 << 20, 1 << 20, len(d), m, "-", hdr)
    emit(31, 0, 1, 1 << 20, len(d), m, "-", "16,16,16")
    emit(47, 0, 3, 77, len(d), m, "-", "16,16,16")
    emit(15, 0, 1 << 20, 1 << 20, len(d), m)     # gzip data to a zlib-only inflate
bad = bytearray(gz_member(d, name=b"q", hcrc=True)); bad[-len(comp(d, 6, -15)) - 8 - 1] ^= 1
emit(31, 0, 1 << 20, 1 << 20, len(d), bytes(bad), "-", "8,8,8")
for flg in (0xe0, 0x20):
    m = bytearray(gz_member(d)); m[3] |= flg
    emit(31, 0, 1 << 20, 1 << 20, len(d), bytes(m))
m = bytearray(gz_member(d)); m[2] = 7
emit(31, 0, 1 << 20, 1 << 20, len(d), bytes(m))
two = gz_member(b"first ") + gz_member(b"second")
emit(31, 0, 1 << 20, 1 << 20, 20, two)
m = bytearray(gz_member(d)); m[-5] ^= 0x80                   # bad length
emit(31, 0, 1 << 20, 1 << 20, len(d), bytes(m))
m = bytearray(gz_member(d)); m[-8] ^= 1                      # bad crc
emit(31, 0, 1 << 20, 1 << 20, len(d), bytes(m))

# 7. Corruption: truncation, bit flips, bad zlib header, bad block type, bad stored lengths, bad check.
for d in (text(900), rnd(300), periodic(700, 5)):
    for level, st in ((0, 0), (6, 0), (6, zlib.Z_FIXED), (9, zlib.Z_HUFFMAN_ONLY)):
        c = comp(d, level, 15, st)
        for cut in sorted(set([0, 1, 2, 3, len(c) // 3, len(c) // 2, len(c) - 5, len(c) - 1])):
            emit(15, rng.choice([0, 4]), rng.choice([1, 9, 1 << 20]), rng.choice([10, 1 << 20]), len(d), c[:cut])
        for _ in range(12):
            b = bytearray(c)
            i = rng.randrange(len(b))
            b[i] ^= 1 << rng.randrange(8)
            emit(15, 0, rng.choice([1, 5, 1 << 20]), rng.choice([3, 260, 1 << 20]), len(d) + 50, bytes(b))
        b = bytearray(c); b[-1] ^= 0xff                        # bad adler32
        emit(15, 0, 1 << 20, 1 << 20, len(d), bytes(b))
emit(15, 0, 64, 64, 64, bytes([0x78, 0x9d]) + b"\x00" * 10)     # bad header check
emit(15, 0, 64, 64, 64, bytes([0x79, 0x9c]) + b"\x00" * 10)     # bad header check
emit(15, 0, 64, 64, 64, bytes([0x88, 0x98]) + b"\x00" * 10)     # window bits 16
emit(15, 0, 64, 64, 64, bytes([0x77, 0x85]) + b"\x00" * 10)     # method 7
emit(-15, 0, 64, 64, 64, bytes([0x07]) + b"\x00" * 10)          # block type 3
emit(-15, 0, 64, 64, 64, bytes([0x01, 0x05, 0x00, 0xfa, 0xfe]) + b"hello")  # stored length mismatch
emit(-15, 0, 64, 64, 64, bytes([0x01, 0x05, 0x00, 0xfa, 0xff]) + b"hello")  # stored, valid
for _ in range(60):                                             # random raw input (code errors of every kind)
    emit(-15, 0, rng.choice([1, 7, 1 << 20]), rng.choice([1, 300, 1 << 20]), 2000, rnd(rng.randrange(1, 80)))

# 8. Matches crossing the window, output in pieces.
for n, per in ((40000, 33000), (50000, 20000), (70000, 32768)):
    base = rnd(per)
    d = (base * (n // per + 1))[:n]
    c = comp(d, 9)
    emit(15, 0, 1 << 20, 1 << 20, n, c)
    emit(15, 0, 4096, 5000, n, c)
    emit(15, 0, 1 << 20, 1023, n, c)
    emit(15, 0, 1 << 20, 259, n, c)
d = text(40000)
c = comp(d, 6, 9)
emit(9, 0, 1 << 20, 600, len(d), c)
emit(10, 0, 300, 513, len(d), c)

# 9. Distances 1..64.
for dist in range(1, 65):
    d = periodic(600 + dist * 7, dist)
    c = comp(d, 6)
    emit(15, 0, 1 << 20, 1 << 20, len(d), c)
    emit(15, 0, 1 << 20, rng.choice([3, 9, 33, 100]), len(d), c)

# 10. Reset between two decodes.
for reset in ("R", "K", "W15", "W-15", "W31", "W47", "W0", "W7", "W100"):
    for d in (text(500), b""):
        emit(15, 0, 1 << 20, 1 << 20, len(d) + 1, comp(d), "-", "-", reset)
        emit(-15, 0, 9, 40, len(d) + 1, comp(d, 6, -15), "-", "-", reset)
emit(31, 0, 1 << 20, 1 << 20, 800, gz_member(text(700), name=b"nm"), "-", "8,8,8", "R")


# 11. Script tests of the other entry points on one stream (ops).
def ops(wbits, outcap, data, dict_, script):
    out.append(f"ops {wbits} {outcap} {hx(data)} {dict_} {','.join(script)}")

ALL = ["i1000000", "o1000000"]
d = text(3000)
c = comp(d)
craw = comp(d, 6, -15)
cfix = comp(b"abcabcabcabc hello hello", 6, -15, zlib.Z_FIXED)
cgz = gz_member(d, name=b"name")

# Queries and resets around a plain decode.
for wb, cc in ((15, c), (-15, craw), (31, cgz), (47, cgz), (0, c)):
    ops(wb, len(d) + 10, cc, "-", ["Y", "M", "N", "G0", "G40000", "g"] + ALL + ["f0", "M", "N", "Y", "G0", "G40000", "g", "E", "M", "N", "Y", "g", "f0"])
    for k in (1, 5, 37, 200):
        ops(wb, len(d) + 10, cc, "-", [f"i{k}", "o1000000", "f0", "M", "N", "Y", "G0", "G40000", "i1000000", f"o{k}", "f0", "M", "G40000", "f0", "M"])
    for r in ("R", "K", "W15", "W-15", "W31", "W47", "W0", "W8", "W7", "W-7", "W-8", "W16", "W100"):
        ops(wb, len(d) + 10, cc, "-", ["i100", "o50", "f0", r, "M", "N"] + ALL + ["f0", "M"])

# inflateCopy mid-stream, including in a fixed block, then continue with the copy.
for wb, cc, dd in ((15, c, d), (-15, craw, d), (31, cgz, d), (-15, cfix, b"x" * 24)):
    ops(wb, len(dd) + 10, cc, "-", ["C"] + ALL + ["f0"])
    for k in (1, 2, 3, 9, 50, 400, len(cc) - 3):
        ops(wb, len(dd) + 10, cc, "-", [f"i{k}", "o1000000", "f0", "C", "M"] + ALL + ["f0", "M", "N"])
        ops(wb, len(dd) + 10, cc, "-", ["i1000000", f"o{k}", "f0", "C", "M", "G40000", "o1000000", "f0"])
    ops(wb, len(dd) + 10, cc, "-", ALL + ["f0", "C", "f0", "E"])
    ops(wb, len(dd) + 10, cc, "-", ["E", "C", "f0"])

# inflatePrime: the first bits of a raw stream come through inflatePrime.
for dd in (text(500), b"", rnd(300), b"a"):
    cr = comp(dd, 6, -15)
    b0 = cr[0]
    ops(-15, len(dd) + 5, cr[1:], "-", [f"P8/{b0}"] + ALL + ["f0"])
    ops(-15, len(dd) + 5, cr[1:], "-", [f"P3/{b0 & 7}", f"P5/{b0 >> 3}"] + ALL + ["f0"])
    if len(cr) > 2:
        v = cr[0] | (cr[1] << 8)
        ops(-15, len(dd) + 5, cr[2:], "-", [f"P16/{v}"] + ALL + ["f0"])
        ops(-15, len(dd) + 5, cr[2:], "-", [f"P7/{v & 127}", f"P9/{v >> 7}"] + ALL + ["f0"])
for p in ("P0/0", "P-1/0", "P-1/5", "P1/1", "P16/65535", "P17/0", "P32/0", "P33/1", "P-2/0", "P31/1", "P24/7"):
    ops(-15, 100, craw, "-", [p, p] + ALL + ["f0"])
    ops(15, 100, c, "-", [p] + ALL + ["f0"])
    ops(-15, 100, craw, "-", ["i3", "o100", "f0", p, "M"] + ALL + ["f0"])
for i in range(8):
    ops(-15, 100, craw, "-", [f"P8/{i}"] * 7 + ALL + ["f0"])

# inflateSync: full-flush points, corrupted starts, empty input, bits in the bit buffer.
def flushed(parts, wbits):
    co = zlib.compressobj(6, zlib.DEFLATED, wbits)
    res = b""
    marks = []
    for p in parts:
        res += co.compress(p) + co.flush(zlib.Z_FULL_FLUSH)
        marks.append(len(res))
    return res + co.flush(), marks
parts = [text(700), rnd(200), text(900), periodic(500, 7)]
for wb in (15, -15, 31):
    cs, marks = flushed(parts, wb)
    total = sum(len(p) for p in parts) + 10
    ops(wb, total, cs, "-", ["S"] + ALL + ["S", "f0"])
    ops(wb, total, cs, "-", ["i0", "o100", "S", "S", "f0"])
    ops(wb, total, cs, "-", ["P16/0", "S", "i1000000", "S", "o1000000", "f0"])
    ops(wb, total, cs, "-", ["P7/5", "i1", "S", "i1000000", "S", "o1000000", "f0", "Y"])
    for m in marks[:-1]:
        bad = bytearray(cs)
        for j in range(5, min(40, m - 6)):
            bad[j] ^= 0x5a
        ops(wb, total, bytes(bad), "-", ALL + ["f0", "S", "Y", "f0", "M", "N"])
        ops(wb, total, bytes(bad), "-", ["i3", "o1000000", "f0", "S", "i1000000", "S", "f0"])
        ops(wb, total, cs, "-", [f"i{m}", "o1000000", "f0", "Y", "M", "i1000000", "f0"])
        ops(wb, total, cs, "-", [f"i{m - 2}", "o1000000", "f0", "Y", "S", "i1000000", "S", "f0"])
    for k in (1, 2, 3, 4, 7, 100):
        ops(wb, total, rnd(k), "-", ["i1000000", "S", "S", "f0"])
    ops(wb, total, b"\x00\x00\xff\xff" + cs, "-", ["i1000000", "S", "o1000000", "f0"])
    ops(wb, total, b"\x00\x00\xff" + cs, "-", ["i1", "S", "i2", "S", "i1000000", "S", "o1000000", "f0"])

# Dictionaries through the script: d at Z_NEED_DICT, too early, too late, NULL; raw streams.
dic = text(300)
cd = comp(d, 6, 15, zdict=dic)
cdraw = comp(d, 6, -15, zdict=dic)
for script in (ALL + ["f0", "d", "f0"], ALL + ["f0", "n", "d", "f0"], ["d"] + ALL + ["f0"], ALL + ["f0", "G40000", "d", "G40000", "f0"],
               ["i2", "o100", "f0", "d", "i1000000", "o1000000", "f0"], ALL + ["f0", "d", "C", "f0", "G40000"]):
    ops(15, len(d) + 5, cd, dic.hex(), script)
    ops(-15, len(d) + 5, cdraw, dic.hex(), script)
ops(-15, len(d) + 5, cdraw, "-", ["d"] + ALL + ["f0"])
ops(-15, len(d) + 5, cdraw, "-", ["n"] + ALL + ["f0"])
ops(15, len(d) + 5, cd, text(200).hex(), ALL + ["f0", "d", "f0"])
big = rnd(40000)
ops(-15, len(d) + 5, comp(d, 6, -15, zdict=big[-32768:]), big.hex(), ["d", "G40000"] + ALL + ["f0", "G40000"])
ops(-9, len(d) + 5, comp(d, 6, -9, zdict=big[-512:]), big.hex(), ["d", "G40000"] + ALL + ["f0"])

# inflateUndermine / inflateValidate with bad check values.
for wb, cc in ((15, c), (31, cgz)):
    bad = bytearray(cc)
    bad[-1] ^= 1
    bad[-5] ^= 1
    for script in (["U1"], ["U0"], ["V0"], ["V1"], ["V0", "V1"], ["U1", "V0"]):
        ops(wb, len(d) + 5, bytes(bad), "-", script + ALL + ["f0", "M", "f4"])
        ops(wb, len(d) + 5, cc, "-", script + ALL + ["f4"])
    ops(wb, len(d) + 5, bytes(bad), "-", ["i10", "o1000000", "f0", "V0", "i1000000", "f0"])

# Flush modes in a script, block and tree boundaries.
for f in (0, 1, 2, 3, 4, 5, 6, 7, -1):
    ops(15, len(d) + 5, c, "-", ALL + [f"f{f}", f"f{f}", "M"])
    ops(15, len(d) + 5, c, "-", ["i40", "o1000000", "f5", "M", "f5", "M", "f6", "M", "i1000000", "f6", "M", "f0"])

# 12. uncompress / uncompress2 / uncompress_z / uncompress2_z.
def unc_line(v, dsize, dl, sl, src):
    src_s = "null" if src is None else hx(src)
    out.append(f"unc {v} {dsize} {dl} {sl} {'null' if src is None else 'x'} {src_s}")

VARS = ("u", "u2", "uz", "u2z")
for dd in (b"", b"a", text(1000), rnd(500), periodic(70000, 3), rnd(70000)):
    cc = comp(dd)
    n = len(dd)
    for v in VARS:
        unc_line(v, n + 3, n + 3, len(cc), cc)
        unc_line(v, n, n, len(cc), cc)
        unc_line(v, n + 3, n, len(cc) + 5, cc + b"junk!")
        unc_line(v, max(n, 1), max(n - 1, 0), len(cc), cc)
        unc_line(v, n // 2 + 1, n // 2, len(cc), cc)
        unc_line(v, 0, 0, len(cc), cc)
        unc_line(v, 5, 0, len(cc), cc)
        unc_line(v, "null", 0, len(cc), cc)
        unc_line(v, n + 3, n + 3, max(len(cc) - 4, 0), cc)
        unc_line(v, n + 3, n + 3, len(cc) // 2, cc)
        unc_line(v, n + 3, n + 3, 0, cc)
for v in VARS:
    cc = comp(text(300))
    unc_line(v, 400, "null", len(cc), cc)
    unc_line(v, 400, 400, "null", cc)
    unc_line(v, "null", 400, len(cc), cc)
    unc_line(v, 400, 400, 0, None)
    unc_line(v, 400, 400, 5, None)
    unc_line(v, 0, 0, 0, None)
    unc_line(v, "null", 0, 0, None)
    unc_line(v, 400, 400, len(cc), comp(text(300), 6, 15, zdict=b"dictionary"))
    unc_line(v, 400, 400, len(cc), gz_member(text(300)))
    unc_line(v, 400, 400, len(cc), comp(text(300), 6, -15))
    bad = bytearray(cc)
    bad[len(bad) // 2] ^= 0x33
    unc_line(v, 400, 400, len(bad), bytes(bad))
    bad = bytearray(cc)
    bad[-1] ^= 1
    unc_line(v, 400, 400, len(bad), bytes(bad))
    unc_line(v, 400, 400, 2, cc)
    unc_line(v, 400, 400, 1, cc)
    unc_line(v, 400, 400, 3, b"\x78\x9c\x03")
    for k in (1, 2, 3, 10):
        unc_line(v, 400, 400, k, rnd(k))
for i in range(60):
    dd = rng.choice([text, rnd])(rng.randrange(0, 3000))
    cc = comp(dd, rng.choice([0, 1, 6, 9]), rng.choice([9, 12, 15]))
    dl = rng.choice([len(dd), len(dd) + 7, max(0, len(dd) - rng.randrange(1, 50)), 0])
    sl = rng.choice([len(cc), max(0, len(cc) - rng.randrange(1, 10)), len(cc) + 3])
    src = cc + b"\x00" * max(0, sl - len(cc))
    unc_line(rng.choice(VARS), dl + rng.choice([0, 1, 9]), dl, sl, src)

# 13. inflateInit_ / inflateInit2_ version and size checks.
for ver in ("null", "1.3.2.zlib-ng", "1", "1.0", "2.3.90", "0.9", "x"):
    for size in (112, 111, 113, 0, -1, 88):
        for wb in ("-", "15", "8", "7", "-8", "-15", "-16", "16", "24", "31", "47", "48", "0", "40", "-7", "100"):
            out.append(f"ver {ver} {size} {wb}")

print("\n".join(out))
