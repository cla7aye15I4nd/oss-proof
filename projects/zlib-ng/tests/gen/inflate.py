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

print("\n".join(out))
