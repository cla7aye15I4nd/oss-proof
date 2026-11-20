#!/usr/bin/env python3
"""Inputs for the deflate.c / compress.c differential test (format: tests/c/deflate.c), written to stdout.
Deterministic. Covers every level 0..9 and every strategy, every windowBits (raw, zlib, gzip) and memLevel, every
flush mode and sequences of them, input and output split at many points (1-byte chunks, zero-length calls),
inputs around the window size and 2 * wsize, repetitive / random / text / all-zero / mixed data, dictionaries,
gzip headers, deflateParams / deflateCopy / deflatePrime / deflatePending / deflateUsed / deflateTune /
deflateReset* / deflateBound / deflateGetDictionary mid-stream, calls after Z_STREAM_END and after errors, tiny
avail_out, invalid arguments, and the compress* family with exact / short / zero / NULL buffers.
"""
import random
import sys

QUICK = len(sys.argv) > 1 and sys.argv[1] == "quick"
rng = random.Random(20261119)
out = []
KINDS = "zrtpbm"


def data(kind, n, seed=None):
    if n == 0:
        return "-"
    return "gen:%s:%d:%d" % (kind, n, rng.randrange(1, 1 << 31) if seed is None else seed)


def bound_out(n):
    return n + n // 8 + n // 64 + 600


def d(level, wbits, mem, strat, dat, n, script, dic="-", hdr="-", outcap=None, method=8):
    out.append("def %d %d %d %d %d %s %s %s %d %s" % (
        level, method, wbits, mem, strat, dat, dic, hdr, bound_out(n) if outcap is None else outcap,
        ",".join(script) if script else "-"))


def finish(ic=1 << 30, oc=1 << 30):
    return ["L4/%d/%d" % (ic, oc), "f4", "p", "u"]


# 1. Every level x strategy x wrapper, a few data kinds and sizes (window boundaries for wbits 9..15).
sizes = [0, 1, 2, 3, 4, 7, 100, 257, 258, 259, 262, 1000, 4000]
for level in range(-1, 10):
    for strat in range(5):
        for wb in (15, -15, 31, 9, -9, 25, 8):
            kind = KINDS[(level + strat + wb) % 6]
            n = rng.choice(sizes)
            d(level, wb, 8, strat, data(kind, n), n, finish())

# 2. Sizes around the window and 2 * wsize, every windowBits, chunked input and output.
lim = 40000 if QUICK else 140000
for wb in range(9, 16):
    w = 1 << wb
    for n in sorted({w - 1, w, w + 1, 2 * w - 262, 2 * w, 2 * w + 1, 3 * w + 7, 32768 + 300}):
        if n > lim:
            continue
        for level in (0, 1, 2, 3, 5, 6, 7, 9):
            kind = rng.choice("trpm")
            wrap = rng.choice((wb, -wb, wb + 16))
            d(level, wrap, rng.randint(1, 9), rng.choice((0, 0, 1)), data(kind, n), n,
              finish(rng.choice((n + 1, 997, 4096, 65536)), rng.choice((1 << 30, 1000, 64))))

# 3. memLevel 1..9 with block-filling inputs (symbol buffer full: lit_bufsize = 1 << (memLevel + 6)).
for mem in range(1, 10):
    for level in (1, 2, 4, 6, 8, 9):
        n = (1 << (mem + 6)) * rng.choice((1, 3)) + rng.randint(0, 50)
        n = min(n, 30000)
        d(level, 15, mem, rng.choice((0, 1, 3, 4)), data(rng.choice("trbm"), n), n, finish())

# 4. Flush modes and sequences, tiny output buffers, 1-byte chunks, zero-length calls.
for case in range(160 if QUICK else 400):
    level = rng.randint(0, 9)
    strat = rng.choice((0, 0, 0, 1, 2, 3, 4))
    wb = rng.choice((15, -15, 31, 12, -10, 26))
    n = rng.choice((0, 1, 50, 300, 2000, 9000))
    script = []
    for _ in range(rng.randint(1, 6)):
        r = rng.random()
        if r < 0.5:
            script.append("L%d/%d/%d" % (rng.choice((0, 0, 1, 2, 3, 5)), rng.choice((1, 7, 100, 1 << 30)),
                                         rng.choice((1, 3, 64, 1 << 30))))
        elif r < 0.6:
            script += ["i0", "o%d" % rng.choice((0, 1, 5)), "f%d" % rng.randint(-1, 6)]
        elif r < 0.7:
            script.append("p")
        elif r < 0.8:
            script.append("u")
        else:
            script += ["i%d" % rng.randint(0, 50), "o%d" % rng.randint(0, 20), "f%d" % rng.randint(0, 5)]
    script += ["L4/%d/%d" % (rng.choice((1, 50, 1 << 30)), rng.choice((1, 9, 1 << 30))), "f4", "f0", "i1", "f4", "f2"]
    d(level, wb, rng.randint(1, 9), strat, data(rng.choice(KINDS), n), n, script)

# 5. deflateParams mid-stream (level and strategy changes), deflateCopy, deflatePrime, deflateTune, resets.
for case in range(200 if QUICK else 500):
    level = rng.randint(0, 9)
    n = rng.choice((100, 3000, 20000 if not QUICK else 6000, 70000 if not QUICK else 9000))
    wb = rng.choice((15, -15, 31, 10))
    script = []
    for _ in range(rng.randint(1, 5)):
        r = rng.random()
        if r < 0.35:
            script.append("L0/%d/%d" % (rng.choice((n // 3 + 1, 999)), rng.choice((1 << 30, 500))))
        elif r < 0.55:
            script.append("Q%d/%d" % (rng.randint(-1, 9), rng.choice((0, 0, 1, 2, 3, 4))))
        elif r < 0.62:
            script.append("C")
        elif r < 0.7:
            script.append("P%d/%d" % (rng.choice((0, 1, 3, 7, 8, 13, 16, 31, 63, 64, 65, -1)), rng.randint(-50000, 50000)))
        elif r < 0.76:
            script.append("T%d/%d/%d/%d" % (rng.choice((0, 4, 32, 258)), rng.choice((0, 3, 16, 258)),
                                             rng.choice((3, 8, 128, 258)), rng.choice((1, 4, 128, 4096))))
        elif r < 0.82:
            script.append(rng.choice(("R", "K")))
        elif r < 0.9:
            script.append("B%d" % rng.choice((0, 1, 100, 65536, 1 << 40)))
        else:
            script.append("G%d" % rng.choice((0, 32768)))
    script += finish(rng.choice((1 << 30, 777)), rng.choice((1 << 30, 333)))
    d(level, wb, rng.randint(1, 9), rng.choice((0, 0, 1, 2, 3, 4)), data(rng.choice(KINDS), n), n, script)

# 6. Dictionaries (set before data, too late, NULL, larger than the window), deflateGetDictionary.
for case in range(80 if QUICK else 200):
    level = rng.randint(0, 9)
    wb = rng.choice((15, -15, 31, 9, -9, 12))
    dn = rng.choice((0, 1, 3, 100, 600, 40000))
    dic = data(rng.choice("trp"), dn) if dn else rng.choice(("-", "null"))
    n = rng.choice((0, 10, 1000, 5000))
    pre = rng.choice((["D"], ["D", "D"], ["d"], ["L0/5/1000", "D"], ["G32768", "D", "G32768", "g"]))
    d(level, wb, 8, rng.choice((0, 0, 2, 3)), data(rng.choice("trpm"), n), n,
      pre + ["G32768"] + finish() + ["G32768"], dic=dic)

# 7. gzip headers: extra / name / comment / hcrc, small output buffers (header written in pieces).
for case in range(100 if QUICK else 250):
    ex = rng.choice((-1, 0, 1, 10, 300, 70000))
    nm = rng.choice((-1, 0, 5, 300))
    cm = rng.choice((-1, 0, 7, 400))
    hdr = "%d/%d/%d/%d/%d/%d/%d/%d" % (rng.randint(0, 1), rng.randrange(1 << 32), rng.randint(0, 4),
                                       rng.randint(0, 300), ex, nm, cm, rng.randint(0, 1))
    n = rng.choice((0, 5, 400))
    mem = rng.choice((1, 2, 8))
    script = ["H", "B%d" % n, "b%d" % n] + finish(rng.choice((1, 1 << 30)), rng.choice((1, 7, 100, 1 << 30)))
    d(rng.randint(0, 9), rng.choice((31, 25, 15)), mem, 0, data("t", n), n, script, hdr=hdr,
      outcap=n + max(ex, 0) + max(nm, 0) + max(cm, 0) + 200)

# 8. Invalid arguments, calls after end and after errors, tiny avail_out.
for args in ((10, 8, 15, 8, 0), (-2, 8, 15, 8, 0), (6, 7, 15, 8, 0), (6, 8, 7, 8, 0), (6, 8, 16, 8, 0),
             (6, 8, -16, 8, 0), (6, 8, 32, 8, 0), (6, 8, 15, 0, 0), (6, 8, 15, 10, 0), (6, 8, 15, 8, 5),
             (6, 8, 15, 8, -1), (6, 8, 8, 8, 0), (6, 8, -8, 8, 0), (6, 8, 24, 8, 0), (6, 8, -8, 1, 0)):
    lv, me, wb, ml, st = args
    d(lv, wb, ml, st, data("t", 50), 50, finish(), method=me)
for level in range(10):
    d(level, 15, 8, 0, data("t", 300), 300, ["f4", "o0", "f4", "L4/1000/1", "f4", "f0", "i5", "f4", "f-1", "f7",
                                            "f3", "p", "E"])
    d(level, 31, 8, 0, data("r", 300), 300, ["o1", "f0", "o1", "f1", "o1", "f4", "L4/300/1", "f4"])
    d(level, 15, 8, 0, "null", 0, ["i0", "o10", "f4", "f4"])
    d(level, 15, 8, 0, data("z", 20000), 20000, ["L2/1000/7", "L3/1000/7", "L4/1000/7"])

# 9. compress, compress2, compress_z, compress2_z.
for case in range(120 if QUICK else 300):
    fn = rng.choice(("c", "c2", "cz", "c2z"))
    n = rng.choice((0, 1, 10, 1000, 30000))
    dat = data(rng.choice(KINDS), n) if n else rng.choice(("-", "null"))
    bound = n + (n >> 12) + (n >> 14) + (n >> 25) + 13 + 100
    oc = rng.choice((bound, bound, 0, 5, n // 2))
    cell = rng.choice((oc, oc, 0, max(oc - 1, 0)))
    outs = rng.choice((str(oc), str(oc), "N"))
    if outs == "N":
        cell = rng.choice((0, 0, 5))
    cells = rng.choice((str(min(cell, oc) if outs != "N" else cell), "N"))
    if outs != "N" and cells != "N" and int(cells) > oc:
        cells = str(oc)
    out.append("cmp %s %d %s %s %s" % (fn, rng.randint(-1, 10), dat, outs, cells))

# 10. deflateTune with max_lazy outside 0..258 (it is also the insert count of the medium strategy: INT_MIN made
# deflate_medium divide by zero before patch 0013), on runs and short periods that give overlapping matches.
for level in range(1, 10):
    for lazy in (-2147483648, -2147483647, -1, 259, 300, 2147483647):
        for kind, n in (("z", 5000), ("p", 3000)):
            d(level, 15, 8, 0, data(kind, n, 7 if kind == "z" else 59), n,
              ["T8/%d/128/64" % lazy] + finish(), method=8)

# 11. A Z_FULL_FLUSH that empties the lookahead at level 2, more input, deflateParams to level 7: levels 2-6 leave
# prev slots of the earlier input, and before patch 0019 deflate_slow took a match at or after strstart here
# (found with an instrumented copy of match_tpl.h). The case runs deflate_slow's test of match_start against strstart.
d(2, -15, 8, 0, data("b", 100000, 940932758), 100000,
  ["o%d" % (1 << 30), "i55128", "f3", "i16582", "f0", "Q7/0", "L4/%d/%d" % (1 << 30, 1 << 30)])

print("\n".join(out))
