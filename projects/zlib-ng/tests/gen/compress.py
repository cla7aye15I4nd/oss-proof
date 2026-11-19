#!/usr/bin/env python3
"""Inputs for the compressBound (compress.c) differential test, written to stdout. Deterministic.
Lines: compressBound <sourceLen>. Every length up to 100 (the sourceLen == 0 and sourceLen < 9 terms and
the (x + 7) >> 3 rounding), powers of two and their neighbours, the largest value without wraparound
(0xe38e38e38e38e377) and its neighbours, and values whose bound wraps modulo 2^64.
"""
import random

rng = random.Random(20261118)
M64 = (1 << 64) - 1
vals = set(range(0, 101))
for e in range(1, 64):
    for d in (-2, -1, 0, 1, 2):
        vals.add((1 << e) + d)
for d in range(-3, 4):
    vals.add(0xe38e38e38e38e377 + d)
vals |= {M64, M64 - 1, M64 - 7, M64 - 8, M64 - 9, (1 << 63) + 5}
for _ in range(200):
    vals.add(rng.randrange(1 << rng.randrange(1, 65)))
print("\n".join("compressBound %d" % v for v in sorted(vals)))
