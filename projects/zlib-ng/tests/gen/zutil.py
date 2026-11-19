#!/usr/bin/env python3
"""Inputs for the zutil.c differential test, written to stdout. Deterministic.
Lines: zlibVersion | zlibCompileFlags | zError <int> | zcalloc_free <items> <size>
       | zng_alloc_aligned <size> <align> | zng_free_aligned_null
zError is tried on every code in -12..12 (the documented -6..2 and both sides of it), and at INT_MIN,
INT_MAX and a few large values.
zcalloc_free and zng_alloc_aligned use small sizes: the Lean heap copies a block on every store, so memory
and time grow quadratically with the size. zng_alloc_aligned is tried with align = 0 (refused) and with
power-of-two alignments from 8 up (its only caller, gz_buffer_alloc, passes 64); the result prints whether
the pointer is aligned, writes every byte, reads them back and frees the block.
Not tested: huge sizes or alignments (the block holds size + align + 8 bytes; the Lean side would build the whole block; the C result depends on the memory,
which the allocation oracle models); 1 <= align <= 7 (the C writes before its block); and alignments that
are not powers of two (zng_free_aligned then loads the saved pointer through a misaligned void **, which
UBSan reports; the runtime model does not check the alignment of that load).
"""
import random

rng = random.Random(20261118)
out = ["zlibVersion", "zlibCompileFlags"]
for e in range(-12, 13):
    out.append("zError %d" % e)
for e in (-2**31, -2**31 + 1, -2**31 + 2, -1000, -100, 100, 1000, 2**31 - 2, 2**31 - 1):
    out.append("zError %d" % e)
for items, size in ((0, 0), (1, 0), (0, 5), (1, 1), (1, 7), (3, 5), (16, 16), (256, 2), (7, 60), (60, 7),
                    (300, 2), (100, 4), (1, 500), (0, 4294967295), (4294967295, 0)):
    out.append("zcalloc_free %d %d" % (items, size))
for _ in range(40):
    out.append("zcalloc_free %d %d" % (rng.randrange(1, 25), rng.randrange(1, 25)))
for size in (0, 1, 7, 8, 9, 63, 64, 65, 100, 1000, 4096):
    for align in (0, 8, 16, 32, 64, 128, 4096):
        out.append("zng_alloc_aligned %d %d" % (size, align))
for size in (0xffffffc0, 0xffffffff, 1 << 31):
    out.append("zng_alloc_aligned %d 0" % size)
for _ in range(30):
    out.append("zng_alloc_aligned %d %d" % (rng.randrange(0, 600), rng.choice((8, 16, 32, 64, 256))))
out.append("zng_free_aligned_null")
print("\n".join(out))
