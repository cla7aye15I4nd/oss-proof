#!/usr/bin/env python3
"""Input generator for differential testing jdatasrc.c."""

for preset in [0, 1, 2]:
    for nonnull, sz in [(0, 0), (0, 10), (1, 0), (1, 1), (1, 16), (1, 64), (1, 1000000)]:
        print(f"mem_src {nonnull} {sz} {preset}")

skip_cases = [
    (16, 0, 0),
    (16, -5, 0),
    (16, 5, -3),
    (16, 5, 11),
    (16, 16, 0),
    (16, 16, 1),
    (16, 17, 0),
    (16, 17, 1),
    (16, 18, 0),
    (16, 18, 1),
    (16, 19, 0),
    (16, 25, 3),
    (1, 0, 1),
    (1, 1, 0),
    (1, 1, 2),
    (64, 63, 1),
    (64, 64, 5),
]
for sz, n1, n2 in skip_cases:
    print(f"skip {sz} {n1} {n2}")
