#!/usr/bin/env python3
"""Input generator for differential testing jutils.c."""
import random

rng = random.Random(0x5011)

for a in [0, 1, 2, 7, 8, 9, 15, 16, 17, 1001, 65500, 1048576, 2**31 - 1, 2**40 + 123]:
    for b in [1, 2, 3, 4, 7, 8, 16, 64, 127]:
        if a + b < 2**63:
            print(f"jdiv_round_up {a} {b}")
            if a + b - 1 < 2**63:
                print(f"jround_up {a} {b}")

for _ in range(80):
    b = rng.choice([1, 2, 3, 4, 5, 7, 8, 13, 16, 32, 64, 128, 1024])
    a = rng.randint(0, 10_000_000)
    print(f"jdiv_round_up {a} {b}")
    print(f"jround_up {a} {b}")

for n in [0, 1, 2, 7, 8, 15, 16, 63, 64, 255, 512]:
    print(f"jzero_far {n}")

for i in range(80):
    print(f"natural_order {i}")
