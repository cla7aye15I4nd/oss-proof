#!/usr/bin/env python3
"""Input generator for differential testing jdmarker.c."""

markers = [0xFE] + list(range(0xE0, 0xF0))
limits = [0, 1, 11, 12, 13, 14, 15, 1024, 65535, 999999900, 1000000000, 4294967295]

for m in markers:
    for lim in limits:
        print(f"jpeg_save_markers {m} {lim}")

for bad_m in [0, -1, 0xD8, 0xDD, 0xDF, 0xF0, 0xFD, 0xFF, 256]:
    print(f"jpeg_save_markers {bad_m} 65535")
