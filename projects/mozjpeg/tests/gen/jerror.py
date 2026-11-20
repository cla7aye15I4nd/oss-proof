#!/usr/bin/env python3
"""Input generator for differential testing jerror.c."""

for idx in range(132):
    trace_level = (idx % 5) - 2
    num_warnings = (idx * 3) - 10
    print(f"jpeg_std_error {trace_level} {num_warnings} {idx}")

for idx in [-1, 132, 200]:
    print(f"jpeg_std_error 5 10 {idx}")
