#!/usr/bin/env python3
"""Input generator for differential testing jdapimin.c."""

for ver in [0, 62, 70, 80, 90]:
    for sz in [0, 1, 655, 656, 657, 700]:
        print(f"create {ver} {sz}")

for st in [0, 200, 201, 202, 205, 207, 210, 999]:
    print(f"abort_destroy {st}")

for st in [0, 199, 200, 202, 205, 210, 211]:
    for val in [0, 1]:
        print(f"input_complete {st} {val}")
        print(f"has_multiple_scans {st} {val}")
