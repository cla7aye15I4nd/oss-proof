#!/usr/bin/env python3
"""Input generator for differential testing jdmaster.c."""

DSTATE_READY = 202

# Sharp shrink-on-load vectors (scale_num=1, scale_denom in {1, 2, 4, 8}) and general scaling
dims = [(0, 0), (1, 1), (1001, 753), (1920, 1080), (4000, 3000), (65500, 65500)]
for cmd in ["core", "calc"]:
    for sden in [1, 2, 4, 8, 16]:
        for w, h in dims:
            print(f"{cmd} {DSTATE_READY} 0 {w} {h} 1 {sden} 3 3 2 0 0 0 2 2")

# Output colorspaces (GRAYSCALE=1, RGB=2, YCbCr=3, CMYK=4, YCCK=5, EXT_RGB=6..EXT_ARGB=15, RGB565=16, UNKNOWN=0)
for ocs in [0, 1, 2, 3, 4, 5, 6, 7, 10, 12, 15, 16]:
    for fancy in [0, 1]:
        for quant in [0, 1]:
            print(f"calc {DSTATE_READY} 0 1001 753 1 4 3 3 {ocs} {fancy} 0 {quant} 2 2")

# Lossless mode & CCIR601 & different sampling factors
for ll in [0, 1]:
    for nc, mh, mv in [(1, 1, 1), (3, 1, 1), (3, 2, 1), (3, 2, 2), (4, 2, 2)]:
        print(f"calc {DSTATE_READY} {ll} 800 600 1 2 {nc} 3 2 0 1 0 {mh} {mv}")

# Bad state ERREXIT1 check
for gs in [200, 201, 203, 205, 210]:
    print(f"calc {gs} 0 100 100 1 1 3 3 2 0 0 0 2 2")
