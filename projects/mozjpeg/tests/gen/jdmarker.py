#!/usr/bin/env python3
"""Input generator for differential testing jdmarker.c."""

markers = [0xFE] + list(range(0xE0, 0xF0))
limits = [0, 1, 11, 12, 13, 14, 15, 1024, 65535, 999999900, 1000000000, 4294967295]

for m in markers:
    for lim in limits:
        print(f"jpeg_save_markers {m} {lim}")

for bad_m in [0, -1, 0xD8, 0xDD, 0xDF, 0xF0, 0xFD, 0xFF, 256]:
    print(f"jpeg_save_markers {bad_m} 65535")

# jpeg_resync_to_restart vectors covering action 1/2/3, wraparound desired, stuffing 0xff 0x00,
# repeated 0xff padding, EOF (fill_mem_input_buffer), and input suspension (suspend_input).
resync_cases = [
    # action = 3 immediately (unread > M_RST7 or in [M_SOF0, M_RST0))
    (0xD9, 0, 0, "1122"),
    (0xDA, 3, 0, "ffd0"),
    (0xC0, 2, 0, "ffd2"),
    (0xCF, 7, 0, "ffd0"),
    # action = 1 immediately (unread in RST0..RST7 matching desired)
    (0xD0, 0, 0, "aabb"),
    (0xD5, 5, 0, "aabb"),
    # action = 3 via desired+1 / desired+2 mod 8
    (0xD1, 0, 0, "aabb"),
    (0xD2, 0, 0, "aabb"),
    (0xD0, 7, 0, "aabb"),
    (0xD1, 7, 0, "aabb"),
    # extreme valid desired bounds (near INT32_MIN + 2 and INT32_MAX - 3)
    (0xD0, 2147483645, 0, "ffd5"),
    (0xD0, -2147483646, 0, "ffd5"),
    # action = 2 via desired-1 / desired-2 mod 8, or unread < M_SOF0
    (0xD7, 0, 0, "0102ffffd199"),
    (0xD6, 0, 0, "ff00ffd0aa"),
    (0x00, 3, 0, "deadbeefffe0aa"),
    (0x00, 3, 0, "ff00ff00ffd41122"),
    # restart loop continuing through multiple action=2 steps
    (0x00, 4, 0, "ffd21122ffd33344ffd455"),
    # empty / truncated stream hitting fill_mem_input_buffer -> JWRN_JPEG_EOF & M_EOI
    (0x00, 0, 0, "-"),
    (0x00, 1, 0, "1234ff0056"),
    (0x00, 2, 0, "ffffff"),
    # suspension cases returning FALSE and preserving discardedBytes
    (0x00, 0, 1, "-"),
    (0x00, 0, 1, "1122"),
    (0x00, 0, 1, "11ff"),
    (0xD7, 0, 1, "ff00aa"),
]

for unread, desired, mode, hex_data in resync_cases:
    print(f"resync {unread} {desired} {mode} {hex_data}")
