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

# Helper builders for JPEG marker streams
def mk_seg(marker, payload):
    ln = len(payload) + 2
    return bytes([0xFF, marker, (ln >> 8) & 0xFF, ln & 0xFF]) + payload

SOI = b"\xFF\xD8"
EOI = b"\xFF\xD9"
DQT_BASIC = mk_seg(0xDB, bytes([0] + [16] * 64))
DQT_16BIT = mk_seg(0xDB, bytes([0x10]) + bytes(128))
DHT_BASIC = mk_seg(0xC4, bytes([0, 0, 1] + [0]*14 + [0]))
DRI_4 = mk_seg(0xDD, b"\x00\x04")
DAC_BASIC = mk_seg(0xCC, b"\x00\x05\x10\x04")
APP0_JFIF = mk_seg(0xE0, b"JFIF\x00\x01\x02\x01\x00\x48\x00\x48\x00\x00")
APP0_JFIF_THUMB = mk_seg(0xE0, b"JFIF\x00\x01\x01\x00\x00\x01\x00\x01\x02\x02" + b"\x11" * 12)
APP0_JFIF_BAD_MAJOR = mk_seg(0xE0, b"JFIF\x00\x02\x00\x00\x00\x01\x00\x01\x00\x00")
APP0_JFXX_JPEG = mk_seg(0xE0, b"JFXX\x00\x10abcdef")
APP14_ADOBE_YCCK = mk_seg(0xEE, b"Adobe\x00\x64\x00\x00\x00\x00\x02")
COM_HELLO = mk_seg(0xFE, b"hello world from mozjpeg")
APP1_EXIF = mk_seg(0xE1, b"Exif\x00\x00\x01\x02\x03")

SOF0_GRAY = mk_seg(0xC0, bytes([8, 0, 8, 0, 16, 1, 1, 0x11, 0]))
SOF0_YCBCR = mk_seg(0xC0, bytes([8, 0, 16, 0, 16, 3, 1, 0x22, 0, 2, 0x11, 1, 3, 0x11, 1]))
SOF0_CMYK = mk_seg(0xC0, bytes([8, 0, 8, 0, 8, 4, 1, 0x11, 0, 2, 0x11, 0, 3, 0x11, 0, 4, 0x11, 0]))
SOF0_RGB_IDS = mk_seg(0xC0, bytes([8, 0, 8, 0, 8, 3, ord('R'), 0x11, 0, ord('G'), 0x11, 0, ord('B'), 0x11, 0]))
SOF2_PROG = mk_seg(0xC2, bytes([8, 0, 16, 0, 16, 3, 1, 0x22, 0, 2, 0x11, 1, 3, 0x11, 1]))
SOF3_LOSSLESS = mk_seg(0xC3, bytes([8, 0, 8, 0, 8, 1, 1, 0x11, 0]))
SOF9_ARITH = mk_seg(0xC9, bytes([8, 0, 8, 0, 8, 1, 1, 0x11, 0]))
SOF10_PROG_ARITH = mk_seg(0xCA, bytes([8, 0, 8, 0, 8, 1, 1, 0x11, 0]))
SOF5_BAD = mk_seg(0xC5, bytes([8, 0, 8, 0, 8, 1, 1, 0x11, 0]))
SOS_1COMP = mk_seg(0xDA, bytes([1, 1, 0x00, 0, 63, 0]))
SOS_3COMP = mk_seg(0xDA, bytes([3, 1, 0x00, 2, 0x11, 3, 0x11, 0, 63, 0]))
SOS_3COMP_P2 = mk_seg(0xDA, bytes([3, 1, 0x00, 2, 0x11, 3, 0x11, 0, 0, 0]))

rm_cases = [
    # Valid baseline grayscale / YCbCr / CMYK / RGB-IDs
    (0, 0, SOI + DQT_BASIC + DHT_BASIC + SOF0_GRAY + SOS_1COMP),
    (0, 1, SOI + APP0_JFIF + DQT_BASIC + DHT_BASIC + DRI_4 + SOF0_YCBCR + SOS_3COMP),
    (0, 0, SOI + APP0_JFIF_THUMB + SOF0_GRAY + SOS_1COMP),
    (0, 0, SOI + APP0_JFIF_BAD_MAJOR + SOF0_GRAY + SOS_1COMP),
    (0, 0, SOI + APP0_JFXX_JPEG + SOF0_GRAY + SOS_1COMP),
    (0, 8, SOI + APP14_ADOBE_YCCK + SOF0_CMYK + SOS_1COMP),
    (0, 0, SOI + SOF0_RGB_IDS + SOS_1COMP),
    # Saved COM / APP1 truncation & multiple saved markers
    (0, 15, SOI + APP0_JFIF + COM_HELLO + APP1_EXIF + APP14_ADOBE_YCCK + SOF0_YCBCR + SOS_3COMP),
    (0, 2, SOI + COM_HELLO + SOF0_GRAY + SOS_1COMP),
    # Progressive / Lossless / Arithmetic / DAC / 16-bit DQT
    (0, 0, SOI + DQT_16BIT + DAC_BASIC + SOF2_PROG + SOS_3COMP_P2),
    (0, 0, SOI + SOF3_LOSSLESS + SOS_1COMP),
    (0, 0, SOI + SOF9_ARITH + SOS_1COMP),
    (0, 0, SOI + SOF10_PROG_ARITH + SOS_1COMP),
    # Tables only (SOI + DQT + EOI)
    (0, 0, SOI + DQT_BASIC + EOI),
    # Unknown APP / TEM / RST0 padding
    (0, 0, SOI + mk_seg(0xE5, b"\x01\x02") + b"\xFF\x01" + b"\xFF\xD0" + SOF0_GRAY + SOS_1COMP),
    # Error cases
    (0, 0, b""),
    (0, 0, b"\x00\x01"),
    (0, 0, b"\xFF\xE0\x00\x02"),  # JERR_NO_SOI
    (0, 0, SOI + b"\xFF\xD8"),    # JERR_SOI_DUPLICATE
    (0, 0, SOI + SOF5_BAD),       # JERR_SOF_UNSUPPORTED
    (0, 0, SOI + SOF0_GRAY + SOF0_GRAY),  # JERR_SOF_DUPLICATE
    (0, 0, SOI + SOS_1COMP),      # JERR_SOS_NO_SOF
    (0, 0, SOI + mk_seg(0xC0, bytes([8, 0, 8, 0, 8, 2, 1, 0x11, 0, 1, 0x11, 0]))),  # JERR_BAD_COMPONENT_ID
    (0, 0, SOI + mk_seg(0xC0, bytes([8, 0, 8, 0, 8, 1, 1, 0x11, 0, 99]))),  # JERR_BAD_LENGTH
    (0, 0, SOI + SOF0_GRAY + mk_seg(0xDB, bytes([0x04] + [1]*64))),  # JERR_DQT_INDEX
    (0, 0, SOI + SOF0_GRAY + mk_seg(0xC4, bytes([0x09] + [0]*16))),  # JERR_DHT_INDEX
    (0, 0, SOI + SOF0_GRAY + mk_seg(0xCC, b"\x04\x01")),  # JERR_DAC_INDEX
    (0, 0, SOI + SOF0_GRAY + mk_seg(0xDD, b"\x00\x01\x02")),  # JERR_BAD_LENGTH in DRI
    (0, 0, SOI + mk_seg(0xFE, b"\x00")),  # unknown marker length < 2 (JERR_BAD_LENGTH via bogus FF FE 00 01)
    (0, 0, SOI + b"\xFF\xFE\x00\x01"),
    (0, 0, SOI + b"\xFF\x77"),    # JERR_UNKNOWN_MARKER
    (0, 0, SOI + SOF0_GRAY),      # fill_mem_input_buffer -> JWRN_JPEG_EOF -> M_EOI
    # Suspension cases (mode=1)
    (1, 0, b"\xFF"),
    (1, 15, SOI + APP0_JFIF[:6]),
    (1, 2, SOI + COM_HELLO[:8]),
    (1, 0, SOI + SOF0_GRAY),
]

for mode, mask, raw in rm_cases:
    h = raw.hex() if raw else "-"
    print(f"read_markers {mode} {mask} {h}")
