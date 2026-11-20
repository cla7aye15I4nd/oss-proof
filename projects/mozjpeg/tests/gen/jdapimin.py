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

def mk_seg(marker, payload):
    ln = len(payload) + 2
    return bytes([0xFF, marker, (ln >> 8) & 0xFF, ln & 0xFF]) + payload

SOI = b"\xFF\xD8"
EOI = b"\xFF\xD9"
DQT0 = mk_seg(0xDB, bytes([0] + [16] * 64))
DQT1 = mk_seg(0xDB, bytes([1] + [8] * 64))
DHT0 = mk_seg(0xC4, bytes([0, 0, 1] + [0]*14 + [0]))
APP0_JFIF = mk_seg(0xE0, b"JFIF\x00\x01\x01\x00\x00\x01\x00\x01\x00\x00")
APP14_YCCK = mk_seg(0xEE, b"Adobe\x00\x64\x00\x00\x00\x00\x02")
COM_HI = mk_seg(0xFE, b"mozjpeg-wave3")
SOF0_GRAY = mk_seg(0xC0, bytes([8, 0, 8, 0, 16, 1, 1, 0x11, 0]))
SOF0_YCBCR = mk_seg(0xC0, bytes([8, 0, 16, 0, 24, 3, 1, 0x22, 0, 2, 0x11, 1, 3, 0x11, 1]))
SOF0_CMYK = mk_seg(0xC0, bytes([8, 0, 8, 0, 8, 4, 1, 0x11, 0, 2, 0x11, 0, 3, 0x11, 0, 4, 0x11, 0]))
SOF0_BIG_WH = mk_seg(0xC0, bytes([8, 0xFF, 0xF0, 0xFF, 0xF0, 1, 1, 0x11, 0])) # 65520 > JPEG_MAX_DIMENSION=65500
SOF0_ZERO_H = mk_seg(0xC0, bytes([8, 0, 0, 0, 8, 1, 1, 0x11, 0]))
SOF0_ZERO_W = mk_seg(0xC0, bytes([8, 0, 8, 0, 0, 1, 1, 0x11, 0]))
SOF0_SAMP0 = mk_seg(0xC0, bytes([8, 0, 8, 0, 8, 1, 1, 0x01, 0]))
SOF0_MCU_BIG = mk_seg(0xC0, bytes([8, 0, 8, 0, 8, 3, 1, 0x44, 0, 2, 0x11, 0, 3, 0x11, 0])) # 16+1+1 = 18 > D_MAX_BLOCKS_IN_MCU
SOF2_PROG = mk_seg(0xC2, bytes([8, 0, 8, 0, 8, 1, 1, 0x11, 0]))
SOS_GRAY = mk_seg(0xDA, bytes([1, 1, 0x00, 0, 63, 0]))
SOS_YCBCR = mk_seg(0xDA, bytes([3, 1, 0x00, 2, 0x11, 3, 0x11, 0, 63, 0]))
SOS_BAD_COMP = mk_seg(0xDA, bytes([1, 9, 0x00, 0, 63, 0]))

VALID_GRAY = SOI + DQT0 + DHT0 + SOF0_GRAY + SOS_GRAY + EOI
VALID_YCBCR = SOI + APP0_JFIF + COM_HI + DQT0 + DQT1 + DHT0 + SOF0_YCBCR + SOS_YCBCR + EOI
VALID_CMYK = SOI + APP14_YCCK + DQT0 + SOF0_CMYK + mk_seg(0xDA, bytes([4, 1, 0, 2, 0, 3, 0, 4, 0, 0, 63, 0]))
TABLES_ONLY = SOI + DQT0 + EOI
VALID_PROG = SOI + DQT0 + DHT0 + SOF2_PROG + mk_seg(0xDA, bytes([1, 1, 0x00, 0, 0, 0])) + EOI

rh_cases = [
    (1, 0, 0, VALID_GRAY),
    (0, 0, 0, VALID_GRAY),
    (1, 0, 3, VALID_YCBCR),
    (1, 0, 0, VALID_CMYK),
    (1, 0, 0, VALID_PROG),
    (0, 0, 0, TABLES_ONLY),
    (1, 0, 0, TABLES_ONLY),  # JERR_NO_IMAGE
    (1, 0, 0, b""),          # JERR_INPUT_EMPTY
    (0, 0, 0, b""),          # JERR_INPUT_EMPTY
    (1, 0, 0, b"\x00\x00"),  # JERR_NO_SOI
    (1, 0, 0, SOI + DQT0 + SOF0_GRAY),  # JERR_SOF_NO_SOS (EOF before SOS)
    (1, 0, 0, SOI + SOF0_BIG_WH + SOS_GRAY),  # JERR_IMAGE_TOO_BIG
    (1, 0, 0, SOI + SOF0_ZERO_H + SOS_GRAY),  # JERR_EMPTY_IMAGE
    (1, 0, 0, SOI + SOF0_ZERO_W + SOS_GRAY),  # JERR_EMPTY_IMAGE
    (1, 0, 0, SOI + SOF0_SAMP0 + SOS_GRAY),   # JERR_BAD_SAMPLING
    (1, 0, 0, SOI + SOF0_MCU_BIG + SOS_YCBCR),# JERR_BAD_MCU_SIZE
    (1, 0, 0, SOI + DQT0 + SOF0_YCBCR + SOS_YCBCR), # JERR_NO_QUANT_TABLE on tbl 1
    (1, 0, 0, SOI + DQT0 + SOF0_GRAY + SOS_BAD_COMP), # JERR_BAD_COMPONENT_ID in per_scan_setup/get_sos
    # suspension cases
    (1, 1, 0, SOI + APP0_JFIF[:6]),
    (0, 1, 0, b"\xFF"),
]

for req, mode, mask, raw in rh_cases:
    h = raw.hex() if raw else "-"
    print(f"read_header {req} {mode} {mask} {h}")

# consume_seq: init_state, fill_mode, steps, bytes
cs_cases = [
    (200, 0, 3, VALID_GRAY),
    (200, 0, 3, TABLES_ONLY),
    (200, 0, 3, VALID_PROG),
    (205, 0, 2, b"\x11\x22" + EOI),  # DSTATE_SCANNING hitting EOI via consume_markers
    (206, 0, 2, b"\xFF\xFE\x00\x02" + EOI),
    (207, 0, 2, SOS_GRAY + EOI),
    (205, 1, 2, b"\x11\x22"),        # suspend in consume_markers
    (200, 1, 2, SOI + SOF0_GRAY),    # suspend in DSTATE_INHEADER
    (999, 0, 1, VALID_GRAY),         # JERR_BAD_STATE
]

for init_st, mode, steps, raw in cs_cases:
    h = raw.hex() if raw else "-"
    print(f"consume_seq {init_st} {mode} {steps} {h}")

# finish: init_state, eoi_reached, fill_mode, trailing bytes
fin_cases = [
    (207, 0, 0, EOI),
    (207, 0, 0, b"\x12\x34\xFF\xFE\x00\x04hi" + EOI),
    (207, 0, 0, b"\x00\xFF\x00" + EOI),
    (210, 1, 0, b""),
    (207, 1, 0, b""),                 # already hit EOI
    (207, 0, 0, b"\x11\x22"),        # fill_mem_input_buffer -> EOI warning then terminates
    (207, 0, 1, b"\x11\x22"),        # suspend_input -> FALSE
    (202, 0, 0, EOI),                # JERR_BAD_STATE
    (200, 0, 0, EOI),                # JERR_BAD_STATE
]

for init_st, eoi, mode, raw in fin_cases:
    h = raw.hex() if raw else "-"
    print(f"finish {init_st} {eoi} {mode} {h}")
