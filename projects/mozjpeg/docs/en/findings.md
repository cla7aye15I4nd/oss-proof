# Findings: issues found in mozjpeg

No upstream defects or ISO C17 undefined behaviours have been established on the Tier 0
decompression functions verified so far (`jutils.c`, `jerror.c`, `jcomapi.c`, teardown/query helpers
in `jdapimin.c`, `jpeg_save_markers`, and `jpeg_calc_output_dimensions`).

If future verification of header parsing, Huffman decoding, IDCT, or upsampling confirms an
upstream bug or strict ISO C17 undefined behaviour reachable through documented API calls, it will be
documented here together with its concrete C reproduction and patch.
