# mozjpeg-f

Kernel-checked Lean 4 verification of `mozjpeg` 5.0.0 (`08265790`, static 8-bit LP64 Linux build:
`-DBUILD_SHARED_LIBS=FALSE -DWITH_JPEG8=1 -DWITH_TURBOJPEG=FALSE -DPNG_SUPPORTED=FALSE -DWITH_SIMD=FALSE`),
scoped to Tier 0 untrusted-input decompression paths.

Proved so far: strict ISO C17 pointer and `memset` undefined-behaviour rejection in the runtime;
`jutils.c` (`jdiv_round_up`, `jround_up`, `jzero_far`); `jerror.c` (`jpeg_std_error`, exact message
table bounds, and non-vacuity); `jcomapi.c` (`jpeg_abort`, `jpeg_destroy`); `jdapimin.c` teardown
and query functions (`jpeg_destroy_decompress`, `jpeg_abort_decompress`, `jpeg_input_complete`,
`jpeg_has_multiple_scans`); `jdmarker.c` (`jpeg_save_markers`); and `jdmaster.c`
(`jpeg_core_output_dimensions`, `jpeg_calc_output_dimensions`, including Sharp's shrink-on-load
`scale_num = 1`, `scale_denom ∈ {2, 4, 8}` functional and concrete witness theorems).

Header parsing (`jpeg_read_header`, `jpeg_consume_input`), pool/memory management
(`jpeg_CreateDecompress`), source setup (`jpeg_mem_src`), restart resynchronization
(`jpeg_resync_to_restart`), and scanline/raw pixel decode (`jpeg_start_decompress`,
`jpeg_read_scanlines`, `jpeg_read_raw_data`, `jpeg_finish_decompress`) are not done. Differential
tests under AddressSanitizer and UndefinedBehaviorSanitizer (`tests/`) compare the real C static
library against the Lean translations as evidence of translation fidelity, not proof.

Status: https://www.dataisland.org/oss-proof/mozjpeg/en/progress.html

See [`AGENTS.md`](AGENTS.md) for working rules.
