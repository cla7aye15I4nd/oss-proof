# mozjpeg

Verification target: `mozjpeg` 5.0.0 (`08265790`) built as a portable static 8-bit x86_64 Linux
LP64 library (`libjpeg.a`), scoped to Tier 0 untrusted-input decompression entry points reached from
default `Sharp` / `libvips` callers.

## Build configuration

The verified library is built from the pinned upstream source with these CMake options:

```
-DBUILD_SHARED_LIBS=FALSE -DWITH_JPEG8=1 -DWITH_TURBOJPEG=FALSE -DPNG_SUPPORTED=FALSE -DWITH_SIMD=FALSE
```

- `WITH_JPEG8=1` matches the `libjpeg` v8 API (`JPEG_LIB_VERSION = 80`) used by modern Linux builds.
- `WITH_TURBOJPEG=FALSE` and `PNG_SUPPORTED=FALSE` omit the higher-level `turbojpeg` wrapper and
  PNG CLI dependencies.
- `WITH_SIMD=FALSE` disables platform SIMD kernels so all decompression paths run portable scalar C.

## Scope

- **Tier 0 decompression safety:** no undefined behaviour under strict ISO C17, no memory errors, and
  clean return (or `error_exit` longjmp exit without leaked heap state) across untrusted JPEG
  decompression entry points (`jpeg_std_error`, `jpeg_CreateDecompress`, `jpeg_mem_src`,
  `jpeg_save_markers`, `jpeg_read_header`, `jpeg_consume_input`, `jpeg_has_multiple_scans`,
  `jpeg_input_complete`, `jpeg_core_output_dimensions`, `jpeg_calc_output_dimensions`,
  `jpeg_resync_to_restart`, `jpeg_start_decompress`, `jpeg_read_scanlines`, `jpeg_read_raw_data`,
  `jpeg_finish_decompress`, `jpeg_abort_decompress`, `jpeg_destroy_decompress`, `jpeg_abort`,
  `jpeg_destroy`).
- **Functional theorems** where stated: `jdiv_round_up` exact ceiling division, `jpeg_std_error`
  table/method setup, and `jpeg_core_output_dimensions` under shrink-on-load scaling
  (`scale_num = 1`, `scale_denom ∈ {1, 2, 4, 8}`).

## What is proved so far

- The strict ISO C17 runtime model rejects `NULL + 0`, dangling `+ 0`, `NULL - NULL`,
  cross-object pointer subtraction, and zero-length `memset` on `NULL`.
- `jdiv_round_up`, `jround_up`, and `jzero_far` (`jutils.c`) are safe; `jdiv_round_up` computes
  exact `⌈a / b⌉` for non-overflowing nonnegative inputs.
- `jpeg_std_error` (`jerror.c`) is safe and initializes `last_jpeg_message = 131`,
  `jpeg_std_message_table`, and standard error methods, paired with a concrete non-vacuity witness.
- `jpeg_abort`, `jpeg_destroy` (`jcomapi.c`), `jpeg_abort_decompress`, `jpeg_destroy_decompress`,
  `jpeg_input_complete`, and `jpeg_has_multiple_scans` (`jdapimin.c`) are safe under valid object
  invariants.
- `jpeg_save_markers` (`jdmarker.c`) is safe across all `COM` / `APP0`..`APP15` / invalid marker
  codes and `max_alloc_chunk` bounds.
- `jpeg_core_output_dimensions` and `jpeg_calc_output_dimensions` (`jdmaster.c`) are safe, and
  `jpeg_core_output_dimensions` returns exact `ceil(width / denom)` and `ceil(height / denom)` for
  `scale_num = 1`, `scale_denom ∈ {1, 2, 4, 8}`, backed by a concrete 1001×753 shrink-on-load
  witness for `jpeg_calc_output_dimensions`.

Remaining Tier 0 decompression functions (`jpeg_CreateDecompress`, `jpeg_mem_src`,
`jpeg_read_header`, `jpeg_consume_input`, `jpeg_resync_to_restart`, `jpeg_start_decompress`,
`jpeg_read_scanlines`, `jpeg_read_raw_data`, `jpeg_finish_decompress`) are not done. Differential
tests under AddressSanitizer and UndefinedBehaviorSanitizer compare every translated module against
the real C static library; these tests are evidence of translation fidelity, not proof. See
[status](progress.html), [deviations](deviations.html), and [findings](findings.html).
