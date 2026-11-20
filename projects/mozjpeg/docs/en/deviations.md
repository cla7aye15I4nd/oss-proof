# Deviations: what a call must satisfy

This page lists every premise of a goal that is narrower than `jpeglib.h`, or that a caller must
satisfy for the theorem to apply. A call outside these premises is not covered: it is neither proved
safe nor claimed to be unsafe.

## Every call

- The library is `mozjpeg` 5.0.0 (`08265790`), built for static x86_64 Linux LP64 with
  `-DBUILD_SHARED_LIBS=FALSE -DWITH_JPEG8=1 -DWITH_TURBOJPEG=FALSE -DPNG_SUPPORTED=FALSE -DWITH_SIMD=FALSE`.
  SIMD kernels (`libjpeg-turbo` / NASM paths), 12-bit/16-bit lossless paths where unproved, and the
  `turbojpeg` API are not covered.
- Heap objects passed through public structs (`jpeg_error_mgr`, `jpeg_decompress_struct`,
  `jpeg_memory_mgr`, `jpeg_decomp_master`, `jpeg_input_controller`, `jpeg_marker_reader`,
  `comp_info` array) must be live, properly typed, base-pointer allocations as maintained by
  `jpeg_CreateDecompress` and header setup (`ValidDecompCore`, `ValidDecompDimsInput`).
- When an error handler (`ERREXIT` / `ERREXIT1`) triggers in C, `error_exit` transfers control by
  `longjmp`; the model returns `JpegRes.errExit code` with `err->msg_code` and `err->msg_parm.i[0]`
  updated.

## Narrower than `jpeglib.h`

| Function | Premise | Lean | Reason |
| --- | --- | --- | --- |
| `jdiv_round_up`, `jround_up` (internal) | `0 ≤ a`, `0 < b`, `a + b < 2^63` (and `a + b - 1 < 2^63`). | `Goal.jdiv_round_up_safety`, `Goal.jround_up_safety`, `Goal.jdiv_round_up_functional` | Signed `long` addition `(a + b)` overflows in C17 if `a + b ≥ 2^63`; division by zero or negative rounding is excluded. |
| `jpeg_core_output_dimensions`, `jpeg_calc_output_dimensions` | `ValidDecompDimsInput`: `0 ≤ num_components ≤ 10`, `image_width ≤ 65500`, `image_height ≤ 65500`, sampling factors in `1..4`, `comp_info` holds at least `num_components` entries, `global_state == DSTATE_READY` (for `jpeg_calc_output_dimensions`). | `Goal.jpeg_core_output_dimensions_safety`, `Goal.jpeg_calc_output_dimensions_safety` | Enforces JPEG standard header invariants (`MAX_COMPONENTS = 10`, `JPEG_MAX_DIMENSION = 65500`) checked before calling dimension setup. |
| `jpeg_core_output_dimensions` (shrink functional) | `scale_num = 1`, `scale_denom ∈ {1, 2, 4, 8}`, `master->lossless == 0`. | `Goal.jpeg_core_output_dimensions_shrink_functional` | Captures Sharp's shrink-on-load scaling path specifically. |
| `jpeg_save_markers` | `0 ≤ mem->max_alloc_chunk ≤ 1000000000` and valid marker reader array of length `16`. | `Goal.jpeg_save_markers_safety` | Matches `MAX_ALLOC_CHUNK` and `SOF` APPn table length in `jmemnobs.c` / `jdmarker.c`. |
| `jpeg_consume_input`, `jpeg_read_header`, `jpeg_finish_decompress` | `ValidDecompIoBase` (`bytes_in_buffer < 2^20`, `num_warnings + 2^25 < 2^63`, `input_scan_number + 2^21 < 2^31`, live standard `mem`/`src`/`marker`/`inputctl` callbacks without custom user overrides; for `inheaders == 0` multi-scan resumption, `MultiScanReady`: `sawSOF ≠ 0`, `0 ≤ num_components ≤ 10`, `1 ≤ h/v_samp_factor ≤ 4`, `0 ≤ DCT_h_scaled_size ≤ 8`; for `jpeg_finish_decompress`, post-header `inheaders == 0` or pre-header `noop`/`dummy_consume_data` pass hooks). | `Goal.jpeg_consume_input_safety`, `Goal.jpeg_read_header_safety`, `Goal.jpeg_finish_decompress_safety` | Bounds warning/scan counters against signed integer overflow, fixes `fill_mem_input_buffer` / `suspend_input` source callbacks, and records `initial_setup` postconditions across scan boundaries. |
