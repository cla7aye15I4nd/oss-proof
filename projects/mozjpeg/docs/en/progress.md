# Status of the results

Overall library status: **not done**.

| Area | Kind | Status |
| --- | --- | --- |
| Strict ISO C17 pointer, checked arithmetic, and `memset` UB rejection | Runtime model | done |
| `jdiv_round_up`, `jround_up`, `jzero_far`: safety and `jdiv_round_up` functional value | Internal helpers | done |
| `jpeg_std_error`: safety, message-table initialization, and non-vacuity witness | Public C API | done |
| `jpeg_abort`, `jpeg_destroy`, `jpeg_abort_decompress`, `jpeg_destroy_decompress`: safety | Public C API | done |
| `jpeg_input_complete`, `jpeg_has_multiple_scans`: safety | Public C API | done |
| `jpeg_save_markers`: safety (`COM` / `APPn` / invalid marker `error_exit`) | Public C API | done |
| `jpeg_core_output_dimensions`: safety and shrink-on-load (`1/2`, `1/4`, `1/8`) exact dimensions | Public C API | done |
| `jpeg_calc_output_dimensions`: safety and 1001×753 `1/4` shrink-on-load non-vacuity witness | Public C API | done |
| `jpeg_CreateDecompress`, `jpeg_mem_src` (pool allocator and memory source init) | Public C API | not done |
| `jpeg_read_header`, `jpeg_consume_input`, `jpeg_resync_to_restart` (marker & header parsing) | Public C API | not done |
| `jpeg_start_decompress`, `jpeg_read_scanlines`, `jpeg_read_raw_data`, `jpeg_finish_decompress` | Public C API | not done |
