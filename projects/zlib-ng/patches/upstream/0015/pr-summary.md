# PR 0015: Check gzip buffer allocation before computing `state->out`

- **Proposed PR Title**: `Check gzip buffer allocation before computing state->out`
- **Target Base**: `zlib-ng/zlib-ng` `develop` (`5f1f4899`)
- **Upstream PR**: Ready to submit
- **Commits**: 1 (`upstream.patch`)
- **Files**: `gzlib.c`, `test/test_gzfile_api_errors.cc`

## Problem & Root Cause

In `gz_buffer_alloc()` (`gzlib.c`), after allocating `state->buffers` and assigning `state->in = state->buffers`, the code computes:

```c
state->out = state->buffers + in_size;
```

*before* checking whether `state->buffers == NULL`. When allocation fails and `in_size > 0`, evaluating `NULL + in_size` is undefined behavior in ISO C17 §6.5.6p8 (reported directly by Clang UBSan as applying nonzero offset to null pointer). Furthermore, `(out_size && state->out == NULL)` in the old error check only ever evaluated to false when allocation succeeded.

## Fix Summary

Check `if (state->in == NULL)` immediately after allocation (freeing nothing and returning `Z_MEM_ERROR`), and only then assign `state->out = state->buffers + in_size;` when `out_size != 0`.

Add an opt-in regression test `gzfile_api_errors.gzip_buffer_allocation_failure` in `test/test_gzfile_api_errors.cc` gated by `ZLIB_NG_TEST_GZ_ALLOC_LIMIT` (sets `gzbuffer(file, 1 << 29)` so ASan `allocator_may_return_null=1:max_allocation_size_mb=1024` exercises OOM cleanly).

## Overlaps & Dependencies

- **Internal (`gzlib.c`)**: disjoint from `0004` (`gzseek64`).
- **Internal (`test/test_gzfile_api_errors.cc`)**: shares file EOF with `0014` (`#2527`).
- **External (`#2517`)**: https://github.com/zlib-ng/zlib-ng/pull/2517 also appends to `test/test_gzfile_api_errors.cc`.

## Verification

- Under normal CI (without `ZLIB_NG_TEST_GZ_ALLOC_LIMIT`), the new test cleanly skips (`GTEST_SKIP()`).
- With `ZLIB_NG_TEST_GZ_ALLOC_LIMIT=1` and `ASAN_OPTIONS=allocator_may_return_null=1:max_allocation_size_mb=1024:detect_leaks=0:detect_invalid_pointer_pairs=2`:
  - Before fix (`5f1f4899`): fails on `build-compat-san` with UBSan (`applying zero/non-zero offset ... to null pointer`).
  - After fix: passes on both `build-compat-san` and `build-native-san` (`[  PASSED  ] 1 test.`), returning `Z_MEM_ERROR` cleanly on `gzwrite()` and `gzclose()`.
