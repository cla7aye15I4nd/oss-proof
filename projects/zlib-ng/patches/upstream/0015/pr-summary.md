# Check gzip buffer allocation before computing state->out

## Problem

In `gz_buffer_alloc()` (`gzlib.c`), after allocating `state->buffers` and setting `state->in = state->buffers`, the code computes:

```c
state->out = state->buffers + in_size;
```

before checking whether `state->buffers == NULL`. When allocation fails and `in_size > 0`, evaluating `NULL + in_size` is undefined behavior in ISO C17 §6.5.6p8 (reported by Clang UBSan as applying a nonzero offset to a null pointer).

## Fix

Check `if (state->in == NULL)` immediately after allocation and return `Z_MEM_ERROR` before computing `state->out = state->buffers + in_size`.

Add an opt-in regression test `gzfile_api_errors.gzip_buffer_allocation_failure` in `test/test_gzfile_api_errors.cc` gated by `ZLIB_NG_TEST_GZ_ALLOC_LIMIT` (requests `gzbuffer(file, 1 << 29)` so ASan `allocator_may_return_null=1:max_allocation_size_mb=1024` triggers allocation failure reliably).

## Related Upstream References

- Note: https://github.com/zlib-ng/zlib-ng/pull/2517 also appends to `test/test_gzfile_api_errors.cc`.

## Testing

- Under default test runs (without `ZLIB_NG_TEST_GZ_ALLOC_LIMIT`), the test cleanly skips via `GTEST_SKIP()`.
- With `ZLIB_NG_TEST_GZ_ALLOC_LIMIT=1` and `ASAN_OPTIONS=allocator_may_return_null=1:max_allocation_size_mb=1024`:
  - Before fix: Clang ASan + UBSan (`ZLIB_COMPAT=ON`) aborts with UBSan (`applying non-zero offset ... to null pointer`).
  - After fix: passes on both `ZLIB_COMPAT=ON` and `ZLIB_COMPAT=OFF`, returning `Z_MEM_ERROR` from `gzwrite()` and `gzclose()`.
