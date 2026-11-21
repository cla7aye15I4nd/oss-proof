# Test the allocation in gz_buffer_alloc() before offsetting it

## Problem

`gz_buffer_alloc()` (`gzlib.c`) allocates the input and output buffers in one block and then computes

```c
state->out = state->buffers + (in_size);
```

before it tests whether `zng_alloc_aligned()` returned `NULL`. When the allocation fails, that is a nonzero offset applied to a null pointer (ISO C17 §6.5.6p8; clang's UndefinedBehaviorSanitizer reports "applying non-zero offset ... to null pointer"). `gzbuffer(file, 1 << 30)` is allowed by `zlib.h`; the first write then asks for 3 GiB, which can fail.

## Fix

Test `state->in == NULL` right after the allocation and set `state->out` only after it succeeded. The second half of the old test (`out_size && state->out == NULL`) is dropped: it cannot be true once the allocation succeeded. The error path is unchanged (`gz_buffer_free()`, `Z_MEM_ERROR`).

Add the opt-in test `gzfile_api_errors.write_buffer_alloc_failure` in `test/test_gzfile_api_errors.cc`: with `ZLIB_NG_TEST_GZ_ALLOC_LIMIT` set, it opens a gzip writer, sets a 1 GiB buffer and writes 3 bytes, and expects `gzwrite()` to return 0 with `Z_MEM_ERROR` and `gzclose()` to return `Z_MEM_ERROR`. It needs an allocator that refuses the 3 GiB request (for example AddressSanitizer with `allocator_may_return_null=1:max_allocation_size_mb=1024`); it is skipped without the variable, and also when the allocation succeeds.

## Related Upstream References

- None in zlib-ng or madler/zlib (`gz_buffer_alloc()` is zlib-ng code). https://github.com/zlib-ng/zlib-ng/pull/2319 (merged) changed the size computation of the same function, a different defect.
- Note: https://github.com/zlib-ng/zlib-ng/pull/2517 also appends to `test/test_gzfile_api_errors.cc`.

## Review Feedback Addressed

- None yet (not submitted).

## Testing

- Clang, `ZLIB_COMPAT=ON`, `WITH_OPTIM=OFF`, `-O0`, AddressSanitizer + UndefinedBehaviorSanitizer, `ZLIB_NG_TEST_GZ_ALLOC_LIMIT=1`, `ASAN_OPTIONS=allocator_may_return_null=1:max_allocation_size_mb=1024`:
  - Before the fix: aborts with "runtime error: applying non-zero offset 2147483648 to null pointer" in `gz_buffer_alloc()`.
  - After the fix: passes.
- GCC's UndefinedBehaviorSanitizer does not report a nonzero offset applied to a null pointer, so a GCC build does not show the defect.
- Clang, `ZLIB_COMPAT=OFF`, `WITH_OPTIM=ON`, same options: passes.
