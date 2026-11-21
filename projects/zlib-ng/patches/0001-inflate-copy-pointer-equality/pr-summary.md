# Avoid cross-object pointer comparison in inflateCopy()

## Problem

When copying the Huffman table cursors (`lencode` and `distcode`), `inflateCopy()` checks whether `state->lencode` points into `state->codes` with a relational range test:

```c
if (state->lencode >= state->codes && state->lencode <= state->codes + ENOUGH - 1)
```

If the stream is paused inside a fixed Huffman block, `state->lencode` points into the static `lenfix` table rather than the heap-allocated `state->codes` array. Relational comparison (`>=`, `<=`) of pointers into distinct objects is undefined behavior (ISO C17 §6.5.8p5; reported by AddressSanitizer with `detect_invalid_pointer_pairs=2`).

## Fix

`lencode` is either the start of `state->codes` (a dynamic block: `inflate` builds the length table first, at `codes`) or a static fixed table, so the range test is replaced by pointer equality, which is defined for any two valid pointers:

```c
if (state->lencode == state->codes) {
    copy->lencode = copy->codes;
    copy->distcode = copy->codes + (state->distcode - state->codes);
}
```

`distcode` is only rebased inside this branch, where it points into `state->codes` as well, so its subtraction stays within one object; otherwise both cursors keep pointing at the static tables, as before.

Add `inflate.copy_midstream_fixed` and `inflate.copy_midstream_dynamic` in `test/test_inflate_copy.cc`: a stream compressed with `Z_FIXED` (or the default strategy) is inflated into half of the output buffer, copied with `inflateCopy()`, and both the original and the copy must finish with the right output.

## Related Upstream References

- Updates open PR: https://github.com/zlib-ng/zlib-ng/pull/2524
- madler/zlib: https://github.com/madler/zlib/pull/1369 was closed with "Applied. Thanks."; the change is not yet visible on public madler `develop`.
- Note: https://github.com/zlib-ng/zlib-ng/pull/2404 also modifies `inflateCopy()` (`state->next`) and `test/test_inflate_copy.cc`.

## Review Feedback Addressed

- None recorded.

## Testing

- With `tests/patch-gtest.sh` (clang, `ZLIB_COMPAT=ON`, `WITH_OPTIM=OFF`, `-fsanitize=address,pointer-compare,pointer-subtract,undefined` on C, `ASAN_OPTIONS=detect_invalid_pointer_pairs=2`):
  - Without the fix: `inflate.copy_midstream_fixed` aborts with `AddressSanitizer: invalid-pointer-pair`.
  - With the fix: `inflate.copy_midstream_fixed` and `inflate.copy_midstream_dynamic` both pass. The dynamic case passes without the fix as well (both pointers are in `state->codes`); it guards the rebasing of the cursors.
- Reproduction in the project's regression suite: `inflate-copy-pointer-equality`.
