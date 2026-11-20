# Avoid cross-object pointer comparison in inflateCopy()

## Problem

When copying Huffman table cursors (`lencode` and `distcode`), `inflateCopy()` checks whether `state->lencode` points into `state->codes` via relational comparison:

```c
if (state->lencode >= state->codes && state->lencode <= state->codes + ENOUGH - 1)
```

If the stream is paused inside a fixed Huffman block (`lenfix` / `distfix`), `state->lencode` points into a static table rather than the heap-allocated `state->codes` array. Relational comparison (`>=`, `<=`) of pointers into distinct objects is undefined behavior in ISO C17 §6.5.8p5 (flagged by AddressSanitizer under `detect_invalid_pointer_pairs=2`).

## Fix

Replace the relational range checks on `lencode` and `distcode` with pointer equality against their only valid bases:

- Check `state->lencode == state->codes` (dynamic tables place `lencode` at the start of `codes`).
- Check `state->distcode == distfix` (fixed table), otherwise adjust relative to `state->codes`.

Add `inflate.copy_midstream_fixed` and `inflate.copy_midstream_dynamic` in `test/test_inflate_copy.cc`, stepping `inflate()` one byte at a time so `inflateCopy()` runs inside both fixed and dynamic blocks.

## Related Upstream References

- Updates open PR: https://github.com/zlib-ng/zlib-ng/pull/2524
- Accepted upstream in `madler/zlib`: https://github.com/madler/zlib/pull/1369 (`"Applied. Thanks."`, pending push to `develop`; `#1369` updates `state->lencode == state->codes`, while this PR also updates `state->distcode == distfix` and adds GoogleTest cases).
- Note: https://github.com/zlib-ng/zlib-ng/pull/2404 also modifies `inflateCopy()` (`state->next`) and `test/test_inflate_copy.cc`.

## Review Feedback Addressed

- None recorded.

## Testing

- Clang (`ZLIB_COMPAT=ON`, `WITH_OPTIM=OFF`, `-fsanitize=address,pointer-compare,pointer-subtract,undefined` on C, `ASAN_OPTIONS=detect_invalid_pointer_pairs=2`):
  - Before fix: `inflate.copy_midstream_fixed` aborts with `AddressSanitizer: invalid-pointer-pair`.
  - After fix: `inflate.copy_midstream_fixed` and `inflate.copy_midstream_dynamic` both pass.
- Clang (`ZLIB_COMPAT=OFF`, `WITH_OPTIM=ON`, ASan + UBSan): both tests pass.
