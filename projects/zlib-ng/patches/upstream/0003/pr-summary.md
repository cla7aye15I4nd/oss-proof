# PR 0003: Avoid cross-object pointer comparison in `inflateCopy()`

- **Proposed PR Title**: `Avoid cross-object pointer comparison in inflateCopy()`
- **Target Base**: `zlib-ng/zlib-ng` `develop` (`5f1f4899`)
- **Upstream PR**: https://github.com/zlib-ng/zlib-ng/pull/2524 (open)
- **Related `madler/zlib` PR**: https://github.com/madler/zlib/pull/1369 (`Applied. Thanks.`, pending push to `develop`; `#1369` updates `state->lencode == state->codes`, while `zlib-ng#2524` also updates `state->distcode == distfix` and adds GoogleTest cases)
- **Commits**: 1 (`upstream.patch`)
- **Files**: `inflate.c`, `test/test_inflate_copy.cc`

## Problem & Root Cause

In `inflateCopy()`, copying the Huffman table cursors (`lencode` and `distcode`) checks whether the source pointers fall inside the stream's `codes` array using:

```c
if (state->lencode >= state->codes && state->lencode <= state->codes + ENOUGH - 1)
```

When the stream is paused inside a fixed Huffman block (`lenfix` / `distfix`), `lencode` and `distcode` point into static const tables rather than `state->codes` on the heap. Evaluating relational operators (`>=`, `<=`) across pointers to distinct objects is undefined behavior in ISO C17 §6.5.8p5 (`ASAN_OPTIONS=detect_invalid_pointer_pairs=2` reports `invalid-pointer-pair` immediately).

## Fix Summary

Replace the relational range checks on `lencode` and `distcode` with pointer equality against the only valid start bases:

- `state->lencode == state->codes` (dynamic tables allocate `lencode` at `codes`), reusing the `next - codes` offset computation;
- `state->distcode == distfix` (fixed block), otherwise dynamic inside `state->codes`.

Add two GoogleTest cases in `test/test_inflate_copy.cc` (`inflate.copy_midstream_fixed`, `inflate.copy_midstream_dynamic`) that pause `inflate()` mid-block via 1-byte `avail_in`/`avail_out` steps, call `inflateCopy()`, and verify both copies finish identically.

## Review Feedback Addressed

No changes requested on upstream `#2524`. Both new tests are isolated in `test/test_inflate_copy.cc`.

## Overlaps & Dependencies

- **Internal (`test/test_inflate_copy.cc`)**: `0011` (`#2528`) also appends to `test/test_inflate_copy.cc`. Independent in `inflate.c`.
- **External (`#2404`)**: https://github.com/zlib-ng/zlib-ng/pull/2404 also edits `inflateCopy()` (`state->next`) and `test/test_inflate_copy.cc`; trivial rebase if `#2404` merges first.

## Verification

- `build-compat-san` (`-fsanitize=address,pointer-compare,pointer-subtract,undefined`, `detect_invalid_pointer_pairs=2`):
  - Before fix (`5f1f4899`): `inflate.copy_midstream_fixed` crashes with `AddressSanitizer: invalid-pointer-pair`.
  - After fix: both `inflate.copy_midstream_fixed` and `inflate.copy_midstream_dynamic` pass (`[  PASSED  ] 2 tests.`).
- `build-native-san` (`ZLIB_COMPAT=OFF`, `WITH_OPTIM=ON`): both tests pass (`[  PASSED  ] 2 tests.`).
