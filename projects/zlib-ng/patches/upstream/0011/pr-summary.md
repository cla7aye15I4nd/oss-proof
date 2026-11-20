# PR 0011: Harden gzip extra copying when shared header state changes

- **Proposed PR Title**: `Harden gzip extra copying when shared header state changes`
- **Target Base**: `zlib-ng/zlib-ng` `develop` (`5f1f4899`)
- **Upstream PR**: https://github.com/zlib-ng/zlib-ng/pull/2528 (open; needs updated force-push)
- **Commits**: 1 (`upstream.patch`)
- **Files**: `inflate.c`, `test/test_inflate_copy.cc`

## Problem & Root Cause

In `inflate()` (`EXTRA` state), copying the gzip `FEXTRA` payload assumes `state->head->extra_len` still equals the length saved by the stream's own `EXLEN` state:

```c
len = state->head->extra_len - state->length;
if (len < state->head->extra_max) {
    memcpy(state->head->extra + len, next,
           len + copy > state->head->extra_max ?
           state->head->extra_max - len : copy);
}
```

When two streams share one `gz_header` (via `inflateCopy()` after the fixed 10-byte gzip header) and the second stream parses a smaller `XLEN`, `state->head->extra_len < state->length` causes unsigned `uint32_t` underflow in `len = extra_len - length` and wraparound in `len + copy`. Overflow itself requires `extra_max` near `2^32 - 65535`, so this is defense-in-depth hardening.

## Fix Summary

Guard the `EXTRA` copy in `inflate.c`:

- Require `state->length <= state->head->extra_len` before computing `len`.
- Compare `copy > state->head->extra_max - len` instead of `len + copy > state->head->extra_max`.

Add `inflate.shared_gzip_header_extra_bounds` in `test/test_inflate_copy.cc` using `inflateCopy()` after the 10-byte gzip header and `extra_max = UINT32_MAX` on a 16-byte stack buffer (no bytes are written once lengths disagree).

## Review Feedback Addressed (`nmoinvaz` & CodeRabbit on `#2528`)

- **Replace opt-in 4 GiB test (`nmoinvaz` inline #1 & #2)**: Adopted `nmoinvaz`'s exact pattern using `uint8_t extra[16]` + `header.extra_max = UINT32_MAX` and valid `inflateCopy()` after the fixed 10-byte header (`first_xlen = 100`, `second_xlen = 10`), removing `<cstdlib>`/`<memory>` and avoiding any 4 GiB test allocation.
- **Remove invalid `inflateGetHeader` usage & standalone reproducer files (`nmoinvaz` #3 & CodeRabbit)**: Replaced standalone C reproducers with GoogleTest and omitted out-of-contract `inflateGetHeader()` usage after `inflate()` has started (calling only after `inflateInit2()`, as documented in `zlib.h.in` / `zlib-ng.h.in`).
- **Single clean commit & concise comments (`nmoinvaz` #1–3, #4)**: Squashed into 1 commit with an explicit message noting hardening scope (`extra_max` above ~`2^32 - 65535`) and replaced multi-line comments with a single-line comment.

## Overlaps & Dependencies

- **Internal (`test/test_inflate_copy.cc`)**: `0003` (`#2524`) also appends to `test/test_inflate_copy.cc`.
- **External (`#2404`)**: https://github.com/zlib-ng/zlib-ng/pull/2404 touches `inflateCopy()` / `test/test_inflate_copy.cc`.

## Verification

- `build-compat-san` & `build-native-san`:
  - Before fix (`5f1f4899`): `inflate.shared_gzip_header_extra_bounds` crashes under ASan with buffer overflow (and a standalone 4 GiB `extra_max = 0xfffffff0U` reproducer similarly crashes with ASan `heap-buffer-overflow`).
  - After fix: `inflate.shared_gzip_header_extra_bounds` passes on both builds (`[  PASSED  ] 1 test.`).
