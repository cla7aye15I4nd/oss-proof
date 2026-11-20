# PR 0008: Skip `inflateSync` input search when `avail_in` is zero

- **Proposed PR Title**: `Skip inflateSync input search when avail_in is zero`
- **Target Base**: `zlib-ng/zlib-ng` `develop` (`5f1f4899`)
- **Upstream PR**: Ready to submit
- **Commits**: 1 (`upstream.patch`)
- **Files**: `inflate.c`, `test/test_inflate_sync.cc`

## Problem & Root Cause

In `inflateSync()`, when a stream has primed bits (`state->bits >= 8`) or transitions cleanly into `SYNC` mode with an empty caller buffer (`strm->next_in == NULL`, `strm->avail_in == 0`), it unconditionally calls `syncsearch(&(state->have), strm->next_in, strm->avail_in)` and executes:

```c
strm->next_in += len;
```

Even when `len == 0`, adding `0` to `NULL` is undefined behavior in ISO C17 §6.5.6p8 (`NULL + 0` is only valid in C++, not C17).

## Fix Summary

Guard both `syncsearch()` and the pointer advance on non-empty input / consumed bytes:

```c
    if (strm->avail_in) {
        len = syncsearch(&(state->have), strm->next_in, strm->avail_in);
        strm->avail_in -= len;
        if (len)
            strm->next_in += len;
        strm->total_in += len;
    }
```

Add `inflate.sync_primed_bits_with_empty_input` in `test/test_inflate_sync.cc`.

## Overlaps & Dependencies

- Independent (`inflate.c` `inflateSync()` and `test/test_inflate_sync.cc` are untouched by all other series).

## Verification

- Confirmed by source inspection and C17 semantics (`NULL + 0` cannot be diagnosed dynamically by C UBSan/ASan, so the regression test passes both before and after the patch while verifying exact API return values and `next_in == nullptr` / `avail_in == 0` preservation).
- `build-compat-san` & `build-native-san`: `inflate.sync_primed_bits_with_empty_input` passes (`[  PASSED  ] 1 test.`).
