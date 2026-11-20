# Copy window matches with memcpy() when the window is not the output

## Problem

`chunkcopy_safe` and `CHUNKCOPY_SAFE` compare (`>=`, `<`) and subtract their source and destination pointers to handle overlapping copies. When `inflate` copies a match from its sliding window into the caller's output buffer (state `MATCH`, and the window copies of `inflate_fast`), the two pointers point into different objects, which is undefined (ISO C17 §6.5.8p5, §6.5.6p9).

## Fix

Files: `inflate.c`, `inffast_tpl.h`.

A match copied from the sliding window to the output is copied with `memcpy(out, from, n); out += n;` instead of `chunkcopy_safe` in state `MATCH` of `inflate`. In `inflate_fast`, each of the four window copies first tests `window == beg` (`beg` is the start of this call's output): when equal, the copy is upstream's `CHUNKCOPY_SAFE` / `chunkcopy_safe`, unchanged; otherwise it is the `memcpy` form. `inflate`'s window is its own allocation and its output the caller's buffer, so there `window != beg` and the copy is the `memcpy`: the copy length already fits the output (`copy <= left`; `inflate_fast` keeps 258 bytes of room, or bails out to `MATCH` in safe mode), and the ranges are in different objects, so the result is the same. `inflateBack` decodes into the caller's window and calls `inflate_fast` with `beg == window`: there both pointers are in the one window, the copy can overlap, and upstream's copy (which handles overlap) is used. Pointer equality is defined for any two valid pointers (ISO C17 §6.5.9p6), and since `beg` points to an element of the output (not one past its end: `inflate_fast` is called with room for at least 3 bytes), it equals `window` only when the output is the window. `infback.c`'s own `MATCH` is unchanged: its `chunkcopy_safe` / `chunkmemset_safe` compare two pointers into the window.

The series is one commit with the library change and one GoogleTest case.

## Related Upstream References

- Not yet submitted upstream.
- https://github.com/zlib-ng/zlib-ng/pull/2432 (merged into `develop` after the pinned commit) changes the non-safe copy path of `inffast_tpl.h`; the series will need a rebase there when it is submitted.

## Review Feedback Addressed

- None yet (not submitted).

## Testing

- `inflate/inflate_far_distance.chunked_output/*` (existing upstream test): without the library change it fails under AddressSanitizer with `detect_invalid_pointer_pairs=2` (`invalid-pointer-pair` in the window copy); with it, all 9 instances pass. Observed with `tests/patch-gtest.sh`.
- `inflate_back_window.overlapping_window_copy` (new, `test/test_inflate_back.cc`): `inflateBack` streams for windowBits 8, 9 and 15 whose window copies overlap (and two at distance `wsize`). It passes with and without the change; with the first version of this patch (unconditional `memcpy`, kept as `tests/regression/infback-window-overlap/first-0004.patch`) it fails with AddressSanitizer `memcpy-param-overlap`, so it guards the `window == beg` branch.
- Reproductions in the project's regression suite: `inflate-window-copy`, `infback-window-overlap`.
