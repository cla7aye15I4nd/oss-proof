# Copy window matches with memcpy() when the window is not the output

Status: tests and upstream-style commit message pending

## Problem

`chunkcopy_safe`, `CHUNKCOPY_SAFE` and `chunkmemset` compare (`>=`, `<`) and subtract a pointer into the window and a pointer into the caller's output, which point into different objects (ISO C17 §6.5.8p5, §6.5.6p9).

## Fix

Files: `inflate.c`, `inffast_tpl.h`.

A match copied from the sliding window to the output is copied with `memcpy(out, from, n); out += n;` instead of `chunkcopy_safe` in state `MATCH` of `inflate`. In `inflate_fast`, each of the four window copies first tests `window == beg` (`beg` is the start of this call's output): when equal, the copy is upstream's `CHUNKCOPY_SAFE` / `chunkcopy_safe`, unchanged; otherwise it is the `memcpy` form. `inflate`'s window is its own allocation and its output the caller's buffer, so there `window != beg` and the copy is the `memcpy`: the copy length already fits the output (`copy <= left`; `inflate_fast` keeps 258 bytes of room, or bails out to `MATCH` in safe mode), and the ranges are in different objects, so the result is the same. `inflateBack` decodes into the caller's window and calls `inflate_fast` with `beg == window`: there both pointers are in the one window, the copy can overlap, and upstream's copy (which handles overlap) is used. Pointer equality is defined for any two valid pointers (ISO C17 §6.5.9p6), and since `beg` points to an element of the output (not one past its end: `inflate_fast` is called with room for at least 3 bytes), it equals `window` only when the output is the window. `infback.c`'s own `MATCH` is unchanged: its `chunkcopy_safe` / `chunkmemset_safe` compare two pointers into the window.

## Related Upstream References

- Not yet submitted upstream.
- Note: https://github.com/zlib-ng/zlib-ng/pull/2432 changes the non-safe copy path of `inffast_tpl.h` (merged into `develop` after the pinned commit).

## Review Feedback Addressed

- None yet.

## Testing

- Reproductions in the project's regression suite: `inflate-window-copy`, `infback-window-overlap`.
- Confirmed on real C: yes (pointer-pair check); `inflateBack` with the revised patch: no report.
- No GoogleTest case in this series yet.
