# Check for NULL dictionary in inflateSetDictionary

## Problem

`inflateSetDictionary(strm, NULL, 0)` on a raw stream computes `NULL + 0`, `NULL - 0` and calls `memcpy` from `NULL` (ISO C17 §6.5.6p8, §7.24.1p2), and returns `Z_OK`, although `zlib.h` documents `Z_STREAM_ERROR` for a `NULL` dictionary. With a nonzero length the call reads from the null buffer.

## Fix

Files: `inflate.c`, `test/test_dict.cc`.

`inflateSetDictionary` returns `Z_STREAM_ERROR` for a `NULL` dictionary, before any other step after the state check:

```c
if (dictionary == NULL)
    return Z_STREAM_ERROR;
```

The series has two commits:

1. The library part of commit `f35ed264` ("Check for NULL dictionary in inflateSetDictionary", Hans Kristian Rosbach) of the open maintainer PR #2516, with its author and message: the check above and its comment. Its test hunk extends `test/test_inflate_api_errors.cc`, which earlier commits of #2516 add and which does not exist at the pinned commit, so it is left out (noted in the commit message).
2. The same test (`NULL` with length 0 and 5 on a raw stream) in `test/test_dict.cc`.

The library change is the one this project proved; `f35ed264` adds a three-line comment above it, which is the only difference.

## Related Upstream References

- https://github.com/zlib-ng/zlib-ng/pull/2516 (Hans Kristian Rosbach, maintainer), open, approved by a reviewer; commit `f35ed264` is this check. No separate PR is planned: this series is replaced by #2516 once it is merged and the pin passes it.
- madler/zlib `ec2603b` (zlib 1.4) folds the same check into `inflateStateCheck(strm) || dictionary == Z_NULL`.

## Review Feedback Addressed

- None (the fix is the maintainer's own commit).

## Testing

- `dictionary.inflate_null_dictionary` (new, `test/test_dict.cc`): without the check, UndefinedBehaviorSanitizer reports a null pointer passed as `memcpy`'s source (`inflate.c`, `updatewindow`) on the call with length 0, which also returns `Z_OK`; with it, both calls return `Z_STREAM_ERROR`. Observed with `tests/patch-gtest.sh`.
- Reproduction in the project's regression suite: `inflatesetdictionary-null`.
