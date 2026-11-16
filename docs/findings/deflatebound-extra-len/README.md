# deflateBound with a gzip extra field of length 2^32 - 2 or 2^32 - 1

Status: reproduced on the real C, upstream `develop` at commit
`757f0527154291bcf6bfbd6396ecde6bedd2db95`. `deflate.c` differs between that commit and zlib 1.4
(commit `99623ef7097352da7993ba614161fd6a311e046e`), the revision this project verifies, only in
the copyright string; no run on that revision is recorded here. No patch of this repository
changes the sum described below. Known upstream
([discussion in upstream PR 1360](https://github.com/madler/zlib/pull/1360)).

`deflateBound` adds `2 + s->gzhead->extra_len` to the wrapper length. `extra_len` is `uInt`, so the
sum is computed at 32 bits and wraps to 0 or 1 for `extra_len` 2^32 - 2 and 2^32 - 1. `deflate`
writes `extra_len & 0xffff` bytes of the field (65534 or 65535). The bound is then about 64 KiB
too small, and one `deflate(Z_FINISH)` with that room returns `Z_OK`
(`tests/goals/deflate-bound/bound.c`, mode `extra`: bound 125 and 126 for 100 input bytes). The
output of that run is not retained; `tests/goals/deflate-bound/run.sh` passes only if exactly two
of the five lengths it tries fail.

For `extra_len` from 2^16 up to 2^32 - 3 the bound counts `extra_len` bytes and `deflate` writes
fewer: the bound is conservative, not wrong.

Effect on the statements:

- Safety is not affected. The point concerns the value of the bound, which the safety goals
  `Goal.deflateBound_safety` and `Goal.deflateBound_z_safety` do not use.
- The specification of the value follows the C. `WrapperLength`, which the value goals
  `Goal.deflateBound` and `Goal.deflateBound_z` use, computes `2 + extra_len` at 32 bits, and the
  translation wraps in the same way. On this point the specification and the translation agree.
  The two value goals are not planned and not done.
- What the wrap breaks is the promise of zlib.h that a buffer of `deflateBound` bytes is enough
  for one `deflate(Z_FINISH)`. A statement of that promise about the C, for a stream whose header
  was set by `deflateSetHeader`, needs a premise excluding the two lengths.
