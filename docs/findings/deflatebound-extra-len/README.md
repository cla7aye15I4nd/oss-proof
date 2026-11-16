# deflateBound with a gzip extra field of length 2^32 - 2 or 2^32 - 1

Status: reproduced on the real C. Known upstream (discussion in upstream PR 1360).

`deflateBound` adds `2 + s->gzhead->extra_len` to the wrapper length. `extra_len` is `uInt`, so the
sum is computed at 32 bits and wraps to 0 or 1 for `extra_len` 2^32 - 2 and 2^32 - 1. `deflate`
writes `extra_len & 0xffff` bytes of the field (65534 or 65535). The bound is then about 64 KiB
too small, and one `deflate(Z_FINISH)` with that room returns `Z_OK`
(`tests/goals/deflate-bound/bound.c`, mode `extra`: bound 125 and 126 for 100 input bytes).

For `extra_len` from 2^16 up to 2^32 - 3 the bound counts `extra_len` bytes and `deflate` writes
fewer: the bound is conservative, not wrong.

Effect on the statements: the specification follows the C. `WrapperLength`, which the value goals
`Goal.deflateBound` and `Goal.deflateBound_z` use, computes `2 + extra_len` at 32 bits, and the
translation wraps in the same way. A statement that the bound is enough for a stream whose header
was set by `deflateSetHeader` needs a premise excluding the two lengths.
