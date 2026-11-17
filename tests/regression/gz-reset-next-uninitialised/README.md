# `x.next + 0` on a never-written field

`gz_reset` does not write `state->x.next`. On a gzip file opened for reading, `gzseek64` and
`gz_skip_have` then evaluate `state->x.next += n` with `n == 0` on that never-written field.
C17 leaves arithmetic on an indeterminate pointer undefined; every real implementation treats
`p + 0` as `p`, and no sanitizer reports it.

The model accepts it: `Ptr.add` returns the pointer unchanged when it adds zero, for every
pointer value (`ZlibF/Runtime/Ptr.lean`). This is a stated limit of the model, not a fixed issue.
`unset.c` opens a gzip file, then calls `gzseek` and `gzdirect`; `probe.h` is compiled into the
verified source and prints each evaluation of `x.next += n` with `n == 0`. `run.sh` checks that
the C evaluates it in both functions and that ASan and UBSan report nothing (`report.txt`).

Run: `ZLIB_SRC=$PWD/zlib bash tests/regression/gz-reset-next-uninitialised/run.sh`.
