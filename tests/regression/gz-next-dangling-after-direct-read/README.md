# `x.next + 0` on a pointer into a freed buffer

A large `gzread` on a gzip file decompresses straight into the caller's buffer and leaves
`state->x.next` pointing into it, with `x.have == 0`. After the caller frees the buffer,
`gzseek64` and `gz_skip_have` evaluate `state->x.next += n` with `n == 0` on that dangling
pointer. C17 leaves arithmetic on a pointer to a freed object undefined; every real
implementation treats `p + 0` as `p`, and no sanitizer reports it.

The model accepts it: `Ptr.add` returns the pointer unchanged when it adds zero, for every
pointer value (`ZlibF/Runtime/Ptr.lean`). This is a stated limit of the model, not a fixed issue.
`dangling.c` makes the calls; the probe of `../gz-reset-next-uninitialised/probe.h` is compiled
into the verified source. `run.sh` checks that the C evaluates `x.next + 0` in both functions and
that ASan and UBSan report nothing (`report.txt`).

Run: `ZLIB_SRC=$PWD/zlib bash tests/regression/gz-next-dangling-after-direct-read/run.sh`.
