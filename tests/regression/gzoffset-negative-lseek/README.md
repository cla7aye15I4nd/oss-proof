# gzoffset64 with a negative descriptor offset

`gzoffset64` takes `LSEEK(fd, 0, SEEK_CUR)`, refuses only -1, and when reading subtracts the
buffered input: `offset -= state->strm.avail_in`. A descriptor whose offset is negative makes this
subtraction overflow `z_off64_t`.

On Linux, `/proc/self/mem` (like `/proc/<pid>/mem` and `/dev/mem`) accepts every 64-bit offset, and
`lseek` returns it unchanged; glibc treats only results from -4095 to -1 as errors. `negative.c`
reads a gzip stream from its own memory through `/proc/self/mem` with `gzdopen` and `gzread`, then
moves the descriptor to `INT64_MIN + 1` itself and calls `gzoffset64`. `lseek` returns
`INT64_MIN + 1`, and without patch 0006 UBSan reports the signed overflow at the subtraction. With
the patch, `gzoffset64` returns -1 for the negative result and nothing is reported (`report.txt`).

The offset of a readable address is positive, so the overflow needs the caller to move the
descriptor after `gzdopen` while the file is being read. `zlib.h` neither allows nor forbids this.
In transparent reading `avail_in` is 0 and nothing overflows; writing does not subtract.

Run: `ZLIB_SRC=$PWD/zlib bash tests/regression/gzoffset-negative-lseek/run.sh` (Linux only).
