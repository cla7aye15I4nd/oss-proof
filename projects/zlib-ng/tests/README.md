# Differential tests: the Lean translation against the real C

The translation in `ZlibNgF/ZlibNg/*.lean` is trusted, not proved. This directory is the evidence that
it matches the C. For each translated function, the same inputs go to

* the **real zlib-ng**: the pinned `zlib-ng/` submodule plus `patches/*.patch` in name order, applied to
  a **copy** (the submodule is never touched) and built as `libz.a` by `build-zlib-ng.sh` with the
  verified configuration
  `-DZLIB_COMPAT=ON -DWITH_OPTIM=OFF -DWITH_CRC32_CHORBA=OFF -DWITH_RUNTIME_CPU_DETECTION=OFF`
  (the script rejects a library that contains Chorba or function-table symbols, and checks that
  `adler32.c` calls `adler32_c` and `crc32.c` calls `crc32_braid`);
* the **Lean translation**, called through the runtime (`C.run` on a heap built by
  `lean/DiffTest/Common.lean`).

The two outputs are compared byte for byte. This is a test, not a proof: it shows that the two agree on
the inputs tried, nothing more. The drivers import the translation modules themselves, never a copy,
and are not part of the checked library.

## Run

```bash
ZLIB_NG_SRC=$PWD/zlib-ng bash tests/run.sh          # from projects/zlib-ng
SAN=1 ZLIB_NG_SRC=$PWD/zlib-ng bash tests/run.sh    # C side under ASan + UBSan (what CI runs)
ZLIB_NG_SRC=$PWD/zlib-ng bash tests/regression/run.sh [case...]   # only the patch reproductions
```

`run.sh` needs `cc`, `cmake`, `patch`, `nm`, `timeout`, `python3`, `tar` and `lake`. Variables:
`ZLIB_NG_SRC` (a zlib-ng checkout), `ZLIB_NG_BUILD` (reuse a copy made by `build-zlib-ng.sh`),
`ONLY=name` (one list entry, or `patches`), `SAN=1`. It exits 0 if all outputs are identical, 1 on the
first difference (it prints the input line and both results), 2 on a setup error. Everything it makes
is in `tests/build/` and `tests/.lake/`. A build directory records the patches, options and flags it was
made with (`BUILD_DIGEST`) and is rebuilt when they change.

## Drivers

| Name | C file | Functions |
| --- | --- | --- |
| `adler32` | `adler32.c`, `arch/generic/adler32_c.c` | `adler32`, `adler32_z`, `adler32_combine`, `adler32_combine64` |
| `crc32` | `crc32.c`, `arch/generic/crc32_braid_c.c`, `crc32_braid_comb.c` | `crc32`, `crc32_z`, `crc32_combine`, `crc32_combine64`, `crc32_combine_gen`, `crc32_combine_gen64`, `crc32_combine_op`, `get_crc_table` (all 256 entries) |
| `zutil` | `zutil.c` | `zlibVersion`, `zlibCompileFlags`, `zError`, `zcalloc` / `zcfree` (write, read back, free), `zng_alloc_aligned` / `zng_free_aligned` (NULL or not, alignment, write, read back, free) |
| `compress` | `compress.c` | `compressBound` |
| `inflate` | `inflate.c`, `inftrees.c`, `inffast_tpl.h` / `chunkset_tpl.h` (`arch/generic/chunkset_c.c`), `inflate_p.h`, `uncompr.c` | `inflateInit2_`, `inflate` (every flush mode, input and output in pieces), `inflateSetDictionary` (on `Z_NEED_DICT`), `inflateGetHeader`, `inflateReset`, `inflateResetKeep`, `inflateReset2`, `inflateEnd`; zlib, gzip and raw streams of every block type, every `windowBits`, dictionaries, gzip headers, corrupted and truncated streams, window-crossing matches, distances 1..64. A line prints every call's return value, stream fields (`next_in` / `next_out` offsets, `avail_*`, `total_*`, `adler`, `data_type`, `msg`), the output bytes and the header fields and buffers. Call scripts on one stream: `inflatePrime`, `inflateSync`, `inflateSyncPoint`, `inflateCopy` mid-stream (then going on with the copy), `inflateGetDictionary`, `inflateSetDictionary` (also `NULL`, too early, too late), `inflateUndermine`, `inflateValidate`, `inflateMark`, `inflateCodesUsed`, resets and calls after `inflateEnd`. `uncompress`, `uncompress2`, `uncompress_z`, `uncompress2_z` with exact, short and empty output, `NULL` pointers and length cells, short, corrupted and trailing input. `inflateInit_` / `inflateInit2_` with wrong versions and structure sizes |
| `infback` | `infback.c` (with the parts of `inflate.c`, `inftrees.c`, `inffast_tpl.h` / `chunkset_tpl.h` it calls) | `inflateBackInit_`, `inflateBack`, `inflateBackEnd`: raw streams of every block type and hand-built fixed-code streams, every `windowBits` 8..15 with a window of exactly that size, input from `next_in` and from `in()` in chunks of 1 byte, odd sizes or all at once, `in()` running out early, `out()` failing at its first and later calls, corrupted and truncated streams, matches wrapping the window, two `inflateBack` calls on one state, init argument errors (`NULL` window, bad `windowBits`, version, `stream_size`), `NULL` and stateless streams. A line prints the return value, `next_in` (which buffer, offset), `avail_in`, `msg`, the number of `in()` calls, the length of every `out()` call and the bytes written. Streams where `inflate_fast`'s window copy would overlap its destination (an open defect of patch 0007 with `inflateBack`, `regression/infback-window-overlap`) are not generated |

## File formats

One test case per line, fields separated by one space. Blank lines are skipped.

| Field | Written as |
| --- | --- |
| function | its C name (`adler32_z`, ...) |
| unsigned integer | decimal |
| signed integer | decimal, optional `-` |
| buffer | `null:LEN` (a NULL pointer, passed with length LEN), `hex:DIGITS` (a non-NULL pointer to those bytes; empty digits give a valid pointer to zero bytes) or `off:K:DIGITS` (a pointer K bytes into a block whose last bytes are the digits: an unaligned buffer) |

The C side allocates every buffer with `malloc` of the exact size, so sanitizers see overreads. The
output has one line per input line. The Lean side prints `FAULT ...` if the translation raises
`Fault.ub` or `Fault.outOfFuel`; the C side cannot fault, so a fault is always a difference. Malformed
input prints `BADINPUT` and fails the run. Inputs that are undefined behaviour in C (a length larger
than the buffer) are not generated.

Types follow LP64: `uLong`, `z_size_t` are 64 bits, `uInt` 32, `z_off_t` and `z_off64_t` signed 64.

## Patch reproductions

`regression/run.sh` builds the source twice per case under ASan (with pointer-pair checks) and UBSan,
at `-O0`: with every patch but the case's own, and with every patch. The first must show the defect (the
named sanitizer report, or no return within the timeout), the second must run without a report and
print the expected result.

| Case | Patch | Defect shown without the patch |
| --- | --- | --- |
| `inflate-copy-pointer-equality` | 0003 | invalid pointer pair in `inflateCopy` |
| `gzseek-offset-overflow` | 0004 | signed overflow in `gzseek64` |
| `deflatebound-gzip-extra-length` | 0006 | `deflateBound` too small for a gzip extra field with `extra_len > 0xffff` |
| `inflate-window-copy` | 0007 | invalid pointer pair (window vs output) in `chunkcopy_safe` |
| `inflatesync-null-next-in` | 0008 | none observable: `NULL + 0` is not reported by any sanitizer; the case checks the calls run alike |
| `inflatesetdictionary-null` | 0009 | `inflateSetDictionary(strm, NULL, 0)` returns `Z_OK` instead of `Z_STREAM_ERROR` |
| `inflate-fast-primed-bits` | 0010 | after `inflatePrime`, `inflate` returns with `avail_in` larger than the caller gave (`next_in` before the buffer) |

Plain regression tests (defects of 2.3.3 that the `develop` branch fixes; each must pass on the verified
source without a sanitizer report): `adler32-null-len-1`, `crc32-combine-negative-len-hang` (the
`g` and `c` runs), `gzbuffer-aligned-alloc-overflow`.

Open defects (undefined behaviour of the verified source with no patch yet; each must still show its report,
and the run fails once it stops reproducing): none.
