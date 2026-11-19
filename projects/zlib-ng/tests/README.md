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
| `gzbuffer-aligned-alloc-overflow` | 0001 | signed overflow in `gz_buffer_alloc` |
| `crc32-combine-negative-len-hang` | 0002 | `crc32_combine_gen(-1)`, `crc32_combine_op(1, 2, 0)`, `crc32_combine(1, 2, -1)` do not return |
| `inflate-copy-pointer-equality` | 0003 | invalid pointer pair in `inflateCopy` |
| `gzseek-offset-overflow` | 0004 | signed overflow in `gzseek64` |
| `adler32-null-len-1` | 0007 | null load in `adler32_len_1` for `adler32(1, Z_NULL, 1)` |

Patches 0005 and 0006 have no reproduction: their defects are not confirmed on real C.
