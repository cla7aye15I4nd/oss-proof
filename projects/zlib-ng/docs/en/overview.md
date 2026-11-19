# zlib-ng

Verification target: the zlib-ng `develop` branch at commit `5f1f4899` with three patches, built as
the zlib-compatible (`ZLIB_COMPAT`) x86_64 Linux LP64 library with the generic C kernels: every
dispatched function (`adler32`, `crc32`, …) runs its portable C version, with no SIMD code.

## Build configuration

The verified library is built with these options (all other options keep their defaults):

```
-DZLIB_COMPAT=ON -DWITH_OPTIM=OFF -DWITH_CRC32_CHORBA=OFF -DWITH_RUNTIME_CPU_DETECTION=OFF
```

- `WITH_OPTIM=OFF` leaves out every architecture-specific source file.
- `WITH_CRC32_CHORBA=OFF` leaves out the Chorba CRC-32 kernel. With it on and run-time detection off,
  `crc32` and `crc32_z` call `crc32_chorba`, which is not translated.
- `WITH_RUNTIME_CPU_DETECTION=OFF` removes the function table: each dispatched call is a direct call to
  its generic C function, `adler32_c` for the Adler-32 functions and `crc32_braid` for the CRC-32
  functions.

## Scope

- **Safety of every public function of `zlib.h`:** no undefined behaviour under strict ISO C17, no
  memory error, and termination, on every input the header allows.
- **Functional theorems** where stated: the version and error strings, `zlibCompileFlags`, the
  Adler-32 checksum and its combination, the rejection values of `crc32_combine*`, and the exact
  value of `compressBound`.
- **Round trip** of `deflate` and `inflate`.

## What is proved so far

- The strict ISO C17 runtime rejects `NULL + 0`, dangling `+ 0`, `NULL - NULL`, cross-object
  pointer subtraction and `memset(NULL, b, 0)`.
- `zlibVersion`, `zlibCompileFlags` and `zError` are safe and return the expected values.
- `adler32` and `adler32_z` are safe and compute the Adler-32 checksum of the buffer, and return 1
  for a `NULL` buffer of any length, as `zlib.h` documents;
  `adler32_combine` and `adler32_combine64` are safe and combine two checksums correctly.
- `get_crc_table`, `crc32` and `crc32_z` are safe on every readable buffer, for every alignment of
  the buffer in memory; the five `crc32_combine*` functions are safe for every argument and reject
  negative lengths with 0.
- `compressBound` is safe and returns the exact bound of the `deflate_quick` path.
- Two internal allocation helpers used by the `gz*` functions (`zcalloc` / `zcfree`,
  `zng_alloc_aligned` / `zng_free_aligned`) are safe, and `zng_alloc_aligned` returns aligned
  memory.

Streaming `deflate*` and `inflate*`, one-shot `compress*` and `uncompress*`, the `gz*` family and
the round trip are not done. Every public function of `zlib.h` is listed as done or not done.

The translation of each function above is also compared with the real C library, built with the
configuration above, on generated inputs. Such tests are evidence that the translation matches the C,
not a proof. See [status](progress.html), [deviations](deviations.html) and
[findings](findings.html).
