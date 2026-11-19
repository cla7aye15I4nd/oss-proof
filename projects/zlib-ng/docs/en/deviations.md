# Deviations: what a call must satisfy

This page lists every premise of a goal that is narrower than `zlib.h`, or that a reader could
miss. A call outside these lines is not covered: it is neither proved safe nor claimed to be
unsafe.

## Every call

- The library is the zlib-ng `develop` branch at commit `5f1f4899` with the seven patches, built for x86_64
  Linux LP64 with `-DZLIB_COMPAT=ON -DWITH_OPTIM=OFF -DWITH_CRC32_CHORBA=OFF -DWITH_RUNTIME_CPU_DETECTION=OFF`,
  so that `adler32` and `adler32_z` run `adler32_c`, and `crc32` and `crc32_z` run `crc32_braid`. A build that
  dispatches to SIMD kernels or to the Chorba CRC-32 kernel (the default) is not covered.
- The static CRC tables `crc_table` and `x2n_table` hold the constants of `crc32_braid_tbl.h`
  (`CrcGlobals`). In C they are constant data; in the model they are part of the heap, so the CRC
  goals state it.
- A buffer argument is either `NULL`, with any `len`, or points to `len` readable bytes inside one
  live object (`BufferBytes`). This is what `zlib.h` asks.
- Theorems hold for every address of every object (`Heap.baseAddr`), so every alignment of a
  buffer is covered.
- The model reads a buffer as 64-bit words (`crc32_braid`, `adler32_swar`) through byte loads; the conversion to
  the word pointer is checked for alignment, the effective-type rule (ISO C17 §6.5p7) is not.

## Narrower than `zlib.h`

| Function | Premise | Lean | Reason |
| --- | --- | --- | --- |
| `compressBound` (value only) | `sourceLen ≤ 0xe38e38e38e38e377`. | `Goal.compressBound_functional` | Above this, the sum wraps and the function returns `ULONG_MAX`. Safety holds for every `sourceLen`. |
| `crc32_combine_op` | The low 32 bits of `op` are not 0. | `Goal.crc32_combine_op_safety` | `zlib.h` allows only an `op` made by `crc32_combine_gen` from a non-negative length, which is never 0; with a zero low half `multmodp` does not return. |
| `zng_alloc_aligned` (internal) | `align ≥ 8` and `8 + size + align < 2^32`; the alignment theorem asks `align = 2^k` with `3 ≤ k ≤ 31`. | `Goal.zng_alloc_aligned_safety`, `Goal.zng_alloc_aligned_alignment` | The only caller (`gz_buffer_alloc`) passes 64 and at most `3 * 2^30` bytes. |

## Inflate and uncompress (goals not done)

The goals of `inflate*` and `uncompress*` are stated on the streams that `zlib.h` lets a program reach
(`InflateReachable`): made by a successful `inflateInit_`, `inflateInit2_` or `inflateCopy`, then changed only by
inflate calls with valid arguments and by the program, which may change `next_in`, `avail_in`, `next_out` and
`avail_out` and memory the library does not own. A stream of `Z_NULL`, or with a `NULL` state, is also accepted.

| Function | Premise | Lean | Reason |
| --- | --- | --- | --- |
| `inflateInit_`, `inflateInit2_` (and every stream made by them) | `zalloc` and `zfree` are `Z_NULL` (the library's default allocator) or already the defaults. | `InitReady` | Calls through a caller's allocator are not modelled. |
| `inflate`, `inflateSync` | `next_in` and `next_out` are `NULL` or point to `avail_in` readable and `avail_out` writable bytes; these buffers and the registered `gz_header` buffers do not overlap one another or the library's allocation. | `StreamIO` | Caller buffers with no reason to overlap. |
| `inflateSync` | `next_in` is not `NULL` when `avail_in` is not 0. | `SyncInput` | `avail_in` counts the bytes at `next_in`. |
| `inflateGetDictionary` | The buffer is `NULL` or has at least 32768 writable bytes. | `Goal.inflateGetDictionary_safety` | `zlib.h` names 32768 bytes as always enough; the call itself needs only the current window size. |
| `inflateCopy` | `dest` and `source` are different streams; `dest` is ready for initialisation. | `Goal.inflateCopy_safety` | The copy of the `z_stream` is a `memcpy`, undefined for the same object. |
| Between calls | The program does not change the other `z_stream` fields, the library's allocation, or a registered `gz_header` record. | `CallerStep` | `zlib.h` reserves them to the library. |
| `uncompress`, `uncompress2`, `uncompress_z`, `uncompress2_z` | `dest` and `source` do not overlap. | `Disjoint` | Caller buffers with no reason to overlap. |

## Behaviour of the verified source

- `crc32_combine`, `crc32_combine64`, `crc32_combine_gen` and `crc32_combine_gen64` return 0 for a
  negative `len2`.
- `adler32` and `adler32_z` return 1 for a `NULL` buffer of any length.
