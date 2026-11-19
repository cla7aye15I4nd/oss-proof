# Deviations: what a call must satisfy

This page lists every premise of a goal that is narrower than `zlib.h`, or that a reader could
miss. A call outside these lines is not covered: it is neither proved safe nor claimed to be
unsafe.

## Every call

- The library is zlib-ng 2.3.3 with the seven patches, built for x86_64 Linux LP64 with
  `-DZLIB_COMPAT=ON -DWITH_OPTIM=OFF -DWITH_CRC32_CHORBA=OFF -DWITH_RUNTIME_CPU_DETECTION=OFF`, so that
  `adler32` and `adler32_z` run `adler32_c`, and `crc32` and `crc32_z` run `crc32_braid`. A build that
  dispatches to SIMD kernels or to the Chorba CRC-32 kernel (the default) is not covered.
- The static CRC tables `crc_table` and `x2n_table` hold the constants of `crc32_braid_tbl.h`
  (`CrcGlobals`). In C they are constant data; in the model they are part of the heap, so the CRC
  goals state it.
- A buffer argument is either `NULL`, with any `len`, or points to `len` readable bytes inside one
  live object (`BufferBytes`). This is what `zlib.h` asks.
- Theorems hold for every address of every object (`Heap.baseAddr`), so every alignment of a
  buffer is covered.

## Narrower than `zlib.h`

| Function | Premise | Lean | Reason |
| --- | --- | --- | --- |
| `compressBound` (value only) | `sourceLen ≤ 0xe38e38e38e38e377`. | `Goal.compressBound_functional` | Above this, the bound wraps modulo 2^64. Safety holds for every `sourceLen`. |
| `zng_alloc_aligned` (internal) | `align` is 0 or at least 8; the alignment theorem asks `align = 2^k` with `3 ≤ k ≤ 31`. | `Goal.zng_alloc_aligned_safety`, `Goal.zng_alloc_aligned_alignment` | The only caller (`gz_buffer_alloc`) passes 64. |

## Behaviour that differs from unpatched zlib-ng

- `crc32_combine`, `crc32_combine64`, `crc32_combine_gen` and `crc32_combine_gen64` return 0 for a
  negative `len2`, and `crc32_combine_op` returns 0 when the low 32 bits of `op` are 0 (patch 0002).
  Unpatched, these calls do not return.
- `adler32` and `adler32_z` return 1 for a `NULL` buffer of length 1 (patch 0007). Unpatched, they
  read through the null pointer.
