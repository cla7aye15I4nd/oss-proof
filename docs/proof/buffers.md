# Buffer utilities: source decisions

This page lists the places in `compress.c`, `uncompr.c` and the bound functions of `deflate.c`
where the C does something that the model has to represent with care. For each it says what the
C does, what the model does, and whether a theorem covers it. The safety proofs of these
functions are on two other pages; this page is their source-reading companion.

The [API contracts](../spec/api/utility.md) give the caller obligations. Terms:
[glossary](../glossary.md).

## Where the results are

| Functions | Safety theorems (required) | Page |
| --- | --- | --- |
| `compress`, `compress_z`, `compress2`, `compress2_z` | `compress_safety`, `compress_z_safety`, `compress2_safety`, `compress2_z_safety` (`ZlibF/Proof/public-compress-safe-mid.lean`) | [Safety of `compress*`](compress-safety.md) |
| `uncompress`, `uncompress_z`, `uncompress2`, `uncompress2_z` | `uncompress_safe`, `uncompress_z_safe`, `uncompress2_safe`, `uncompress2_z_safe` (`ZlibF/Proof/public-uncompress-safe.lean`) | [Safety of `uncompress*`](uncompress-safety.md) |
| `deflateBound`, `deflateBound_z` | `deflateBound_safety`, `deflateBound_z_safety` (`ZlibF/Proof/public-stream-call-safety.lean`) | [Stream compression](deflate.md) |
| `compressBound`, `compressBound_z` | `compressBound`, `compressBound_z` (`ZlibF/Proof/public-compress-bound.lean`): the exact value of the formula. The functions read no memory, so the manifest uses these full contracts as their safety goals | [Safety of `compress*`](compress-safety.md#the-bound-functions) |

These theorems are [registered](../checking/README.md) and
[accepted](../checking/README.md) on commit `bde170e9`
([progress, Scope](../progress.md#scope)). The functional contracts of these functions, such as
the bytes that `uncompress` writes or that every compressor output fits the bound, are not
required for the safety results.

A reading of the C that no theorem states is marked **to confirm**.

## The decisions

### The local stream is automatic storage

- **C.** `compress2_z` and `uncompress2_z` declare `z_stream stream;` as a local. Creating it
  cannot fail and is not a call of the allocator.
- **Model.** The local stream is a fresh record made by `allocLocalZ`. It does not consume a
  call of the allocation-failure oracle and does not shift the index of the library's own
  allocations. It is released before every return. Scalar locals whose address is taken are
  treated the same way.
- **Status.** Covered: the safety theorems run the translation with this local and prove that
  nothing stays allocated. The
  [allocation regression](../../tests/regression/compress-allocation/README.md) compares return
  codes, stored lengths, allocation attempts and live blocks with the C for each failing
  allocation index. That is evidence, not proof.

### The wrappers read their length cells before the `_z` call

- **C.** `compress2` executes `z_size_t got = *destLen;` before it calls `compress2_z`.
  `uncompress2` reads `*destLen` and `*sourceLen` in the same way. The `NULL` tests inside the
  `_z` functions come too late to protect these reads: a `NULL` cell is undefined behaviour in
  the wrapper.
- **Model.** A `NULL` cell in `compress2`, `compress`, `uncompress2` or `uncompress` is
  `Fault.ub`.
- **Status.** The safety goals of these four functions take a non-`NULL` cell; the `_z` forms
  admit `NULL` and refuse it with `Z_STREAM_ERROR`. `zlib.h` does not offer `NULL` cells for the
  wrappers. The allocation regression holds a witness program for the read; a call with a
  `NULL` cell is not a row of the comparison, because it is not a valid call.

### The length cell of `compress*` is a value, not memory

- **C.** `destLen` points to a caller cell. `compress2_z` reads it, and stores the output length
  through it at the end.
- **Model.** The translation takes the value of `*destLen` (`none` for `NULL`) and returns the
  stored value as a second result
  ([translation](../design/translation.md#the-accepted-normalisations)). The cell is not memory.
- **Status.** This limits the safety goals: a length cell that overlaps the source or the
  destination cannot be expressed, so such a call is outside the theorems. The row
  "Whole-buffer compression" of [deviations](../deviations.md) records it. The length cells of
  `uncompress*` are memory, eight-byte blocks, and their separation from the buffers and from
  each other is an explicit premise (row "Counted decompression").

### A `NULL` destination with zero capacity in `compress2_z`

- **C.** `dest == NULL` with `*destLen == 0` passes the argument checks. At the end the function
  computes `stream.next_out - dest`, with both pointers `NULL`.
- **Model.** The general pointer difference `Ptr.diff` faults on `NULL`. The translation of
  this one statement uses `ptrDiff`, which returns 0 for `NULL - NULL`
  (`ZlibF/Zlib/compress.c.lean`).
- **Status.** The safety theorems are proved for the translation with this allowance. Whether
  the C language defines `NULL - NULL` for the selected build is **to confirm**; equal results
  and silent sanitizers do not settle it. It is a trusted-base item, not an open proof step
  ([safety, null pointers](../spec/safety.md#null-pointers-and-pointer-differences)).

### The dummy output pointer of `uncompress2_z`

- **C.** For `dest == NULL` with `*destLen == 0` the function sets
  `dest = (Bytef *)&stream.reserved`, because `next_out` may not be `NULL`. The pointer is only
  ever passed as `next_out` with `avail_out == 0`.
- **Model.** The dummy is a separate local eight-byte block, released before every return. The
  model does not represent that it is part of the stream record.
- **Status.** `uncompress2_z_safe` covers this case for the translation. **To confirm**: with
  `avail_out == 0` the decoder writes nothing through `next_out`, so the difference between a
  field of the record and a separate block cannot be observed.

### The loops refill 32-bit counts from 64-bit lengths

- **C.** `avail_in` and `avail_out` are `unsigned`; the remaining lengths are `z_size_t`. Each
  loop trip refills an empty count with at most `(uInt)-1` bytes. The loop continues only on
  `Z_OK`. `deflateEnd` or `inflateEnd` runs after a successful init, and the return code is
  mapped at the end.
- **Model.** The translation keeps these statements one by one.
- **Status.** Covered by the safety theorems; their termination measures are on the two safety
  pages. A late memory failure of the decoder can follow output that is already written: the
  safety goal of `uncompress*` allows `Z_MEM_ERROR` with a nonempty output.

### `compressBound_z`: wrapped additions and saturation

- **C.** The formula uses wrapping `z_size_t` additions and returns the maximum value when the
  sum wrapped.
- **Model.** A pure function on `UInt64`.
- **Status.** `compressBound` and `compressBound_z` prove the exact value for every input. That
  every compressor output fits the bound is a separate, functional statement, which the safety
  results do not need.

### `deflateBound_z`: `2 + extra_len` is computed in 32 bits

- **C.** `deflateBound_z` reads the wrapper state and the optional gzip header strings; each
  string scan includes the terminating NUL. For the extra field it adds `2 + extra_len`,
  evaluated as 32-bit `unsigned`, to the 64-bit wrapper cost. For `extra_len >= 0xfffffffe` that
  sum wraps, while the header writer emits only `extra_len & 0xffff` bytes.
- **Model.** The translation computes the same wrapped sum.
- **Status.** Safety is covered (`deflateBound_safety`, `deflateBound_z_safety`). The point
  concerns the value of the bound, not safety. For `extra_len` of `2^32 - 2` and `2^32 - 1` the
  bound is too small; this is reproduced on the C
  ([finding](../findings/deflatebound-extra-len/README.md)). A correction with
  `2 + (z_size_t)(extra_len & 0xffff)` was proposed in an
  [upstream discussion](https://github.com/madler/zlib/pull/1360); no patch for it is applied
  (`patches/README.md` lists the patches). Whether the output fits the bound is a functional
  question, which the safety results do not need. A second finding shows a configuration in
  which it does not: [`Z_FIXED` at levels 1 to 3](../findings/deflatebound-fixed-far-matches/README.md).
  **To confirm**: that the output fits the bound on the rest of the source and header domain.
