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
| `compress`, `compress_z`, `compress2`, `compress2_z` | `compress_safety`, `compress_z_safety`, `compress2_safety`, `compress2_z_safety` | [Safety of `compress*`](compress-safety.md) |
| `uncompress`, `uncompress_z`, `uncompress2`, `uncompress2_z` | `uncompress_safe`, `uncompress_z_safe`, `uncompress2_safe`, `uncompress2_z_safe` | [Safety of `uncompress*`](uncompress-safety.md) |
| `deflateBound`, `deflateBound_z` | `deflateBound_safety`, `deflateBound_z_safety` | [Stream compression](deflate.md) |
| `compressBound`, `compressBound_z` | `compressBound`, `compressBound_z`: the exact value of the formula. The functions read no memory, so these full contracts are also their safety goals | [Safety of `compress*`](compress-safety.md#the-bound-functions) |

The functional contracts of these functions, such as the bytes that `uncompress` writes or that
every compressor output fits the bound, are not required for the safety results.

A reading of the C that no theorem states is marked **to confirm**.

## The decisions

### The local stream is automatic storage

- **C.** `compress2_z` and `uncompress2_z` declare `z_stream stream;` as a local. Creating it
  cannot fail and is not a call of the allocator.
- **Model.** The local stream is a fresh record made by `allocLocalZ`. It does not consume a
  call of the allocation-failure oracle and does not shift the index of the library's own
  allocations. It is released before every return. Scalar locals whose address is taken are
  treated the same way.
- **Coverage.** Covered: the safety theorems run the translation with this local and prove that
  nothing stays allocated. An
  [allocation test](../../tests/regression/compress-allocation/README.md) compares return
  codes, stored lengths, allocation attempts and live blocks with the real C for each failing
  allocation index. That is evidence, not proof.

### The wrappers read their length cells before the `_z` call

- **C.** `compress2` executes `z_size_t got = *destLen;` before it calls `compress2_z`.
  `uncompress2` reads `*destLen` and `*sourceLen` in the same way. The `NULL` tests inside the
  `_z` functions come too late to protect these reads: a `NULL` cell is undefined behaviour in
  the wrapper.
- **Model.** A `NULL` cell in `compress2`, `compress`, `uncompress2` or `uncompress` is
  `Fault.ub`.
- **Coverage.** The safety goals of these four functions take a non-`NULL` cell; the `_z` forms
  admit `NULL` and refuse it with `Z_STREAM_ERROR`. `zlib.h` does not offer `NULL` cells for the
  wrappers.

### The length cell of `compress*` is a value, not memory

- **C.** `destLen` points to a caller cell. `compress2_z` writes it twice. After the argument
  checks it reads the capacity and stores 0 at once (`left = *destLen; *destLen = 0;`). After
  the loop it stores the output length. So a return after a failed `deflateInit` leaves 0 in the
  cell, and a refused call does not write the cell. `compress2` copies the cell into a local,
  passes the local to `compress2_z`, and copies it back on every return.
- **Model.** The translation takes the value of `*destLen` (`none` for `NULL`) and returns the
  value the cell holds at the return as a second result: the value passed in for a refused call,
  0 after a failed `deflateInit`, and the output length otherwise
  ([translation](../design/translation.md#the-accepted-normalisations)). The cell is not memory.
- **Coverage.** This limits the safety goals: a length cell that overlaps the source or the
  destination cannot be expressed, so such a call is outside the theorems. The row
  "Whole-buffer compression" of [deviations](../deviations.md) records it.

### The length cells of `uncompress*` are memory

- **C.** `uncompress2_z` reads `*sourceLen` and `*destLen` after the argument checks and writes
  them once, after the loop (`*sourceLen -= len; *destLen -= left;`). A refused call and a
  return after a failed `inflateInit` do not write them. `uncompress2` copies both cells into
  locals and copies them back on every return.
- **Model.** Each cell is an eight-byte block that holds the value in little-endian order.
- **Coverage.** Covered by the safety theorems. That the cells are separate from the buffers and
  from each other is an explicit premise of the goals (row "Counted decompression" of
  [deviations](../deviations.md)).

### A `NULL` destination with zero capacity in `compress2_z`

- **C.** `dest == NULL` with `*destLen == 0` passes the argument checks. At the end the function
  computes `stream.next_out - dest`, with both pointers `NULL`.
- **Model.** The general pointer difference `Ptr.diff` faults on `NULL`. The translation of
  this one statement uses `ptrDiff`, which returns 0 for `NULL - NULL`.
- **Coverage.** The safety theorems are proved for the translation with this allowance.
  **To confirm**: that the selected build defines `NULL - NULL`; the C standard (C17, C23)
  leaves it undefined. It is a trusted-base item
  ([safety, null pointers](../spec/safety.md#null-pointers-and-pointer-differences)).

### The dummy output pointer of `uncompress2_z`

- **C.** For `dest == NULL` with `*destLen == 0` the function sets
  `dest = (Bytef *)&stream.reserved`, because `next_out` may not be `NULL`. The pointer is only
  ever passed as `next_out` with `avail_out == 0`.
- **Model.** The dummy is a separate local eight-byte block, released before every return. The
  model does not represent that it is part of the stream record.
- **Coverage.** `uncompress2_z_safe` covers this case for the translation. **To confirm**: with
  `avail_out == 0` the decoder writes nothing through `next_out`, so the difference between a
  field of the record and a separate block cannot be observed.

### The loops refill 32-bit counts from 64-bit lengths

- **C.** `avail_in` and `avail_out` are `unsigned`; the remaining lengths are `z_size_t`. Each
  loop trip refills an empty count with at most `(uInt)-1` bytes. The loop continues only on
  `Z_OK`. `deflateEnd` or `inflateEnd` runs after a successful init, and the return code is
  mapped at the end.
- **Model.** The translation keeps these statements one by one.
- **Coverage.** Covered by the safety theorems; their termination measures are on the two safety
  pages. A late memory failure of the decoder can follow output that is already written: the
  safety goal of `uncompress*` allows `Z_MEM_ERROR` with a nonempty output.

### `compressBound_z`: wrapped additions and saturation

- **C.** The formula uses wrapping `z_size_t` additions and returns the maximum value when the
  sum wrapped.
- **Model.** A pure function on `UInt64`.
- **Coverage.** `compressBound` and `compressBound_z` prove the exact value for every input.

### `deflateBound_z`: `2 + extra_len` is computed in 32 bits

- **C.** `deflateBound_z` reads the wrapper state and the optional gzip header strings; each
  string scan includes the terminating NUL. For the extra field it adds `2 + extra_len`,
  evaluated as 32-bit `unsigned`, to the 64-bit wrapper cost. For `extra_len >= 0xfffffffe` that
  sum wraps, while the header writer emits only `extra_len & 0xffff` bytes.
- **Model.** The translation computes the same wrapped sum.
- **Coverage.** Safety is covered (`deflateBound_safety`, `deflateBound_z_safety`). The value of
  the bound has two defects in upstream zlib.
    - For `extra_len` of `2^32 - 2` and `2^32 - 1` the bound is too small, as a run of the C
      shows ([finding](../findings/deflatebound-extra-len/README.md)). No patch is applied.
      Upstream knows the case ([discussion](https://github.com/madler/zlib/pull/1360)).
    - With `windowBits` 15, `memLevel` 8, `Z_FIXED` and level 1 to 3 the output can exceed the
      bound, as a run of the C shows
      ([finding](../findings/deflatebound-fixed-far-matches/README.md)). The local patch 0006
      gives `Z_FIXED` the conservative bound.

    **To confirm**: that the output fits the bound on the rest of the source and header domain.
