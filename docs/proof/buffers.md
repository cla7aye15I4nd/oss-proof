# Buffer utilities and output bounds

Source: `compress.c`, `uncompr.c` and the bound entries in `deflate.c`. The
[API contracts](../spec/api/utility.md) give the caller obligations.

This page reads the C of the whole-buffer functions and records the source decisions that
their proofs depend on. The proofs themselves are on two other pages.

| Functions | Safety (required) | Page |
| --- | --- | --- |
| `compress`, `compress_z`, `compress2`, `compress2_z` | `compress_safety`, `compress_z_safety`, `compress2_safety`, `compress2_z_safety` (`ZlibF/Proof/public-compress-safe-mid.lean`) | [Safety of `compress*`](compress-safety.md) |
| `uncompress`, `uncompress_z`, `uncompress2`, `uncompress2_z` | `uncompress_safe`, `uncompress_z_safe`, `uncompress2_safe`, `uncompress2_z_safe` (`ZlibF/Proof/public-uncompress-safe.lean`) | [Safety of `uncompress*`](uncompress-safety.md) |
| `deflateBound`, `deflateBound_z` | `deflateBound_safety`, `deflateBound_z_safety` (`ZlibF/Proof/public-stream-call-safety.lean`) | [Stream compression](deflate.md) |
| `compressBound`, `compressBound_z` | `compressBound`, `compressBound_z` (`ZlibF/Proof/public-compress-bound.lean`). The manifest uses the full contract, the exact value of the formula, as the safety goal: the functions read no memory | this page |

The safety theorems are accepted on commit `bde170e9`
([progress, Scope](../progress.md#scope)). The functional contracts of these functions, such
as the bytes that `uncompress` writes or that every compressor output fits the bound, are not
required.

A source reading that no theorem states is marked **to confirm**.

## Bounds and buffer utility wrappers

`compressBound_z` uses wrapped additions and a saturation test. A proof of the
formula alone does not show that every compressor output fits it.
`deflateBound_z` also reads wrapper state and optional header strings. Each
scan includes the terminating null. It normalizes a negative `wrap` after
finishing and retains every overflow guard.

One point of `deflateBound_z` concerns the value of the bound, not safety:
`2 + extra_len` is evaluated as 32-bit unsigned before addition to the 64-bit
wrapper cost. For `extra_len >= 0xfffffffe` it wraps, whereas emission uses only
`extra_len & 0xffff`. A proposed correction used
`2 + (z_size_t)(extra_len & 0xffff)`
([upstream discussion](https://github.com/madler/zlib/pull/1360)). No patch for
it is applied; `patches/README.md` lists the patches. **to confirm**: the output
bound follows for its stated source and header domain. That is a functional
question and is not required.

`compress2_z` and `uncompress2_z` have automatic local streams. Creating them
must not fail, consume an allocator-oracle call or shift the failure index of
library allocations. Address-taken scalar locals also have automatic lifetime.
Model storage is released on every source return without adding a C allocation.
The [allocation regression](../../tests/regression/compress-allocation/README.md)
records the corrected distinction and error-ordering observations.

The utility loops refill 32-bit availability fields from wider remaining
lengths. They continue only on `Z_OK`, call `End` after successful initialization,
and retain result mapping and final scalar writes. Late decoder memory failure
can follow emitted output; it does not imply an empty destination.

Two source decisions matter to the statements:

- **R-2, wrapper null reads.** `compress2` reads `*destLen` before its `_z` call;
  `uncompress2` reads both scalar cells. The `_z` null tests cannot protect those
  reads. Separate execution witnesses diagnosed them. They are not valid-call
  comparison rows.
- **D-4, null subtraction.** `compress2_z` computes `next_out - dest` after a
  zero-capacity null destination. Its translation explicitly allows null minus
  null to be zero. Whether that matches the selected C language semantics is
  **to confirm**. Equal results and silent sanitizers cannot settle it.

The compressor adapter represents its length pointer as an optional input and a
returned value. It cannot express aliases with byte buffers. Counted
decompressor adapters also have scalar separation limits. Both limits are rows
in [deviations](../deviations.md). A call outside them is outside the theorems.

`uncompress2_z` uses the address of its local stream's `reserved` field as a
non-null dummy output at zero capacity. A separate represented byte can model
that use only if it is never dereferenced and its lifetime and aliasing are
accounted for. **to confirm**: zero capacity excludes a write through it during
the actual decoder call.

