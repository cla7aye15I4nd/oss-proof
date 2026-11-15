# Utilities: allocation and constant queries

`zutil.c` holds the default allocator (`zcalloc`, `zcfree`) and three constant queries. The two
documented queries, `zlibVersion` and `zlibCompileFlags`, are safe. The allocator wrappers have
exact ownership effects: a successful allocation adds one live block, a failed one adds none,
and a free removes exactly its block. This page states those results and says which facts the
stream proofs take from them and which they prove themselves.

Sources: `zlib/zutil.c` and `zlib/zutil.h`; translation: `ZlibF/Zlib/zutil.c.lean`. The public
contracts are in the [API page](../spec/api/utility.md). Terms: [glossary](../glossary.md).

## What is proved

| Result | Kind | Theorem | Module |
| --- | --- | --- | --- |
| `Goal.zlibVersion_safety`, `Goal.zlibCompileFlags_safety` (`ZlibF/Spec/Safety/Queries.lean`) | Safety, required | `zlibVersion_safety`, `zlibCompileFlags_safety` | `ZlibF/Proof/public-stateless-safety.lean` |
| `Goal.zlibVersion`, `Goal.zlibCompileFlags` | Functional | `zlibVersion`, `zlibCompileFlags` | `ZlibF/Proof/public-zlib-version.lean`, `ZlibF/Proof/public-zlib-compile-flags.lean` |
| `Goal.zError` | Not required: `zlib.h` lists `zError` as undocumented | `zError` | `ZlibF/Proof/public-zerror.lean` |
| The allocator wrappers `zcalloc` and `zcfree` | Internal, used by every stream proof | `zcalloc_safe`, `zcalloc_correct_some`, `zcalloc_correct_size`, `zcalloc_correct_none`, `zcfree_safe`, `zcfree_correct`, `zcfree_correct_null`, `zcalloc_zcfree_no_leak` | `ZlibF/Proof/zutil.c.lean` |

All of these are [registered](../checking/README.md) in `tests/audit/theorems.txt` and
[accepted](../checking/README.md) on commit `bde170e9`
([progress, Scope](../progress.md#scope)).

`zcalloc` and `zcfree` are not public functions. Leak freedom of a stream is a clause of the
sequence safety theorems of [inflate](inflate.md) and [deflate](deflate.md), which use these
wrapper results at each allocation and free.

## What the wrapper theorems state

On this build `zcalloc` calls `malloc`, despite its name, and does not zero the block.

| Theorem | Statement |
| --- | --- |
| `zcalloc_safe` | On a `Fresh` heap, for every `items` and `size`, the call returns. Either it returns `NULL` and only the allocation counter moves, or it returns the start of a new writable byte block and adds exactly that block to the live blocks. |
| `zcalloc_correct_some` | When the oracle lets the call succeed, the block is writable, its size is `items * size` reduced modulo `2^32`, and its content is arbitrary. |
| `zcalloc_correct_size` | When `items * size` is below `2^32`, the block has exactly `items * size` bytes. |
| `zcalloc_correct_none` | When the oracle refuses, the result is `NULL` and the heap changes only in the call counter. |
| `zcfree_safe` | For `NULL`, or the start of a live writable byte block, the call returns: `NULL` changes nothing, otherwise exactly that block is removed. |
| `zcfree_correct`, `zcfree_correct_null` | Freeing a live block removes exactly that block from the live blocks; freeing `NULL` changes nothing. |
| `zcalloc_zcfree_no_leak` | `zcalloc` followed by `zcfree` of its result returns, also when the allocation failed, and the set of live blocks is the one before. |

## What the stream proofs prove themselves

The wrapper theorems say nothing about the following. The init, copy and end theorems of
[inflate](inflate.md) and [deflate](deflate.md) prove each of them.

- **The product does not wrap.** `zcalloc(opaque, items, size)` computes `items * size` in
  32-bit `unsigned` arithmetic. A caller that relies on the ordinary product shows that it is
  below `2^32` and then uses `zcalloc_correct_size`. The table below gives the largest products
  of the stream allocations.
- **Fields are written before they are read.** A fresh block has arbitrary integers, and a
  fresh record has `NULL` pointers in the model
  ([uninitialised memory](../spec/safety.md#uninitialised-memory)). An allocation does not make
  a pointer field safe to read.
- **Each block is freed exactly once.** A non-null free needs the block to be live. The heap
  stores liveness; the proofs' `Owns` relation assigns the live blocks to a stream, and the end
  and failure-cleanup proofs free each owned block once.
- **Cleanup after a failed allocation.** `deflateInit2_` allocates a state and four buffers and
  tests the four buffer results together, after all four calls. So a failed earlier allocation
  does not stop the later ones, and the cleanup frees every allocation of that attempt that
  succeeded. `inflateInit2_`, the delayed allocation of the decoder window, and both copy
  functions have their own failure cases.

| Stream allocation on this build | Largest `items * size` in bytes |
| --- | --- |
| Compressor window: `w_size * 2` | 65536 |
| Compressor `prev`: `w_size * sizeof(Pos)` | 65536 |
| Compressor `head`: `hash_size * sizeof(Pos)` | 131072 |
| Compressor pending buffer: `lit_bufsize * 4` | 131072 |
| Decoder window: `(1U << wbits) * 1` | 32768 |
| `deflateCopy`, `inflateCopy` | The corresponding buffer sizes above |

The state records (`deflate_state`, `inflate_state`) are allocated as records of the model, so
their `sizeof` does not enter a product. The buffer bounds follow from the validated parameters
and from the size equations kept in the stream invariant. The table covers the stream
allocations shown; it is not a maximum for the gz functions or for other paths.

## Constant and error queries

| Function | Result and frame |
| --- | --- |
| `zlibVersion` | It returns the pointer to the version string, a read-only static, with the contents the contract gives. The heap is unchanged. |
| `zlibCompileFlags` | It returns the flags derived from the type widths and enabled source branches of this build: 169. The heap is unchanged. |
| `zError(err)` (not required) | The out-of-range branch selects entry 9 of the ten-entry message table. Otherwise `-6 ≤ err ≤ 2`, so `2 - err` is in `[0, 8]` without signed overflow. It returns that entry, a read-only static. The heap is unchanged. |

`zError` tests the range of `err` before it evaluates `2 - err`; a subtraction done first could
overflow for an arbitrary `int`. The value 169 holds for this build only: other type widths or
build options give other flags.

A constant return is still an exact contract: a wrong version pointer or a changed flag bit
fails the function's proof mutant ([proof mutants](../checking/proof-mutants.md)).
