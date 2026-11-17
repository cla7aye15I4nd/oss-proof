# Utilities: allocation and constant queries

`zutil.c` holds the default allocator (`zcalloc`, `zcfree`) and three constant queries. The two
documented queries, `zlibVersion` and `zlibCompileFlags`, are safe. The allocator wrappers have
exact ownership effects: a successful allocation adds one live block, a failed one adds none,
and a free removes exactly its block. This page states those results and says which facts the
stream proofs take from them and which they prove themselves.

Sources: `zlib/zutil.c` and `zlib/zutil.h`, with their Lean translation. The public
contracts are in the [API page](../spec/api/utility.md). Terms: [glossary](../glossary.md).

## What is proved

| Result | Kind | Theorem |
| --- | --- | --- |
| `Goal.zlibVersion_safety`, `Goal.zlibCompileFlags_safety` | Safety, required | `zlibVersion_safety`, `zlibCompileFlags_safety` |
| `Goal.zlibVersion`, `Goal.zlibCompileFlags` | Functional | `zlibVersion`, `zlibCompileFlags` |
| `Goal.zError` | Not required: `zlib.h` lists `zError` as undocumented | `zError` |
| The allocator wrappers `zcalloc` and `zcfree` | Internal, used by every stream proof | `zcalloc_safe`, `zcalloc_correct_some`, `zcalloc_correct_size`, `zcalloc_correct_none`, `zcfree_safe`, `zcfree_correct`, `zcfree_correct_null`, `zcalloc_zcfree_no_leak` |

The five goals of the first three rows are done. The allocator wrapper theorems of the last row
are proved; they are lemmas, not goals.

`zcalloc` and `zcfree` are not public functions. Leak freedom of a stream is a clause of the
sequence safety theorems of [inflate](inflate.md) and [deflate](deflate.md), which use these
wrapper results at each allocation and free.

## What the wrapper theorems state

On this build `zcalloc` calls `malloc`, despite its name, and does not zero the block.

Three terms of the model appear in the premises. A heap is `Fresh` when no block at or above
its next block number is live, so the next allocation gets an unused number. The *allocation
oracle* (`allocOk`) decides for each allocation attempt whether it succeeds; the theorems hold
for every oracle. `h.Owns S` says that the live blocks of the heap `h` are exactly the set `S`.

| Theorem | Premises | Statement |
| --- | --- | --- |
| `zcalloc_safe` | The heap is `Fresh` | For every `items` and `size` the call returns. Either it returns `NULL` and only the allocation counter moves, or it returns the start of a new writable byte block and adds exactly that block to the live blocks. |
| `zcalloc_correct_some` | The heap is `Fresh`; the oracle lets this attempt succeed | The result is the start of a new block. The block is writable, its size is `items * size` reduced modulo `2^32`, and its content is arbitrary. |
| `zcalloc_correct_size` | The heap is `Fresh`; the oracle lets this attempt succeed; `items * size` is below `2^32` | The block has exactly `items * size` bytes. |
| `zcalloc_correct_none` | The oracle refuses this attempt | The result is `NULL`, and the heap changes only in the allocation counter. |
| `zcfree_safe` | The pointer is `NULL`, or the start of a live writable byte block | The call returns. For `NULL` the heap is unchanged; otherwise exactly that byte block is removed. |
| `zcfree_correct` | The pointer is the start of a live byte block `b`; the block is writable; no other table of the heap holds an object under the number `b` (the Lean hypothesis `hother`); `h.Owns S` | The call returns; the live blocks are `S` without `b`; every other byte block is unchanged. |
| `zcfree_correct_null` | None | Freeing `NULL` returns and leaves the heap unchanged. |
| `zcalloc_zcfree_no_leak` | The heap is `Fresh` | `zcalloc` followed by `zcfree` of its result returns, also when the allocation failed, and the set of live blocks is the one before. |

The premises column lists every hypothesis of each theorem. The `opaque` argument is
unrestricted in all of them: the C ignores it.

## What the stream proofs prove themselves

The wrapper theorems say nothing about the following four points. The init, copy and end
theorems of [inflate](inflate.md) and [deflate](deflate.md) prove the first, third and fourth;
the second is not proved for pointer fields.

- **The product does not wrap.** `zcalloc(opaque, items, size)` computes `items * size` in
  32-bit `unsigned` arithmetic. A caller that relies on the ordinary product shows that it is
  below `2^32` and then uses `zcalloc_correct_size`. The table below gives the largest products
  of the stream allocations.
- **Fields are written before they are read.** A fresh block has arbitrary integers, and the
  theorems hold for every value. A fresh record has `NULL` pointers in the model
  ([uninitialised memory](../spec/safety.md#uninitialised-memory)), so a missing write of a
  pointer field does not show in the model. **To confirm** by source review: every pointer
  field is written before it is read.
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

A constant return is still an exact contract: a copy of the translation that returns `NULL` or
another string for the version, or one with a changed flag bit, no longer passes the proof of
that function.
