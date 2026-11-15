# Utilities: allocation and constant queries

Sources: `zlib/zutil.c` and `zlib/zutil.h`; translation:
`ZlibF/Zlib/zutil.c.lean`. These functions support both stream implementations.
Their public contracts are in the [API page](../spec/api/utility.md), and their
ownership role is defined in [safety](../spec/safety.md).

The two documented queries are safe, and the allocator wrappers have exact
ownership effects. This page explains the size arithmetic that the stream
proofs take from the allocator, and the constant queries.

## What is proved

| Result | Kind | Theorem | Module |
| --- | --- | --- | --- |
| `Goal.zlibVersion_safety`, `Goal.zlibCompileFlags_safety` (`ZlibF/Spec/Safety/Queries.lean`) | Safety, required | `zlibVersion_safety`, `zlibCompileFlags_safety` | `ZlibF/Proof/public-stateless-safety.lean` |
| `Goal.zlibVersion`, `Goal.zlibCompileFlags` | Functional, stays | `zlibVersion`, `zlibCompileFlags` | `ZlibF/Proof/public-zlib-version.lean`, `ZlibF/Proof/public-zlib-compile-flags.lean` |
| `Goal.zError` | Not required: `zlib.h` lists `zError` as undocumented | `zError` | `ZlibF/Proof/public-zerror.lean` |
| The allocator wrappers `zcalloc` and `zcfree` | Internal, used by every stream proof | `zcalloc_safe`, `zcalloc_correct_some`, `zcalloc_correct_size`, `zcalloc_correct_none`, `zcfree_safe`, `zcfree_correct`, `zcfree_correct_null`, `zcalloc_zcfree_no_leak` | `ZlibF/Proof/zutil.c.lean` |

All of these are registered in `tests/audit/theorems.txt` and accepted on commit
`bde170e9` ([progress, Scope](../progress.md#scope)).

`zcalloc` and `zcfree` are not public functions. Leak freedom of a stream is a
clause of the sequence safety theorems of [inflate](inflate.md) and
[deflate](deflate.md), which use these wrapper results at each allocation and
free.

The default LP64 allocator branch uses `malloc`, despite the name `zcalloc`.
It does not zero the block. Initialization proofs must establish the field
writes they need, including pointer writes that the model does not track.

## Size arithmetic at callers

`zcalloc(opaque, items, size)` computes `items * size` in 32-bit `unsigned`
arithmetic in this branch. `zcalloc_correct_size` describes that product
faithfully. A caller that expects the ordinary product proves that it is below
`2^32` before it relies on the allocated capacity.

| Default stream allocation | Largest product in bytes |
| --- | --- |
| `deflateInit2_` state | LP64 `sizeof(deflate_state)` |
| Compressor window: `w_size * 2` | 65536 |
| Compressor `prev`: `w_size * sizeof(Pos)` | 65536 |
| Compressor `head`: `hash_size * sizeof(Pos)` | 131072 |
| Compressor pending buffer: `lit_bufsize * 4` | 131072 |
| `inflateInit2_` state | LP64 `sizeof(inflate_state)` |
| Decoder window: `(1U << wbits) * 1` | 32768 |
| `deflateCopy`, `inflateCopy` | Corresponding state and buffer sizes above |

The state sizes must come from the selected ABI layout and agree with the C
layout checks. They are not mathematical constants across configurations. The
buffer bounds derive from validated parameters and the size equations retained
in the stream invariant. This table concerns the stream allocations shown; it
does not assert a maximum allocation for every gz or other API path.

## Success and failure effects

On success, allocation adds a fresh live block of the modeled size. On failure,
it returns null and adds no live block. Neither case makes a new pointer field
safe to read before it has been written. Uninitialized integers have arbitrary
values under [the runtime rules](../spec/safety.md#uninitialised-memory).

`zcfree` accepts null or a block permitted by the allocator interface. A non-null
free requires the corresponding live ownership claim. End and failure-cleanup
proofs must supply it exactly once. The heap stores liveness and allocation
history; the proof's `Owns` relation assigns the live blocks to a stream.

`deflateInit2_` allocates a state and four buffers. Its combined buffer-failure
check comes after the buffer allocations, so a failed earlier allocation does
not imply that later ones were never attempted. Cleanup must free all successful
allocations of that attempt, clear or preserve fields as the source specifies
and restore the previous live-block set. `inflateInit2_`, delayed decoder-window
allocation and both copy functions need their own failure-case compositions.
The allocator wrapper alone proves none of that lifecycle cleanup. The init
and copy theorems prove it: see [inflate](inflate.md) and [deflate](deflate.md).

## Constant and error queries

| Function | Required result and frame |
| --- | --- |
| `zError(err)` | The out-of-range branch selects entry 9. Otherwise `-6 ≤ err ≤ 2`, so `2 - err` is in `[0, 8]` without signed overflow. Return the exact entry of the ten-element message table; preserve the heap. |
| `zlibVersion` | Return the selected version string pointer with the static contents required by the contract; preserve the heap. |
| `zlibCompileFlags` | Derive the exact numeric flags from the selected type widths and enabled source branches; preserve the heap. |

A constant return is still an exact contract: a wrong version pointer or a
changed flag bit fails the function's proof mutant
([checking](../checking/README.md)).

## C correspondence checks

`zError` checks the error range before evaluating `2 - err`. Hoisting subtraction
could overflow for an arbitrary `int`. `zlibCompileFlags` yields 169 for the
reviewed configuration; retain its source decisions rather than treat that
number as universal. Returned version and error strings are read-only statics.
