# Safety of `uncompress*`

`uncompress`, `uncompress_z`, `uncompress2` and `uncompress2_z` are safe on every input that
meets the premises below, whatever the source bytes are: the call returns, has no undefined
behaviour, writes only the destination buffer and the length cells, and frees everything it
allocated. This page gives the statement, its premises and the shape of the proof.

Source: `uncompr.c`. [Buffer utilities](buffers.md) reads the C. Terms:
[glossary](../glossary.md).

## What is proved

| Goal (`ZlibF/Spec/Safety/Utilities.lean`) | Theorem | Module |
| --- | --- | --- |
| `Goal.uncompress2_z_safe` | `uncompress2_z_safe` | `ZlibF/Proof/public-uncompress-safe.lean` |
| `Goal.uncompress2_safe` | `uncompress2_safe` | same |
| `Goal.uncompress_z_safe` | `uncompress_z_safe` | same |
| `Goal.uncompress_safe` | `uncompress_safe` | same |

All four are safety results and are required. Each theorem proves its goal exactly as stated,
with no hypothesis added; the premises below are part of the goal statements. The theorems are
[registered](../checking/README.md) in `tests/audit/theorems.txt` and
[accepted](../checking/README.md) on commit `bde170e9`
([progress, Scope](../progress.md#scope)).

The goals are instances of `UncompressCountedSafe` and `UncompressSingleSafe`
(`ZlibF/Spec/Public/Utilities.lean`). For every input that meets the premises below:

- the call runs without undefined behaviour and returns. In Lean: running the translated
  function on the heap gives `.ok` with a return code and a new heap, not a fault;
- an argument error returns `Z_STREAM_ERROR` and changes nothing;
- otherwise the call writes at most `capacity` bytes into the output buffer, writes the length
  cells, and writes nothing else. The destination-length cell then holds the number of bytes
  written. The goal admits one exception: `Z_MEM_ERROR` with nothing written and both cells
  holding the values they had. That is the return after a failed `inflateInit`, where the C
  does not store through the cells;
- every allocation is freed on every return path;
- the code is `Z_OK`, `Z_BUF_ERROR`, `Z_DATA_ERROR` or `Z_MEM_ERROR`, and `Z_MEM_ERROR` comes
  only after an allocation failed.

Nothing is said about the bytes written. That is the functional goal `Goal.uncompress*`,
which is not required for the safety results.

## What is assumed

| Premise | Meaning |
| --- | --- |
| `Fresh`, `Uniq`, `LibraryGlobals` | The caller heap is well formed and the static tables are the initial ones. |
| `ByteObjectsFit` | Every byte object has fewer than `2^63` bytes. |
| Length cells (`LengthCell`) | Each non-`NULL` length pointer names eight readable and writable bytes. They hold the length in little-endian order: the capacity in `*destLen`, the source length in `*sourceLen`. `uncompress` and `uncompress2` take non-`NULL` cells; the `_z` forms admit `NULL` and refuse it. `uncompress` and `uncompress_z` pass the source length as a value and have no source-length cell. |
| Readable source, writable destination | A non-`NULL` `source` is readable for the source length. A non-`NULL` `dest` is writable for the capacity. |
| Separation, `uncompress2` and `uncompress2_z` (`UtilitySeparation`) | Source, destination, the destination-length cell and the source-length cell are pairwise separate: six conditions. |
| Separation, `uncompress` and `uncompress_z` | Three `Separate` premises of `UncompressSingleSafe`: source and destination; the destination-length cell and the destination; the destination-length cell and the source. |

Two ranges are separate (`Separate`, `ZlibF/Spec/Public/Memory.lean`) when one of them is empty,
or they lie in different blocks, or their byte ranges in one block do not overlap.

The separation has a row in [deviations](../deviations.md), "Counted decompression".

## Structure

```mermaid
flowchart TD
  init["start_state: inflateInit2_ on the local stream"] --> loop
  loop["loop_run_safe: do ... while (err == Z_OK)"] --> call
  call["call_phase_safe: one inflate call (inflate_public)"] --> loop
  loop --> epi["epilogue: store the counts, inflateEnd, free the stream and the dummy output block"]
  epi --> z["uncompress2_z_with_safe"]
  z --> w2["counted2_of_z: uncompress2"]
  z --> w1["single_of_counted: uncompress_z, uncompress"]
```

The proof is written once, for any relation on the result (`CountedWith`, `SingleWith`). The
safety goals instantiate it with `SafeRel`: the output fits the capacity, the consumed input
fits the source, and the return code is one of the documented ones. `SafeState` and `SafeFinal`
are the loop state and the final state of that proof; they hold everything but the format
fact. The functional proof, which is not required for the safety results, extends them with
`NoOver`: no complete stream at the start of the source has been read to its end.

## What the proof uses

- `inflate_public`, the full contract of one `inflate` call (`Goal.inflate`), for each call.
  `Goal.inflate` is a functional contract. The safety proof uses its progress, frame and
  ownership clauses.
- `reach_invariant`, for the decoder of every reachable stream.

No format fact of `inflate` is used.

## Termination

The measure is the unread source plus the unfilled room:
`avail_in + len + avail_out + left`, where `len` and `left` are the C locals: the source bytes
and the destination room not yet given to the stream. The refills move bytes between the stream fields and the
remaining lengths, so they keep it. Each call that returns `Z_OK` consumes input or writes
output. This is the progress clause of `Goal.inflate`,
`rc = Z_OK → (used ≠ 0 ∨ out ≠ []) ∧ flush ≠ Z_FINISH`; the proof uses its first part. So the
measure falls. At the start it is at most `sourceLen + destLen`, which is below `2^64`, the loop
fuel.
The rule is `cdoWhile_decreasing`.
