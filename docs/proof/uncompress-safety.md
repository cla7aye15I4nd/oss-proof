# Safety of `uncompress*`

Source: `uncompr.c`. `uncompress`, `uncompress_z`, `uncompress2` and `uncompress2_z` are safe
on every input. This page explains that result.

## What is proved

| Goal (`ZlibF/Spec/Safety/Utilities.lean`) | Theorem | Module |
| --- | --- | --- |
| `Goal.uncompress2_z_safe` | `uncompress2_z_safe` | `ZlibF/Proof/public-uncompress-safe.lean` |
| `Goal.uncompress2_safe` | `uncompress2_safe` | same |
| `Goal.uncompress_z_safe` | `uncompress_z_safe` | same |
| `Goal.uncompress_safe` | `uncompress_safe` | same |

All four are safety results and are required. They have no hypothesis. They are registered in
`tests/audit/theorems.txt` and accepted on commit `bde170e9`
([progress, Scope](../progress.md#scope)).

The goals are instances of `UncompressCountedSafe` and `UncompressSingleSafe`
(`ZlibF/Spec/Public/Utilities.lean`). For every admitted input:

- the call runs without undefined behaviour and returns (`C.run … = .ok`);
- an argument error returns `Z_STREAM_ERROR` and changes nothing;
- otherwise the call writes at most `capacity` bytes into the output buffer and the length
  cells, and nothing else;
- every allocation is freed on every return path;
- the code is `Z_OK`, `Z_BUF_ERROR`, `Z_DATA_ERROR` or `Z_MEM_ERROR`, and `Z_MEM_ERROR` comes
  only after an allocation failed.

Nothing is said about the bytes written. That is the functional goal `Goal.uncompress*`,
which is not required.

## What is assumed

| Premise | Meaning |
| --- | --- |
| `Fresh`, `Uniq`, `LibraryGlobals` | The caller heap is well formed and the static tables are the initial ones. |
| `ByteObjectsFit` | Every byte object has fewer than `2^63` bytes. |
| Readable source, writable destination, length cells | Each non-null pointer names a range or an eight-byte cell of the stated size. |
| `UtilitySeparation` | Source, destination, the destination-length cell and the source-length cell are pairwise separate. |

The separation has a row in [deviations](../deviations.md), "Counted decompression".

## Structure

```mermaid
flowchart TD
  init["start_state: inflateInit2_ and the bound stream"] --> loop
  loop["loop_run_safe: do ... while (err == Z_OK)"] --> call
  call["call_phase_safe: one inflate call (inflate_public)"] --> loop
  loop --> epi["epilogue: store the counts, inflateEnd, free the stream and the reserved byte"]
  epi --> z["uncompress2_z_with_safe"]
  z --> w2["counted2_of_z: uncompress2"]
  z --> w1["single_of_counted: uncompress_z, uncompress"]
```

The run is shared with the functional proof. `SafeState` and `SafeFinal` hold everything but
the format fact. The functional proof extends them with `NoOver`: no complete stream at the
start of the source has been read to its end. The wrappers are proved once for every data
relation (`CountedWith`, `SingleWith`). The safety goals use the relation `SafeRel`: the
output fits the capacity, the consumed input fits the source, and the code is documented.

## What the proof uses

- `inflate_public`, the full contract of one `inflate` call (`Goal.inflate`), for each call.
  `Goal.inflate` is a functional contract. The safety proof uses its progress, frame and
  ownership clauses.
- `reach_invariant`, for the decoder of every reachable stream.

No format fact of `inflate` is used.

## Termination

The measure is the unread source plus the unfilled room:
`avail_in + len + avail_out + left`. The refills move bytes between the stream fields and the
remaining lengths, so they keep it. Each call that returns `Z_OK` consumes input or writes
output, by the progress clause of `Goal.inflate`: `rc = Z_OK → used ≠ 0 ∨ out ≠ []`. So the
measure falls. At the start it is at most `sourceLen + destLen < 2^64`, below the loop fuel.
The rule is `cdoWhile_decreasing`.
