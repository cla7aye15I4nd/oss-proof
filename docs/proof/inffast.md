# Fast decoding: margins, history and source bits

Source: `zlib/inffast.c`; translation: `ZlibF/Zlib/inffast.c.lean`.
The contract vocabulary is `I-if-*` in
[internal contracts](../spec/internal-contracts.md). Table predicates come
from [table construction](inftrees.md). Window invariant W is explained in
[stream decoding](inflate.md).

`inflate_fast` is an internal function. It has no public goal of its own. Its
theorem states safety under explicit entry conditions, and the two callers,
`inflate` and `inflateBack`, establish those conditions.

## What is proved

| Result | Kind | Theorem | Module |
| --- | --- | --- | --- |
| `Goal.fast_safe` (`ZlibF/Spec/InflateFast.lean`): for every entry environment `Env`, the call returns, and the post `FastPost` gives the frame, the normalised bit buffer and the exact writeback | Safety, internal | `inflate_fast_safe` | `ZlibF/Proof/inffast.c.final.lean` |
| One loop body is safe | Safety, internal | `inflate_fast_body_step_safe` | `ZlibF/Proof/inffast.c.body.lean` |
| A fast call that does not end in `TYPE` or `BAD` strictly consumes output room (`FastProgress`) | Safety (termination of `inflate`) | `inflate_fast_safe_progress` | `ZlibF/Proof/inffast.c.progress.lean` |
| A fast call that does not end in `TYPE` or `BAD` strictly consumes input bits | Safety (termination of `inflateBack`) | `fast_consumes` | `ZlibF/Proof/inffast.c.consume.lean` |
| The static fixed tables have the table shape | Safety, internal | `lenfix_tableSafe`, `distfix_tableSafe` | `ZlibF/Proof/inffast.c.tableok.lean` |
| Source-bit origin and token refinement: a fast step consumes exactly the bits of one format token, and a match copy refines the LZ77 copy | Functional, stays | `actual_body_refines_token`, `actual_body_preserves_origin`, `actual_distance_refines_lz77`, `actual_copy_match_refines_lz77`, `length_lookup_matches_format`, `distance_lookup_matches_format` and the other `*_origin` theorems | `ZlibF/Proof/inffast.c.body-token.lean`, `inffast.c.body-origin.lean` and the modules beside them |

The registered theorems are accepted on commit `bde170e9`
([progress, Scope](../progress.md#scope)).

The required result that uses this page is sequence safety of `inflate`
([stream decoding](inflate.md)) and of `inflateBack`
([callback decoder](callbacks.md)). The functional rows were proved earlier and
stay. They are not required.

A paragraph marked **to confirm** is a reading of the C source that no theorem
named here states in that form. The theorems are checked against the
translation, not against this prose.

## What is assumed

The entry environment (`Env`, `ZlibF/Proof/inffast.c.env.lean`; the structure is `EnvG`, and
`Env` is `EnvG false`, the case of every caller but `inflateBack`, in which the window is
another block than the output) bundles the
premises `I-if-pre-*` below with their witnesses. Input and output lie in heap
byte blocks: distinct blocks, or disjoint ranges of one block. The row "Fast
decoder helpers" in [deviations](../deviations.md) records this. It is an
internal premise: the callers discharge it from their own premises.

## Entry views and loop invariant

`I-if-pre-room` gives mode `LEN`, at least six input bytes and 258 output bytes,
and a readable earlier-output prefix of the outer `inflate` call in the same
output object. Input and output are disjoint. `I-if-pre-bits` gives `bits < 8`
and identifies `hold` with exactly those low buffered bits.
`I-if-pre-tables` supplies initialized, meaningful root/subtable entries.
`I-if-pre-window` supplies the valid history and the default sane-distance mode.

The source forms

```
last = in + (avail_in - 5)
end  = out + (avail_out - 257)
beg  = out - (start - avail_out)
```

Here `beg` starts the outer call's output, not necessarily this fast call's
output. The precondition must justify its pointer subtraction for the actual
buffer view. Write `in0`, `out0` for the fast-call cursors.

At each body entry, use these named invariants:

| Name | Content |
| --- | --- |
| I1 | `in0 ≤ in ≤ in0 + avail_in`; the loop margin gives six readable bytes at the cursor. |
| I2 | `out0 ≤ out`; the loop margin gives 258 writable bytes at the cursor. |
| I3 | `hold < 2^bits`, with body bit counts at most 30 and entry bits below 8. |
| I4 | `beg ≤ out`; the range `[beg, out)` has been produced by the outer call. |

The first body is reached by a `do` loop, so entry premises must supply its
margins directly. Later bodies use `in < last && out < end`.

## Bit counts and the six-byte bound

There are four refill sites for a length/distance pair.

| Site | Guard and read count | Useful bound |
| --- | --- | --- |
| R1, before length lookup | `bits < 15`: read two bytes | Refill leaves 16 to 30 bits. |
| R2, length extras | `bits < op`, `op ≤ 5`: read one byte | Refill leaves at most 12 bits. |
| R3, before distance lookup | `bits < 15`: read two bytes | Refill leaves 16 to 30 bits. |
| R4, distance extras | `bits < op`, `op ≤ 13`: up to two bytes | The guarded refills keep the count at most 28. |

If R1 or R3 is skipped, at least 15 bits are already available. Table meanings
bound a complete code, including its possible subtable lookup, by 15 bits.
R2 provides enough for at most five extras; R4 provides enough for at most 13.
Thus each `bits -= op` removes only available bits. Refills preserve I3, and
the associated shifts stay within their machine widths.

The independent maxima would allow seven input bytes. That combination is
impossible. Suppose R1, R2, R3 and R4 read 2, 1, 2 and 2 bytes. After R1 and a
length code of at most 15 bits, at least one bit remains. After R2 and at most
five length extras, at least `1 + 8 - 5 = 4` remain. After R3 and at most 15
distance-code bits, at least `4 + 16 - 15 = 5` remain. A second R4 byte requires
fewer than five before its first refill, because even that refill left fewer
than `op ≤ 13`. Contradiction.

Each body therefore reads at most six bytes. This is the reason for `last`'s
five-byte subtraction. A literal writes one byte; a match writes at most 258,
from the length table's base/extra interpretation. This justifies `end`'s
257-byte subtraction. The room bounds depend on table semantics, not merely on
allocated table capacity.

## Table reads

A root index `hold & ((1 << rootbits) - 1)` is below `2^rootbits`. T2 supplies
its initialized entry. A link supplies a bounded subtable interval; the masked
subindex lies inside that interval. The table predicate must also establish the
entry's operation, code length and base/extra ranges and that a second-level
entry is not another link. The `goto dolen`/`dodist` paths then terminate after
at most one linked lookup.

Reserved symbols reach the correct error exit. End-of-block reaches the mode
transition prescribed by the caller contract. These exits still require exact
cursor, bit-buffer and state effects.

## Match copies: F3 and F4

Let `done = out - beg`, `dist ≥ 1` be the decoded distance and `3 ≤ len ≤ 258`
the match length.

If `dist ≤ done`, the source starts at `out - dist ≥ beg`. The copy is
sequential: at step k its source is the already produced byte at relative
position `k - dist`. That byte precedes the destination even when source and
destination ranges overlap. This is the DEFLATE repetition rule; replacing the
loop by a disjoint-copy argument would lose it.

If `dist > done`, set `op = dist - done`. The sane-distance check rejects
`op > whave`. After the check, `1 ≤ op ≤ whave ≤ wsize`, so the allocated window
contains the required earlier history. Its three source shapes are:

| Condition | Initial window index | Boundary argument |
| --- | --- | --- |
| `wnext == 0` | `wsize - op` | Copy through the end of the ring. |
| `0 < wnext < op` | `wsize + wnext - op` | Copy `op - wnext` bytes through the end, then up to `wnext` from index 0. |
| `wnext ≥ op` | `wnext - op` | Copy before the current ring cursor. |

Each piece copies only the smaller of its history count and the remaining match
length. If the match outlasts the window contribution, its remaining source is
in output already produced by this call, where the sequential-copy argument
applies. Prove the exact unrolled loop counts, including the positive initial
count for every `do … while (--op)`.

F4 says `whave < wsize` implies `wnext = whave`. In a partial ring, only the
third shape is possible; its source lies in initialized history. In a full ring,
all bytes are history and the wrap shapes are valid. The stronger functional
invariant must identify those bytes with the suffix of the logical output and
dictionary history.

## Rollback and final writeback

The exit returns speculative whole input bytes:

```
len = bits >> 3
in -= len
bits -= len << 3
hold &= (1U << bits) - 1
```

If B bytes were read by this fast call, the accounting invariant gives
`bits ≤ bits_entry + 8B < 8 + 8B`. Hence `len ≤ B` and rollback never precedes
`in0`. The result has fewer than eight buffered bits, so the final mask shift is
valid. The function then writes exact remaining input/output counts and cursors,
`hold`, `bits` and the reached mode back to the stream.

`bits_entry < 8` is essential. Without it rollback could return bytes that this
fast call never read. It is a premise of `Env`. Both callers establish it at
every entry into the fast path: `inflate` in
`ZlibF/Proof/inflate.c.fast-entry.lean`, and `inflateBack` in `LEN_fast_p`
(`ZlibF/Proof/infback.c.safety-fast.lean`).

## From safety to decoding

This section is functional. It is not required; the results it describes were
proved earlier and stay.

The functional loop invariant identifies the consumed low bits with the
original source stream and relate emitted literals/matches to independent
format symbols. The relation is kept through length and distance selection,
extra-bit reads, all copy shapes, linked tables, end and error exits, rollback
and final writeback. It holds for the whole body and the whole call, not only
for one successful token.

The source-origin lemmas establish the exact selected bits for their stated
domains. Connecting them to every legal caller view and to the independent
output semantics is the functional goal of `inflate`, which is not planned.
Speculative lookahead is not justified by the bytes supporting a decoded
symbol; the causal distinction is explained in [inflate](inflate.md).

For termination, a body writes at least one byte or exits on end or error. The
finite output range bounds the number of continuing bodies. Copy loops and
linked lookups also have bounded measures. These bounds stay below the fuel
budget, and the frame holds on every exit. No allocation occurs here; ownership
of the existing state and window is unchanged.

## C correspondence checks

### Fast decoder: margins, copies and rollback

`inflate_fast` enters in `LEN`, with at least six input bytes, 258 output bytes,
`start ≥ avail_out`, and fewer than eight buffered bits. `inflate` checks all these margins.
`inflateBack` checks the byte margins and relies on its mode transitions for `bits < 8`.
The dispatch proof supplies that fact to `LEN_fast_p`
(`ZlibF/Proof/infback.c.safety-dispatch.lean`, `infback.c.safety-fast.lean`).

`last = in + (avail_in - 5)` and `end = out + (avail_out - 257)` use unsigned subtraction.
Their safety depends on the entry margins. Each iteration reads at most six bytes and writes
at most 258. `beg = out - (start - avail_out)` names the beginning of this call's output.
The two callers use `start` equal to the original output room or the callback window size.

`here` is a pointer to a table entry here; the slow decoder copies an entry value.
`dolen` and `dodist` preserve the backward jumps for links. A valid table bounds link depth;
fuel in the translation does not itself prove termination. Error and end-of-block `break`s
skip the loop condition. Pointer comparisons in that condition and in final accounting must
compare pointers in the same object.

Copies from the window and current output retain the source's unrolled loops and read/write
order. Overlapping output matches are intentional: a newly written byte can be read by a
later copy step. They cannot become `memcpy` or a snapshot of the initial source range.
The minimum match length is three. Every pre-decrement copy loop needs a positive count.

On every exit, including invalid symbols and too-far distances, the epilogue returns whole
unused bytes to the input, retains only `bits mod 8` low bits, and writes back pointers and
remaining counts. A semantic proof must track the exact source-bit prefix through this
rollback, not just the number of consumed bytes.
