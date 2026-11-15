# Fast decoding: why `inflate_fast` is safe

Source: `zlib/inffast.c`. Translation: `ZlibF/Zlib/inffast.c.lean`.

`inflate_fast` decodes literals and matches without checking, on each read and write, that
input and output remain. It is safe because its callers enter it only with at least 6 input
bytes and 258 output bytes, and because one round of its loop reads at most 6 bytes and writes
at most 258. This page lists the entry conditions the theorem assumes, shows the loop invariant,
and explains the two bounds.

`inflate_fast` is an internal function. Its callers are `inflate`
([stream decoding](inflate.md)) and `inflateBack` ([callback decoder](callbacks.md)). Notes on
how the translation follows the C are in the
[source notes for the decoder](inflate-source-notes.md#inffastc).

## Results

| Result | Theorem | Module under `ZlibF/Proof/` | Level |
| --- | --- | --- | --- |
| `Goal.fast_safe` (`ZlibF/Spec/InflateFast.lean`): under the entry conditions, the call returns without a fault; the postcondition `FastPost` says exactly what changed | `inflate_fast_safe` | `inffast.c.final.lean` | registered |
| One round of the loop is safe: at most 6 bytes read, at most 258 written, at least one written if the loop continues (`Goal.step_safe`) | `inflate_fast_body_step_safe` | `inffast.c.body.lean` | registered |
| The static fixed tables have the table shape | `lenfix_tableSafe`, `distfix_tableSafe` | `inffast.c.tableok.lean` | registered |
| The same safety statement, and: a call that does not end in mode `TYPE` or `BAD` leaves less output room than it found | `inflate_fast_safe_progress` | `inffast.c.progress.lean` | checked |
| The same, and: a call never increases `bits + 8 * avail_in`, and lowers it unless it ends in `TYPE` or `BAD` | `fast_consumes` | `inffast.c.consume.lean` | checked |

The registered theorems are accepted on commit `bde170e9`
([levels](README.md#status-levels)). The two checked theorems are not in the registry
themselves. They are used inside the proofs of the registered sequence theorems
`inflate_sequence_safety_public` and `inflate_back_sequence_safety`, where they give
termination of the callers' loops. The registered `inflate_fast_safe` is stated for the entry
conditions of `inflate`. The two checked theorems are stated for the entry conditions of both
callers, so they are also what makes the call from `inflateBack` safe.

`FastPost` says: the stream's `next_in`, `avail_in`, `next_out`, `avail_out` and `msg` and the
state's `mode`, `hold` and `bits` were written; output bytes changed only in the range this
call wrote; `bits < 8` and `hold < 2^bits` again; the mode is unchanged, or `TYPE` (end of
block), or `BAD`. Nothing else in the heap changed, and nothing was allocated.

Functional results about `inflate_fast` also exist; see [Functional results](#functional-results).

## Assumptions

The theorems assume the entry conditions below. In Lean they are the fields of the record
`EnvG` (`ZlibF/Proof/inffast.c.env.lean`). `Env` is the case of `inflate`, in which the window
is never the output block; `inflate_fast_safe` is stated for `Env`. These are
internal premises: each caller proves them before the call (`inflate_fast_raw_entry` in
`inflate.c.fast-entry.lean`; `LEN_fast_p` in `infback.c.safety-fast.lean`).

- **Stream.** `strm` points at a writable stream record whose `state` is an inflate state.
- **Input.** `next_in` points into a byte block of fewer than `2^63` bytes. `avail_in ≥ 6`, and
  the `avail_in` bytes lie inside the block.
- **Output.** `next_out` points into a writable byte block of fewer than `2^63` bytes.
  `avail_out ≥ 258`, and the `avail_out` bytes lie inside the block. `start ≥ avail_out`, and
  `start - avail_out` bytes lie before `next_out` in the same block; so `beg` below is a pointer
  into that block.
- **Separation.** Input and output are different blocks, or two ranges of one block that do not
  overlap.
- **Bit buffer.** `bits < 8`, `hold < 2^bits`, `sane ≠ 0`.
- **Window.** `wsize ≤ 32768`, `whave ≤ wsize`, `wnext ≤ wsize`. If `whave ≠ 0`, `window`
  points at `wsize` bytes inside a block. For `inflate` that block is not the output block. For
  `inflateBack` it may be the output block; then `wnext = 0` and the window ends inside the
  output range.
- **Tables.** `lencode` and `distcode` point at tables of the safe shape for `lenbits` and
  `distbits` (`LenTableSafe`, `DistTableSafe`; see
  [decode tables](inftrees.md#the-table-shape)).

The [internal contracts](../spec/internal-contracts.md) page describes the entry of
`inflate_fast` under the names `I-if-pre-room`, `I-if-pre-bits`, `I-if-pre-tables` and
`I-if-pre-window`. Where that description says more than the list above, the list is what the
safety theorems assume.

No premise names the mode. No premise says what the window bytes contain, or that
`whave < wsize` implies `wnext = whave`. Safety needs only the bounds above; the rest belongs to
the [functional argument](#functional-results).

`fast_consumes` has one more premise: every literal/length leaf uses at least one bit
(`LenLeavesPositive`). `inflate_table_len_leaves_positive` proves it for a constructed table
and `lenfix_leavesPositive` for the fixed table.

## The loop and its invariant

```c
last = in + (strm->avail_in - 5);       /* loop while in  < last */
beg  = out - (start - strm->avail_out); /* start of the output of the enclosing call */
end  = out + (strm->avail_out - 257);   /* loop while out < end  */
do {
    /* decode one literal, or one length and distance with its copy */
} while (in < last && out < end);
/* give back unused whole bytes; write in, out, hold, bits back */
```

Write `in0` and `out0` for the values of `next_in` and `next_out` at entry.

```
output block   beg ........ out0 ........ out ............ end ... out0 + avail_out
               | earlier output  | this call |   free; at least 258 bytes at loop entry
input block    in0 ........ in ............ last ... in0 + avail_in
               | read      |   unread; at least 6 bytes at loop entry
```

At the start of every round the following hold (`LS` in `inffast.c.step1.lean`, and the loop
invariant in `fast_loop_wp`, `inffast.c.loop.lean`).

| Name | Says |
| --- | --- |
| I1 | `in0 ≤ in`, and `in + 6 ≤ in0 + avail_in`: six bytes can be read |
| I2 | `out0 ≤ out`, and `out + 258 ≤ out0 + avail_out`: 258 bytes can be written |
| I3 | `bits ≤ 30` and `hold < 2^bits` |
| I4 | `bits + 8 * in0 ≤ bits_entry + 8 * in`: every held bit came from the entry or from a byte this call read |
| I5 | Output bytes outside `[out0, out)` are as they were at entry |

The first round is reached without a test, because the loop is a `do` loop. The entry
conditions give I1 and I2 for it directly. Later rounds get them from the loop condition.

## Why each round keeps the invariant

### At most six bytes are read

One round has four places that read input.

| Place | Guard and read | After it |
| --- | --- | --- |
| R1, before the length lookup | `bits < 15`: read two bytes | 16 to 30 bits |
| R2, length extra bits | `bits < op`, with `op ≤ 5`: read one byte | enough for `op` |
| R3, before the distance lookup | `bits < 15`: read two bytes | 16 to 30 bits |
| R4, distance extra bits | `bits < op`, with `op ≤ 13`: read one byte, and a second if still `bits < op` | enough for `op` |

A code uses at most 15 bits, including a second-level lookup; that is part of the table shape.
So after R1 or R3, or when either is skipped, the code that follows is covered. The `op` bounds
5 and 13 are also part of the table shape. Hence every `bits -= op` takes away only bits that
are there, and every shift is by less than the width of its operand.

Adding up the four maxima gives seven bytes. Seven cannot happen. Suppose R1, R2, R3 and R4
read 2, 1, 2 and 2 bytes.

1. After R1 at least 16 bits are held. The length code takes at most 15: at least 1 remains.
2. R2 adds 8 and the length extra bits take at most 5: at least 4 remain.
3. R3 adds 16 and the distance code takes at most 15: at least 5 remain.
4. R4 reads its second byte only if, after the first, fewer than `op ≤ 13` bits are held. Then
   fewer than 5 were held before R4. This contradicts step 3.

So one round reads at most six bytes, which is why `last` is five bytes before the end of the
input. One round writes one literal or a match of at most 258 bytes, which is why `end` is 257
bytes before the end of the output. The bound 258 comes from the table shape: a length base
plus its largest extra value is at most 258. `inflate_fast_body_step_safe` states both bounds.

### Table reads

The root index is `hold & ((1 << lenbits) - 1)`, which is below `2^lenbits`; the table shape
puts `2^lenbits` entries inside the array. A root entry is a leaf or a link. A link designates a
second-level table that lies inside the array and holds only leaves, so the `goto dolen` or
`goto dodist` happens at most once per code.

An invalid code sets `msg` and mode `BAD` and leaves the loop. An end-of-block code sets mode
`TYPE` and leaves the loop. Both go through the same exit code as a normal end.

### Match copies {#match-copies-f3-and-f4}

Let `dist ≥ 1` be the decoded distance and `len` the length, with `3 ≤ len ≤ 258`.

**From the output.** If `dist ≤ out - beg`, the source `out - dist` is at or after `beg`, in the
output block. The copy runs byte by byte, forward. Each byte it reads was written before the
round or by an earlier step of the same copy, also when `dist < len` and the ranges overlap.

**From the window.** Otherwise `op = dist - (out - beg)` bytes come from the window. The C
tests `op > whave` and, because `sane ≠ 0`, leaves with an error. After the test
`1 ≤ op ≤ whave ≤ wsize`. In particular `whave ≠ 0`, so the window block exists. There are
three source positions.

| Condition | First window index | Why it is inside `[0, wsize)` |
| --- | --- | --- |
| `wnext == 0` | `wsize - op` | `1 ≤ op ≤ wsize` |
| `0 < wnext < op` | `wsize + wnext - op` | `op ≤ wsize` and `wnext < op`. The copy runs to the end of the ring, then continues at index 0 for up to `wnext` bytes |
| `wnext ≥ op` | `wnext - op` | `op ≤ wnext ≤ wsize` |

Each piece copies the smaller of what the window holds there and what the match still needs. If
the match is longer, the rest comes from the output, as above.

For `inflateBack` the window is the output buffer itself. Then `wnext = 0`, only the first row
applies, and the premise that the window ends inside the output range keeps the read in the
block.

### Giving bytes back and writing back

```c
len = bits >> 3;
in -= len;
bits -= len << 3;
hold &= (1U << bits) - 1;
```

I4 gives `bits ≤ bits_entry + 8 * (in - in0)`. With `bits_entry < 8` this means
`len ≤ in - in0`: the function gives back only bytes it read itself, and `in` does not move
before `in0`. Afterwards `bits < 8`, so the mask shift is in range. This is where the entry
condition `bits < 8` is used. Without it the function could step back over bytes that the caller
had consumed.

`inflate` tests `bits < 8` in its own condition for taking the fast path. `inflateBack` does not
test it; its invariant gives `bits < 8` whenever mode `LEN` is entered (`LEN_fast_p`).

The function then computes the new `avail_in` and `avail_out` from pointer differences inside
one block each and stores them with the cursors, `hold` and `bits`
(`fast_finish_wp`, `inffast.c.final.lean`).

## Why the loops end

The measure of the main loop is the free output room, `out0 + avail_out - out`
(`fast_loop_wp`). A round that does not leave the loop writes at least one byte, so the measure
falls. It is below `2^63`, far below the loop fuel of `2^64`.

Inside a round, a copy loop runs `op` or `len` times and counts down, and a code needs at most
one extra lookup.

## Where the hard part is

The two margins are small and they are exact. The loop is safe only because a round can never
read a seventh byte, and that is not visible in any one statement: it follows from how the four
refills interact with the bit counts that the tables allow. The proof follows the same case
split as the argument above, on the heap, for every table of the safe shape.

The second hard point is the output block. It is read and written in the same round, the source
of a match can overlap its destination, and input and output may be two ranges of one block
(`tests/regression/inflate-shared-block`). The loop invariant therefore tracks the whole output
array, not a separate view of "old" and "new" bytes.

## Readings of the C that no theorem states

- A window byte that a match reads was written earlier. For `inflate` this follows from the
  window shape W.5 of [stream decoding](inflate.md#window-shape-w): in a window that is not
  full `wnext = whave`, so only the third row of the table can occur, and it reads below
  `wnext`. `EnvG` does not carry W.5, and the safety theorem does not need it: in the model a
  read of a byte that was never written returns an arbitrary value and is not a fault
  ([trusted base](../trusted-base.md)). **to confirm**.

## Functional results

These results say what the fast decoder computes. They are registered, and they are not
required for the safety results.

| Result | Theorems | Modules |
| --- | --- | --- |
| A round consumes exactly the bits of one format token, and the bits it consumes are the next bits of the source | `actual_body_refines_token`, `actual_body_preserves_origin` | `inffast.c.body-token.lean`, `inffast.c.body-origin.lean` |
| A length or distance lookup returns the format's symbol | `length_lookup_matches_format`, `distance_lookup_matches_format` | `inffast.c.length-semantics.lean`, `inffast.c.distance-semantics.lean` |
| A match copy is the LZ77 copy of the format | `actual_distance_refines_lz77`, `actual_copy_match_refines_lz77` | `inffast.c.distance-result.lean`, `inffast.c.match-history.lean` |

For these the invariant is larger: it relates the consumed bits to the source stream and the
window contents to the earlier output. No theorem connects them to every caller view of
`inflate`; that would be the functional correctness of `inflate`, which is not required for the
safety results. Bytes read ahead and given back play no part in the meaning of a decoded
symbol; see [stream decoding](inflate.md#causality-and-history-across-calls). An earlier note
on what the functional invariant has to carry is kept in the
[history](../history/proof-functional-notes.md).
