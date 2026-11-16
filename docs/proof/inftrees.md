# Decode tables: why `inflate_table` is safe, and why its tables are safe to read

Source: `zlib/inftrees.c`. Translation: `ZlibF/Zlib/inftrees.c.lean`.

`inflate_table` turns a list of code lengths into a lookup table. Two things are proved. The
call itself never faults and writes only its scratch array and the table space. And the table
it leaves has a shape, defined below, under which every later lookup by `inflate` and
`inflate_fast` reads an initialised entry inside the table. This page explains both, with the
arithmetic of canonical codes that they rest on.

`inflate_table` is an internal function. Its callers are `inflate`
([stream decoding](inflate.md)) and `inflateBack` ([callback decoder](callbacks.md)).

## Results

All theorems in this table are listed in `tests/audit/theorems.txt`. The level of each result
is recorded in [progress, Scope](../progress.md#scope). Modules are under `ZlibF/Proof/`.

| Result | Theorem | Module |
| --- | --- | --- |
| **T1.** For every call that meets the premises, `inflate_table` returns without a fault. Only `work` and the table space changed. The result is 0, 1 or -1 | `inflate_table_safe` | `inftrees.c.lean` |
| The result is -1 exactly when the lengths are not an acceptable code; 1 only for `LENS` and `DISTS` | `inflate_table_correct_ret` | `inftrees.c.lean` |
| **T2.** After a call that returns 0, the table has [the table shape](#the-table-shape) for the returned root width | `inflate_table_decoder_safe` | `inftrees.c.decoder-safe.lean` |
| After a call that returns 0, the returned pointer is `used` entries after `*table`, with `used` at most 128, 852 or 592. For `LENS` and `DISTS`, the root table and every second-level table that a link designates end at or before entry `used` (`TableReadExtent`), so a table built behind this one cannot be reached | `inflate_table_read_extent` | `inftrees.c.read-extent.lean` |
| Two lemmas about lists of code lengths, without the heap, that the proof of T2 uses. `root_cover`: for lengths that are not over-subscribed, each root index is filled by exactly one code of length at most `root`, or holds the link of one group of longer codes, or is not written; the last case needs a Kraft sum that does not reach the index, which a complete code excludes (`RootCell`). `group_cover`: for a complete code, each index of a second-level table wide enough for its group belongs to exactly one code of the group. The fact about the heap, that every entry a lookup can reach is a leaf or a link of the table shape, is T2 | `root_cover`, `group_cover` | `inftrees.c.cover.root.lean`, `inftrees.c.cover.group.lean` |
| `inflate_fixed` points the state at the two static tables and changes four fields | `inflate_fixed_ok` | `inftrees.c.fixed.lean` |
| For `LENS` and `DISTS`, after a call that returns 0: an entry that the slow decoder accepts with few bits held stays the same when more bits arrive | `constructor_establishes_query_stability` | `inftrees.c.decode.stability.lean` |

One more theorem is a lemma and is not listed: `inflate_table_len_leaves_positive`
(`inftrees.c.decoder-safe.lean`). It says that, after a `LENS` call that returns 0, every
literal/length leaf of the table uses at least one bit. Both callers use it, inside the proofs
of the two sequence theorems. `inflate` needs it for clause `tables` of
[its invariant](inflate.md#the-invariant), which includes this fact
(`inflate.c.dynamic-install.lean`). The callback decoder needs it for termination
(`infback.c.safety-table-lens.lean`; [fast decoding](inffast.md#assumptions)).

Functional results about the meaning of the entries are listed under
[Functional results](#functional-results).

## Assumptions

`inflate_table(type, lens, codes, table, bits, work)` does not check its arguments. The theorems
assume the following (`CallPre`, `ZlibF/Proof/inftrees.c.main.lean`). These are internal
premises: each caller proves them at each call. In
[internal contracts](../spec/internal-contracts.md) they are `I-it-pre-lens`, `I-it-pre-codes`,
`I-it-pre-work` and `I-it-pre-table`.

| Premise | `CODES` | `LENS` | `DISTS` |
| --- | --- | --- | --- |
| Number of symbols `codes` | at most 19 | at most 288 | at most 32 |
| Each length `lens[i]`, `i < codes` | at most 7 | at most 15 | at most 15 |
| Requested root width `*bits` | at least 7 | any | any |
| Writable table space after `*table` | 128 entries | 852 entries | 592 entries |

In all three cases `lens` has `codes` readable entries, `work` has `codes` writable entries, and
`work` is not the same array as `lens`.

Incomplete and over-subscribed codes are inside the domain; the call returns -1 for them. The
callers pass narrower values than the theorem allows: 19 three-bit lengths and a root of 7 for
`CODES`, at most 286 symbols for `LENS`, at most 30 for `DISTS`.

## What the function does

```c
for (sym = 0; sym < codes; sym++) count[lens[sym]]++;     /* 1. count the lengths      */
/* find min and max; clamp root between them */
left = 1;
for (len = 1; len <= MAXBITS; len++) {                     /* 2. Kraft check            */
    left <<= 1; left -= count[len];
    if (left < 0) return -1;
}
if (left > 0 && (type == CODES || max != 1)) return -1;
for (...) offs[len + 1] = offs[len] + count[len];          /* 3. sort symbols by length */
for (sym = 0; sym < codes; sym++)
    if (lens[sym] != 0) work[offs[lens[sym]]++] = (unsigned short)sym;
for (;;) {                                                 /* 4. one code per round     */
    /* write the entry for work[sym] at every index whose low bits are huff */
    /* step huff to the next code, backwards */
    /* when the length passes root: size a new second-level table, link it */
}
/* 5. if the code is incomplete, fill the one remaining entry with an invalid marker */
```

## The table shape

T2 says that a successful call leaves a table with the following shape. `LenTableSafe` and
`DistTableSafe` (`ZlibF/Proof/inffast.c.tableok.lean`) state it for a table that starts at index
`o` of an array, with root width `R`.

- `R ≤ 15`, and the `2^R` root entries lie inside the array.
- Each root entry is a leaf or a link.
- A **leaf** is a literal, a length or distance base, an end-of-block code, or an invalid code.
  A length base has at most 5 extra bits and a base value of at least 3, and the base plus the
  largest extra value is at most 258. A distance base has at most 13 extra bits and a base
  value of at least 1.
- A **link** has an index width `op` between 1 and 15 and an offset `val`. The `2^op` entries at
  `o + val` lie inside the array, and all of them are leaves.
- The bits of a root entry plus the bits of a leaf reached through it are at most 15.

For `CODES` the shape is simpler (`CodeLengthTableSafe`): no links, a root of at most 7, and
every entry uses between 1 and `root` bits and holds a symbol below 19 or an invalid marker.

The fixed tables `lenfix` and `distfix` have the same shape (`lenfix_tableSafe`,
`distfix_tableSafe`). The decoder invariants carry the shape from the call that built a table
to every lookup in it (clause `tables` of
[`InflateInv`](inflate.md#the-invariant)).

## Why each step is safe

### Counting and the Kraft check

`count[lens[sym]]` is in range because every length is at most 15 and `count` has 16 entries.

Let `c_l` be the number of symbols of length `l`. The loop keeps

```
left_0 = 1
left_l = 2 * left_(l-1) - c_l
```

and returns -1 as soon as `left_l` is negative. Define the first code of each length by

```
B_1 = 0
B_(l+1) = 2 * (B_l + c_l)
```

Then `left_l = 2^l - B_l - c_l`. A call that passes the check therefore has `B_l + c_l ≤ 2^l`:
all codes of length `l` fit in `l` bits. `left` is a signed `int`; its largest value is `2^15`,
so the shift and the subtraction do not overflow.

After the loop, a positive `left` means an incomplete code. The C accepts that in one case
only: the type is not `CODES` and `max = 1`, that is, one symbol of length 1.

### Sorting: F2

`offs[1] = 0` and `offs[l+1] = offs[l] + c_l`. The i-th symbol of length `l`, in symbol order,
goes to `work[offs[l] + i]`. That index is below the number `m` of symbols with a nonzero
length, and `m ≤ codes`, so the write is inside `work`. Different symbols go to different slots.
Afterwards `work[0..m)` holds the coded symbols sorted by length, then by symbol. This is fact
**F2** of [the method](method.md#structural-facts-used-by-several-proofs). The main loop reads
`work[sym]` only for `sym < m`.

### The code walk

DEFLATE sends a code most significant bit first, and a table index takes input bits least
significant bit first. So the function keeps the current code bit-reversed, in `huff`. Let
`rev_l(v)` be the low `l` bits of `v` in reverse order. The loop invariant is

```
huff = rev_len(B_len + i)      for the i-th code of length len
```

and so `huff < 2^len`.

- The first code is 0, and its reverse is 0.
- To step to the next code of the same length, the C clears the leading ones of `huff` from the
  top bit down and sets the first zero. That is an increment done backwards. If `huff` was all
  ones it becomes 0.
- When the next symbol has a greater length, the canonical code gets zeros appended at the low
  end. After reversal they are at the high end, so `huff` already has the right value.

For a complete code the last step wraps `huff` to 0. For the one-symbol code it leaves 1. The C
uses `huff != 0` after the loop to decide whether to write the invalid marker of step 5.

`ZlibF/Proof/inftrees.c.math.lean` proves the reversal and increment facts, without the heap.

### Writing a root entry

For a code with `len ≤ root`, the C writes the entry at the indices

```
huff + (2^root - 2^len), ..., huff + 2 * 2^len, huff + 2^len, huff
```

`fill` starts at `2^root`, a multiple of `2^len`, and goes down by `2^len` to 0, so it does not
wrap. Since `huff < 2^len`, every index is below `2^root`. These are exactly the root indices
whose low `len` bits equal `huff`.

### Sizing and linking a second-level table

When `len > root`, the codes that share the same low `root` bits of `huff` get one second-level
table. The C sizes it before writing:

```c
curr = len - drop;                 /* drop = root */
left = (int)(1 << curr);
while (curr + drop < max) {
    left -= count[curr + drop];
    if (left <= 0) break;
    curr++;
    left <<= 1;
}
```

`left` is the number of free slots at the current width. If the codes of that length use up the
slots, the width is enough. Otherwise the width grows by one bit. The loop stops at `max` at
the latest, so `count[curr + drop]` is read at an index of at most 15. After the loop every
code of the group has `len - root ≤ curr`. The entries are then written as in the root table,
with `huff >> drop` in place of `huff` and `2^curr` in place of `2^root`.

The new table starts at `next`, which is the table base plus the sizes of all tables so far.
`used` is that total. For `LENS` and `DISTS` the C first adds the size `2^curr` of the new
table to `used`, compares the sum with 852 (`LENS`) or 592 (`DISTS`), and returns 1 if it is
larger. Only then does it link the new table; the entries are written in the rounds that
follow. The root table gets the same comparison before the main loop, with `used = 2^root`. So
every write is inside the space the premises give.

The root link stores the width `curr` in `op` and the offset `next - *table` in the 16-bit
field `val`. At that point `next - *table = used - 2^curr`, so

```
val + 2^op = used ≤ 852   for LENS
val + 2^op = used ≤ 592   for DISTS
```

The offset fits the field, and the table it designates ends inside the space. Two theorems
state this for the table a successful call returns. `inflate_table_read_extent` gives
`val + 2^op ≤ used` for every root link, with `used ≤ 852` or `used ≤ 592`.
`inflate_table_decoder_safe` gives, for every root link, that the `2^op` entries at `val` lie
inside the array and are leaves (`LinkOK`, a part of the table shape).

`CODES` has no such test. It does not need one: with every length at most 7 and a requested
root of at least 7, `root = max`, so no code is longer than the root and the table has
`2^root ≤ 128` entries. This is why the premises for `CODES` are stronger.

### Every index is covered

Fill and link writes must together cover every index, or a lookup could read an entry that was
never written.

Give each code of length `l` the interval of 15-bit words that start with it. It has
`2^(15-l)` words. For a complete code these intervals are disjoint and cover all `2^15` words
(`inftrees.c.cover.tile.lean`). A root index stands for the words that start with its `root`
bits. Either a code of length at most `root` is a prefix of those words, and its fill wrote the
index; or longer codes share that prefix, and the first of them wrote a link there
(`root_cover`). The same argument inside a second-level table gives `group_cover`.

Two cases are not complete codes and are handled apart.

- One symbol of length 1: `root = 1`. The loop writes index 0, and step 5 writes an invalid
  marker at index 1.
- No symbol at all: the C writes two invalid entries, sets `*bits = 1`, advances `*table` by
  two and returns 0.

### What a leaf holds

The entry for symbol `w` takes `op` and `val` from the static arrays `lbase` and `lext` (for
`LENS`, symbols from 257) or `dbase` and `dext` (for `DISTS`). The index into those arrays is
`w - 257` or `w`. It is in range because `codes ≤ 288` or `codes ≤ 32`; the arrays have 31 and
32 entries. For `CODES` the base and extra pointers are not used: every symbol is below 19 and
takes the literal branch.

`inftrees.c.cover.leaf.lean` checks, entry by entry, that every value in the four arrays gives
a leaf of the shape above. `inflate_table_decoder_safe` puts coverage and leaf values together.

### Shifts

Every shift count of the function is a code length or a table width: `1U << root`,
`1U << (len - drop)`, `1 << curr`, `1U << (len - 1)`. Code lengths are between 1 and 15 where
these are evaluated, and `drop` is 0 or `root`, with `root < len` in a second-level table. So
every count is between 0 and 15.

## Why the loops end

`inflate_table_safe` includes termination. Each loop has its own bound.

- The counting, Kraft, offset and sorting loops run over fixed ranges: 16 lengths or `codes`
  symbols.
- The main loop handles one coded symbol per round; `sym` goes from 0 to `m`, with `m ≤ 288`.
- Inside a round: the fill loop counts `fill` down to 0 in steps of `2^len`; the backward
  increment moves a one-bit mask down at most 15 places; the sizing loop raises `curr` by one
  per round and stops at `max ≤ 15`.

All of these are far below the loop fuel of `2^64`.

## Where the hard part is

Safety of the writes is easy once `huff < 2^len` is known. The hard part is coverage: that no
index of any table is left unwritten. It needs the whole theory of canonical codes (the
intervals above), a model of which codes share a second-level table, and a proof that the
sizing loop, which looks ahead in `count`, gives each group exactly the width its codes need.
Coverage looks like a functional property, but the decoders' safety depends on it, since they
do not check an entry before using it.

## Readings of the C that no theorem states

- "The constants 852 and 592 are large enough for every valid code." No theorem here states
  this. The proofs do not need it: when the space runs out the C returns 1 and the decoder
  reports an error. zlib's own exhaustive search (`examples/enough.c`) is the source of the
  claim. **to confirm**.

## Source notes {#c-correspondence-checks}

The fixed tables are copies of `inffixed.h`. They are not the output of `inflate_table`: four
entries of `lenfix`, at indices 99, 227, 355 and 483, differ in the flag of an invalid code.
This and the other notes on how the translation follows `inftrees.c` are in the
[source notes for the decoder](inflate-source-notes.md#inftreesc).

## Functional results

These results say what the entries mean. They are proved, and they are not required for the
safety results.

| Result | Theorems | Modules |
| --- | --- | --- |
| The written entries are the canonical leaves and links for the given lengths | `inflate_table_content`, `constructor_establishes_decode_table_invariant` | `inftrees.c.content.lean`, `inftrees.c.decode.invariant.lean` |
| A lookup in the table decodes the symbol that the format assigns to the input bits | `decode_table_matches_format`, `decode_table_leaf_sound`, `decode_table_classifies_input` | `inftrees.c.decode.*.lean` |

The mathematical definition of a canonical code is `F-code-*` in the
[format guide](../spec/format/README.md).
