# Source notes for the decoder: `inflate.c`, `inffast.c`, `inftrees.c`

This page records details of the C source at places where a shortcut in the translation would
change what the program does: evaluation order, integer conversions, fall-through, values kept
across helper boundaries. It is for a reader who compares `zlib/*.c` with `ZlibF/Zlib/*.c.lean`.

The notes are readings of the C. They are not theorems. The theorems are stated about the
translation ([stream decoding](inflate.md), [fast decoding](inffast.md),
[decode tables](inftrees.md)), and the differential tests compare the translation with the
compiled C; those tests are evidence of fidelity, not proof. The rules the translation follows
are in [translation semantics](../design/translation.md).

## `inflate.c`

### Control flow and the bit buffer

The translation keeps the C registers of `inflate` (`next`, `have`, `put`, `left`, `hold`,
`bits` and the others) in one record, `IL`. Each mode is a helper function that can return in
three ways, as the C does:

- a `break` of the switch returns to the dispatcher, which reads `state->mode` from the heap
  again;
- `goto inf_leave` jumps to the common exit with the registers as they stand. Reads and writes
  made so far are kept;
- `return` leaves the function at once.

A case that falls through calls the helper of the next case.

Details of the C that are observable:

- `TYPE` falls into `TYPEDO` without writing `mode`. If the block header cannot be read for lack
  of input, the saved mode is still `TYPE`. This shows in `data_type` and at the next entry.
- `PULLBYTE` tests for input before it changes anything. A `NEEDBITS` that fails keeps every
  byte pulled on earlier rounds. `DROPBITS` changes `hold` before it subtracts from `bits`.
  `BYTEBITS` uses the old bit count in both of its expressions.
- `BITS(n)` casts `hold` to `unsigned` before masking with `(1U << n) - 1`. `hold` itself is
  `unsigned long`.
- In `HEAD`, the header check adds a 32-bit shifted term to `hold >> 8` in 64-bit arithmetic.
  High bits put there by `inflatePrime` take part.
- `DICT` returns `Z_NEED_DICT` after `RESTORE` and the update of `total_in`. It does not pass
  through `inf_leave`. `MEM` and `SYNC` also return directly.
- `CHECK` updates the output totals and the checksum, then resets the local output baseline
  `out`. The exit code uses the new baseline, so the same bytes are not counted twice.
- `inf_leave` restores the registers before it updates the window. If the window allocation
  fails, the function returns `Z_MEM_ERROR` before the later updates of the totals and the
  checksum. Output already written stays written.

`inflatePrime` clears the bit buffer for a negative count. It refuses a count above 16 and a
total above 32. It masks `value` in the `long` expression and converts to `unsigned long`
afterwards, so a negative `value` goes through that order of conversions.

`inflateMark` sign-extends `back`, converts to `unsigned long`, shifts left by 16, converts back
to `long`, and adds the conditional term. On this platform the out-of-range conversions are
modular. The error result is `-65536`.

### Window, dictionaries, copying

`updatewindow` allocates the window without initialising it, then copies the last `wsize` bytes
or a suffix split at the end of the ring. `inflateGetDictionary` returns the part from
`window + wnext` to the end, followed by the part before `wnext`. `inflateSetDictionary` checks
the Adler-32 identifier in mode `DICT` and passes the end of the dictionary to `updatewindow`.

A window is allocated in two places: in `updatewindow`, when it is called with
`window == NULL` (from the exit code of `inflate` and from `inflateSetDictionary`), and in
`inflateCopy`, for the copy of a stream that has one. A window is freed in four places:

- `inflateReset` frees it when `wbits != reqbits`, then sets `wbits = reqbits`. In every case
  it sets `wsize`, `whave` and `wnext` to 0. When the two widths are equal the block stays and
  is reused.
- `inflateReset2` frees it when its width `wbits` differs from the width that the new
  `windowBits` asks for, then calls `inflateReset`.
- `inflateSync`, after a match, calls `inflateReset`. Then, if `wbits == 0`, it frees a window
  that is still there and sets `wbits = 15`.
- `inflateEnd` frees it, and then the state.

`inflateResetKeep` frees nothing. It leaves the window block and the three counters as they
are.

`inflateCopy` allocates through the source stream's allocator. If the window allocation fails
it frees the new state. It sets `dest->state` to `NULL` when the state check rejects the source
and on both allocation failures. On success it copies both records and repairs the back pointer.
If `lencode` is the state's own `codes` array, it points `lencode` and `distcode` into the
copy's array; pointers at the fixed tables are kept. It rebases `next` and copies `whave` window
bytes. The proof of the pointer repair uses the invariant
clause `origin` (`CopyTableOrigin`) and `CopyTableOrigin.dynamic_geometry`
(`ZlibF/Proof/inflate.c.copy-origin.lean`): `next` and a dynamic `distcode` are offsets into
`codes`, and `next` may be one past its end.

`memcpy` between two disjoint ranges of one byte object is allowed in the model. Overlapping
ranges fault.

### Initialisation, recovery and pointers

`inflateInit2_` zeroes the new state, then sets fields and calls `inflateReset2`. The version
check looks at the first byte of the version string and at the structure size, 112 in this
build. `inflateReset2` rejects a `windowBits` below `-15` before it negates the value, so
`INT_MIN` never reaches the negation.

`inflateStateCheck` evaluates its tests left to right and stops at the first that fails, so no
field is read through a pointer that an earlier test rejected. A pointer to a deflate state is
not a valid inflate state in the model, whatever the layout of the two structures.
`inflateBackInit_` and `inflateInit2_` create different objects, and each has its own end
function.

`inflateGetHeader` keeps the caller's pointer and writes `head->done` without a test for `NULL`.
In `EXTRA` the C assigns inside the condition, and `NAME` and `COMMENT` use post-increments.

`syncsearch` takes `have` through a pointer. The translation passes the value and returns the
new one, and `inflateSync` stores it where the C call returns. `inflateSync` searches the bytes
held in the bit buffer first, then the caller's input, and restores `total_in`, `total_out` and
the wrapper facts after the reset. The four-byte local arrays of `inflateSync` and of the header
CRC are real temporary byte storage, released on every return.

`inflateGetDictionary` takes its optional length through a pointer. The translation returns the
value instead. So the theorems do not cover a `dictLength` cell that aliases other caller data.

### Statements of the table and trailer lemmas

`inflate_TABLE_run` covers the extraction of the three counts and the exit for too many length
or distance symbols. `inflate_LENLENS_run` assumes `have ≤ ncode ≤ 19` and that the entries
written so far are 3-bit values (`Good3`); `TABLE` gives the first and earlier rounds give the
second. `ll1_run`, `lz_run` and `llTail_run` are its three loop parts.

The call of `inflate_table` for the code-length code uses `inflate_table_safe` and
`inflate_table_correct_ret`. `inflate_CHECK_run` assumes that the static checksum tables are
intact (`StaticsOK`) and names the bytes written during this call (`PutAt`). For an Adler-32
value that is not in canonical form the one-byte update has its own relation
([Adler-32](adler32.md)); the goal does not assume a canonical seed.

## `inffast.c`

`inflate_fast` forms `last = in + (avail_in - 5)` and `end = out + (avail_out - 257)` with
unsigned subtraction. The entry margins of six input bytes and 258 output bytes keep both from
wrapping. `beg = out - (start - avail_out)` is the start of the output of the enclosing call:
`inflate` passes its original `avail_out` as `start`, and `inflateBack` passes the window size.

`here` is a pointer to a table entry; the slow decoder in `inflate.c` copies the entry instead.
`dolen` and `dodist` are labels reached by backward `goto` when an entry is a link. The `break`
at an error or at end of block skips the loop condition. The loop condition and the final
accounting compare pointers into the same object.

The match copies are loops, unrolled three bytes at a time, with reads and writes in the order
of the C. A match may overlap its own output: a byte written by one step is read by a later
step. A `memcpy`, or a copy from a snapshot of the source, would give a different result. Every
`do { ... } while (--op)` loop is entered with a positive count.

On every exit, also after an invalid code or a distance too far back, the function returns the
unused whole bytes to the input, keeps `bits & 7` bits, and writes back the pointers and the
remaining counts.

## `inftrees.c`

### Entries and flag order

A `code` has two byte fields, `op` and `bits`, and a 16-bit `val`. The table space is
`ENOUGH_LENS = 852` plus `ENOUGH_DISTS = 592` entries, 1444 in all. Code lengths are at most 15.
The order in which the code-length code lengths arrive is
`16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15`.

| `op` | Meaning |
| --- | --- |
| 0 | literal |
| 1 to 15 | link to a second-level table; the low bits give its index width |
| 16 + e | length or distance base with e extra bits |
| 96 | end of block (bits 32 and 64 both set) |
| 64, 68 or 193 | invalid code |

The decoders test these flags in a fixed order. The slow literal/length decoder tests end of
block before invalid. The fast decoder tests literal, then length, then link, then end of block
or invalid. `DIST` has no `op != 0` test of the kind `LEN` has. `CODELENS` reads `val` without
looking at `op`. An alphabet of all-zero lengths gives two invalid entries with `val = 0`; the
stream then fails at the missing end-of-block code.

The fixed tables are copies of `inffixed.h`: 512 literal/length entries with root 9 and 32
distance entries with root 5. They are not the output of `inflate_table`. Building them with
`inflate_table` would change four literal/length entries, at indices 99, 227, 355 and 483: the
generated invalid flag is 68 or 193, and the header has 64. All three reject the reserved
symbols. The translation uses the header's values.

The base and extra arrays and the order array are constants. The error messages are read-only
strings; callers can read them through `strm->msg`.

### `inflate_table`

The function runs its steps in this order: count the lengths, check the Kraft sum, sort the
symbols, fill the table, write the tail. It does not check its arguments. The no-symbol case
writes two invalid entries and updates both out-parameters before it returns 0. An
over-subscribed code, or an incomplete code that is not allowed, returns -1. Running out of
table space returns 1, possibly after entries have been written.

The C passes `table` and `bits` as pointers. The translation passes `*table` and `*bits` by
value and returns the new values. On an error return the two values are unchanged, but entries
already written stay. In `CODELENS` the caller assigns `lencode` before the call for the length
table, and assigns `distcode` from the advanced `next` before the call for the distance table.

Arithmetic details:

- `count` and `offs` are arrays of 16-bit values, with the C promotions and narrowing.
- `left` is signed, with signed shifts and subtractions. The later `1 << curr` is a signed
  expression; the earlier `1U << root` is unsigned.
- The variable `min` changes meaning at `min = fill`: from then on it holds the current table
  size.
- `fill -= incr`, and the caller's final `while (copy--)`, are unsigned.
- A root link stores a pointer difference narrowed to 16 bits. `inflate_table_decoder_safe`
  states, for the stored value, that the second-level table it designates lies inside the array
  and holds only leaves (`LinkOK`).

### Slow lookup with too few bits

The slow decoder can look up a root entry before it holds `root` bits. It accepts the entry when
the entry's own length is at most the number of bits held; otherwise it pulls a byte and looks
again. The entry it accepts does not change when more bits arrive
(`constructor_establishes_query_stability`, for a `LENS` or `DISTS` table that `inflate_table`
returned with 0). A link needs the second lookup and both lengths.

Why the bytes read ahead do not have to be valid is explained in
[stream decoding](inflate.md#causality-and-history-across-calls).
