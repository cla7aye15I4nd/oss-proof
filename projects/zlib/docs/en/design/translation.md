# Translating C without changing its behaviour

Each C function of the selected source is rewritten by hand as a Lean function, statement by
statement. This page gives the rule, the four accepted normalisations, the further forms in
which the translations depart from the C text, and two functions shown with their C, so that a
reader can compare a translation with its source. The kernel does not check a
translation against C. Review and differential tests do; tests are evidence of
fidelity, not proof.

[Architecture](architecture.md) defines the types used here (`M`, `Fault`, `cwhile`, pointers).
[Trusted base](../trusted-base.md) records the limits of the model.

## The rule

A translation keeps the statements of the C function in their order. It does not reorder
checks, drop a read or a write, or replace an algorithm, except in the four accepted
normalisations and the six further forms listed below. A proof that is hard is not a reason to
change a translation. A mismatch with the C is a translation bug, and it is corrected against the
C. The domain of a theorem is not narrowed to hide a difficulty either. A defect of the C is
called a confirmed finding only when a run of the real C on a concrete input shows it (a
sanitizer report, or a result that breaks a promise of `zlib.h`), or when it is undefined
behaviour by the letter of the C standard that a patch fixes.

Four normalisations are accepted. They are listed with examples
in [the accepted normalisations](#the-accepted-normalisations):

1. An out-parameter of an internal function is passed by value and returned as a second result.
2. Two reads of one location with no store between them are one read.
3. Consecutive assignments to fields of one record are one record update.
4. A signed operation that a preceding test of the same function keeps in range is written
   with the plain operator.

The translations also use six further forms: for example, a value just stored is used again
without a read, and an operand is evaluated before the short-circuit test that guards it in C.
[Forms not covered by the four accepted normalisations](#forms-not-covered-by-the-four-accepted-normalisations)
says what the translation does in each form, gives instances with file and function, and states
what the agreement with the C rests on.

## The source that is translated

One build is translated: default x86_64 Linux, static library, LP64. A runtime parameter never
selects a different compiled branch. Preprocessor choices are resolved against the pinned zlib
source with the project's patches applied in name order.

| Source family | Selected branches |
| --- | --- |
| Compression | Gzip enabled; `FASTEST`, `LIT_MEM`, `UNALIGNED_OK` and debug checks disabled; default `MAX_WBITS` 15 and `MAX_MEM_LEVEL` 9 |
| Decode tables and inflate | Gzip and fast decoding enabled; `BUILDFIXED`, `MAKEFIXED`, `PKZIP_BUG_WORKAROUND`, `INFLATE_STRICT` and invalid-distance recovery disabled. Fixed tables come from `inffixed.h` |
| CRC | Static tables; braid parameters `N = 5` and `W = 8`. The little-endian branch runs; the big-endian branch is not exercised |
| Gzip files | LP64 large-file entries and C99 formatting; Windows, wide-character and `Z_SOLO` paths are not selected. One I/O request is at most `2^30` bytes |

Each translation file lists its preprocessor choices in its header comment. These choices are
readings of the source for this build. No proof checks them: **to confirm** by review against
the preprocessed source.

The translation of `zlib/X.c` is the file `X.c.lean`, and that of `zlib/X.h` is `X.h.lean`.
(`deflate.c` is split over three files.) A translation file holds no proofs. Each function
keeps its C name, and its docstring starts with the C signature. The C text of each block is
quoted in a comment above the Lean lines that translate it.

## A worked example: `syncsearch`

`syncsearch` is a helper of `inflateSync` in `zlib/inflate.c`. It searches a buffer for the
pattern `00 00 FF FF`.

```c
local unsigned syncsearch(unsigned FAR *have, const unsigned char FAR *buf,
                          unsigned len) {
    unsigned got;
    unsigned next;

    got = *have;
    next = 0;
    while (next < len && got < 4) {
        if ((int)(buf[next]) == (got < 2 ? 0 : 0xff))
            got++;
        else if (buf[next])
            got = 0;
        else
            got = 4 - got;
        next++;
    }
    *have = got;
    return next;
}
```

Its translation:

```lean
/-- `local unsigned syncsearch(unsigned FAR *have, const unsigned char FAR *buf, unsigned len)`.
`have` is the value of `*have`; the result is (return value, `*have` afterwards). -/
def syncsearch (have_ : UInt32) (buf : BPtr) (len : UInt32) : M (UInt32 × UInt32) := do
  -- got = *have; next = 0;
  let (next, got) ← cwhile (σ := UInt32 × UInt32)
    -- while (next < len && got < 4) {
    (fun (next, got) => pure (next < len && got < 4, (next, got)))
    (fun (next, got) => do
      let b ← index8 buf next.toNat
      -- if ((int)(buf[next]) == (got < 2 ? 0 : 0xff)) got++; else if (buf[next]) got = 0; else got = 4 - got;
      let got := if b.toNat == (if got < 2 then 0 else 0xff) then got + 1 else if b != 0 then 0 else 4 - got
      -- next++;
      pure (next + 1, got))
    (0, have_)
  -- *have = got; return next;
  return (next, got)
```

How to read it:

| C | Lean | What to check |
| --- | --- | --- |
| The function returns `unsigned` and may have undefined behaviour | Result type `M (UInt32 × UInt32)` | `M α` is `Heap → Except Fault (α × Heap)`: a value and the new heap, or `Fault.ub`, or `Fault.outOfFuel`. |
| `unsigned *have` | Argument `have_ : UInt32`, and the second component of the result | Normalisation 1. The caller reads the cell before the call and stores the second result after it; see below. |
| Locals `got`, `next` | Loop state `(next, got) : UInt32 × UInt32` | Locals that a loop changes are carried as the loop state. `unsigned` is `UInt32`. The start state `(0, have_)` is `next = 0; got = *have`. |
| `while (c) body` | `cwhile cond body start` | `cwhile` tests the condition, runs the body, and repeats, at most `2^64` tests; then `Fault.outOfFuel`. This loop runs fewer than `2^32` times, because `next` rises to `len`. |
| `next < len && got < 4` | `next < len && got < 4` | Both operands read only locals, so the short-circuit order cannot be observed. |
| `buf[next]` | `index8 buf next.toNat` | `index8 p i` is pointer arithmetic then a load. It faults when `buf` is NULL, when its array is freed, and when the index is outside the array. An out-of-bounds read in C is `Fault.ub` here. |
| `buf[next]` read again in `else if` | The same `b` | Normalisation 2. No store lies between the two reads. |
| `(int)(buf[next]) == (got < 2 ? 0 : 0xff)` | `b.toNat == (if got < 2 then 0 else 0xff)` | A byte promoted to `int` is in 0..255; comparing the values as natural numbers gives the same result. |
| `got++`, `4 - got`, `next++` | `got + 1`, `4 - got`, `next + 1` on `UInt32` | Unsigned arithmetic wraps in C and in `UInt32`. No check is wanted. |
| `*have = got; return next;` | `return (next, got)` | See the out-parameter row. |

The call site in `inflateSync` shows the other half of the out-parameter:

```c
len = syncsearch(&(state->have), strm->next_in, strm->avail_in);
```

```lean
let (len, hv) ← syncsearch (← rdS st (·.«have»)) z.next_in z.avail_in
wrS st fun s => { s with «have» := hv }
```

`rdS st f` reads a field of the state record `*st`, and `wrS st f` replaces the record by `f`
of it. The C stores `state->have` inside the callee; the Lean stores it right after the callee
returns. Nothing reads the field in between. A fault inside the callee ends the run in both.

## A second example: signed arithmetic and record fields

The start of the body of `inflateReset2` in `zlib/inflate.c`, after the two declarations
`int wrap;` and `struct inflate_state FAR *state;`. `GUNZIP` is defined in this build, so the
lines between `#ifdef GUNZIP` and `#endif` are compiled:

```c
    /* get the state */
    if (inflateStateCheck(strm)) return Z_STREAM_ERROR;
    state = (struct inflate_state FAR *)strm->state;

    /* extract wrap request from windowBits parameter */
    if (windowBits < 0) {
        if (windowBits < -15)
            return Z_STREAM_ERROR;
        wrap = 0;
        windowBits = -windowBits;
    }
    else {
        wrap = (windowBits >> 4) + 5;
#ifdef GUNZIP
        if (windowBits < 48)
            windowBits &= 15;
#endif
    }

    /* set number of window bits, free window if different */
    if (windowBits && (windowBits < 8 || windowBits > 15))
        return Z_STREAM_ERROR;
    if (state->window != Z_NULL && state->wbits != (unsigned)windowBits) {
        ZFREE(strm, state->window);
        state->window = Z_NULL;
    }
```

Its translation:

```lean
  -- if (inflateStateCheck(strm)) return Z_STREAM_ERROR;
  if (← inflateStateCheck strm) != 0 then return Z_STREAM_ERROR
  let z ← ldZStream strm
  let state ← castInflateState z.state
  let mut windowBits := windowBits
  let mut wrap : Int32 := 0
  -- if (windowBits < 0) { if (windowBits < -15) return Z_STREAM_ERROR; wrap = 0; windowBits = -windowBits; }
  if windowBits < 0 then
    if windowBits < -15 then return Z_STREAM_ERROR
    wrap := 0
    windowBits ← chkI32 (-(windowBits.toInt))
  else
    -- wrap = (windowBits >> 4) + 5;
    wrap ← chkI32 ((windowBits >>> 4).toInt + 5)
    -- if (windowBits < 48) windowBits &= 15;
    if windowBits < 48 then windowBits := windowBits &&& 15
  -- if (windowBits && (windowBits < 8 || windowBits > 15)) return Z_STREAM_ERROR;
  if windowBits != 0 && (windowBits < 8 || windowBits > 15) then return Z_STREAM_ERROR
  -- if (state->window != Z_NULL && state->wbits != (unsigned)windowBits) { ZFREE; window = Z_NULL; }
  let s ← ldInflateState state
  if s.window != .null && s.wbits != i2u windowBits then
    ZFREEB strm s.window
    wrS state fun s => { s with window := .null }
```

| C | Lean | What to check |
| --- | --- | --- |
| `int windowBits`, `int wrap` | `Int32` | `int` is `Int32`. `let mut` is a local that is assigned again. |
| `strm->state` | `ldZStream strm`, then the field `z.state` | `ldZStream p` is `*p` for a `z_stream *`. It faults when `p` is NULL or its record is freed. |
| `(struct inflate_state *)strm->state` | `castInflateState z.state` | The stream's state pointer may name an inflate state or a deflate state. The cast faults when it names a deflate state: C would read through the wrong type. |
| `-windowBits` | `chkI32 (-(windowBits.toInt))` | The negation is computed on unbounded integers. `chkI32` returns the `Int32` when the result fits and `Fault.ub "signed integer overflow"` when it does not. |
| `(windowBits >> 4) + 5` | `chkI32 ((windowBits >>> 4).toInt + 5)` | The same check for the addition. `windowBits` is not negative in this branch, so the shift has no sign question. |
| `windowBits &= 15`, the comparisons | `&&&`, `<`, `>` on `Int32` | These cannot overflow. |
| `state->window`, `state->wbits` | `ldInflateState state`, then fields of `s` | One load of the record serves both field reads (normalisation 2). |
| `(unsigned)windowBits` | `i2u windowBits` | Conversion of `int` to `unsigned` is defined in C: reduction modulo `2^32`. |
| `ZFREE(strm, state->window)` | `ZFREEB strm s.window` | The macro calls `strm->zfree`. Only the default allocator is modelled: `ZFREEB` frees the block when that field is `zcfree`, and is `Fault.ub` for any other function pointer. Freeing faults on a block that is not live. |
| `state->window = Z_NULL` | `wrS state fun s => { s with window := .null }` | A field write is a load of the record, a record update and a store. |

An early `return` in C is `return` inside the Lean `do` block: the rest of the block is not run.

## The accepted normalisations

**1. An out-parameter of an internal function is passed by value and returned as a second
result.** The model has no pointer to a scalar field of a record or to a scalar local. The
example is `syncsearch` above: `unsigned *have` is the argument `have_` and the second result,
and the caller stores it. Other uses: `inflate_table` (`table`, `bits`), `gz_load` (`have`) and
the `&next` of the `inflateBack` input callback.

The same representation is used for the scalar out-parameters of some public functions:
`destLen` of `compress*`, `dictLength` of `inflateGetDictionary` and `deflateGetDictionary`,
`pending` and `bits` of `deflatePending`, and `bits` of `deflateUsed`. Normalisation 1 is worded
for internal functions only; for these public functions the representation is a limit of the
model: the caller's cell is not memory, so a cell that overlaps one of the buffers
cannot be expressed, and the safety goal of the function says nothing about the cell's memory.
[Deviations](../deviations.md) has the rows
["Result cells"](../deviations.md#stream-calls-inflate-and-deflate) and
["Whole-buffer compression"](../deviations.md#whole-buffer-utilities-and-checksums). The length cells
of `uncompress*` and the `errnum` cell of `gzerror` are memory: eight-byte blocks and a four-byte
block.

**2. Two reads of one location with no store between them are one read.** In `syncsearch`:

```c
        if ((int)(buf[next]) == (got < 2 ? 0 : 0xff))
            got++;
        else if (buf[next])
```

```lean
      let b ← index8 buf next.toNat
      let got := if b.toNat == (if got < 2 then 0 else 0xff) then got + 1 else if b != 0 then 0 else 4 - got
```

Both C reads give the same byte and fault in the same cases, because nothing is stored between
them.

**3. Consecutive assignments to fields of one record are one record update.** In `inflateSync`:

```c
        state->mode = SYNC;
        state->hold >>= state->bits & 7;
        state->bits -= state->bits & 7;
```

```lean
      let h ← shr64 s.hold (s.bits &&& 7)
      wrS st fun s => { s with mode := SYNC, hold := h, bits := s.bits - (s.bits &&& 7) }
```

The three statements write three different fields, and each right side reads only fields that
the statements before it did not write. So the values are the same as in C. `shr64` is the
checked shift; its count is at most 7 here, so it does not fault and its position before the
update cannot be observed.

**4. A signed operation that a preceding test of the same function keeps in range is written
with the plain operator.** In `zError` (`zutil.c`, through the macro `ERR_MSG` of `zutil.h`):

```c
#define ERR_MSG(err) z_errmsg[(err) < -6 || (err) > 2 ? 9 : 2 - (err)]
```

```lean
  let i : Int32 := if err < -6 || err > 2 then 9 else 2 - err
```

Lean's `Int32` subtraction wraps; C's is undefined on overflow. The subtraction runs only when
`-6 ≤ err ≤ 2`, so the result is in 0..8 and the two agree. Another use is the `%` on `Int64` in
`adler32_combine_`, after the test `len2 < 0`.

A signed operation with no such test uses a checked helper (`chkI32` in the second example).
The helpers are listed in [architecture](architecture.md#where-the-trusted-semantics-is).

## Forms not covered by the four accepted normalisations

The translations use the six forms below. None of the four accepted normalisations covers them
as worded. That the Lean agrees with the C in these places is trusted, not proved: it rests on
a reading of each place, and no theorem states it
([trusted base, item 3](../trusted-base.md#3-manual-translation)). The tables below are
examples, not a complete list: other instances, and other forms, may exist.

**1. A value just stored is used again instead of being read back.**

| File, function | C | Lean |
| --- | --- | --- |
| `inflate.c.lean`, `inflateSync` | `state->have = 0; syncsearch(&(state->have), buf, len);` | The field is set to 0, and the call is `syncsearch 0 buf len`: the callee gets the literal, not the field read back. The second call of the function does read the field. |
| `inflate.c.lean`, `inflate_CODELENS` and `inflate_LENLENS`; `infback.c.lean`, `back_TABLE` (two places) | `state->next = state->codes; state->lencode = (const code FAR *)(state->next);` | One update with `next := codesP c.st, lencode := codesP c.st`. `inflate_LENLENS` sets `distcode` the same way, for `state->lencode = state->distcode = (const code FAR *)(state->next)`. |
| `deflate_strategies.c.lean`, `deflate_stored` | `s->strstart = s->w_size; s->insert = s->strstart;` | One update with `strstart := d.w_size, insert := d.w_size`. |
| `deflate_strategies.c.lean`, `deflate_stored` (the two window slides) | `s->strstart -= s->w_size; zmemcpy(s->window, s->window + s->w_size, s->strstart);` and later `if (s->insert > s->strstart) s->insert = s->strstart;` | The new value is the local `ss`. The copy length and the test of `insert` use `ss`; the field is stored afterwards (form 6). |
| `inflate.c.lean`, `updatewindow` | `state->wnext += dist; if (state->wnext == state->wsize) state->wnext = 0; if (state->whave < state->wsize) state->whave += dist;` | The sum is the local `wnext`, which is compared with `wsize` and set to 0 when equal. One update then stores `wnext` and `whave`: the field is not stored and read back in between. |
| `deflate_base.c.lean`, `flush_pending` | `s->pending -= len; if (s->pending == 0)` | The difference is the local `pend`. It is stored, and the test uses `pend`, not the field. |

The second and third rows differ from normalisation 3: a right side reads a field that an
earlier statement of the group wrote.

**2. An operand is evaluated before the short-circuit test that guards it in C.** C evaluates
the right operand of `&&` and `||` only when the left operand does not decide. In a Lean `do`
block, a nested action `(← e)` inside a condition runs before the condition is evaluated, and a
record loaded by a `let` above the condition is loaded in every case.

| File, function | What runs early |
| --- | --- |
| `inflate.c.lean`, `inflateSync` | `ldInflateState st` runs before `z.avail_in == 0 && s.bits < 8`. C reads `state->bits` only when `strm->avail_in == 0`. |
| `inflate.c.lean`, `inflatePrime` | The state is loaded before the left operand `bits > 16` is tested. C reads `state->bits` only when that operand is false. |
| `inflate.c.lean`, `inflateValidate` | The state is loaded before `check != 0 && s.wrap != 0` and before the same test of `reqwrap`. |
| `deflate.c.lean`, `deflate` | The state is loaded before the test that starts with the operand `strm->next_out == Z_NULL`. `RANK flush` and `RANK old_flush`, which are checked signed arithmetic, run before `z.avail_in == 0 &&`. The stream is loaded before `s->status == FINISH_STATE &&`. |
| `deflate.c.lean`, `deflateParams` | The checked sum `(s->strstart - s->block_start) + s->lookahead` is computed before the left operand `strm->avail_in` is tested. C computes it only when `strm->avail_in` is 0. |
| `deflate_strategies.c.lean`, `deflate_stored` | The state and `s->strm->avail_in` are loaded before `flush != Z_NO_FLUSH && flush != Z_FINISH &&`. `s->strm->avail_in` is loaded before the left operand `left >= min_block` is tested. |
| `deflate_strategies.c.lean`, `deflate_fast_body`, `deflate_slow_body` | The state is loaded before `hash_head != NIL &&`. |
| `trees.c.lean`, `detect_data_type` | `s->dyn_ltree[n].Freq` is read before `(block_mask & 1) &&`. |
| `gzread.c.lean`, `gz_look` | The gz state is loaded before the left operand `strm->avail_in == 0` is tested. The stream is loaded before `state->junk == 0 &&`. |
| `gzread.c.lean`, `gz_skip`, `gz_read` | The stream is loaded before `state->eof &&`. In `gz_read` the gz state is loaded before `n == 0 &&` and before `len &&`. |

In every row except three, the early operation stores nothing and is a load of a record that
the same function has already loaded, directly or through the state check it calls, or a load
of the stream embedded in the gz state that the function has already loaded. The three
others can fault in the model on a state for which the C does not evaluate the operand: the two
rows with checked arithmetic (`deflate`, `deflateParams`) and the array read of
`detect_data_type`. In `deflate`, only `RANK old_flush` can fault: `flush` has passed the range
test at the start of the function, and `old_flush` is the stored field `last_flush`. The safety theorems show that the translation does not fault in
their domain, so the difference lies outside it.

Where the right operand is a call, or a read through a pointer that the left operand tests, the
translation keeps the C order with nested `if`s. Examples: `strm == Z_NULL || strm->state ==
Z_NULL` in `inflateBack`, and `state->skip && gz_zero(state) == -1` in `gzvprintf`.

**3. A field value is taken from a record that was loaded before a store.** Normalisation 2
covers two reads with no store between them. Here a store lies between the load and the use; it
writes another field or another record.

| File, function | What is reused |
| --- | --- |
| `deflate.c.lean`, `deflate` | The state `d` and the stream `z` are loaded before `s->last_flush = flush`. `d.pending` and `z.avail_in` are used after that store. |
| `deflate_strategies.c.lean`, `deflate_stored` | `s->strm` is read once at the start (`let strm := d.strm`) and used for every later `s->strm`, across stores to other fields of `*s`. |
| `inflate.c.lean`, `inflate_leave` | The stream `z` is loaded after `RESTORE()`. `z.avail_in`, `z.avail_out` and `z.next_out` are used after the call of `updatewindow` and after the store of `total_in` and `total_out`. |

**4. A shift by a constant count is written with the plain operator.** A shift whose count is a
variable goes through a checked helper (`shl32`, `shr32`, `shl64`, `shr64`, `ishl`, `ushl`,
`shl1`, `shl1i32`, `shlUs`, `shrUs`). A shift whose count is a literal smaller than the operand
width is written `>>>` or `<<<`: for example `s.hold >>> 8` for `state->hold >>= 8` in
`inflateSync`, and `adler >>> 16` in `adler32_z`. For an unsigned operand the two languages agree
on such a shift. The functions that contain a plain shift, by file:

| File | Functions |
| --- | --- |
| `adler32.c.lean` | `adler32_z`, `adler32_combine_` |
| `compress.c.lean` | `compressBound_z` |
| `crc32.c.lean` | `byte_swap`, `crc_word`, `crc_word_big`, `multmodp`, `x2nmodp`, `braidTab`, `braidBigTab`, `crcByte`, and the helper `loadWord` |
| `deflate.c.lean` | `deflatePrime`, `deflate`, `deflateBound_z` |
| `deflate_base.c.lean` | `d_code`, `tally_dist`, `putShortMSB` |
| `deflate_strategies.c.lean` | `longest_match`, `deflate_stored` |
| `gzguts.h.lean` | the helpers `load32`, `store32`, `load64`, `store64` |
| `gzlib.c.lean` | `gzbuffer` |
| `gzread.c.lean` | `gz_load`, `gz_look`, `gz_fetch`, `gz_read`, `gzungetc` |
| `gzwrite.c.lean` | `gz_init`, `gz_comp` |
| `infback.c.lean` | `back_STORED` |
| `inffast.c.lean` | `inflate_fast` |
| `inflate.c.lean` | `inflateReset2`, `inflatePrime`, `ZSWAP32`, `CRC2`, `CRC4`, `inflate_STORED`, `inflate_HCRC`, `inflate_OS`, `inflate_FLAGS`, `inflate_HEAD`, `inflateSync`, `inflateMark` |
| `inftrees.c.lean` | `buildStep` |
| `trees.c.lean` | `put_short`, `d_code`, `bi_reverse`, `bi_flush`, `gen_codes`, `_tr_stored_block`, `_tr_align`, `compress_block`, `detect_data_type`, `_tr_flush_block`, `_tr_tally` |
| `zutil.c.lean` | `zlibCompileFlags` |

Some of these plain shifts are not an unsigned operand with a literal count:

- The operand is signed and the count is a literal: `windowBits >>> 4` in `inflateReset2`,
  `(s->bi_valid + bits) >> 3` in `deflatePrime`, `n >>= 1` on a `z_off64_t` in `x2nmodp`,
  `k <<< 3` in `braidTab` and `braidBigTab`, `-(1L << 16)` in `inflateMark`,
  `(state->flags >> 9) & 1` in `inflate_HCRC` (`flags` is an `int`), and the constants
  `STORED_BLOCK << 1`, `STATIC_TREES << 1` and `DYN_TREES << 1` in `trees.c.lean`. A right shift
  of a negative value is implementation-defined in C, not undefined; the build's compiler and
  Lean's `Int32` and `Int64` both shift arithmetically.
- The count is a variable: `value >>> put` in `deflatePrime` (signed operand; `put` has passed
  the checked `ishl 1 put` of the same loop pass), and `(1 : Int64) <<< bits.toInt64` in
  `inflatePrime` (the tests before it leave `1 ≤ bits ≤ 16`, so this one is normalisation 4).
- The helpers `loadWord`, `load64` and `store64` shift by eight times a loop index below 8.

**5. Locals of `inflate` that C leaves uninitialised start at fixed values.** `IL.init` in
`inflate.c.lean` gives the locals `copy`, `len`, `from`, `here` and `last` the values 0, NULL
and a zero `code`. `inflateBack` uses the same record. The rule for an uninitialised integer is
an arbitrary value, and a theorem must hold for every value. The file header of
`inflate.c.lean` records this choice. Whether `inflate` can read one of these locals before
assigning it is **to confirm** by source review: the model fixes these values, so a proof
about the current translation does not show it.

**6. A store is written after a call that follows it in C.** The C stores a field and then
calls `zmemcpy`. The Lean runs the copy first and writes the field in a record update after it.

| File, function | C | Lean |
| --- | --- | --- |
| `deflate_strategies.c.lean`, `deflate_stored` | `s->matches = 2; zmemcpy(s->window, s->strm->next_in - s->w_size, s->w_size);` | `memcpyB` runs first. `matches := 2` is in the update after it, together with `strstart` and `insert`. |
| `deflate_strategies.c.lean`, `deflate_stored` (the two window slides) | `s->strstart -= s->w_size; zmemcpy(s->window, s->window + s->w_size, s->strstart);` The second slide has `s->block_start -= s->w_size;` before these. | The new values are the locals `ss` and `bs`. `memcpyB` runs, and one update after it stores `strstart` (and `block_start`) with `matches` and `insert`. |

In these places the copy reads and writes bytes of the window and of the input, and the moved
stores write fields of the state record.

A related regrouping has no call in it. In `flush_pending` (`deflate_base.c.lean`) the C
interleaves stores to two records: `strm->next_out += len; s->pending_out += len;
strm->total_out += len; strm->avail_out -= len; s->pending -= len;`. The Lean computes both new
pointers, writes the three stream fields in one update and then the two state fields in
another. Normalisation 3 speaks of consecutive assignments to one record.

## Integer types and arithmetic

Macros are expanded in source order. Reads, writes, branch conditions and early returns are
kept. Short-circuit evaluation is kept where the right operand is a call or a read through a
pointer that the left operand tests; the places where an operand is evaluated early are form 2
of [the list above](#forms-not-covered-by-the-four-accepted-normalisations).
Integer promotions and the usual arithmetic conversions are written out:
`unsigned short + int` is computed as `int` on this target.

| C type | Lean type on LP64 |
| --- | --- |
| `unsigned char` | `UInt8` |
| `unsigned short` | `UInt16` |
| `unsigned`, `unsigned int` | `UInt32` |
| `unsigned long`, `size_t`, `z_size_t` | `UInt64` |
| `int` | `Int32` |
| `long`, `z_off_t`, `z_off64_t` | `Int64` |

Unsigned operations wrap at their width. A signed operation is checked for representability,
except under normalisation 4. A shift by a variable count goes through a checked helper. The
helper for an unsigned operand faults when the count is not below the operand width. The helpers
for an `int` operand also fault on a negative count, and the left shifts among them on a negative
operand or a result that does not fit. A shift by a literal count below the operand width is
written with the plain operator; form 4 of the list above names the places and the exceptions.
Lean's arithmetic is total; that alone never justifies a C operation.

An enumerator has a `UInt32` name for unsigned state fields and an `Int32` name with the suffix
`_i` for uses at C type `int`. A macro that collides with an enumerator is named `GZ_<name>`:
`GZ_COPY` is the `gzguts.h` macro, and `COPY` is the `inflate.h` enumerator.

## How each C object is represented

| C object or operation | Representation |
| --- | --- |
| Struct | A record in its kind's heap table, referenced by block number |
| `p->f` and `p->f = v` | Record-field read and record update, without ABI offset arithmetic |
| Embedded array | An array field; copying the record copies it |
| Pointer into an embedded array | A reference that names the record, the field and an index |
| Byte buffer | A heap byte block and an offset |
| `head` and `prev` word arrays | A heap word block and an element offset |
| Static table | A static reference or a checked constant table; a store faults |
| Local whose address is taken | A represented object made at its declaration and released before each return |
| String literal | `strLitRef` into the closed, read-only table of the source's literals; no allocation |
| `ZALLOC` and `ZFREE` | The default allocator with its failure oracle; a custom allocator is `Fault.ub` |

The record types are generated from the C headers ([runtime schema](../runtime-schema.md)).
A generated array field does not carry its declared length in its type; proofs carry that fact.

A local object does not consume a call of the allocation-failure oracle: giving it the
semantics of `ZALLOC` would change which real allocation fails. A local whose address is taken
does not stay live after its C lifetime ends.

## Fresh memory

Fresh integer contents are arbitrary. A theorem holds for every value, including values read or
copied beyond the initialised part of `prev` or of the match lookahead. A translation does not
replace those contents by zero.

A fresh pointer field is NULL in this model. That is weaker than C, where it is indeterminate.
A NULL comparison, a copy and a `free(NULL)` do not detect an unwritten field, so a missing
write of a pointer field does not show in the model. That the C writes each pointer field of a
newly allocated record before it reads it is **to confirm** by source review: no theorem states
it, and none can in this model. What the proofs show is narrower: the invariant of each kind of
state (`InflateInv`, `DInv`, `GzInv`) holds on every reachable stream and on every gz handle
with a history, and the invariant says what the pointer fields it names hold
([trusted base](../trusted-base.md#2-runtime-and-object-schema)).

A proof does not assume that repeated reads of an uninitialised cell agree, although the model
gives the cell one stable value.

For a record type `K` of the schema, `K.zeroed` is the record after an actual whole-record
zeroing statement in the C, and `K.garbage` is a fresh record. They are not interchangeable.
See [safety, model limits](../spec/safety.md#3-faults-undefined-behaviour-and-model-gaps).

## Library operations

`K` below stands for a record kind, as in `stZStream` and `copyInflateState`.

| C operation | Translation |
| --- | --- |
| Byte `memcpy`, `zmemcpy` | `memcpyB`, with its range and non-overlap checks |
| Whole-record `memcpy` | `copyK dst src`; it checks overlap, unlike a load followed by a store |
| `memmove` | The move operation, which permits overlap |
| Byte `memset` | `memsetB` |
| Zero a wider array | `Ptr.fill p 0 n`, with the element count |
| Fill a wider array with byte `c` | `Ptr.memset p c n`, which repeats `c` in each element |
| Whole-record zeroing | `stK p K.zeroed` |

`memcpy` copies arbitrary values as well as initialised ones. The runtime faults on NULL even
for a zero-length copy. The modelled operations count elements, so a C byte count is converted.
[Trusted base](../trusted-base.md) lists their differences from C.

## Control flow

A loop carries its locals in explicit state, through a runtime loop. A `do … while` runs the body
before the test. `break`, `continue` and a `return` inside a loop use control tags that keep
their distinct destinations. A `goto` is modelled by an exception (`goto inf_leave` in `inflate`)
or by a flag
that makes a block run again (`goto dolen` in `inflate_fast`). A switch fall-through is a tail
call of the next case. The header comments of `inflate.c.lean` and `inffast.c.lean` describe
their schemes.

The loop bound is not permission to stop early. Exhaustion is `Fault.outOfFuel`, and a
termination proof excludes it. Every undefined operation the C can reach stays visible as
`Fault.ub`, within the documented model differences: pointer bounds, liveness, read-only
stores, invalid comparisons, signed arithmetic and overlapping copies.
