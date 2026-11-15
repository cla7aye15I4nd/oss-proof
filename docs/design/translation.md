# Translating C without changing its behaviour

Each C function of the selected source is rewritten by hand as a Lean function, statement by
statement. This page gives the rule, the four accepted normalisations, and two functions shown
with their C, so that a reader can compare a translation with its source himself. The kernel
does not check a translation against C. Review and differential tests do; tests are evidence of
fidelity, not proof.

[Architecture](architecture.md) defines the types used here (`M`, `Fault`, `cwhile`, pointers).
[Trusted base](../trusted-base.md) records the limits of the model.

## The rule

A translation keeps the statements of the C function in their order. It does not reorder
checks, drop a read or a write, or replace an algorithm. A proof that is hard is not a reason to
change a translation. A mismatch with the C is a translation bug: it is corrected against the C,
and a differential test that catches it is added.

Four normalisations are accepted (owner's decision of 2026-11-15). They are listed with examples
in [the accepted normalisations](#the-accepted-normalisations):

1. An out-parameter of an internal function is passed by value and returned as a second result.
2. Two reads of one location with no store between them are one read.
3. Consecutive assignments to fields of one record are one record update.
4. A signed operation that a preceding test of the same function keeps in range is written
   with the plain operator.

Anything outside these four is a translation bug.

## The source that is translated

One build is translated: default x86_64 Linux, static library, LP64. A runtime parameter never
selects a different compiled branch. Preprocessor choices are resolved against `zlib/` with the
patches of `patches/` applied in name order.

| Source family | Selected branches |
| --- | --- |
| Compression | Gzip enabled; `FASTEST`, `LIT_MEM`, `UNALIGNED_OK` and debug checks disabled; default `MAX_WBITS` 15 and `MAX_MEM_LEVEL` 9 |
| Decode tables and inflate | Gzip and fast decoding enabled; `BUILDFIXED`, `MAKEFIXED`, `PKZIP_BUG_WORKAROUND`, `INFLATE_STRICT` and invalid-distance recovery disabled. Fixed tables come from `inffixed.h` |
| CRC | Static tables; braid parameters `N = 5` and `W = 8`. The little-endian branch runs; the big-endian branch is not exercised |
| Gzip files | LP64 large-file entries and C99 formatting; Windows, wide-character and `Z_SOLO` paths are not selected. One I/O request is at most `2^30` bytes |

Each translation file lists its preprocessor choices in its header comment. These choices are
readings of the source for this build. No proof checks them: **to confirm** by review against
the preprocessed source.

`zlib/X.c` is translated in `ZlibF/Zlib/X.c.lean`, and `zlib/X.h` in `ZlibF/Zlib/X.h.lean`.
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

Its translation in `ZlibF/Zlib/inflate.c.lean`:

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

The start of `inflateReset2` in `zlib/inflate.c`:

```c
    if (inflateStateCheck(strm)) return Z_STREAM_ERROR;
    state = (struct inflate_state FAR *)strm->state;

    if (windowBits < 0) {
        if (windowBits < -15)
            return Z_STREAM_ERROR;
        wrap = 0;
        windowBits = -windowBits;
    }
    else {
        wrap = (windowBits >> 4) + 5;
        if (windowBits < 48)
            windowBits &= 15;
    }

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
`pending` and `bits` of `deflatePending`, and `bits` of `deflateUsed`. There it is a limit of the
model as well: the caller's cell is not memory, so a cell that overlaps one of the buffers
cannot be expressed. [Deviations](../deviations.md) has the row for `compress*`. The length cells
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

## Integer types and arithmetic

Macros are expanded in source order. Reads, writes, branch conditions, early returns and
short-circuit evaluation are kept. Integer promotions and the usual arithmetic conversions are
written out: `unsigned short + int` is computed as `int` on this target.

| C type | Lean type on LP64 |
| --- | --- |
| `unsigned char` | `UInt8` |
| `unsigned short` | `UInt16` |
| `unsigned`, `unsigned int` | `UInt32` |
| `unsigned long`, `size_t`, `z_size_t` | `UInt64` |
| `int` | `Int32` |
| `long`, `z_off_t`, `z_off64_t` | `Int64` |

Unsigned operations wrap at their width. A signed operation is checked for representability,
except under normalisation 4. A shift is checked for the operand width and the count, including
a negative count. Lean's arithmetic is total; that alone never justifies a C operation.

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

The record types are generated from the C headers ([runtime schema](../runtime-schema.md)). A
translator adds to the schema through the generator and does not write a second record layout.
A generated array field does not carry its declared length in its type; proofs carry that fact.

A local object does not consume a call of the allocation-failure oracle: giving it the
semantics of `ZALLOC` would change which real allocation fails. A local whose address is taken
does not stay live after its C lifetime ends.

## Fresh memory

Fresh integer contents are arbitrary. A theorem holds for every value, including values read or
copied beyond the initialised part of `prev` or of the match lookahead. A translation does not
replace those contents by zero.

A fresh pointer field is NULL in this model. That is weaker than C, where it is indeterminate.
For every pointer field that is read from a newly allocated record, a translation comment names
the earlier statement that writes it, and the proof establishes that order. A NULL comparison, a
copy and a `free(NULL)` do not detect an unwritten field. A proof does not assume that repeated
reads of an uninitialised cell agree, although the model gives the cell one stable value.

For a record type `K` of the schema, `K.zeroed` is the record after an actual whole-record
zeroing statement in the C, and `K.garbage` is a fresh record. They are not interchangeable.
See [safety, section 3](../spec/safety.md#3-faults-undefined-behaviour-and-model-gaps).

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
`Libc.lean` and the generated `LibcTables.lean` define them; [trusted base](../trusted-base.md)
lists their differences from C.

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

## What a new or changed translation comes with

- The source module that mirrors the C file.
- A function-level differential test.
- Comments that record each translation decision beside the C lines it concerns.

A change to `ZlibF/Runtime/` is its own commit, with the reason and the proofs it affects,
because every function proof depends on it. The runtime changes only for a confirmed mismatch
with C. [Checking](../checking/README.md) describes the audit and the proof mutants.

When a proof exposes a possible upstream bug, the public domain stays as it is. The cause is one
of four: the proof technique, a wrong specification, a translation mismatch, or a real C defect.
The last is called a confirmed finding only with a concrete input and a sanitizer reproduction.

[Design](README.md) · [Documentation home](../README.md)
