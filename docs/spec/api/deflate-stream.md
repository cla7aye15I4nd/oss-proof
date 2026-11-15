# Stream compression

[API manual](README.md) · [Shared stream rules](streams.md) · [Stream decompression](inflate-stream.md)

Use a `z_stream` compressor when input arrives in pieces, output space is limited, or you
need a chosen wrapper, dictionary or flush boundary. A wrapper is the header, trailer and
integrity information added around the DEFLATE data; raw DEFLATE has none. Initialize once, call `deflate` with
successive buffers, and end the stream even if compression is abandoned. For a single buffer,
see [compress and compress2](utility.md#compress2_z).

| Task | Entries |
| --- | --- |
| Start or reuse | [Init](#deflateinit_), [configured init](#deflateinit2_), [reset](#deflatereset), [reset retaining history](#deflateresetkeep) |
| Supply metadata or history | [Dictionary](#deflatesetdictionary), [read history](#deflategetdictionary), [gzip header](#deflatesetheader) |
| Compress and size output | [Deflate](#deflate), [bound](#deflatebound_z), [pending output](#deflatepending), [last flush bits](#deflateused) |
| Adjust or branch | [Parameters](#deflateparams), [tuning](#deflatetune), [priming](#deflateprime), [copy](#deflatecopy) |
| Release storage | [End](#deflateend) |

The contracts follow the pinned `deflate.c` and `zlib.h` in the default LP64 Linux build. No
patch touches `deflate.c` ([patches](../../../patches/README.md)).
These are focused contracts: Pre describes ordinary correct use and is deliberately narrower than
what the function accepts. Cases outside Pre that the C still handles appear under Errors or
**Outside focused scope**. A call outside Pre is not thereby undefined, and it need not return an
error code. See [how to read a contract](contracts.md) for the domain and effect labels.

**What is proved.** Safety only: each call returns without undefined behaviour or a memory error,
writes only what its goal names, and leaks nothing ([safety](../safety.md)). Each entry gives its
goal under **Proof goals**, in the five items and with the fixed phrases that
[Reading a Proof goals paragraph](contracts.md#reading-a-proof-goals-paragraph) defines: the goal and its theorem; the conditions under which it
applies, in the order of the Lean statement; what it covers for every value; what it guarantees
(returns, state, writes, allocations); and what it leaves to another goal. The proof assumes the
conditions listed there, not the documentary Pre. Post, the return tables and the notes describe
functional behaviour. They are read from the C, are **to confirm** where no registered theorem
states them, and are not required for the safety results. [Progress](../../progress.md) records the
state of each goal.

## Shared conventions

Under each stated Pre, the documented behaviour is that the call terminates without a runtime
fault and that Post holds. A call that leaves the stream live preserves its representation
invariant. The part of this that is proved is the safety goal of the entry.

First, how data changes hands in one call. `next_in` points to the start of the input not yet read,
and `avail_in` is the number of bytes readable from there. `next_out` points to the next writable
position, and `avail_out` is the output room that remains, also in bytes. One call may consume only
part of the input and deliver only part of the output. Read the updated pointers and counts, take
the bytes delivered, then give the same stream more input or more output room.

- **Live stream:** a writable `z_stream` with a compressor state established by successful
  init or copy, preserved by legal calls, and not ended. The caller does not alter its
  internal state or allocator fields. Calls on one stream are sequential.
- **Buffers:** input covers `avail_in` readable bytes; output covers `avail_out` writable
  bytes. They do not overlap each other, the stream or its owned state. A non-NULL scalar
  result points to a writable cell separate from other results and stream memory.
  These separation conditions are assumptions of the contracts. Where a safety goal assumes one
  too, its **Proof goals** says so and [deviations](../../deviations.md) has a row.
- **Allocator:** the default allocator/free pair is used, or both fields are NULL before
  init. Allocation may fail on any attempt. Custom allocator callbacks are outside this page's scope.
- **Frame and ownership:** calls change only their stream, its owned state and stated
  output regions. Caller input is read-only. Caller buffers and header records remain caller-owned.
  Only init and copy allocate; only their failure cleanup and `deflateEnd` free memory.
  Other calls preserve the stream's allocation set.
- **Header lifetime:** a retained gzip header and its optional fields remain readable and
  unchanged while used. Non-NULL `name` and `comment` have a terminating zero; `extra`
  covers its stated length. The contracts on this page take `extra_len <= 65535`.
- **Checked refusals:** except for init and bounds, a failed stream check returns
  `Z_STREAM_ERROR` before normal operation, without writes. `deflateCopy` additionally
  clears a non-NULL destination state. Query output cells are untouched on this refusal.
- **Restricted domain** means these explicit memory, lifetime and call-order conditions,
  plus the entry's Pre. It does not mean every representable pointer or integer is accepted.
  Error summaries cover stream records and states that the checks can read, not arbitrary
  invalid addresses.
- **Reachable stream:** the proof goals speak of a reachable stream where the contracts say live
  stream ([how to read a contract](contracts.md)). A call that a goal covers extends the stream's
  history: when it returns, with any code, the stream is reachable again and the goal of the next
  call applies. `deflateEnd` ends the history.
- **Result cells as values:** `deflateGetDictionary`, `deflatePending` and `deflateUsed` report
  results through pointers (`uInt *dictLength`, `unsigned *pending`, `int *bits`). The translation
  does not model these cells as memory: each function takes only the fact that a pointer is NULL
  or not, and returns the values. So the goals say nothing about the address of a result cell, and
  a cell that overlaps another object cannot be expressed.

## deflateInit_

```c
int ZEXPORT deflateInit_(z_streamp strm, int level, const char *version, int stream_size);
```

Start a compressor with the default zlib wrapper and compression settings.

### Return values and next calls {#api-deflateinit_-returns}

**Return type.** `int` — zlib status code

The result separates an established compressor from compatibility, argument and allocation failures. Only Z_OK establishes a live stream that needs ending.

| Returned value | Meaning and conditions | Caller’s next step |
| --- | --- | --- |
| `Z_OK`<br>**Compressor established** | Compatibility and parameters are valid, and all five allocations succeed; zlib wrapping, window 15, memory level 8 and the default strategy are installed. | Supply buffers and begin compression; eventually call deflateEnd, even if abandoning the task. |
| `Z_VERSION_ERROR`<br>**Compatibility refused** | version is NULL, its first byte does not match, or stream_size differs from sizeof(z_stream). This check precedes the strm check and changes no stream fields. | Correct the version and structure size before initialization; this result creates no new state to release. |
| `Z_STREAM_ERROR`<br>**Null stream** | Compatibility passes, but strm is NULL. | Provide a writable stream record satisfying initialization preconditions. |
| `Z_STREAM_ERROR`<br>**Parameters refused** | level is neither -1 nor 0..9. Refusal precedes allocation, but msg has been cleared and default allocator installation may have cleared opaque. | Correct the parameters and reinitialize under the init preconditions; there are no new allocations to end. |
| `Z_MEM_ERROR`<br>**State allocation failed** | The initial state allocation fails; state retains its entry value and no newly allocated block remains live. | After addressing memory pressure, retry under the init preconditions; this failure needs no deflateEnd. |
| `Z_MEM_ERROR`<br>**Buffer allocation failed and cleaned up** | After state allocation succeeds, all four buffer allocations are attempted. Any failure releases every new block, sets state to NULL and reports insufficient memory in msg. | Cleanup is complete for this call; address memory pressure before initializing again. |

**Reading the result.**

- No input is consumed and no output is written. Level -1 selects 6.

### Calling conditions and effects {#api-deflateinit_-contract}

**Domain:** Restricted domain. **Effect:** allocate and initialise.

**Pre:** `strm` is writable and owns no live compressor state. Its allocator fields are
initialised as above. `level` is -1 or 0..9. `version` has a readable first byte matching
`ZLIB_VERSION`, and `stream_size == sizeof(z_stream)`.

**Proof goals.**

- **Goal.** `Goal.deflateInit__safety` ([Safety/Initialisation.lean](../../../ZlibF/Spec/Safety/Initialisation.lean)); required. Theorem: `ZlibF.Spec.Public.InitSafetyProof.deflateInit__safety` ([public-init-safety.lean](../../../ZlibF/Proof/public-init-safety.lean)).
- **Applies when** (`InitArguments`):
    1. the heap is a library heap (`Fresh`, `Uniq`, `LibraryGlobals`);
    2. `version` is NULL or its first byte is readable (`VersionValue`);
    3. `strm` is NULL, or points to a readable stream record whose `zalloc` and `zfree` are each NULL or the default function (`DefaultOrNull`).
- **Covered without condition.** Every `level`, valid or not; every `stream_size`; every value of the first byte of `version`; every value of the other fields of the record, `state` included; every allocation outcome. The goal is wider than Pre: it also covers a NULL `strm`, a wrong version or `stream_size`, and a record whose `state` is not NULL. If that record was a live stream, the call still returns, but the old state stays allocated and the record no longer points to it: the account records that leak, it does not exclude it.
- **Guarantees** (`InitResultSafe`).
    - *Returns.* The call returns. With a NULL `strm` the code is `Z_VERSION_ERROR` or `Z_STREAM_ERROR`.
    - *State.* With `Z_OK`, `strm` is a reachable stream.
    - *Writes.* With a NULL `strm`, nothing: the heap is unchanged. Otherwise only the stream record and blocks the call itself allocates.
    - *Allocations.* With `Z_OK`, every block the call allocated is one of the stream's own blocks, and nothing is freed (`LiveChange`). With any other code the allocated blocks are the same as before the call. So no leak here means no leak of the call's own allocations: a state the record pointed to before the call stays allocated.
- **Not in this goal.** A stream whose `zalloc` or `zfree` is a custom function: outside every goal ([deviations](../../deviations.md)). Which code each refusal and each allocation failure returns, and the field values after the call: functional goal `Goal.deflateInit_`, not required for the safety results. That some call does return `Z_OK`: `Goal.deflate_initialisation_domain` ([Safety/Domains.lean](../../../ZlibF/Spec/Safety/Domains.lean)), required.

<details markdown="1" class="ar-return-exact" data-return-exact="deflateInit_"><summary>Complete return conditions and boundaries</summary>

**Post:** the `deflateInit2_` contract holds with method `Z_DEFLATED`, window 15,
`memLevel` 8 and `Z_DEFAULT_STRATEGY`. Level -1 selects 6. No input is consumed and
no output is written. Return `Z_OK` on success or `Z_MEM_ERROR` with complete cleanup.

**Outside focused scope:** the same version and argument refusals as `deflateInit2_` apply.
The `deflateInit` macro supplies version and structure size.

</details>

## deflateInit2_

```c
int ZEXPORT deflateInit2_(z_streamp strm, int level, int method, int windowBits,
                           int memLevel, int strategy, const char *version, int stream_size);
```

Start a compressor with a chosen wrapper and compression settings.

The parameters decide different things. `level` trades compression speed against match-search
effort. `method` selects the compression method; this entry accepts DEFLATE only. `memLevel` sets
the memory given to the internal index and the symbol buffer. `strategy` adjusts which matching or
coding strategy is used. `windowBits` encodes both the wrapper and the window size: remove the sign
or the added constant to get an exponent b, and the window has `2^b` bytes. So 15, -15 and 31 all
mean 32768 bytes, with a zlib, a raw and a gzip wrapper.

### Return values and next calls {#api-deflateinit2_-returns}

**Return type.** `int` — zlib status code

The result separates an established compressor from compatibility, argument and allocation failures. Only Z_OK establishes a live stream that needs ending.

| Returned value | Meaning and conditions | Caller’s next step |
| --- | --- | --- |
| `Z_OK`<br>**Compressor established** | Compatibility and parameters are valid, and all five allocations succeed; the selected wrapper and settings are installed. | Supply buffers and begin compression; eventually call deflateEnd, even if abandoning the task. |
| `Z_VERSION_ERROR`<br>**Compatibility refused** | version is NULL, its first byte does not match, or stream_size differs from sizeof(z_stream). This check precedes the strm check and changes no stream fields. | Correct the version and structure size before initialization; this result creates no new state to release. |
| `Z_STREAM_ERROR`<br>**Null stream** | Compatibility passes, but strm is NULL. | Provide a writable stream record satisfying initialization preconditions. |
| `Z_STREAM_ERROR`<br>**Parameters refused** | method, level, windowBits, memLevel or strategy is outside its accepted range. Refusal precedes allocation, but msg has been cleared and default allocator installation may have cleared opaque. | Correct the parameters and reinitialize under the init preconditions; there are no new allocations to end. |
| `Z_MEM_ERROR`<br>**State allocation failed** | The initial state allocation fails; state retains its entry value and no newly allocated block remains live. | After addressing memory pressure, retry under the init preconditions; this failure needs no deflateEnd. |
| `Z_MEM_ERROR`<br>**Buffer allocation failed and cleaned up** | After state allocation succeeds, all four buffer allocations are attempted. Any failure releases every new block, sets state to NULL and reports insufficient memory in msg. | Cleanup is complete for this call; address memory pressure before initializing again. |

**Reading the result.**

- No input is consumed and no output is written. Level -1 selects 6.

### Calling conditions and effects {#api-deflateinit2_-contract}

**Domain:** Restricted domain. **Effect:** allocate and initialise.

**Pre:** the stream and version conditions of `deflateInit_` hold. Parameters are:
`level` -1 or 0..9; `method == Z_DEFLATED`; `memLevel` 1..9; `strategy` 0..4;
`windowBits` 8..15 for zlib, -15..-9 for raw, or 25..31 for gzip.

**Proof goals.**

- **Goal.** `Goal.deflateInit2__safety` ([Safety/Initialisation.lean](../../../ZlibF/Spec/Safety/Initialisation.lean)); required. Theorem: `ZlibF.Spec.Public.InitSafetyProof.deflateInit2__safety` ([public-init-safety.lean](../../../ZlibF/Proof/public-init-safety.lean)).
- **Applies when** (`InitArguments`):
    1. the heap is a library heap (`Fresh`, `Uniq`, `LibraryGlobals`);
    2. `version` is NULL or its first byte is readable (`VersionValue`);
    3. `strm` is NULL, or points to a readable stream record whose `zalloc` and `zfree` are each NULL or the default function (`DefaultOrNull`).
- **Covered without condition.** Every `level`, `method`, `windowBits`, `memLevel` and `strategy`, valid or not; every `stream_size`; every value of the first byte of `version`; every value of the other fields of the record, `state` included; every allocation outcome. The goal is wider than Pre: it also covers a NULL `strm`, a wrong version or `stream_size`, and a record whose `state` is not NULL. If that record was a live stream, the call still returns, but the old state stays allocated and the record no longer points to it: the account records that leak, it does not exclude it.
- **Guarantees** (`InitResultSafe`).
    - *Returns.* The call returns. With a NULL `strm` the code is `Z_VERSION_ERROR` or `Z_STREAM_ERROR`.
    - *State.* With `Z_OK`, `strm` is a reachable stream.
    - *Writes.* With a NULL `strm`, nothing: the heap is unchanged. Otherwise only the stream record and blocks the call itself allocates.
    - *Allocations.* With `Z_OK`, every block the call allocated is one of the stream's own blocks, and nothing is freed (`LiveChange`). With any other code the allocated blocks are the same as before the call. So no leak here means no leak of the call's own allocations: a state the record pointed to before the call stays allocated.
- **Not in this goal.** A stream whose `zalloc` or `zfree` is a custom function: outside every goal ([deviations](../../deviations.md)). Which code each refusal and each allocation failure returns, and the field values after the call: functional goal `Goal.deflateInit2_`, not required for the safety results. That some call does return `Z_OK`: `Goal.deflate_initialisation_domain` ([Safety/Domains.lean](../../../ZlibF/Spec/Safety/Domains.lean)), required.

<details markdown="1" class="ar-return-exact" data-return-exact="deflateInit2_"><summary>Complete return conditions and boundaries</summary>

**Post:** `Z_OK` establishes a live stream with five owned allocations and the selected
settings. A zlib window request of 8 becomes 9. Totals are zero, `msg` is NULL,
`data_type` is `Z_UNKNOWN`, and `adler` is 1 for raw/zlib or 0 for gzip.
I/O pointers and available counts are unchanged; no bytes are consumed or emitted.
The caller releases the state with `deflateEnd`.

`Z_MEM_ERROR` leaves no newly allocated block live. If the state allocation fails,
`state` retains its entry value. If a later allocation fails, `state` becomes NULL and
`msg` reports insufficient memory. Once the state allocation succeeds, all four buffer
allocations are attempted before failure cleanup.

**Outside focused scope:** a NULL/mismatched version first byte or wrong structure size
returns `Z_VERSION_ERROR` without changing the stream. With compatible version and NULL
`strm`, return `Z_STREAM_ERROR`. Other scalar parameters outside the accepted ranges
return `Z_STREAM_ERROR` before allocation, after clearing `msg` and installing default
allocator fields where needed. Installing the default allocator clears `opaque`.
The safety goal covers these calls: each one returns and leaves the allocated blocks as they
were. Which code each one returns is stated by the functional init goals.

</details>

## deflateSetDictionary

```c
int ZEXPORT deflateSetDictionary(z_streamp strm, const Bytef *dictionary, uInt dictLength);
```

Load preset bytes as compression history without emitting them as input data.

`dictLength` is the byte count of the whole dictionary given, and `w_size` is the configured
history window in bytes. Of a dictionary that is too long, only the usable suffix is kept as
history, but the zlib dictionary identifier still covers the whole dictionary given.

### Return values and next calls {#api-deflatesetdictionary-returns}

**Return type.** `int` — zlib status code

The result says whether preset history was accepted; the dictionary is not emitted as ordinary compressed input.

| Returned value | Meaning and conditions | Caller’s next step |
| --- | --- | --- |
| `Z_OK`<br>**History loaded** | Dictionary and stream preconditions hold; history retains an available suffix of at most one window, while the zlib checksum covers the full dictionary. | Begin compression; a decoder requiring preset history must receive the same dictionary. next_in and avail_in are restored and no output is delivered. |
| `Z_STREAM_ERROR`<br>**Dictionary conditions refused** | The stream check fails, or the request uses gzip, a NULL dictionary, zlib past its initial state, nonzero lookahead, or raw input outside a completed block boundary; no stream changes occur. | Establish legal dictionary-call conditions. If an existing live stream remains, use a legal operation or deflateEnd. |

**Reading the result.**

- The safety goal and the functional goal both cover a raw dictionary replaced at a legal block boundary and repeated zlib calls before the first deflate; repeated zlib calls accumulate Adler-32.

### Calling conditions and effects {#api-deflatesetdictionary-contract}

**Domain:** Restricted domain. **Effect:** update history and dictionary checksum.

**Pre:** live raw or zlib stream, immediately after init or `deflateReset`, before its first
`deflate` and first dictionary call. `dictionary` is non-NULL, covers `dictLength`
readable bytes and is separate from the window.

**Proof goals.**

- **Goal.** `Goal.deflateSetDictionary_safety` ([Safety/Streams.lean](../../../ZlibF/Spec/Safety/Streams.lean)); required. Theorem: `ZlibF.Spec.Public.StreamCallSafetyProof.deflateSetDictionary_safety` ([public-stream-call-safety.lean](../../../ZlibF/Proof/public-stream-call-safety.lean)).
- **Applies when** (`StreamCallDomain`):
    1. `strm` is a reachable stream (`StreamReachable`);
    2. the platform size bound holds (`ByteObjectsFit`);
    3. `dictionary` is NULL or points to `dictLength` readable bytes outside the stream's own blocks (`CallerRange`).
- **Covered without condition.** Every `dictLength` and every dictionary content. Every reachable stream, in every phase: before the first `deflate`, mid-stream, while finishing, and after `Z_STREAM_END`. The goal is wider than Pre: `dictionary` may be NULL, the wrapper may be gzip, and the call may come at any point. The C refuses the cases listed in the return table.
- **Guarantees** (`StreamCallSafe`).
    - *Returns.* The call returns.
    - *State.* The stream keeps its invariant (`StreamInvariant`).
    - *Writes.* Only the stream record and the stream's own blocks.
    - *Allocations.* Exact allocation account (`LiveChange`).
- **Not in this goal.** A NULL or inconsistent stream, for example one that was already ended: `Goal.deflate_refusal`. Which code is returned and the history after the call: functional goal `Goal.deflateSetDictionary`, not required for the safety results.

<details markdown="1" class="ar-return-exact" data-return-exact="deflateSetDictionary"><summary>Complete return conditions and boundaries</summary>

**Post:** return `Z_OK`. History retains an available suffix of the dictionary, at most
one window. The dictionary checksum for zlib covers the entire supplied dictionary.
The original `next_in` and `avail_in` are restored; `total_in` increases by
`min(dictLength, w_size)`. No compressed output is delivered and no allocation occurs.
The decoder must be given the same preset dictionary when required.

**Outside focused scope:** gzip, NULL dictionary, zlib after its initial state, nonzero
lookahead, or raw input not at a completed block boundary returns `Z_STREAM_ERROR`
without changes. Raw replacement at legal boundaries and repeated zlib calls before the first
`deflate` are covered by the safety goal and by the functional goal. Repeated zlib calls
accumulate Adler-32 rather than restarting it.

</details>

## deflateGetDictionary

```c
int ZEXPORT deflateGetDictionary(z_streamp strm, Bytef *dictionary, uInt *dictLength);
```

Read the current compression history, including accepted lookahead.

"Accepted" here does not mean encoded. The compressor reads some input ahead into the window while
it decides on matches. The internal field `strstart` is the array index of the next byte to
process, and `lookahead` is the number of bytes read ahead after it. In the formula below, `w_size`
is the configured history window in bytes, not the capacity `window_size` of the whole physical
array. `n` is the number of history bytes this call copies at most.

### Return values and next calls {#api-deflategetdictionary-returns}

**Return type.** `int` — zlib status code

The status reports query success; optional output parameters carry the actual history bytes and length.

| Returned value | Meaning and conditions | Caller’s next step |
| --- | --- | --- |
| `Z_OK`<br>**History query complete** | For a live stream, a non-NULL dictionary receives the last n bytes of the window region, and a non-NULL dictLength receives n, where n = min(strstart + lookahead, window size). | Use the requested results; either output may be omitted independently, and the unchanged stream can continue legally. |
| `Z_STREAM_ERROR`<br>**Stream check failed** | The stream check fails before normal operation; neither the stream nor result cells are written. | Establish a live stream and the call preconditions; this result does not complete the operation. |

**Reading the result.**

- The byte count includes accepted lookahead; it need not contain a full window of all past input.

### Calling conditions and effects {#api-deflategetdictionary-contract}

**Domain:** Restricted domain. **Effect:** query with optional output buffers.

**Pre:** live stream. `dictionary` is NULL or writable for one window, separate from the
window; `dictLength` is NULL or a valid scalar output cell.

**Proof goals.**

- **Goal.** `Goal.deflateGetDictionary_safety` ([Safety/Streams.lean](../../../ZlibF/Spec/Safety/Streams.lean)); required. Theorem: `ZlibF.Spec.Public.StreamCallSafetyProof.deflateGetDictionary_safety` ([public-stream-call-safety.lean](../../../ZlibF/Proof/public-stream-call-safety.lean)).
- **Applies when** (`StreamCallDomain`):
    1. `strm` is a reachable stream (`StreamReachable`);
    2. the platform size bound holds (`ByteObjectsFit`);
    3. `dictionary` is NULL or points to `min(w_size, strstart + lookahead)` writable bytes, the number the call copies, outside the stream's own blocks (`CallerRange`).
- **Covered without condition.** Every reachable stream, in every phase: before the first `deflate`, mid-stream, while finishing, and after `Z_STREAM_END`. The goal is wider than Pre, which asks for one whole window of room. `dictLength` is a value in the translation, not memory ([shared conventions](#shared-conventions)), so the goal asks nothing of that pointer.
- **Guarantees** (`StreamCallSafe`).
    - *Returns.* The call returns.
    - *State.* The stream keeps its invariant (`StreamInvariant`).
    - *Writes.* Only the stream record, the stream's own blocks, and bytes within the 32768 bytes at `dictionary`.
    - *Allocations.* Exact allocation account (`LiveChange`).
- **Not in this goal.** A NULL or inconsistent stream, for example one that was already ended: `Goal.deflate_refusal`. The bytes copied and the length reported: functional goal `Goal.deflateGetDictionary`, not required for the safety results.

<details markdown="1" class="ar-return-exact" data-return-exact="deflateGetDictionary"><summary>Complete return conditions and boundaries</summary>

**Post:** return `Z_OK`. Let `n = min(strstart + lookahead, w_size)` in the live state.
A non-NULL `dictionary` receives the last `n` bytes of that window region, in order;
a non-NULL `dictLength` receives `n`. Either result may be omitted independently.
The stream is unchanged. History need not contain a full window of all previously supplied input.

</details>

## deflateResetKeep

```c
int ZEXPORT deflateResetKeep(z_streamp strm);
```

Restart output and progress counters while retaining compression history.

### Return values and next calls {#api-deflateresetkeep-returns}

**Return type.** `int` — zlib status code

The result says whether output progress was reset; success retains history that later compression may reference.

| Returned value | Meaning and conditions | Caller’s next step |
| --- | --- | --- |
| `Z_OK`<br>**Progress reset; history retained** | The stream is live in any phase. Counters, checksum and wrapper progress reset; pending output and unfinished lookahead are discarded, and the gzip header pointer is cleared. | Continue only with history retention accounted for; use deflateReset for empty history. The stream still owns its allocations. |
| `Z_STREAM_ERROR`<br>**Stream check failed** | The stream check fails before normal operation; neither the stream nor result cells are written. | Establish a live stream and the call preconditions; this result does not complete the operation. |

**Reading the result.**

- This entry is undocumented. I/O pointers and available counts are unchanged; no allocation or free occurs, and level, strategy and tuning are retained.

### Calling conditions and effects {#api-deflateresetkeep-contract}

**Domain:** Restricted domain. **Effect:** reset, retaining history and allocations.

**Pre:** live stream in any phase. This is an undocumented entry; use `deflateReset`
when the next compressed stream must start with empty history.

**Proof goals.** No required goal: `zlib.h` declares this function under "undocumented functions (not part of the zlib API)". A direct call is not a step of the deflate sequence goal either: `StreamOperation` leaves it out ([deviations](../../deviations.md), row "Direct `deflateResetKeep`"). A goal is stated for the single call, not required: `Goal.deflateResetKeep` ([Functional/Lifecycle.lean](../../../ZlibF/Spec/Functional/Lifecycle.lean)), with the theorem `ZlibF.Spec.Public.DeflateResetKeepProof.deflate_resetkeep_public` ([public-deflate-reset-keep.lean](../../../ZlibF/Proof/public-deflate-reset-keep.lean)).

<details markdown="1" class="ar-return-exact" data-return-exact="deflateResetKeep"><summary>Complete return conditions and boundaries</summary>

**Post:** return `Z_OK`. Totals become zero, `msg` becomes NULL and `data_type` becomes
`Z_UNKNOWN`. Pending output, unfinished lookahead and bit/block progress are discarded;
wrapper emission restarts and `adler` becomes 1 for raw/zlib or 0 for gzip.
The custom gzip header pointer is cleared. Level, strategy, tuning, window and hash history
are retained. I/O pointers and available counts are unchanged. No allocation or free occurs.

A later compressor call can refer to pre-reset history. This reset alone therefore does
not promise a stream decodable with an empty dictionary.

</details>

## deflateReset

```c
int ZEXPORT deflateReset(z_streamp strm);
```

Reuse a stream for new compression with empty history.

### Return values and next calls {#api-deflatereset-returns}

**Return type.** `int` — zlib status code

The result says whether the stream is ready for reuse with empty history. Success retains the existing allocations.

| Returned value | Meaning and conditions | Caller’s next step |
| --- | --- | --- |
| `Z_OK`<br>**Reset to empty history** | The stream is live in any phase, including after Z_STREAM_END. Counters, wrapper and pending progress reset; history and dictionary are forgotten, tuning returns to current-level defaults and the gzip header pointer is cleared. | Supply buffers for the new task and register its dictionary or gzip header if needed. Eventually call deflateEnd. |
| `Z_STREAM_ERROR`<br>**Stream check failed** | The stream check fails before normal operation; neither the stream nor result cells are written. | Establish a live stream and the call preconditions; this result does not complete the operation. |

**Reading the result.**

- Unfinished input and undelivered output are discarded; I/O pointers and counts are unchanged, while level, strategy, wrapper and memory settings are retained.

### Calling conditions and effects {#api-deflatereset-contract}

**Domain:** Restricted domain. **Effect:** reset, retaining allocations and configuration.

**Pre:** live stream in any phase, including after `Z_STREAM_END`.

**Proof goals.**

- **Goal.** `Goal.deflateReset_safety` ([Safety/Streams.lean](../../../ZlibF/Spec/Safety/Streams.lean)); required. Theorem: `ZlibF.Spec.Public.StreamCallSafetyProof.deflateReset_safety` ([public-stream-call-safety.lean](../../../ZlibF/Proof/public-stream-call-safety.lean)).
- **Applies when** (`StreamCallDomain`; this call has no argument condition):
    1. `strm` is a reachable stream (`StreamReachable`);
    2. the platform size bound holds (`ByteObjectsFit`).
- **Covered without condition.** Every reachable stream, in every phase: before the first `deflate`, mid-stream, while finishing, and after `Z_STREAM_END`.
- **Guarantees** (`StreamCallSafe`).
    - *Returns.* The call returns.
    - *State.* The stream keeps its invariant (`StreamInvariant`).
    - *Writes.* Only the stream record and the stream's own blocks.
    - *Allocations.* Exact allocation account (`LiveChange`).
- **Not in this goal.** A NULL or inconsistent stream: no required goal covers it for this function; the lemma `Zlib.Deflate.Proofs.deflateReset_reject` ([deflate.c.life.reset.lean](../../../ZlibF/Proof/deflate.c.life.reset.lean)) states the refusal. The return value and the field values after the call: functional goal `Goal.deflateReset`, not required for the safety results.

<details markdown="1" class="ar-return-exact" data-return-exact="deflateReset"><summary>Complete return conditions and boundaries</summary>

**Post:** return `Z_OK`. The `deflateResetKeep` counter, wrapper and pending-output reset
holds, and history is logically empty. A previous dictionary is forgotten; tuning returns
to the defaults for the current level. The level and strategy last selected by
`deflateParams`, wrapper, window and memory settings are retained. The gzip header is
forgotten. I/O pointers and available counts are unchanged. No allocation or free occurs.
Unfinished input already accepted and undelivered output are discarded.

</details>

## deflateSetHeader

```c
int ZEXPORT deflateSetHeader(z_streamp strm, gz_headerp head);
```

Select the header for the next gzip stream.

### Return values and next calls {#api-deflatesetheader-returns}

**Return type.** `int` — zlib status code

The result says whether the gzip header pointer was registered; success does not mean header bytes have been emitted.

| Returned value | Meaning and conditions | Caller’s next step |
| --- | --- | --- |
| `Z_OK`<br>**Header pointer registered** | A live gzip stream accepts head; NULL selects defaults, while a non-NULL header remains caller-owned and no header bytes are copied or emitted yet. | Keep the record and optional fields alive and unchanged through header emission; continue with deflate. Either reset clears the pointer. |
| `Z_STREAM_ERROR`<br>**Stream refuses gzip header** | The stream check fails or the wrapper is not gzip; nothing changes. | Register under the header-call preconditions on a live gzip stream; an existing live stream can still continue legally or end. |

**Reading the result.**

- Focused use registers before the first deflate; late registration is accepted but does not rewrite already emitted header bytes.

### Calling conditions and effects {#api-deflatesetheader-contract}

**Domain:** Restricted domain. **Effect:** retain a caller-owned header pointer.

**Pre:** live gzip stream, after init or reset and before its first `deflate`.
`head` is NULL for defaults, or satisfies the shared header conditions.

**Proof goals.**

- **Goal.** `Goal.deflateSetHeader_safety` ([Safety/Streams.lean](../../../ZlibF/Spec/Safety/Streams.lean)); required. Theorem: `ZlibF.Spec.Public.StreamCallSafetyProof.deflateSetHeader_safety` ([public-stream-call-safety.lean](../../../ZlibF/Proof/public-stream-call-safety.lean)).
- **Applies when** (`StreamCallDomain`):
    1. `strm` is a reachable stream (`StreamReachable`);
    2. the platform size bound holds (`ByteObjectsFit`);
    3. `head` is NULL, or names a live header record that is not one of the stream's own blocks, whose `extra` is NULL or points to `extra_len` readable bytes outside the stream's own blocks, and whose `name` and `comment` are each NULL or a NUL-terminated string (`HeaderMemory`);
    4. no `deflate` call has started the stream since init or `deflateReset`: its status is still `INIT_STATE` or `GZIP_STATE` (`DeflateNotStarted`).
- **Covered without condition.** Every wrapper: the stream need not be a gzip stream, which is wider than Pre. The call order is the same as in Pre.
- **Guarantees** (`StreamCallSafe`).
    - *Returns.* The call returns.
    - *State.* The stream keeps its invariant (`StreamInvariant`).
    - *Writes.* Only the stream record and the stream's own blocks.
    - *Allocations.* Exact allocation account (`LiveChange`).
- **Not in this goal.** A call after `deflate` has started the stream: outside every goal ([deviations](../../deviations.md), row "Other stream arguments"). A NULL or inconsistent stream: no required goal states the refusal for this function; the functional goal `Goal.deflateSetHeader` has it as a clause. The return value and the header bytes that `deflate` later writes: functional goal `Goal.deflateSetHeader`, not required for the safety results.

<details markdown="1" class="ar-return-exact" data-return-exact="deflateSetHeader"><summary>Complete return conditions and boundaries</summary>

**Post:** return `Z_OK` and retain `head`; no header bytes are copied or output yet.
Subsequent `deflate` writes the requested text flag, time, OS, optional extra/name/comment,
and optional header CRC. Compression settings determine the extra flags byte.
The caller keeps the record and fields alive until header emission completes.
Either reset clears the pointer. No allocation or ownership transfer occurs.

**Outside focused scope:** non-gzip or a failed stream check returns `Z_STREAM_ERROR`
without changes. Late registration is accepted for gzip but does not rewrite header bytes
already emitted. The functional goal `Goal.deflateSetHeader` includes that case; the safety
goal does not (**Proof goals**).

</details>

## deflatePending

```c
int ZEXPORT deflatePending(z_streamp strm, unsigned *pending, int *bits);
```

Report output waiting inside the compressor.

### Return values and next calls {#api-deflatepending-returns}

**Return type.** `int` — zlib status code

The status says whether the requested values fit their output types; pending bytes and bits are output parameters, not the return value.

| Returned value | Meaning and conditions | Caller’s next step |
| --- | --- | --- |
| `Z_OK`<br>**Query complete** | The stream is live, and pending is omitted or its whole-byte count fits unsigned. Requested pending and bits outputs receive current counts; the stream and buffers are unchanged. | Use the requested results and continue legal stream operations; either or both outputs may be NULL. |
| `Z_BUF_ERROR`<br>**Requested byte count saturated** | pending is non-NULL and the internal whole-byte count exceeds unsigned; `*pending` is set to UINT_MAX. Requested bits is still written and the stream is unchanged. | Treat the byte result as saturated, not exact; repeating the same query does not recover precision. The stream remains usable under legal calls. |
| `Z_STREAM_ERROR`<br>**Stream check failed** | The stream check fails before normal operation; neither the stream nor result cells are written. | Establish a live stream and the call preconditions; this result does not complete the operation. |

**Reading the result.**

- For normal compression history, bits is 0..7; it is the current pending bit count, not the last-flush count reported by deflateUsed.

### Calling conditions and effects {#api-deflatepending-contract}

**Domain:** Restricted domain. **Effect:** query with optional scalar results.

**Pre:** live stream; each result is NULL or a valid separate output cell.

**Proof goals.**

- **Goal.** `Goal.deflatePending_safety` ([Safety/Streams.lean](../../../ZlibF/Spec/Safety/Streams.lean)); required. Theorem: `ZlibF.Spec.Public.StreamCallSafetyProof.deflatePending_safety` ([public-stream-call-safety.lean](../../../ZlibF/Proof/public-stream-call-safety.lean)).
- **Applies when** (`StreamCallDomain`; this call has no argument condition):
    1. `strm` is a reachable stream (`StreamReachable`);
    2. the platform size bound holds (`ByteObjectsFit`).
- **Covered without condition.** Every reachable stream, in every phase: before the first `deflate`, mid-stream, while finishing, and after `Z_STREAM_END`. The result pointers are values in the translation, not memory ([shared conventions](#shared-conventions)): the goal asks nothing of them, while Pre asks for writable cells.
- **Guarantees** (`StreamCallSafe`).
    - *Returns.* The call returns.
    - *State.* The stream keeps its invariant (`StreamInvariant`).
    - *Writes.* Only the stream record and the stream's own blocks.
    - *Allocations.* Exact allocation account (`LiveChange`).
- **Not in this goal.** A NULL or inconsistent stream: no required goal states the refusal for this function; the functional goal `Goal.deflatePending` has it as a clause. The return value and the two counts: functional goal `Goal.deflatePending`, not required for the safety results.

<details markdown="1" class="ar-return-exact" data-return-exact="deflatePending"><summary>Complete return conditions and boundaries</summary>

**Post:** return `Z_OK`. If requested, `pending` receives the undelivered whole-byte count
and `bits` the remaining bit count (0..7 for legal compression history).
The stream and its buffers are unchanged. Omitted results are not written.

If a represented pending count exceeds `unsigned`, the requested byte count saturates
and return is `Z_BUF_ERROR`; a requested bit result is still written. The functional
goal includes this numerical refusal even though normal default-build buffers are smaller.

</details>

## deflateUsed

```c
int ZEXPORT deflateUsed(z_streamp strm, int *bits);
```

Report the last byte's bit use at the most recent byte-boundary flush.

### Return values and next calls {#api-deflateused-returns}

**Return type.** `int` — zlib status code

The return value is query status; optional bits carries the bit use at the last byte-boundary flush.

| Returned value | Meaning and conditions | Caller’s next step |
| --- | --- | --- |
| `Z_OK`<br>**Saved bit use read** | The stream is live; a non-NULL bits receives the stored value. In normal history it is 1..8 after a byte-boundary flush, or 0 if none occurred since init or reset. | Use the saved result, or omit it with NULL; the stream is unchanged and may continue legally. |
| `Z_STREAM_ERROR`<br>**Stream check failed** | The stream check fails before normal operation; neither the stream nor result cells are written. | Establish a live stream and the call preconditions; this result does not complete the operation. |

**Reading the result.**

- The functional goal returns the stored value for every checked state without imposing normal-history ranges on arbitrary represented states. It differs from the current pending bits from deflatePending.

### Calling conditions and effects {#api-deflateused-contract}

**Domain:** Restricted domain. **Effect:** query with an optional scalar result.

**Pre:** live stream; `bits` is NULL or a valid output cell.

**Proof goals.**

- **Goal.** `Goal.deflateUsed_safety` ([Safety/Streams.lean](../../../ZlibF/Spec/Safety/Streams.lean)); required. Theorem: `ZlibF.Spec.Public.StreamCallSafetyProof.deflateUsed_safety` ([public-stream-call-safety.lean](../../../ZlibF/Proof/public-stream-call-safety.lean)).
- **Applies when** (`StreamCallDomain`; this call has no argument condition):
    1. `strm` is a reachable stream (`StreamReachable`);
    2. the platform size bound holds (`ByteObjectsFit`).
- **Covered without condition.** Every reachable stream, in every phase: before the first `deflate`, mid-stream, while finishing, and after `Z_STREAM_END`. The result pointers are values in the translation, not memory ([shared conventions](#shared-conventions)): the goal asks nothing of them, while Pre asks for writable cells.
- **Guarantees** (`StreamCallSafe`).
    - *Returns.* The call returns.
    - *State.* The stream keeps its invariant (`StreamInvariant`).
    - *Writes.* Only the stream record and the stream's own blocks.
    - *Allocations.* Exact allocation account (`LiveChange`).
- **Not in this goal.** A NULL or inconsistent stream: no required goal states the refusal for this function; the functional goal `Goal.deflateUsed` has it as a clause. The return value and the count: functional goal `Goal.deflateUsed`, not required for the safety results.

<details markdown="1" class="ar-return-exact" data-return-exact="deflateUsed"><summary>Complete return conditions and boundaries</summary>

**Post:** return `Z_OK`. If requested, store the saved bit-use count: 1..8 after a
byte-boundary flush, or 0 since init/reset if none occurred. The stream is unchanged.
This saved count differs from the currently pending bits returned by `deflatePending`.

The functional goal returns the stored value for every checked state, without assuming that
an arbitrary represented state satisfies the normal-history range.

</details>

## deflatePrime

```c
int ZEXPORT deflatePrime(z_streamp strm, int bits, int value);
```

Prefix raw compression output with a caller-supplied bit fragment.

### Return values and next calls {#api-deflateprime-returns}

**Return type.** `int` — zlib status code

The result says whether a bit fragment joined pending output. A buffer-space refusal inserts none of the fragment.

| Returned value | Meaning and conditions | Caller’s next step |
| --- | --- | --- |
| `Z_OK`<br>**Bits appended** | The stream check passes, bits is 0..16 and pending space is sufficient; the low bits bits of value are appended least significant first, with complete bytes entering pending output. | Within Pre, insert only before the first deflate on a raw stream and account for the prefix when interpreting output; no bytes are delivered to next_out. |
| `Z_BUF_ERROR`<br>**Bit count out of range** | bits is outside 0..16; refusal occurs before pending-byte compaction and inserts no bits. | Correct the count and satisfy the priming preconditions before another call. |
| `Z_BUF_ERROR`<br>**Insufficient pending space** | bits is 0..16 but the pending buffer lacks room for the fragment; no bits are inserted, though existing pending bytes may have been compacted. | Repeating the same call does not create space; legally handle pending output within the chosen bit-splicing protocol before deciding whether to retry. |
| `Z_STREAM_ERROR`<br>**Stream check failed** | The stream check fails before normal operation; neither the stream nor result cells are written. | Establish a live stream and the call preconditions; this result does not complete the operation. |

**Reading the result.**

- The implementation does not check wrapper or first-call timing; accepting a fragment alone does not guarantee ordinary stream validity after arbitrary insertion. No allocation occurs.

### Calling conditions and effects {#api-deflateprime-contract}

**Domain:** Restricted domain. **Effect:** append bits to pending output.

**Pre:** live raw stream before its first `deflate` after init or `deflateReset`;
`bits` is 0..16 and `value` is any `int`. The caller accounts for these prefix bits
when interpreting the later compressed stream.

**Proof goals.**

- **Goal.** `Goal.deflatePrime_safety` ([Safety/Streams.lean](../../../ZlibF/Spec/Safety/Streams.lean)); required. Theorem: `ZlibF.Spec.Public.StreamCallSafetyProof.deflatePrime_safety` ([public-stream-call-safety.lean](../../../ZlibF/Proof/public-stream-call-safety.lean)).
- **Applies when** (`StreamCallDomain`):
    1. `strm` is a reachable stream (`StreamReachable`);
    2. the platform size bound holds (`ByteObjectsFit`);
    3. no `deflate` call has started the stream since init or `deflateReset`: its status is still `INIT_STATE` or `GZIP_STATE` (`DeflateNotStarted`).
- **Covered without condition.** Every `bits` and `value`; every wrapper. The goal is wider than Pre, which asks for a raw stream and `bits` in 0..16. The call order is the same as in Pre.
- **Guarantees** (`StreamCallSafe`).
    - *Returns.* The call returns.
    - *State.* The stream keeps its invariant (`StreamInvariant`).
    - *Writes.* Only the stream record and the stream's own blocks.
    - *Allocations.* Exact allocation account (`LiveChange`).
- **Not in this goal.** A call after `deflate` has started the stream: outside every goal ([deviations](../../deviations.md), row "Other stream arguments"). A NULL or inconsistent stream: no required goal covers it for this function; the lemma `Zlib.Deflate.Proofs.deflatePrime_refused` ([deflate.c.prime.lean](../../../ZlibF/Proof/deflate.c.prime.lean)) states the refusal. Which code is returned and the pending bits after the call: functional goal `Goal.deflatePrime`, not required for the safety results.

<details markdown="1" class="ar-return-exact" data-return-exact="deflatePrime"><summary>Complete return conditions and boundaries</summary>

**Post:** `Z_OK` appends the low `bits` bits of `value`, least significant first,
to the logical pending bit sequence. Complete bytes join pending output and fewer than
8 bits remain buffered. No bytes are delivered to `next_out`; no allocation occurs.
`Z_BUF_ERROR` inserts no bits when the pending buffer has insufficient space.
Existing pending bytes may be compacted within their owned buffer before that refusal.

**Outside focused scope:** counts outside 0..16 give `Z_BUF_ERROR` before compaction;
a failed stream check gives `Z_STREAM_ERROR`. The implementation does not check wrapper
or first-call timing. Its functional goal covers exact pending-bit effects there, without
promising ordinary stream validity for arbitrary inserted fragments.

</details>

## deflateParams

```c
int ZEXPORT deflateParams(z_streamp strm, int level, int strategy);
```

Change level and strategy, finishing the old block when needed.

### Return values and next calls {#api-deflateparams-returns}

**Return type.** `int` — zlib status code

The result says whether the new level and strategy were installed. Completing the old block may first consume input and deliver output.

| Returned value | Meaning and conditions | Caller’s next step |
| --- | --- | --- |
| `Z_OK`<br>**New settings installed** | Parameters are valid and required old-block work is complete; level -1 selects 6, and a changed level restores its standard tuning. A required flush uses the old settings and may make I/O progress. | Account for output and unconsumed input through the updated pointers and counts, then continue with the new settings. |
| `Z_BUF_ERROR`<br>**Old block incomplete** | Required old-block work is incomplete; level and strategy retain their old values, but compression progress, including input consumed and output delivered, is retained. | Provide more output room, preserve the updated stream and remaining input, and retry deflateParams; the live stream and allocations are retained. |
| `Z_STREAM_ERROR`<br>**Setting arguments refused** | level is neither -1 nor 0..9, or strategy is outside 0..4; refusal changes no stream fields. | Correct the arguments and retry in a legal stream phase; the new settings have not taken effect. |
| `Z_STREAM_ERROR`<br>**Required flush refused** | The arguments are valid, but a required deflate(Z_BLOCK) returns Z_STREAM_ERROR, for example after finishing began or when buffer conditions fail; new settings are not installed. | Determine the stream phase and the buffer conditions the call started in. Once finishing began, follow the Z_FINISH protocol, or legally reset/end. |
| `Z_STREAM_ERROR`<br>**Stream check failed** | The stream check fails before normal operation; neither the stream nor result cells are written. | Establish a live stream and the call preconditions; this result does not complete the operation. |

**Reading the result.**

- For an exact input boundary, first complete deflate(Z_BLOCK) until avail_out is nonzero, and supply no new input before changing parameters.

### Calling conditions and effects {#api-deflateparams-contract}

**Domain:** Restricted domain. **Effect:** update settings; may consume input and emit output.

**Pre:** live stream before finishing, valid stream buffers and any active header;
`level` is -1 or 0..9 and `strategy` is 0..4. To choose an exact input boundary, complete
`deflate(Z_BLOCK)` until `avail_out` is nonzero and supply no new input before this call.

**Proof goals.**

- **Goal.** `Goal.deflateParams_safety` ([Safety/Streams.lean](../../../ZlibF/Spec/Safety/Streams.lean)); required. Theorem: `ZlibF.Spec.Public.StreamCallSafetyProof.deflateParams_safety` ([public-stream-call-safety.lean](../../../ZlibF/Proof/public-stream-call-safety.lean)).
- **Applies when** (`StreamCallDomain`):
    1. `strm` is a reachable stream (`StreamReachable`);
    2. the platform size bound holds (`ByteObjectsFit`);
    3. conditions 3 to 6 of [deflate](#deflate) on the buffers and the gzip header (`StreamBuffers`, `ActiveHeader`): the call can run `deflate(strm, Z_BLOCK)`.
- **Covered without condition.** Every `level` and `strategy`, valid or not. Every reachable stream, in every phase: before the first `deflate`, mid-stream, while finishing, and after `Z_STREAM_END`. The goal is wider than Pre in the argument values, in the phase, and in the buffers (as for [deflate](#deflate)).
- **Guarantees** (`StreamCallSafe`).
    - *Returns.* The call returns.
    - *State.* The stream keeps its invariant (`StreamInvariant`).
    - *Writes.* Only the stream record, the stream's own blocks and the `avail_out` bytes at `next_out`.
    - *Allocations.* Exact allocation account (`LiveChange`).
- **Not in this goal.** A NULL or inconsistent stream, for example one that was already ended: `Goal.deflate_refusal`. Which code is returned, the settings installed and the bytes written: functional goal `Goal.deflateParams`, not required for the safety results.

<details markdown="1" class="ar-return-exact" data-return-exact="deflateParams"><summary>Complete return conditions and boundaries</summary>

**Post:** `Z_OK` installs the requested settings (level -1 means 6). Changing level
restores that level's standard tuning values. A needed block flush uses the old settings
and can consume some input and deliver output. I/O pointers, available counts and totals
account for exactly those bytes; unconsumed input remains available.

`Z_BUF_ERROR` means the old block could not yet be completed; level and strategy remain
unchanged, but compression progress and emitted output are retained. Provide more output
room and retry. The live stream and its allocation set are preserved on either result.

**Outside focused scope:** invalid level/strategy gives `Z_STREAM_ERROR` without changes.
A needed block flush can also return `Z_STREAM_ERROR`, including after finishing has begun.

</details>

## deflateTune

```c
int ZEXPORT deflateTune(z_streamp strm, int good_length, int max_lazy, int nice_length, int max_chain);
```

Set the four expert match-search tuning values.

These settings change how much work goes into finding repeated fragments; they do not specify
output bytes. The first three are lengths in input bytes, and the last is a number of candidates:

| Argument | What it controls |
| --- | --- |
| `good_length` | When the match already found is at least this long, a further search gets a smaller budget of chain candidates. |
| `max_lazy` | The length threshold below which lazy matching still tries the next position; the fast matcher uses it to limit position-by-position insertion after a short match. |
| `nice_length` | A match of at least this length ends the search early. |
| `max_chain` | The largest number of candidates one search examines. |

For example, a larger `max_chain` may let the search see an earlier, longer match, and may also
cost more comparisons. It does not promise smaller output every time; the arguments are stored by
the C rule given below.

### Return values and next calls {#api-deflatetune-returns}

**Return type.** `int` — zlib status code

The result only reports whether the four tuning fields were stored; it does not guarantee later compression properties for arbitrary values.

| Returned value | Meaning and conditions | Caller’s next step |
| --- | --- | --- |
| `Z_OK`<br>**Tuning stored** | A live stream accepts every int argument; good_length, max_lazy and max_chain convert to unsigned, while nice_length remains signed. No input is consumed or output delivered. | Choose tuning suitable for subsequent compression; deflateReset or a level change via deflateParams restores standard values. |
| `Z_STREAM_ERROR`<br>**Stream check failed** | The stream check fails before normal operation; neither the stream nor result cells are written. | Establish a live stream and the call preconditions; this result does not complete the operation. |

**Reading the result.**

- The C recommends max_lazy >= 3 and max_chain >= 4; setter success alone establishes neither later safety nor compression bounds for every choice.

### Calling conditions and effects {#api-deflatetune-contract}

**Domain:** Restricted domain (live stream); all `int` tuning arguments are covered.

**Effect:** update tuning fields.

**Pre:** live stream.

**Proof goals.**

- **Goal.** `Goal.deflateTune_safety` ([Safety/Streams.lean](../../../ZlibF/Spec/Safety/Streams.lean)); required. Theorem: `ZlibF.Spec.Public.StreamCallSafetyProof.deflateTune_safety` ([public-stream-call-safety.lean](../../../ZlibF/Proof/public-stream-call-safety.lean)).
- **Applies when** (`StreamCallDomain`; this call has no argument condition):
    1. `strm` is a reachable stream (`StreamReachable`);
    2. the platform size bound holds (`ByteObjectsFit`).
- **Covered without condition.** Every value of the four tuning arguments. Every reachable stream, in every phase: before the first `deflate`, mid-stream, while finishing, and after `Z_STREAM_END`.
- **Guarantees** (`StreamCallSafe`).
    - *Returns.* The call returns.
    - *State.* The stream keeps its invariant (`StreamInvariant`).
    - *Writes.* Only the stream record and the stream's own blocks.
    - *Allocations.* Exact allocation account (`LiveChange`).
- **Not in this goal.** A NULL or inconsistent stream: no required goal states the refusal for this function; the functional goal `Goal.deflateTune` has it as a clause. The return value and the fields stored: functional goal `Goal.deflateTune`, not required for the safety results.

<details markdown="1" class="ar-return-exact" data-return-exact="deflateTune"><summary>Complete return conditions and boundaries</summary>

**Post:** return `Z_OK`. Store `good_length`, `max_lazy` and `max_chain` after conversion
to unsigned, and `nice_length` as signed. No input is consumed, no output is delivered and
no allocation occurs. A changed level in `deflateParams`, or `deflateReset`, restores
standard tuning. This setter contract alone does not establish later compression bounds
or safety for every tuning choice; the C recommends `max_lazy >= 3` and `max_chain >= 4`.

</details>

## deflateBound_z

```c
z_size_t ZEXPORT deflateBound_z(z_streamp strm, z_size_t sourceLen);
```

Compute a size bound using the stream's current configuration and wrapper.

This query answers how many output bytes are enough for the whole input. `sourceLen` is the input
byte count, written `n` below; `w` is the wrapper size: header, trailer and optional fields
together. `floor(x)` rounds down. `SIZE_MAX` is the largest value of the return type `z_size_t`;
"saturates" means that a larger mathematical result returns this maximum and does not wrap to a
small number.

### Return values and next calls {#api-deflatebound_z-returns}

**Return type.** `z_size_t` — Output-capacity bound (bytes)

The return is an output-capacity bound in bytes, not a zlib status code. It can saturate at SIZE_MAX.

| Returned value | Meaning and conditions | Caller’s next step |
| --- | --- | --- |
| `bound`<br>**Output byte bound** | For a live stream, the formula uses the current window, memory level, compression level and full wrapper size; NULL or a safely checkable invalid stream uses the larger fixed/stored formula plus 18. All results saturate at SIZE_MAX and leave the heap unchanged. | Apply the stated capacity guarantee only after init/setup and before compression, with fixed configuration/dictionary/header, standard tuning and no prime bits; buffer representability and avail_in/avail_out capacity conditions must also hold. |

**Reading the result.**

- SIZE_MAX may be exact or saturated; it does not promise an addressable buffer of that size. There is no error code.
- Under the capacity premises, giving all input and at least this much output room to one deflate(Z_FINISH) must yield Z_STREAM_END; a schedule of only Z_NO_FLUSH then Z_FINISH has the total-output bound, while other flushes may exceed it.

### Calling conditions and effects {#api-deflatebound_z-contract}

**Domain:** Restricted domain (live stream and readable retained header); every
`z_size_t sourceLen` is included. **Effect:** query.

**Pre:** live stream and shared header conditions. For the output-capacity guarantee below,
call after init and any dictionary/header setup, before compression. Keep configuration,
header and dictionary fixed; use standard tuning and no inserted prime bits.

**Proof goals.**

- **Goal.** `Goal.deflateBound_z_safety` ([Safety/Streams.lean](../../../ZlibF/Spec/Safety/Streams.lean)); required. Theorem: `ZlibF.Spec.Public.StreamCallSafetyProof.deflateBound_z_safety` ([public-stream-call-safety.lean](../../../ZlibF/Proof/public-stream-call-safety.lean)).
- **Applies when** (`StreamCallDomain`):
    1. `strm` is a reachable stream (`StreamReachable`);
    2. the platform size bound holds (`ByteObjectsFit`);
    3. conditions 4 to 6 of [deflate](#deflate) on the gzip header (`ActiveHeader`);
    4. a header record that was given to `deflateSetHeader` is live and readable at this call, not only while the header is being written: the record is live and is not one of the stream's own blocks, a non-NULL `extra` points to `extra_len` readable bytes outside the stream's own blocks, and a non-NULL `name` or `comment` is a NUL-terminated string (`DeflateHeaderLive`).
- **Covered without condition.** Every `sourceLen`. Every reachable stream, in every phase: before the first `deflate`, mid-stream, while finishing, and after `Z_STREAM_END`.
- **Guarantees** (`StreamCallSafe`).
    - *Returns.* The call returns.
    - *State.* The stream keeps its invariant (`StreamInvariant`).
    - *Writes.* Only the stream record and the stream's own blocks.
    - *Allocations.* Exact allocation account (`LiveChange`).
- **Not in this goal.** A NULL or inconsistent stream: no required goal covers it for this function; the lemma `Zlib.Deflate.Proofs.deflateBound_z_nostate` ([deflate.c.life.bound.lean](../../../ZlibF/Proof/deflate.c.life.bound.lean)) states the value returned and that the heap is unchanged. The value returned, and whether that much output room is enough: functional goal `Goal.deflateBound_z`, not required for the safety results.

<details markdown="1" class="ar-return-exact" data-return-exact="deflateBound_z"><summary>Complete return conditions and boundaries</summary>

**Post:** the heap is unchanged. The numerical target is the following mathematical value,
saturated at `SIZE_MAX`, where `n = sourceLen` and `w` is the full wrapper size:

- Window 15 and memory level 8: `n + floor(n/4096) + floor(n/16384) + floor(n/33554432) + 7 + w`.
- Otherwise, if window bits are at most hash bits and level is nonzero:
  `n + floor(n/8) + floor(n/256) + floor(n/512) + 4 + w`.
- Otherwise: `n + floor(n/32) + floor(n/128) + floor(n/2048) + 7 + w`.

`w` is 0 for raw, 6 for zlib plus 4 when preset history is present, or 18 for gzip plus
its optional extra field (including two length bytes), terminated name/comment and header CRC.

**Output capacity:** separately from the numerical formula, for a representable adequate
buffer, when the input and output sizes fit `avail_in` and `avail_out`, supplying all
`n` bytes to one `deflate(Z_FINISH)` with at least the bound of output room must return
`Z_STREAM_END`. A clean schedule using only `Z_NO_FLUSH` before
`Z_FINISH` has the total-output bound. Other flush schedules can exceed it.
A saturated result is not a promise that an addressable buffer of that size exists.

**Outside focused scope:** NULL or a safely checkable invalid stream receives the larger
of the fixed/stored formulas above, plus 18, with saturation. There is no error code.
The functional goal covers every readable gzip header length, including an `extra_len`
above 65535, which the contracts on this page leave out.

</details>

## deflateBound

```c
uLong ZEXPORT deflateBound(z_streamp strm, uLong sourceLen);
```

Return the `uLong` form of the compression bound.

### Return values and next calls {#api-deflatebound-returns}

**Return type.** `uLong` — Output-capacity bound (bytes)

This returns the uLong form of the deflateBound_z bound, still in bytes. ULONG_MAX is a numeric limit, not an error code.

| Returned value | Meaning and conditions | Caller’s next step |
| --- | --- | --- |
| `bound`<br>**uLong output byte bound** | The deflateBound_z value is returned if it fits uLong; otherwise the result is ULONG_MAX. NULL or a safely checkable invalid stream uses its conservative fallback formula too. The stream is unchanged. | For capacity planning, follow deflateBound_z conditions on setup timing, fixed settings, tuning, no prime bits, buffers and flush schedule. |

**Reading the result.**

- ULONG_MAX may be exact or capped; numerical equality alone adds no capacity guarantee.
- On default LP64, uLong and z_size_t are both 64 bits, so the two queries agree.

### Calling conditions and effects {#api-deflatebound-contract}

**Domain:** Restricted domain, as `deflateBound_z`; every `uLong sourceLen` is included.

**Effect:** query.

**Pre:** the `deflateBound_z` conditions apply.

**Proof goals.**

- **Goal.** `Goal.deflateBound_safety` ([Safety/Streams.lean](../../../ZlibF/Spec/Safety/Streams.lean)); required. Theorem: `ZlibF.Spec.Public.StreamCallSafetyProof.deflateBound_safety` ([public-stream-call-safety.lean](../../../ZlibF/Proof/public-stream-call-safety.lean)).
- **Applies when** (`StreamCallDomain`):
    1. `strm` is a reachable stream (`StreamReachable`);
    2. the platform size bound holds (`ByteObjectsFit`);
    3. conditions 4 to 6 of [deflate](#deflate) on the gzip header (`ActiveHeader`);
    4. a header record that was given to `deflateSetHeader` is live and readable at this call, not only while the header is being written: the record is live and is not one of the stream's own blocks, a non-NULL `extra` points to `extra_len` readable bytes outside the stream's own blocks, and a non-NULL `name` or `comment` is a NUL-terminated string (`DeflateHeaderLive`).
- **Covered without condition.** Every `sourceLen`. Every reachable stream, in every phase: before the first `deflate`, mid-stream, while finishing, and after `Z_STREAM_END`.
- **Guarantees** (`StreamCallSafe`).
    - *Returns.* The call returns.
    - *State.* The stream keeps its invariant (`StreamInvariant`).
    - *Writes.* Only the stream record and the stream's own blocks.
    - *Allocations.* Exact allocation account (`LiveChange`).
- **Not in this goal.** A NULL or inconsistent stream: no required goal covers it for this function; the lemma `Zlib.Deflate.Proofs.deflateBound_nostate` ([deflate.c.life.bound.lean](../../../ZlibF/Proof/deflate.c.life.bound.lean)) states the value returned and that the heap is unchanged. The value returned, and whether that much output room is enough: functional goal `Goal.deflateBound`, not required for the safety results.

<details markdown="1" class="ar-return-exact" data-return-exact="deflateBound"><summary>Complete return conditions and boundaries</summary>

**Post:** return its numerical result if it fits `uLong`, otherwise `ULONG_MAX`.
On the default LP64 target both types have 64 bits and the results agree.
The stream is unchanged. Output adequacy requires the separate schedule and capacity
conditions of `deflateBound_z`, rather than following from the numerical equality alone.

</details>

## deflate

```c
int ZEXPORT deflate(z_streamp strm, int flush);
```

Accept input and deliver part or all of a valid compressed stream.

`flush` says how far the caller wants the call to go: an ordinary call lets the compressor choose
when to emit output, a flush request establishes the chosen boundary, and `Z_FINISH` asks to end
the whole stream. A request does not enlarge a limited output buffer: when the room is used up,
take the output and continue by the protocol below.

### Return values and next calls {#api-deflate-returns}

**Return type.** `int` — zlib status code

The result separates continuation, completion of the whole compressed stream, and refusal or inability to progress. Updated pointers and counts show this call’s consumed and delivered bytes.

| Returned value | Meaning and conditions | Caller’s next step |
| --- | --- | --- |
| `Z_OK`<br>**Continuation may be needed** | The call has not reported whole-stream completion. It may have consumed input or delivered header, data, flush-marker or trailer bytes; full output can leave unconsumed input or pending output. | Collect output and use updated counts; replenish full output, keeping the same flush during a flush. Once finishing begins, add no input and continue only with Z_FINISH until Z_STREAM_END. |
| `Z_STREAM_END`<br>**Complete compressed stream delivered** | Only with Z_FINISH, all supplied input and all compressed output, including the wrapper trailer, have been delivered. | Retain final output; call deflateEnd to release state, or deflateReset for a new stream. This result itself does not free state. |
| `Z_BUF_ERROR`<br>**No output room** | Initial checks pass but avail_out is 0; no input is consumed or output delivered, and the existing live stream is retained. | Supply valid nonempty output room; keep the same flush during a flush and use only Z_FINISH during finishing. |
| `Z_BUF_ERROR`<br>**Cannot progress now** | No input or pending output is available, and no stronger flush is requested; the current non-Z_FINISH call cannot progress. | Wait for input, or request a stronger legal flush when the application needs it; do not loop unchanged. The stream remains live. |
| `Z_BUF_ERROR`<br>**Input offered after final processing** | New input is supplied after final-block processing began; none of it is accepted, though old pending output may be delivered before refusal. The live stream is retained. | Collect any delivered output and keep unaccepted input for another task; offer no further input to this stream, and finish with Z_FINISH or legally reset/end. |
| `Z_STREAM_ERROR`<br>**Stream or call arguments refused** | The stream check fails, flush is invalid (including Z_TREES), next_out is NULL, nonzero input has NULL next_in, or a non-Z_FINISH flush is used after finishing began. Initial refusal consumes and delivers no bytes. | Establish that the stream is live and correct buffers or flush; after finishing begins use only Z_FINISH. A failed stream check does not guarantee that an arbitrary state can be retried or ended. |

**Reading the result.**

- The status is not a byte count; I/O pointers, avail_in/avail_out and total_in/total_out record actual progress. The call allocates and frees nothing.
- A completed nonterminal flush still returns Z_OK, not stream completion; use output room and the flush protocol to determine boundary completion. Error returns can still change msg or the remembered flush.

### Calling conditions and effects {#api-deflate-contract}

**Domain:** Restricted domain. **Effect:** consume input, emit output and update progress.

**Pre:** live stream with valid buffers and any active header. `next_out` is non-NULL and
`avail_out > 0`; `next_in` may be NULL only with zero input. `flush` is `Z_NO_FLUSH`,
`Z_PARTIAL_FLUSH`, `Z_SYNC_FLUSH`, `Z_FULL_FLUSH`, `Z_FINISH` or `Z_BLOCK`.
If output fills during a flush, continue with the same flush and more room.
After finishing begins, supply no new input and continue only with `Z_FINISH`.
For ordinary format validity, begin from init/`deflateReset` (or a copy of that history),
use legal dictionary/header setup, standard tuning and no arbitrary priming.

**Proof goals.**

- **Goal.** `Goal.deflate_safety` ([Safety/Streams.lean](../../../ZlibF/Spec/Safety/Streams.lean)); required. Theorem: `ZlibF.Spec.Public.StreamCallSafetyProof.deflate_safety` ([public-stream-call-safety.lean](../../../ZlibF/Proof/public-stream-call-safety.lean)).
- **Applies when** (`StreamCallDomain`):
    1. `strm` is a reachable stream (`StreamReachable`);
    2. the platform size bound holds (`ByteObjectsFit`);
    3. `next_in` is NULL or points to `avail_in` readable bytes, and `next_out` is NULL or points to `avail_out` writable bytes; neither range lies in the stream's own blocks, and the two ranges do not overlap (`StreamBuffers`);
    4. while the gzip header is being written (stream status `GZIP_STATE` to `HCRC_STATE`) and a header record was given to `deflateSetHeader`: the record is live and is not one of the stream's own blocks; a non-NULL `extra` points to `extra_len` readable bytes outside the stream's own blocks; a non-NULL `name` or `comment` is a NUL-terminated string (`HeaderMemory`);
    5. the caller has kept what is already written: the field being written (`extra`, `name` or `comment`) still covers the part already written, and was not set to NULL after part of it was written (`DeflateHeaderProgress`);
    6. while the header is being written: the input range, the output range, `extra` (`extra_len mod 2^16` bytes), `name` and `comment` (each through its NUL) do not overlap one another, and `extra`, `name` and `comment` lie outside the stream's own blocks (`DeflateHeaderApart`). Conditions 4 to 6 together are `ActiveHeader`.
- **Covered without condition.** Every `flush` value, also one that is not a flush code; every sequence of input bytes. Every reachable stream, in every phase: before the first `deflate`, mid-stream, while finishing, and after `Z_STREAM_END`. The goal is wider than Pre: `next_out` may be NULL, `avail_out` may be zero, `next_in` may be NULL with a nonzero `avail_in`, and `flush` may be any `int`. The C refuses or reports these cases (return table above).
- **Guarantees** (`StreamCallSafe`).
    - *Returns.* The call returns.
    - *State.* The stream keeps its invariant (`StreamInvariant`).
    - *Writes.* Only the stream record, the stream's own blocks and the `avail_out` bytes at `next_out`.
    - *Allocations.* Exact allocation account (`LiveChange`).
- **Not in this goal.** A NULL or inconsistent stream, for example one that was already ended: `Goal.deflate_refusal`. Which code is returned and which bytes are written: functional goal `Goal.deflate`, not required for the safety results.

<details markdown="1" class="ar-return-exact" data-return-exact="deflate"><summary>Complete return conditions and boundaries</summary>

**Post:** `used` is the number of input bytes this call consumes and `made` the number of output
bytes it delivers; `old avail_in` and `old avail_out` are the input count and the output room
given before the call. Then `used <= old avail_in` and `made <= old avail_out`.
Pointers advance by those amounts, available counts fall by them, and totals increase by
them with unsigned wrapping. Input stays unchanged; output outside the delivered prefix
stays unchanged. Some input can remain when output fills. No allocation or free occurs.

Across calls, delivered bytes form a prefix of a valid encoding of accepted input, using
the chosen wrapper, settings and preset dictionary. Completed output decodes to that input.
This specifies valid output, not one unique compressed byte sequence. Once the header has been
written, `adler` tracks the accepted input, with Adler-32 for zlib and CRC-32 for gzip; raw has
no input checksum.

`Z_OK` means continuation may be needed. `Z_STREAM_END` occurs only with `Z_FINISH`, after
all supplied input and all compressed output, including trailer, have been delivered.
The live state remains owned until `deflateEnd` or reusable via `deflateReset`.

When a requested flush is fully delivered, `Z_BLOCK` completes a block without byte padding;
`Z_PARTIAL_FLUSH` adds an empty fixed block; `Z_SYNC_FLUSH` makes all preceding input available
to a decoder and ends with an aligned empty stored block. `Z_FULL_FLUSH` also resets match
history: later blocks do not refer before that completed flush. Restarting a raw decoder there
requires retaining the exact boundary and delivering the entire flush marker first.
`Z_FINISH` closes the final block and writes the wrapper trailer.

**Errors:** `Z_BUF_ERROR` covers zero output room, no possible progress with no input and
no stronger flush, or input offered after final-block processing began. It preserves a
live stream; provide room/input as appropriate. `Z_STREAM_ERROR` covers the stream check,
invalid flush (including `Z_TREES`), invalid NULL I/O combinations, or non-finish flush after
finishing began. Initial argument refusals consume no input or output. A later
`Z_BUF_ERROR` for new input after finishing may first deliver old pending output; no new
input is accepted. `msg` and remembered flush can change. The safety goal and the
functional goal both include all signed flush values and these refusals.

</details>

## deflateEnd

```c
int ZEXPORT deflateEnd(z_streamp strm);
```

Release the compressor, discarding any unfinished work.

### Return values and next calls {#api-deflateend-returns}

**Return type.** `int` — zlib status code

The result distinguishes the compression phase before release. Both Z_OK and Z_DATA_ERROR release all five stream allocations and clear state.

| Returned value | Meaning and conditions | Caller’s next step |
| --- | --- | --- |
| `Z_OK`<br>**State released** | The live stream’s saved status is not BUSY_STATE; every stream allocation is freed exactly once and state is NULL. | Retain caller-owned buffers and header; initialize again before compression. The result alone does not confirm delivery of all output. |
| `Z_DATA_ERROR`<br>**Unfinished task released** | The live stream’s saved status is BUSY_STATE, reporting unfinished compression; all stream allocations are nevertheless freed and state is NULL. | Do not call deflateEnd again for cleanup; unfinished compression has been abandoned, and further compression requires initialization. |
| `Z_STREAM_ERROR`<br>**End refused** | The stream check fails, including a second End; this call frees nothing. | Do not treat this result as successful release; establish the actual stream lifetime before any compression or attempted cleanup. |

**Reading the result.**

- The status depends on internal phase, not merely whether all output was delivered. Caller input, output and header storage remain caller-owned and are not freed.

### Calling conditions and effects {#api-deflateend-contract}

**Domain:** Restricted domain. **Effect:** free owned state.

**Pre:** live stream in any phase, with the default free routine intact.

**Proof goals.**

- **Goal.** `Goal.deflateEnd_safety` ([Safety/Streams.lean](../../../ZlibF/Spec/Safety/Streams.lean)); required. Theorem: `ZlibF.Spec.Public.StreamCallSafetyProof.deflateEnd_safety` ([public-stream-call-safety.lean](../../../ZlibF/Proof/public-stream-call-safety.lean)).
- **Applies when.** `strm` is a reachable stream (`StreamReachable`). The platform size bound is not asked.
- **Covered without condition.** Every reachable stream, in every phase: before the first `deflate`, mid-stream, while finishing, and after `Z_STREAM_END`.
- **Guarantees.**
    - *Returns.* The call returns, with `Z_OK` or `Z_DATA_ERROR`.
    - *State.* `strm->state` is NULL.
    - *Writes.* Only the stream record and the stream's own blocks.
    - *Allocations.* Exact allocation account (`LiveChange`): the stream's own blocks are freed; nothing else is freed and nothing is allocated.
- **Not in this goal.** A NULL or inconsistent stream: no required goal covers it for this function; the lemma `Zlib.Deflate.Proofs.deflateEnd_reject` ([deflate.c.life.end.lean](../../../ZlibF/Proof/deflate.c.life.end.lean)) states the refusal. Which of the two codes is returned, and the values of the other stream fields: functional goal `Goal.deflateEnd`, not required for the safety results.

<details markdown="1" class="ar-return-exact" data-return-exact="deflateEnd"><summary>Complete return conditions and boundaries</summary>

**Post:** free all five owned allocations exactly once and set `state` to NULL.
Caller input/output and header storage are unchanged and remain caller-owned.
Return `Z_DATA_ERROR` if the saved status is busy, otherwise `Z_OK`.
Both results release everything: `Z_DATA_ERROR` reports unfinished compression, not failed cleanup.
No later compression call is valid until reinitialisation.

**Outside focused scope:** a failed stream check, including a second end, returns
`Z_STREAM_ERROR` without freeing anything. Return status depends on internal compression
phase, not merely whether every produced byte was delivered.

</details>

## deflateCopy

```c
int ZEXPORT deflateCopy(z_streamp dest, z_streamp source);
```

Create an independent compressor with the same compression progress.

### Return values and next calls {#api-deflatecopy-returns}

**Return type.** `int` — zlib status code

The result says whether the destination gained independent compression state. Failure cleanup covers this call’s new allocations and leaves the source unchanged.

| Returned value | Meaning and conditions | Caller’s next step |
| --- | --- | --- |
| `Z_OK`<br>**Independent state copied** | The source is live and the destination satisfies the distinct empty-record preconditions; the destination gains five allocations and equivalent progress with relocated internal pointers, while the source is unchanged. | Each stream needs its own deflateEnd; assign separate output room before continuing both. Copied I/O pointers initially coincide and the retained header remains shared caller-owned storage. |
| `Z_MEM_ERROR`<br>**Allocation failed and cleaned up** | Any new allocation fails; every new block is released, dest->state is cleared, other destination fields and the source are unchanged, and no new live destination exists. | Do not end the failed destination; after addressing memory pressure, retry under copy preconditions. The source can continue legally or end. |
| `Z_STREAM_ERROR`<br>**Null destination** | dest is NULL and copying does not begin. | Provide a writable destination distinct from the source and owning no state, then follow the copy preconditions. |
| `Z_STREAM_ERROR`<br>**Source check failed** | The destination is non-NULL but the source check fails; dest->state is cleared and no copy allocations occur. | Establish a live source and use only a distinct destination owning no state; this result does not mean any arbitrary preexisting destination state was freed. |

**Reading the result.**

- The contract excludes self-copy and overwriting a live destination; those cases have no leak-free guarantee.

### Calling conditions and effects {#api-deflatecopy-contract}

**Domain:** Restricted domain. **Effect:** allocate and copy owned state.

**Pre:** `source` is live. `dest` is a different writable `z_stream` with no owned state,
separate from the source's memory. Source buffers and any retained header satisfy their lifetimes.

**Proof goals.**

- **Goal.** `Goal.deflateCopy_safety` ([Safety/Copy.lean](../../../ZlibF/Spec/Safety/Copy.lean)); required. Theorem: `Zlib.Deflate.Universal.deflate_copy_safety` ([public-deflate-copy.lean](../../../ZlibF/Proof/public-deflate-copy.lean)).
- **Applies when** (the main clause):
    1. `source` is a reachable stream (`StreamReachable`). The statement also takes its invariant and default allocator as hypotheses (`DGood`, `DefAlloc`); every reachable stream has them (`Goal.deflate_sequence_safety`, first clause);
    2. `dest` points to a readable stream record that is not the `source` record (`source ≠ dest`). The platform size bound is not asked.
- **Covered without condition.** Every content of the `dest` record; every allocation outcome. Without any condition, in the same goal: a NULL `dest` returns `Z_STREAM_ERROR` with the heap unchanged; a NULL `source` with a readable `dest` record returns `Z_STREAM_ERROR` and only sets `dest->state` to NULL. A `source` record whose `zalloc`, `zfree` or `state` is NULL is refused in the same way as a NULL `source`. The goal is wider than Pre: `dest` may hold any field values. If `dest` was a live stream, its old state stays allocated and the record no longer points to it.
- **Guarantees.**
    - *Returns.* The call returns, with `Z_OK` or `Z_MEM_ERROR`. `Z_MEM_ERROR` is returned only after an allocation failed (`AllocationFailed`).
    - *State.* The `source` record and its state are unchanged. With `Z_OK`, `dest` satisfies the stream invariant (`StreamInvariant`), and is a reachable stream by the definition of `StreamReachable`. With `Z_MEM_ERROR`, `dest->state` is NULL and the other fields of `dest` are unchanged.
    - *Writes.* Only the `dest` record and blocks the call itself allocates.
    - *Allocations.* With `Z_OK`, the new blocks are exactly five: the new state record and its four buffers (`window`, `prev`, `head`, `pending_buf`). Nothing is freed. The safety goal does not say that `dest->state` points to this record; the functional goal `Goal.deflateCopy` does. With `Z_MEM_ERROR` the allocated blocks are the same as before the call.
- **Not in this goal.** A `source` whose state the stream check refuses (a wrong back pointer or status): `Goal.deflate_refusal`. `dest == source`: outside every goal ([deviations](../../deviations.md), row "Copy destination"). What the copy contains: functional goal `Goal.deflateCopy`, not required for the safety results.

<details markdown="1" class="ar-return-exact" data-return-exact="deflateCopy"><summary>Complete return conditions and boundaries</summary>

**Post:** `Z_OK` gives `dest` five new owned allocations containing equivalent compression
state; the source is unchanged. The copied stream fields include totals, allocator fields,
I/O pointers and retained header pointer. Internal owned pointers are relocated to the new
allocations. Both streams require their own `deflateEnd` and can continue independently.
Their copied caller I/O pointers initially refer to the same buffers; assign separate output
room before continuing both. The header remains shared caller-owned storage.

`Z_MEM_ERROR` frees every new allocation, clears `dest->state` and leaves other destination
fields and the source unchanged. There is no new live state to release.

**Outside focused scope:** NULL destination gives `Z_STREAM_ERROR`; a failed source check
also clears a non-NULL destination's state. The safety goal and the functional goal both
assume distinct streams. Self-copy and overwriting an already live destination are excluded here and do not
receive a leak-free contract.

</details>

[Back to the API manual](README.md) · [Contract conventions](contracts.md)
