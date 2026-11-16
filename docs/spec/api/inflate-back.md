# Callback decompression

[API manual](README.md) · [Shared stream rules](streams.md) · [Stream decompression](inflate-stream.md)

The callback interface lets a caller supply input chunks and receive decoded output directly
from its window. Start with [inflateBackInit_](#inflatebackinit_), decode with
[inflateBack](#inflateback), and release state with [inflateBackEnd](#inflatebackend).
The caller's window remains caller-owned throughout.

These focused contracts follow the pinned [infback.c](../../../zlib/infback.c) and
[zlib.h](../../../zlib/zlib.h) in the default LP64 Linux build. See
[contract conventions](contracts.md) for domain/effect labels.

**What is proved.** The required goal of each function is its safety goal: no undefined behaviour, no
memory error, no leak, and termination ([safety](../safety.md)). Each entry names that goal under
**Proof goals**, with its premises. The proof assumes those premises, not the documentary Pre; where
the two differ, the Lean statement counts. The return values, output bytes and state changes
described here are functional behaviour. They are read from the C and are **to confirm** where no
registered theorem states them. They are not a planned proof target.
[Progress](../../progress.md) records the level of each goal.

Each function has its own required safety goal: `Goal.inflateBackInit__safety`,
`Goal.inflateBack_safety` and `Goal.inflateBackEnd_safety` in
[Safety/Back.lean](../../../ZlibF/Spec/Safety/Back.lean). The sequence goal
`Goal.inflate_back_sequence_safety` in [Sequences.lean](../../../ZlibF/Spec/Public/Sequences.lean)
is required as well. It adds that every history leaves a valid decoder state; its call clause and
its end clause are the ones the goals of `inflateBack` and `inflateBackEnd` repeat. The functional
goals `Goal.inflateBackInit_`, `Goal.inflateBack` and `Goal.inflateBackEnd` are in
[Back.lean](../../../ZlibF/Spec/Public/Back.lean). The decoding clauses of `Goal.inflateBack`
(what reaches `out`) are not planned.

<a id="callback-decoder-history"></a>
A **callback-decoder history** (`BackSafeReachable`) is what the goals of `inflateBack` and
`inflateBackEnd` range over. It starts with a call of `inflateBackInit_` that returned `Z_OK`:

- on a library heap (`Fresh`, `Uniq`, `LibraryGlobals`), with `stream_size` 112 and a `version`
  whose first byte is `'1'`; a call with another size or version byte does not return `Z_OK`;
- on a readable stream record whose `zalloc` and `zfree` are each NULL or the default function,
  with any value in its other fields, `state` included (`BackInitArguments`);
- with `windowBits` 8 to 15 and a non-NULL window of `2^windowBits` writable bytes that is a slice
  of a heap byte block.

It continues with any number of two kinds of step. One is an `inflateBack` call that met
conditions 2, 3, 5 and 6 of [its goal](#inflateback) and returned. The other is a caller edit
that changes only `next_in`, `avail_in`, `next_out`, `avail_out` and memory the stream does not
own, and keeps the bytes of the window slice. An edit also keeps the read-only flag of every
block that stays live, which no C code can change. The premises that are narrower than `zlib.h` are rows of
[deviations](../../deviations.md#callback-decoder).

`inflateBack` decodes raw DEFLATE. The caller handles any zlib/gzip header, trailer and checksum.
The caller owns a writable window of at least `2^windowBits` bytes. It is also the output buffer.
Use 15 bits and 32768 bytes for general streams; smaller windows can reject valid long distances.

```mermaid
flowchart LR
    I["inflateBackInit_: allocate state"] --> B["inflateBack: decode one stream"]
    B -->|another stream| B
    B -->|success or decode error| E["inflateBackEnd: free state"]
    I -->|no decode needed| E
```

The callbacks have these types:

```c
typedef unsigned (*in_func)(void FAR *, z_const unsigned char FAR * FAR *);
typedef int (*out_func)(void FAR *, unsigned char FAR *, unsigned);
```

`in(in_desc, &buf)` returns a byte count and sets `buf`; zero means no input and ignores `buf`.
`out(out_desc, buf, len)` receives up to one window of bytes; zero means success.
Descriptors may be NULL if the callback supports that value.

## inflateBackInit_

```c
int ZEXPORT inflateBackInit_(z_streamp strm, int windowBits, unsigned char FAR *window,
                             const char *version, int stream_size);
```

**Purpose.** Allocate decoder state and attach the caller's window.
The `inflateBackInit` macro supplies `version` and `stream_size`.

### Return values and next calls {#api-inflatebackinit_-returns}

**Return type.** `int` — zlib status code

The result says whether callback decoder state was created and attached to the caller’s window.

| Returned value | Meaning and conditions | Caller’s next step |
| --- | --- | --- |
| `Z_OK`<br>**Callback decoder created** | The version and stream size match, 8 <= windowBits <= 15, the window is non-NULL, and state allocation succeeded. | Keep the window alive and decode with inflateBack; eventually call inflateBackEnd. |
| `Z_VERSION_ERROR`<br>**Version or structure size mismatch** | version is NULL, its major-version byte differs, or stream_size is wrong; this returns before stream access. | Correct the version and structure size before initializing again; this failure needs no end call. |
| `Z_STREAM_ERROR`<br>**Stream, window or bit count refused** | strm or window is NULL, or windowBits is outside 8..15. | Provide a valid inactive stream, window and bit count before initializing again; this failure needs no end call. |
| `Z_MEM_ERROR`<br>**State allocation failed** | State allocation failed; msg and default allocator fields may change, while the old state field is retained. | Initialization may be tried again when resources are available; no new allocation was retained and this failure needs no inflateBackEnd. |

**Reading the result.**

- The window remains caller-owned; this function creates callback API state, not state for ordinary inflate.

### Calling conditions and effects {#api-inflatebackinit_-contract}

**Domain.** Restricted domain: valid caller memory, an inactive stream and default allocation.

**Pre.** A non-NULL `strm` points to a writable `z_stream` with initialized `zalloc`, `zfree`
and `opaque`. Use NULL or the default allocator/free pair; do not overwrite live library state.
A non-NULL `version` has a readable first byte. On the initialization path, `window` provides
`2^windowBits` writable bytes separate from the stream. Keep that slice alive until end.

**Effects.** May initialize allocator fields and `opaque`, clear `msg` and allocate one state.
The window remains caller-owned and is not allocated, cleared or freed here.

**Proof goals.**

- **Goal.** `Goal.inflateBackInit__safety` ([Safety/Back.lean](../../../ZlibF/Spec/Safety/Back.lean)); required. Theorem: `ZlibF.Spec.Public.BackSafetyProof.inflateBackInit__safety` ([public-back-safety.lean](../../../ZlibF/Proof/public-back-safety.lean)).
- **Applies when** (1 to 3 are `InitArguments`, the conditions of `inflateInit2_`):
    1. the heap is a library heap (`Fresh`, `Uniq`, `LibraryGlobals`);
    2. `version` is NULL or its first byte is readable (`VersionValue`);
    3. `strm` is NULL, or points to a readable stream record whose `zalloc` and `zfree` are each NULL or the default function (`DefaultOrNull`);
    4. when `window` is not NULL and `windowBits` is 8 to 15, `window` covers `2^windowBits` writable bytes (`Writable`).
- **Covered without condition.** Every `windowBits`, also outside 8 to 15; a NULL `window`; every `stream_size`; every value of the first byte of `version`; every value of the other fields of the record, `state` included; every allocation outcome. The goal is wider than Pre: it also covers a NULL `strm`, a wrong version or `stream_size`, and a record whose `state` is not NULL. If that record was a live decoder and the call returns `Z_OK`, the old state stays allocated and the record no longer points to it: the account records that leak, it does not exclude it.
- **Guarantees.**
    - *Returns.* The call returns. With a NULL `strm` the code is `Z_VERSION_ERROR` or `Z_STREAM_ERROR`.
    - *State.* With `Z_OK`, the stream record points to a valid callback-decoder state in the new block, and that state's window is `window` (`BackValid`).
    - *Writes.* With a NULL `strm`, nothing: the heap is unchanged. Otherwise only the stream record and the block the call itself allocates (`Frame`).
    - *Allocations.* With `Z_OK`, exactly one block is new, the state record, and nothing is freed (`LiveChange`). With any other code the allocated blocks are the same as before the call.
- **Not in this goal.** A stream whose `zalloc` or `zfree` is a custom function: outside every goal ([deviations](../../deviations.md)). Which code each refusal and the allocation failure returns, and the field values after the call: functional goal `Goal.inflateBackInit_`, not required for the safety results. That a valid call does return `Z_OK`: `Goal.inflate_back_initialisation_domain` ([Public/Domains.lean](../../../ZlibF/Spec/Public/Domains.lean)), required.

<details markdown="1" class="ar-return-exact" data-return-exact="inflateBackInit_"><summary>Complete return conditions and boundaries</summary>

**Post.** `Z_OK` attaches fresh state for `inflateBack` with `8 <= windowBits <= 15`.
Input/output pointers, availability counters, totals, `adler` and `data_type` are unchanged.
Only selected state fields are initialized; use this state with the callback API.

**Errors.** A NULL version, different major-version byte or wrong stream size gives
`Z_VERSION_ERROR` before stream access. NULL `strm`/`window`, or bits outside 8..15, gives
`Z_STREAM_ERROR`. Allocation failure gives `Z_MEM_ERROR`: `msg` and allocator defaults may
have changed, but the old `state` field is retained. No state was allocated, so no end call
is needed after failed init in this inactive-stream domain.

</details>

## inflateBack

```c
int ZEXPORT inflateBack(z_streamp strm, in_func in, void FAR *in_desc,
                        out_func out, void FAR *out_desc);
```

**Purpose.** Decode one complete raw stream through the input and output callbacks.

### Return values and next calls {#api-inflateback-returns}

**Return type.** `int` — zlib status code

The result covers callback decoding of one complete raw stream. This function never returns Z_OK, and every call starts a fresh stream.

| Returned value | Meaning and conditions | Caller’s next step |
| --- | --- | --- |
| `Z_STREAM_END`<br>**Raw stream and output complete** | A complete raw DEFLATE stream was decoded and every output callback returned zero. | Preserve the unread suffix in next_in/avail_in; decode another independent stream or call inflateBackEnd. |
| `Z_BUF_ERROR`<br>**Input callback had no more data** | next_in is NULL on return; the input callback returned zero and input was exhausted. | The current decode is incomplete; end it, or prepare complete input and start a fresh decode from the beginning rather than resuming a pause. |
| `Z_BUF_ERROR`<br>**Output callback failed** | next_in is non-NULL on return; an output callback returned nonzero. A final output failure changes an otherwise Z_STREAM_END result to this value. | Handle the caller’s output failure; end the decoder or start an independent decode from the beginning, without ordinary inflate-style continuation. |
| `Z_DATA_ERROR`<br>**Malformed DEFLATE** | Malformed raw DEFLATE was found and msg set; output may already have been delivered, and a final output failure does not replace this error. | Call inflateBackEnd, or prepare input again for a new stream on the next inflateBack call. |
| `Z_STREAM_ERROR`<br>**Stream or state missing** | strm or state is NULL; no callbacks are invoked. | First create a valid callback decoder with inflateBackInit_; ordinary inflate state cannot be used with this interface. |

**Reading the result.**

- For Z_BUF_ERROR, distinguish input exhaustion from output failure by whether next_in is NULL; this is not ordinary inflate’s buffer-retry protocol.
- The input callback returns a byte count, with zero meaning no input; the output callback returns zero for success. Output can be delivered before errors and on the final error path.

### Calling conditions and effects {#api-inflateback-contract}

**Domain.** Restricted domain: a live callback decoder, valid separated slices and a finite,
returning callback protocol. Arbitrary malformed input bytes are included.

**Pre.** Init succeeded and end has not run. Keep the stream, state and window live.
Initialize `next_in`; NULL requests callback input immediately and ignores `avail_in`.
Otherwise initialize `avail_in` and provide that many readable bytes at `next_in`.
Initial and callback-provided input slices do not overlap the window, stream or private state.
Neither callback is NULL. Every callback returns safely and the total input supplied is bounded.

Callbacks may read only the input/output bytes supplied to them and their own valid objects.
They may update, allocate or free their own memory, but preserve the stream, private state and
window slice. An input chunk remains readable and unchanged until the next input callback or
return, including across output callbacks. Output callbacks read at most `len` window bytes.
Callback storage and the window may share an allocation when their used byte slices do not overlap.
No concurrent or re-entrant access to this stream is allowed.

**Effects.** Reset decoding for a new stream, consume input, write the window and invoke callbacks.
Full windows and a final nonempty partial window are delivered to `out`, including on error.
Callbacks may therefore observe output before a later format or input failure.
The library allocates and frees nothing; callback allocations remain the caller's responsibility.

**Proof goals.**

- **Goal.** `Goal.inflateBack_safety` ([Safety/Back.lean](../../../ZlibF/Spec/Safety/Back.lean)); required. Theorem: `ZlibF.Spec.Public.BackSafetyProof.inflateBack_safety` ([public-back-safety.lean](../../../ZlibF/Proof/public-back-safety.lean)). The goal has three clauses: the refusal of a NULL stream, the refusal of a stream record whose state is NULL, and one call on a history. The first and the third are clauses 1 and 3 of the sequence goal `Goal.inflate_back_sequence_safety`.
- **Applies when.** The first refusal has no condition. The second asks that `strm` points to a readable stream record. The call on a history asks:
    1. `strm` has a [callback-decoder history](#callback-decoder-history) (`BackSafeReachable`); the premise `BackValid` names its record and its state;
    2. `next_in` is NULL, or covers `avail_in` readable bytes (`Bytes`) that do not overlap the window (`Separate`);
    3. the callbacks follow a protocol (`CallbackProtocol`) whose invariant holds at the call: each of `in` and `out` returns, changes only the callbacks' own blocks, and keeps the bytes of the window slice; `in` hands out a readable chunk that does not overlap the window; `out` keeps the current input chunk readable ([deviations](../../deviations.md#callback-decoder) lists every clause);
    4. the protocol's total input, the first chunk included, is below `2^48` bytes (`inputBound`);
    5. the platform size bound holds at the call, and each callback step keeps it (`ByteObjectsFit`, `BackPlatform`);
    6. every input chunk lies in a heap byte block: the first one (`BackFirstChunk`) and each one `in` hands out (`BackPlatform`).
- **Covered without condition.** Every input byte sequence, well formed or not, and every split of it into chunks; an `in` that returns 0; an `out` that reports failure; every value of `in_desc` and `out_desc`; callbacks that allocate and free memory of their own. In the second refusal, every value of the other fields of the record.
- **Guarantees.**
    - *Returns.* On a NULL `strm`, and on a stream record whose `state` is NULL, the call returns `Z_STREAM_ERROR`. On a history it returns `Z_STREAM_END`, `Z_DATA_ERROR` or `Z_BUF_ERROR`.
    - *State.* On a history the stream keeps a valid callback-decoder state over the same window, with the same window size (`BackValid`), and the protocol's invariant holds after the call. The stream then has a history again, and the goal of the next call applies.
    - *Writes.* In the two refusals, nothing: the heap is unchanged. On a history, only the stream record, the state record, the callbacks' own blocks and the block of the window; when that block is not one of the callbacks' own, only the window slice of it (`CallbackFrame`).
    - *Allocations.* On a history, a block outside the callbacks' own is allocated after the call exactly when it was before: the library allocates and frees nothing.
- **Not in this goal.** A stream record whose non-NULL state does not come from `inflateBackInit_`, for example one from `inflateInit_`: no goal covers it. What reaches `out`, which of the three codes is returned, and `next_in` and `avail_in` after the call: functional goal `Goal.inflateBack`, not required for the safety results, not planned. Conditions 4 to 6, the heap-block window and the rule for caller edits are narrower than `zlib.h`: rows of [deviations](../../deviations.md#callback-decoder).

<details markdown="1" class="ar-return-exact" data-return-exact="inflateBack"><summary>Complete return conditions and boundaries</summary>

**Post.** `Z_STREAM_END` means the complete raw stream was decoded and every output call succeeded.
The concatenated chunks are its uncompressed bytes, with no preset dictionary.
`next_in`/`avail_in` identify the unread suffix of the initial or last callback chunk.
After input exhaustion they are NULL/zero; otherwise the pointer advances by the consumed bytes.
Totals, `adler` and `data_type` are unchanged; `next_out`/`avail_out` are not the output interface.
The stream retains its state and window for another independent decode or end.

**Errors.** `Z_BUF_ERROR` means input exhaustion or a nonzero output result; it never returns `Z_OK`.
For `Z_BUF_ERROR`, NULL `next_in` identifies input exhaustion; non-NULL identifies output failure.
`Z_DATA_ERROR` means malformed DEFLATE and sets `msg`. A final output failure changes
`Z_STREAM_END` to `Z_BUF_ERROR`; it does not replace another error already selected.
NULL `strm` or NULL state gives `Z_STREAM_ERROR` without callbacks. Other invalid states are
outside this domain: a state from ordinary `inflateInit_` is not a callback decoder.
After a decode error, end still releases the state; another call starts a fresh stream.

</details>

## inflateBackEnd

```c
int ZEXPORT inflateBackEnd(z_streamp strm);
```

**Purpose.** Release the state allocated by callback init.

### Return values and next calls {#api-inflatebackend-returns}

**Return type.** `int` — zlib status code

The result says whether internal callback state was released; the caller always manages its window.

| Returned value | Meaning and conditions | Caller’s next step |
| --- | --- | --- |
| `Z_OK`<br>**Internal state released** | The valid callback decoder’s internal state was freed and state set to NULL; the window and other fields are unchanged. | The caller’s window may now be released or reused; reinitialize before decoding again. |
| `Z_STREAM_ERROR`<br>**No release performed** | strm, state or zfree is NULL; no memory is freed. | Check the lifetime and matching free function; these checks do not establish that an arbitrary non-NULL state is valid. |

### Calling conditions and effects {#api-inflatebackend-contract}

**Domain.** Restricted domain: a live callback decoder with valid default free, plus the checked
NULL-stream, NULL-state and NULL-free refusal cases.

**Pre.** For cleanup, init succeeded, end has not run and no decode or callback is active.
The stream and attached state remain valid; retain the matching `zfree` and `opaque`.
Cleanup is permitted after successful decoding and after any decode error.

**Effects.** Free exactly the internal state and clear `state`.

**Proof goals.**

- **Goal.** `Goal.inflateBackEnd_safety` ([Safety/Back.lean](../../../ZlibF/Spec/Safety/Back.lean)); required. Theorem: `ZlibF.Spec.Public.BackSafetyProof.inflateBackEnd_safety` ([public-back-safety.lean](../../../ZlibF/Proof/public-back-safety.lean)). The goal has three clauses: the refusal of a NULL stream, the refusal of a stream record whose `state` or `zfree` is NULL, and the end of a history. The third is clause 4 of the sequence goal `Goal.inflate_back_sequence_safety`.
- **Applies when.** The first refusal has no condition. The second asks that `strm` points to a readable stream record. The end of a history asks:
    1. `strm` has a [callback-decoder history](#callback-decoder-history) (`BackSafeReachable`).
- **Covered without condition.** Every history: straight after init, and after a decode that returned `Z_STREAM_END`, `Z_DATA_ERROR` or `Z_BUF_ERROR`. The end clause has no platform premise. In the second refusal, every value of the other fields of the record.
- **Guarantees.**
    - *Returns.* On a NULL `strm`, and on a stream record whose `state` or `zfree` is NULL, the call returns `Z_STREAM_ERROR`. On a history it returns `Z_OK`.
    - *State.* On a history the `state` field of the stream record is NULL after the call. The history ends.
    - *Writes.* In the two refusals, nothing: the heap is unchanged. On a history, only the stream record and the state block (`Frame`).
    - *Allocations.* On a history exactly the state block is freed, and nothing is allocated (`LiveChange`).
- **Not in this goal.** A stream record whose non-NULL state does not come from `inflateBackInit_`: no goal covers it. The other field values after the call: functional goal `Goal.inflateBackEnd`, not required for the safety results.

<details markdown="1" class="ar-return-exact" data-return-exact="inflateBackEnd"><summary>Complete return conditions and boundaries</summary>

**Post.** `Z_OK` leaves `state` NULL. The caller's window and all other stream fields are unchanged.
The caller may now release or reuse its window; the library never frees it.

**Errors.** NULL `strm`, NULL state or NULL `zfree` gives `Z_STREAM_ERROR` and frees nothing.
These checks do not validate an arbitrary non-NULL state or detect ownership mistakes.

[Back to the API manual](README.md) · [Contract conventions](contracts.md)

</details>
