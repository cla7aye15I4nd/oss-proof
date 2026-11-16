# Deviations: what a call must satisfy

This page is for someone who calls zlib and asks: is my call covered by a safety theorem? The
checklist below answers by function family, in C terms. The tables after it give the exact Lean
premise behind each line, the goals that state it, and what the real C does outside it.

A call that satisfies the lines for its function is covered. A call outside them is not covered:
it is neither proved safe nor claimed to be unsafe.

- **What is listed.** Every premise of a required safety goal that is narrower than `zlib.h`, or
  that a reader could miss. A premise that only repeats `zlib.h` is in the Lean statement of the
  goal, which is the authority; [coverage](coverage.md) names the goal of each function.
- **Result cells.** Eight functions store a result through a pointer that the translation
  represents as a value and not as memory: `destLen` of the four `compress*` functions,
  `dictLength` of the two `GetDictionary` functions, and the result pointers of `deflatePending`
  and `deflateUsed`. Their goals have no premise on the cell and say nothing about its memory. The
  checklist gives the line a caller has to keep, and marks it "no Lean predicate". The rows
  ["Result cells"](#stream-calls-inflate-and-deflate) and
  ["Whole-buffer compression"](#whole-buffer-utilities-and-checksums) give the details.
- **What is not listed here.** Conditions on the model that a caller cannot act on, and the limits
  of functional and model theorems: these are in [model limits](model-limits.md). What is trusted
  and not proved is in the [trusted base](trusted-base.md).
- **Evidence.** Where the real C is known to misbehave outside a premise, the row links the
  reproduction; [sanitizer reports](sanitizer-reports.md) lists them all.

A premise narrower than `zlib.h` is also written in the docstring of the Lean definition that
states it. A premise never justifies dropping a failing public case: a wrong goal is corrected
with its counterexample, and a wrong translation or runtime is corrected in that layer
([verification policy](anti-cheating.md)).

## Checklist for a caller

Each line ends with the Lean predicate that states it; a line that no predicate states says so.
`NULL` is allowed wherever a line says so, and only there.

**Every call**

- The library is the default x86_64 Linux build: LP64, static, compiled from the pinned source
  with the five patches.
- `zalloc` and `zfree` of every `z_stream` are `Z_NULL`, so zlib uses its default allocator
  (`DefaultOrNull`). A custom allocator is not covered. A failing `malloc` is covered.
- No single object in memory has 2^63 bytes or more (`ByteObjectsFit`). This is the LP64 limit
  `PTRDIFF_MAX` on one object; it does not limit total memory or the length of a stream.
- The lines hold for the whole history. A call on a stream or a file is covered when every earlier
  call on it, from its init or open on, also satisfied its lines, whatever those calls returned
  (`StreamReachable`, `GzHistory`, `BackSafeReachable`).

**`inflateInit`, `inflateInit2`, `deflateInit`, `deflateInit2`** (the `zlib.h` macros and the
functions behind them)

- `strm` is `NULL` or points to a `z_stream` whose `zalloc` and `zfree` are `Z_NULL`
  (`InitArguments`).
- Nothing else is asked. The other fields of the `z_stream`, `state` included, may hold any
  value. `version`, which the macros pass for you, is `NULL` or a readable string, and
  `stream_size` is any value: on a mismatch the call returns an error code and leaves no
  allocation behind. Every `level`, `windowBits`, `memLevel` and `strategy` is covered.

This answers the most common call:

```c
z_stream s;
s.zalloc = Z_NULL;
s.zfree = Z_NULL;
s.opaque = Z_NULL;
int rc = inflateInit(&s);   /* covered by Goal.inflateInit__safety */
```

The call is covered, and the struct does not have to be zeroed first. When it returns `Z_OK`,
the theorem also says that the stream is reachable, so every later call on `s` is covered by the
goals below. [Note 1](#note-1-init-and-unset-fields) says what the model does with the fields
the code leaves unset.

When the call does not return `Z_OK` or `Z_VERSION_ERROR`, do not pass `s` to another zlib
function unless you had set `s.state = Z_NULL` before the call. Two failures leave `state` as it
was with the allocator fields filled in: `Z_MEM_ERROR` when the state record cannot be allocated,
and `Z_STREAM_ERROR` of `deflateInit` or `deflateInit2` for a bad parameter. With `state` unset,
a later call is then outside every goal ([note 2](#note-2-refused-streams)).

`Z_VERSION_ERROR` also leaves `state` as it was, but the function returns before it fills in
`zalloc` and `zfree`. They were `Z_NULL` by the line above and still are, so every later call on
`s` is refused with `Z_STREAM_ERROR` whatever `state` holds (`RefusedInflate`, `RefusedDeflate`):
the state check tests the two allocator fields before it reads `state`.

**`inflate`, `deflate`, `deflateParams`**

- `next_in` is `NULL` or points to `avail_in` readable bytes. `next_out` is `NULL` or points to
  `avail_out` writable bytes (`StreamBuffers`).
- The input range and the output range do not overlap, and neither lies in memory that zlib
  allocated for the stream (`StreamBuffers`).
- Between two calls you change only `next_in`, `avail_in`, `next_out` and `avail_out` of the
  `z_stream`, and memory that zlib did not allocate for the stream (`Rebuffer`).
- If a `gz_header` is attached, the lines under "gzip header" hold (`ActiveHeader`).

**`inflateSync`**

- `next_in` is `NULL` with `avail_in == 0`, or points to `avail_in` readable bytes outside the
  stream's own memory (`StreamArguments`).

**Dictionaries: `inflateSetDictionary`, `deflateSetDictionary`, `inflateGetDictionary`,
`deflateGetDictionary`**

- The dictionary pointer is `NULL`, or a buffer outside the stream's own memory: readable for
  `dictLength` bytes for the two `Set` calls, writable for the bytes returned for the two `Get`
  calls (`CallerRange`). `zlib.h` says that 32768 bytes are always enough for a `Get` call.
- For the two `Get` calls, `dictLength` is `NULL` or points to a `uInt` variable of your own that
  overlaps neither the dictionary buffer, the `z_stream` nor the stream's own memory. No Lean
  predicate states this line: the translation returns the length as a value (row
  ["Result cells"](#stream-calls-inflate-and-deflate)).

**gzip header, reading: `inflateGetHeader`, then `inflate`**

- At `inflateGetHeader`: `head` is not `NULL`. Its `extra`, `name` and `comment` are each `NULL` or
  writable for `extra_max`, `name_max` and `comm_max` bytes. The record and these buffers are
  outside the stream's own memory (`HeaderMemory`).
- The record stays attached to the stream until a successful `inflateReset` or `inflateReset2`,
  an `inflateSync` that finds a sync point (it resets the stream), an `inflateGetHeader` call
  that replaces it, or `inflateEnd`. While it is attached, the record
  and its buffers stay valid in the same way at every `inflate` call, also after the header is
  complete (`HeaderMemory` in `ActiveHeader`).
- While `inflate` is still reading the header, the `extra` buffer does not overlap the unread
  input, and you do not lower `extra_len` in the record (`InflateHeaderProgress`).
- A copy made by `inflateCopy` is attached to the same record. These lines hold at every
  `inflate` call on the copy too, until the copy is detached in one of the same ways.

**gzip header, writing: `deflateSetHeader`, `deflatePrime`, then `deflate`, `deflateParams`,
`deflateBound`, `deflateBound_z`**

- `deflateSetHeader` and `deflatePrime` are called before the first `deflate` call after init or
  reset, as `zlib.h` says (`DeflateNotStarted`).
- At `deflateSetHeader`: `head` is `NULL`, or a record outside the stream's own memory. Its `extra`
  is `NULL` or readable for `extra_len` bytes outside the stream's own memory. Its `name` and
  `comment` are each `NULL` or a NUL-terminated string (`HeaderMemory`).
- The record stays attached to the stream until `deflateReset`, a `deflateSetHeader` call that
  replaces it, or `deflateEnd`.
- From `deflateSetHeader` until `deflate` has written the header out, at every `deflate`,
  `deflateParams`, `deflateBound` and `deflateBound_z` call:
  - the record and its buffers are still valid as in the line for `deflateSetHeader`
    (`HeaderMemory` in `ActiveHeader`);
  - the input range and the output range of the `z_stream`, the extra field, the name and the
    comment do not overlap one another, and the three header buffers are outside the stream's
    own memory (`DeflateHeaderApart`);
  - when a `deflate` call has returned in the middle of the extra field, the name or the
    comment, you do not shorten that field or set it to `NULL` (`DeflateHeaderProgress`).
- After the header is written out, `deflate` and `deflateParams` ask nothing of the record. zlib
  does not report that moment.
- `deflateBound` and `deflateBound_z` read an attached record whenever they are called, also
  after the header is written out. At every such call the record and its buffers are valid as in
  the line for `deflateSetHeader` (`DeflateHeaderLive`).
- A copy made by `deflateCopy` is attached to the same record. These lines hold for the calls on
  the copy too.

**`inflateCopy`, `deflateCopy`**

- `source` is a stream as in the next item, and `dest` points to a `z_stream` that is not
  `source` (`source ≠ dest`).
- The copy points to the same `gz_header` record as `source`. The lines under "gzip header" then
  hold for the calls on both streams.

**The other stream calls** (`inflateEnd`, `deflateEnd`, `inflateReset`, `inflateReset2`,
`inflatePrime`, `inflateMark`, `deflateReset`, `deflateTune`, `deflatePending`, `deflateUsed`)

- No premise on the arguments. The stream is one that an init or a copy returned `Z_OK` for and
  that was used as this checklist says.
- You do not call `deflateResetKeep` directly on a deflate stream. `zlib.h` lists it among the
  undocumented functions, and a history that contains a direct call is outside the deflate goals.
  `deflateReset`, which calls it and then clears the hash tables, is covered (`StreamOperation`).
- `deflatePending` and `deflateUsed`: each result pointer (`pending`, `bits`) is `NULL` or points
  to a variable of your own that overlaps neither the `z_stream` nor the stream's own memory. No
  Lean predicate states this line: the translation returns the results as values (row
  ["Result cells"](#stream-calls-inflate-and-deflate)).

**A `NULL` or inconsistent stream**

- These are refused: a stream pointer that is `NULL`; a `z_stream` whose `state` is `Z_NULL`, as
  after `End`; and a struct copy of a `z_stream` that is still live. The refusal is a clause of
  the safety goal of every stream function except the four init functions
  ([note 2](#note-2-refused-streams)).
- The value returned is `Z_STREAM_ERROR`, with two exceptions that follow the C: `inflateMark`
  returns `-65536`, and `deflateBound` and `deflateBound_z` return the bound they give for a
  `NULL` stream, which is not an error value.
- A refused call leaves memory as it was. One exception: `inflateCopy` and `deflateCopy` from a
  refused source set `dest->state` to `Z_NULL`. For `inflate` and `inflateSync` the goal states
  this in a weaker form: no block that was allocated before the call is written, and the same
  blocks are allocated after it ([note 2](#note-2-refused-streams) says why).
- Not covered: a `z_stream` with a set allocator whose `state` holds a stale or garbage pointer.
  This includes a struct copy used after the original was ended, and a `z_stream` whose init
  failed after it filled in the allocator fields and left an unset `state` in place (see the
  init lines above).

**`compress`, `compress2`, `compress_z`, `compress2_z`**

- `source` is readable for `sourceLen` bytes, `dest` is writable for `*destLen` bytes, and the
  two do not overlap (`CompressArguments`). A `NULL` `source` with `sourceLen == 0` and a `NULL`
  `dest` with `*destLen == 0` are allowed.
- The calls that the C refuses with `Z_STREAM_ERROR` are covered whatever the other arguments
  are: a `NULL` `source` with a nonzero `sourceLen`, a `NULL` `dest` with a nonzero `*destLen`,
  and a `NULL` `destLen` for the `_z` forms (`compressRejected`).
- `compress` and `compress2` take a non-`NULL` `destLen` (`CompressorSafety`).
- `destLen` points to a variable of your own that does not overlap `source` or `dest`. No Lean
  predicate states this line: the translation takes `*destLen` as a value (row
  ["Whole-buffer compression"](#whole-buffer-utilities-and-checksums)).

**`uncompress`, `uncompress2`, `uncompress_z`, `uncompress2_z`**

- `source` is `NULL` or readable for the source length, and `dest` is `NULL` or writable for
  `*destLen` bytes. `destLen`, and `sourceLen` of the `2` forms, are each `NULL` or point to eight
  readable and writable bytes (`LengthCell`).
- `source`, `dest` and the length variables do not overlap one another (`UtilitySeparation`).
- `uncompress` and `uncompress2` take non-`NULL` length pointers.

**Checksums and queries**

- `adler32`, `adler32_z`: `buf` is `NULL` only with `len == 0`; otherwise it is readable for `len`
  bytes (`AdlerBufferBytes`).
- `crc32`, `crc32_z`: `buf` is `NULL`, or readable for `len` bytes.
- `crc32_combine_op`: `op` is a value that `crc32_combine_gen` or `crc32_combine_gen64` returned,
  as `zlib.h` says.
- The combine functions, `compressBound`, `compressBound_z`, `zlibVersion` and `zlibCompileFlags`
  have no premise.

**Callback decoder: `inflateBackInit`, `inflateBack`, `inflateBackEnd`**

- At `inflateBackInit`: `zalloc` and `zfree` are `Z_NULL`; `windowBits` is 8 to 15; `window` is
  not `NULL`, is writable for `2^windowBits` bytes, and is a byte array or part of one, not a
  byte field inside a structure (`BackInitArguments`, `BackSafeReachable.init`). The `state`
  field of the `z_stream` may hold any value.
- At each `inflateBack` call, `strm->next_in` is `NULL`, or points to `avail_in` readable bytes
  that do not overlap the window and that are a byte array or part of one (`BackFirstChunk`).
- Your `in` and `out` functions return, write only memory of your own, and do not write the
  window, the `z_stream` or zlib's state. Each chunk that `in` hands out is readable, is a byte
  array or part of one, does not overlap the window, and stays readable until the next `in` call
  (`CallbackProtocol`, `BackPlatform`).
- One `inflateBack` call is offered fewer than 2^48 input bytes in all, the first chunk included
  (`inputBound`).
- Between two `inflateBack` calls you do not write the window, and you change only the four
  buffer fields of the `z_stream` (`BackSafeReachable.caller`). When `window` points to the first
  byte of an array, this holds for the whole array, also past `2^windowBits` bytes: between two
  calls you write no byte of it.

**gzip files: the `gz*` functions**

- `path` and `mode` are `NULL` or NUL-terminated strings (`GzOpenSafe`, `GzDopenSafe`).
- A buffer passed to `gzread`, `gzfread` or `gzgets` is writable, and a buffer passed to
  `gzwrite` or `gzfwrite` is readable, for the length the call names. The `errnum` pointer of
  `gzerror` is `NULL` or points to an `int` of your own (`GzRange`).
- These buffers, the `int` of `gzerror`, the argument of `gzputs`, and the format and every `%s`
  argument of `gzprintf` and `gzvprintf` are memory of your own, not memory that zlib allocated
  for the file. In particular, never pass the string that `gzerror` returned back into a call on
  the same file (`GzRange`, `GzArguments`).
- The argument of `gzputs` is a NUL-terminated string, not `NULL` (`CString`).
- A `gzprintf` or `gzvprintf` format is a NUL-terminated string whose arguments match its
  conversions. It uses only integer, character and string conversions; no `%f`, `%p`, `%n`, `h`
  or `hh` modifiers, or `*` widths (`Formatted`).
- Between calls you do not write memory that zlib allocated for the file (`GzCallerFrame`).
- You do not use a file after the call that closed it: `gzclose`, or `gzclose_r` or `gzclose_w`
  on a file of that mode. The file is freed, as in C.
- Termination of `gzread`, `gzfread`, `gzgetc`, `gzgetc_`, `gzgets` and `gzungetc` is proved when the file
  descriptor can deliver fewer than 2^61 more bytes (`ReadsFinite`). Without that, the proof
  still shows that these calls cause no undefined behaviour.
- A `NULL` file is refused by every function, with nothing changed (`Goal.gz_refusal`). The
  `gzgetc()` macro on `NULL` is undefined behaviour in C and is not covered.

## Build and platform

The columns of every table below: the premise and the Lean predicate that states it; what it
asks; the goals that state it; and what is known outside it.

| Premise | What it asks | Goals | Outside the premise |
| --- | --- | --- | --- |
| Initial configuration | Default x86_64 Linux, LP64, static build and default allocator: `zalloc` and `zfree` are each `NULL` or the default function (`DefaultOrNull`, `DefAlloc`) | Every goal | Other build configurations are not planned ([scope](progress.md#scope)). A stream whose `zalloc` or `zfree` is a custom function is outside every goal. Failure of the default allocator is inside: the safety goals hold for every allocation outcome. |
| Platform byte-object scope (`ByteObjectsFit`) | Each byte object has fewer than `2^63` bytes, including caller, static and embedded storage | See the list below | A stated [system environment premise](spec/platform.md): the LP64 `PTRDIFF_MAX` object limit. It is per object, with no limit on total memory or stream length. Proving an operating-system limit is outside the zlib proof. |

Where the goals state `ByteObjectsFit`:

- on the heap of every stream call (`StreamCallDomain`, and clause 2 of `StreamSequenceSafety`);
- for inflate streams, also on every earlier heap of the history, before each call and after each
  caller edit (`StreamReachable.step`, `.rebuffer`); a deflate history carries it only at the call
  a goal states;
- in the `compress*` and `uncompress*` goals (`CompressorSafety`, `UncompressCountedSafe`,
  `UncompressSingleSafe`);
- on the heap of every gz open and after every caller edit of a gz history (`GzHistory`,
  `GzOpenSafe`, `GzDopenSafe`), which covers the caller's path and mode strings
  ([regression](../tests/verification/regressions/gzopen-path-ptrdiff.lean));
- for the callback decoder, on the heap of each `inflateBack` call and after each call-back step
  (`BackSafeReachable.step`, `BackPlatform`).

The init, End, checksum and refusal goals do not need it. The premise can be met: the public
caller witness has it (`inflate_default_witness_platform`). The functional goals
(`Goal.inflate`, `Goal.inflate_sequence`, the utility contracts, `Goal.gzopen`, `Goal.gzopen64`,
`Goal.gz_initialisation_domain`) state it in the same way.

The conditions that goals put on the model's heap (`Fresh`, `Uniq`, `LibraryGlobals`,
`CrcGlobals`), the loop fuel, the CRC address model and null pointer arithmetic are not duties of
a caller. They are in [model limits](model-limits.md#conditions-on-the-model-that-goals-state).

## Stream calls: inflate and deflate

The safety goal of a stream function holds on every reachable stream (`StreamReachable`) whose
arguments satisfy `StreamArguments`. `zlib.h` describes these calls for buffers the caller keeps
apart; the goals state the separation as a hypothesis.

| Premise | What it asks | Goals | Outside the premise |
| --- | --- | --- | --- |
| Stream initialisation (`InitArguments`) | `strm` is `NULL`, or a readable record whose `zalloc` and `zfree` are each `NULL` or the default function (`DefaultOrNull`). `version` is `NULL` or readable for its first byte. The heap is well formed ([model limits](model-limits.md#conditions-on-the-model-that-goals-state)). The other fields of the record, `state` included, the first byte of `version` and `stream_size` are arbitrary. `Goal.inflateBackInit__safety` asks one thing more, which `zlib.h` asks as well: a non-`NULL` window with `windowBits` 8 to 15 is writable for `2^windowBits` bytes. | `Goal.inflateInit2__safety`, `Goal.inflateInit__safety`, `Goal.deflateInit2__safety`, `Goal.deflateInit__safety`, `Goal.inflateBackInit__safety` | Only `DefaultOrNull` is narrower than `zlib.h`. A wrong version, a wrong `stream_size` and a `NULL` stream are inside the goals: the call returns an error code and leaves no block behind (`InitResultSafe`). See [note 1](#note-1-init-and-unset-fields). |
| First call of a history (`StreamReachable.inflateInit`, `.deflateInit`) | A history starts at an init call that returned `Z_OK`, on a readable record with `DefaultOrNull`, a `version` whose first byte is `'1'`, and `stream_size = 112`. | Both sequence goals, and every one-function stream goal through `StreamReachable` | Not a narrowing: these are the conditions under which the C returns `Z_OK`, apart from `DefaultOrNull`. There is no clause on `state`. |
| Stream buffers (`StreamBuffers`) | The input range (`next_in`, `avail_in`) and the output range (`next_out`, `avail_out`) are separate, and neither lies in storage the stream owns. Each range is `NULL` or readable, and the output range is writable. | `Goal.inflate_safety`, `Goal.deflate_safety`, `Goal.deflateParams_safety`, and these calls in both sequence goals (`StreamArguments`). The functional `Goal.inflate` and `Goal.deflate` assume it too. | A call whose input overlaps its output, or whose buffers lie inside the stream's own state, is not covered. |
| Caller edits between calls (`Rebuffer`) | Between two calls of a history the caller changes only `next_in`, `avail_in`, `next_out` and `avail_out` of the stream record, and memory the stream does not own. | Both sequence goals; every one-function stream goal through `StreamReachable` | This is `zlib.h`'s rule: the application updates the buffer fields, and all other fields "must not be updated by the application". A history in which the caller writes another field of the record, or a block the stream owns, is outside. |
| Other stream arguments (`StreamArguments`) | `inflateSync`: the input range is `NULL` with `avail_in = 0`, or readable and outside the stream's storage. `deflatePrime`: no `deflate` call has started the stream (`DeflateNotStarted`); `deflateSetHeader` has the same ordering rule (row "Header arguments"). The header and dictionary calls have their own rows. The other stream calls have no argument premise. | The function's safety goal, and the same call in a sequence goal | The ordering rule is `zlib.h`'s ("before the first deflate() call"). The excluded order is undefined behaviour of the real C ([reproduction](../tests/regression/deflate-history-domain/README.md)). |
| Dictionary buffers (`CallerRange`) | The dictionary argument is `NULL`, or a readable range (writable for the two `Get` calls) with no byte in a block the stream owns. For `inflateGetDictionary` the range has `whave` bytes; for `deflateGetDictionary`, `min(w_size, strstart + lookahead)` bytes. | `Goal.inflateGetDictionary_safety`, `Goal.deflateGetDictionary_safety`, `Goal.inflateSetDictionary_safety`, `Goal.deflateSetDictionary_safety`, and these calls in the sequence goals | A dictionary buffer inside the stream's window or other storage is not covered. |
| Result cells (`dictLength`, `pending`, `bits`) | No premise, and none can be stated. The translation passes these scalar out-parameters as values, not as memory. `inflateGetDictionary` takes the value of `*dictLength`, or `none` for `NULL` (`Option UInt32`, `ZlibF/Zlib/inflate.c.lean`). `deflateGetDictionary`, `deflatePending` and `deflateUsed` take only the fact whether each pointer is `NULL` (`Bool`, `ZlibF/Zlib/deflate.c.lean`). Each function returns the value the C stores as a further result. | `Goal.inflateGetDictionary_safety`, `Goal.deflateGetDictionary_safety`, `Goal.deflatePending_safety`, `Goal.deflateUsed_safety`, and these calls in the sequence goals | The goals say nothing about the memory of the result cell. That a non-`NULL` pointer is writable, and that the cell lies apart from the dictionary buffer, the stream record and the storage the stream owns, cannot be expressed. The C stores through the pointer with a plain assignment (`*dictLength = ...`, `*pending = ...`, `*bits = ...`). A call whose result cell is an ordinary variable of the caller, apart from these regions, is the call the model represents; any other call is not covered. This is the same limit as the length cell of `compress*` (row "Whole-buffer compression"). The working rules accept this representation for an out-parameter of an internal function only; these are public functions, and whether their translations change to take the cell as memory is an open decision of the owner ([progress](progress.md#no-fault-coverage-of-zlibh-functions), item 3). |
| Header arguments (`HeaderMemory`, `DeflateNotStarted`, `DeflateHeaderLive`) | `inflateGetHeader`: the header record is not `NULL`, is not owned by the stream, and its `extra`, `name` and `comment` buffers are `NULL` or writable for `extra_max`, `name_max` and `comm_max` bytes. `deflateSetHeader`: the header is `NULL` or a record the stream does not own, whose non-`NULL` `extra` is readable for `extra_len` bytes and has no byte in a block the stream owns, and whose non-`NULL` `name` and `comment` are NUL-terminated strings shorter than `2^64` bytes; and no `deflate` call has started the stream. `name` and `comment` have no ownership clause at this call; the row "Deflate gzip header regions" has it. `deflateBound`, `deflateBound_z`: `ActiveHeader` (the four rows below) and a set gzip header that is live at any time, not only while it is written. | `Goal.inflateGetHeader_safety`, `Goal.deflateSetHeader_safety`, `Goal.deflateBound_safety`, `Goal.deflateBound_z_safety`, and these calls in the sequence goals | `inflateGetHeader` with a `NULL` header is outside: the C stores through the pointer (`head->done = 0`). The ordering rule of `deflateSetHeader` is `zlib.h`'s; a `NULL` header set while the header is being written is dereferenced by the real C ([reproduction](../tests/regression/deflate-history-domain/README.md)). |
| Attached gzip header stays live (`HeaderMemory` in `ActiveHeader`) | At every `inflate` call, in every mode, also after the header is complete (`done` set): the record given to `inflateGetHeader` is still a live record that the stream does not own, and its non-`NULL` `extra`, `name` and `comment` are still writable for `extra_max`, `name_max` and `comm_max` bytes, outside the stream's storage. For a deflate stream, at every `deflate`, `deflateParams`, `deflateBound` and `deflateBound_z` call while the status is `GZIP_STATE` .. `HCRC_STATE` (`DeflateHeaderWriting`): the record given to `deflateSetHeader` is live and not owned by the stream, its non-`NULL` `extra` is readable for `extra_len` bytes outside the stream's storage, and its non-`NULL` `name` and `comment` are NUL-terminated strings. `GZIP_STATE` is the status of a gzip stream from init or reset on, before any `deflate` call, so the period starts at `deflateSetHeader`. After the header is written the caller may release it, except for `deflateBound` and `deflateBound_z` (row above). A stream made by `inflateCopy` or `deflateCopy` has the header pointer of its source, so the row holds for the calls on the copy too. | `Goal.inflate_safety`, `Goal.deflate_safety`, `Goal.deflateParams_safety`, `Goal.deflateBound_safety`, `Goal.deflateBound_z_safety`, and these calls in both sequence goals | For `inflate` the premise asks more than the C uses: `inflate.c` reads and writes `state->head` only in the header modes (`HEAD` .. `HCRC`), and not after `done` is set. A caller that frees the record or its buffers after `done` and then calls `inflate` again is not covered. `inflateReset` detaches the record. For `deflate` the premise asks for `extra_len` readable bytes; the C reads `extra_len mod 2^16`. |
| Inflate gzip extra field (`InflateHeaderProgress`) | While `inflate` reads a gzip header (`HEAD` .. `HCRC`) into an attached `gz_header`, its `extra` buffer (`extra_max` bytes) is separate from the unread input; in `EXTRA`, the record's `extra_len` is not below `state->length`. | `Goal.inflate_safety` and every `inflate` call of `Goal.inflate_sequence_safety`; also the functional `Goal.inflate` and `Goal.inflate_sequence` | Each excluded case is undefined behaviour of the real C in EXTRA's `zmemcpy` ([reproduction](../tests/regression/inflate-gzip-extra/README.md)): an overlapping copy, or a write past `extra_max` after a caller lowers `extra_len` inside the extra field. `zlib.h` does not say whether either layout is permitted. |
| Deflate gzip header regions (`DeflateHeaderApart`) | While the status is `GZIP_STATE` .. `HCRC_STATE` and a `gz_header` is attached, at every `deflate`, `deflateParams`, `deflateBound` and `deflateBound_z` call: the input range, the output range, the extra field (`extra_len mod 2^16` bytes), the name and the comment (each through its NUL) are pairwise separate byte ranges, which may share a block; the extra field, name and comment lie outside the storage the stream owns. The input and output ranges are the ones the `z_stream` fields name at that call, also for `deflateBound` and `deflateBound_z`, which do not use them. | `Goal.deflate_safety`, `Goal.deflateParams_safety`, `Goal.deflateBound_safety`, `Goal.deflateBound_z_safety` and every such call of `Goal.deflate_sequence_safety`; also the functional `Goal.deflate` and `Goal.deflate_sequence` | These regions have no reason to overlap. Two excluded cases are undefined behaviour of the real C ([reproduction](../tests/regression/deflate-gzip-name-output/README.md)): a name in the output range or in `pending_buf` has its NUL overwritten by a flush or a header byte, and the name loop reads past the buffer. `zlib.h` does not say whether these layouts are permitted. |
| Deflate gzip header progress (`DeflateHeaderProgress`) | At each call of the row above, when an earlier `deflate` call returned in the middle of a field of the attached `gz_header`, the caller has kept what was already written: a field still covers the part written (`gzindex`), and in `EXTRA_STATE`, `NAME_STATE` or `COMMENT_STATE` that field is not set to `NULL` part-way (`gzindex = 0` when it is `NULL`). | The same goals as the row above | The excluded edits are undefined behaviour of the real C ([reproduction](../tests/regression/deflate-history-domain/README.md)): a shortened field is read past its end; a field set to `NULL` part-way is skipped without resetting `gzindex`, and the next string is read from `gzindex` on, past its end. `zlib.h` asks the caller to provide the header before the first `deflate` call; it does not say whether the record may change while it is written. |
| Refused streams (`RefusedInflate`, `RefusedDeflate`) | A refused stream is `NULL`, or a readable record whose state is `NULL`, whose `zalloc` or `zfree` is `NULL`, or whose state is a live state record the check refuses (a wrong back pointer, `mode` or `status`). | The refusal clause of the safety goal of each stream function except the four init functions, and of `Goal.inflateCopy_safety` and `Goal.deflateCopy_safety`; `Goal.inflate_refusal`, `Goal.deflate_refusal` | This covers a record after `End`, the destination of a failed copy, a struct copy of a live record, a record after an init that returned `Z_VERSION_ERROR` when its `zalloc` and `zfree` were `NULL` before the call, and a record after any other failed init when its `state` is `NULL`: the init stored `NULL` there, or the field was `NULL` before the call. Three kinds of record are outside: see [note 2](#note-2-refused-streams). |
| Copy destination | In the clause for a copy from a reachable source: the destination is a readable stream record that is not the source record (`source ≠ dest`), and the source has the default allocator (`DefAlloc`). The refusal clauses ask only for a readable destination record, or for nothing when `dest` is `NULL`; they have no `source ≠ dest` premise. | `Goal.inflateCopy_safety`, `Goal.deflateCopy_safety`, and the functional `Goal.inflateCopy`, `Goal.deflateCopy` | With `dest == source` and a reachable source, the C `zmemcpy(dest, source, sizeof(z_stream))` copies an object onto itself, which is undefined behaviour; the case is not covered. With `dest == source` and a refused source the call is covered by the refusal clause: the C returns `Z_STREAM_ERROR` before the copy and sets `dest->state` to `NULL`. A destination that partly overlaps the source record, a buffer or a state record cannot be expressed: the model keeps `z_stream` records in their own table ([model limits](model-limits.md#how-the-runtime-represents-c), address and layout model). `zlib.h` does not say whether such a layout is permitted. |
| Direct `deflateResetKeep` | A deflate call history (`StreamOperation .deflate`) has no direct `deflateResetKeep` call; `deflateReset` and `deflateInit2_` stay. | `Goal.deflate_sequence_safety` and the one-function deflate goals through `StreamReachable` | Not a narrowing below `zlib.h`, which declares `deflateResetKeep` under "undocumented functions (not part of the zlib API)"; its goal is not a required public target ([progress](progress.md#scope)). The real C is unsafe there: after `deflateResetKeep`, `deflate(Z_BLOCK)`, `deflateCopy` and a `Z_RLE` or `Z_HUFFMAN_ONLY` flush on the copy, a later `deflate` follows an uninitialised `prev` slot and reads outside the window ([finding](findings/deflate-copy-pending-prev/README.md)); without the copy a later match can be wrong ([finding](findings/deflate-resetkeep-stale-hash/README.md)). Safety of the single call is still proved (no fault, termination); `deflateReset` goes through it. |

### When a gzip header and its buffers must be valid

| Stream | Period | What must hold |
| --- | --- | --- |
| inflate | From `inflateGetHeader` to the next successful `inflateReset` or `inflateReset2`, the next `inflateSync` that finds a sync point, the next `inflateGetHeader`, or `inflateEnd`, at every `inflate` call | The record is live; `extra`, `name` and `comment` are `NULL` or writable for their `_max` sizes |
| inflate | While `inflate` reads the header (`HEAD` .. `HCRC`) | Also: `extra` does not overlap the unread input; `extra_len` is not lowered |
| deflate | At `deflateSetHeader` | Before the first `deflate` call; `extra` readable for `extra_len` bytes and outside the stream's storage; `name` and `comment` NUL-terminated |
| deflate | From `deflateSetHeader` until the header is written (`GZIP_STATE` .. `HCRC_STATE`), at every `deflate`, `deflateParams`, `deflateBound` and `deflateBound_z` call | The record and buffers are live; no field is shortened or set to `NULL`; input, output, extra, name and comment are pairwise separate; extra, name and comment are outside the stream's storage |
| deflate | After the header is written, until `deflateReset`, the next `deflateSetHeader` or `deflateEnd` | `deflate` and `deflateParams` ask nothing of the record. `deflateBound` and `deflateBound_z` still ask that the record and buffers are live, as at `deflateSetHeader` |
| a copy | From `inflateCopy` or `deflateCopy` on | The copy has the header pointer of its source. Every row holds for the calls on the copy, until the copy is reset or ended |

### Note 1: init and unset fields

In C, the fields that the caller of `inflateInit` leaves unset hold indeterminate values. The
model has no such value. An unset integer field has an arbitrary value, and an unset pointer
field has some value the model can express: `NULL` or a reference to a model object. The four
init goals and `Goal.inflateBackInit__safety` hold for every such value, because `InitArguments`
constrains only `zalloc` and `zfree`. The C agrees with this reading: the init functions assign `strm->state` and do not read
it. That the model has no "uninitialised pointer" value is a limit of the model
([trusted base](trusted-base.md), item 2).

The three non-vacuity goals of the stream families keep a clause `state = NULL` before init,
through the predicate `InitDomain`. `Goal.inflate_initialisation_domain`,
`Goal.deflate_initialisation_domain` and `Goal.inflate_back_initialisation_domain` say that init
returns `Z_OK` on every such heap when no allocation fails; the clause narrows no safety goal
there. The first call of a callback-decoder history (`BackSafeReachable.init`) does not have the
clause: its premise is `BackInitArguments`, which is `InitDomain` without it
([callback decoder](#callback-decoder)).

### Note 2: refused streams

Where the refusal is stated. The safety goal of every documented inflate and deflate stream
function except the four init functions has two clauses: the refusal of a refused stream
(`RefusedInflate` or `RefusedDeflate`), and the call on a reachable stream. These are the goals
of `ZlibF/Spec/Safety/Streams.lean`, those of `inflateEnd` and `deflateEnd` included.
`Goal.inflateCopy_safety` and `Goal.deflateCopy_safety`
(`ZlibF/Spec/Safety/Copy.lean`) have a clause for a refused source, beside their clauses for a
`NULL` argument.

Two further goals state refusals of several functions at once
(`ZlibF/Spec/Safety/Refusals.lean`). `Goal.inflate_refusal` covers `inflate`, `inflateEnd`,
`inflateReset`, `inflateReset2`, `inflateGetDictionary`, `inflateSetDictionary`, and `inflateCopy`
from a refused source. `Goal.deflate_refusal` covers `deflate`, `deflateSetDictionary`,
`deflateParams`, `deflateGetDictionary`, and `deflateCopy` from a refused source. Each of their
clauses is also the refusal clause of that function's safety goal.

What a refused call returns. `Z_STREAM_ERROR`, except that `inflateMark` returns `-65536`, and
`deflateBound` and `deflateBound_z` return a bound: their goals state that the call on a refused
stream returns the same value as the call on a `NULL` stream with the same `sourceLen`. The C
does not treat a refused stream as an error in these two functions; it falls back to the
conservative bound.

What a refused call changes. For every function except `inflate`, `inflateSync` and the two
copies, the heap after the call is the heap before it. A copy from a refused source stores `NULL`
in the `state` field of the destination record, as the C does (`dest->state = Z_NULL`), and
changes nothing else; the clause asks that the destination is a readable record and the source
pointer is not `NULL`, and it does not ask that the two records differ. The refusals of `inflate`
and `inflateSync` are stated with a frame and an unchanged ledger, on a heap that is `Fresh` (no
live block at or above the next unused block number, a condition on the model's memory): the
call writes no block that was live, every live block is as it was, and no block is created or
freed. They are not stated as heap equality, because each of the two translations allocates and
frees a local four-byte array, so the model's block counters may grow.

A `z_stream` after a failed init is in the refusal domain when its `state` is `NULL`, or when
its `zalloc` or `zfree` is `NULL`. `inflateInit2_` stores `NULL` in `state` when it rejects
`windowBits`, and `deflateInit2_` when one of its four buffers cannot be allocated. On
`Z_VERSION_ERROR`, on `Z_MEM_ERROR` from the allocation of the state record, and on
`Z_STREAM_ERROR` of `deflateInit2_` for a bad parameter, the C returns before it writes `state`,
and the field keeps the value it had before the call. The last two returns come after the C has
replaced a `NULL` `zalloc` and `zfree` by the default functions: if `state` was not `NULL`, the
record is then one of the three kinds below. The `Z_VERSION_ERROR` return comes before that, so
`zalloc` and `zfree` also keep their values: if either was `NULL`, as the init premise asks, the
record is refused whatever `state` holds.

Three kinds of record are outside the refusal domain when `zalloc` and `zfree` are set.

1. **A state field that holds a garbage address**, as in a never-initialised automatic
   `z_stream`. It cannot be expressed: in the model the field is `NULL`, an inflate state number
   or a deflate state number, and a pointer in fresh memory is `NULL`
   ([model limits](model-limits.md#how-the-runtime-represents-c), row "Uninitialised pointers
   become NULL"). In C the check reads through the pointer, which is undefined behaviour.
2. **A dangling state**: the field names a state that is not live. It can be expressed and the
   predicate excludes it. In C the check reads the freed state, which is undefined behaviour.
3. **A wrongly typed state**: a deflate state passed to an inflate function, or the reverse. It
   can be expressed and the predicate excludes it. In C the check reads the state through the
   other structure type, which is undefined behaviour.

## Whole-buffer utilities and checksums

| Premise | What it asks | Goals | Outside the premise |
| --- | --- | --- | --- |
| Whole-buffer compression (`CompressArguments`) | The source and the destination do not overlap: `Separate source n dest c`. The source is readable and the destination writable for its capacity, unless the call is one the C refuses (`compressRejected`). `compress` and `compress2` take a non-`NULL` length cell; a `NULL` cell is admitted only for the `_z` forms. | `Goal.compress_safety`, `Goal.compress2_safety` and their `_z` forms | Overlapping source and destination are not covered. The length cell `*destLen` is a scalar value in the translation (`Option UInt64`, `ZlibF/Zlib/compress.c.lean`), not memory: that the cell is writable, and that it lies apart from the source and the destination, cannot be expressed, and a call in which it is not is not covered. Whether the translation changes to take the cell as memory is an open decision of the owner, as for the row "Result cells" of the stream calls. |
| Counted decompression (`UtilitySeparation`, `UncompressCountedSafe`, `UncompressSingleSafe`) | Source, destination, the destination-length cell and the source-length cell are pairwise separate. `uncompress` and `uncompress_z` need the source/destination and length-cell/data separations. A length cell is eight readable and writable bytes (`LengthCell`); `uncompress` and `uncompress2` take non-`NULL` cells. | `Goal.uncompress_safe`, `Goal.uncompress2_safe` and their `_z` forms | Aliasing a length cell with a data buffer or with another cell is not covered. Unlike `compress*`, the cells `*destLen` and `*sourceLen` are memory in the translation (`ZlibF/Zlib/uncompr.c.lean`), so the separation is a stated premise, not a limit of the model. |
| Adler initialization queries (`AdlerBufferBytes`) | `buf` is `NULL` only with zero length; a non-`NULL` readable buffer has its full length domain. | `Goal.adler32_safety`, `Goal.adler32_z_safety`, and the functional `Goal.adler32`, `Goal.adler32_z` | Narrower than the pinned header's unqualified wording about `NULL`. With `NULL` and `len = 1` the C reads `buf[0]`. The CRC goals keep `BufferBytes`, which admits `NULL` with any length. See the note below. |
| CRC combination operator | The operator is one that `crc32_combine_gen` or `crc32_combine_gen64` returned. | `Goal.crc32_combine_op_safety` | This is `zlib.h`'s domain for `crc32_combine_op`, not a narrowing. An arbitrary `op` value is not covered. |

Note on `adler32` with `NULL`: upstream [PR #1364](https://github.com/madler/zlib/pull/1364)
reported the one-byte read of a `NULL` `buf`. The maintainer closed it on 6 November 2026,
keeping the code and announcing a restriction on `len` in `zlib.h`. The `develop` head
`99623ef7097352da7993ba614161fd6a311e046e` does not contain that text; this row is to be compared
with it when it lands.

## Callback decoder

`Goal.inflate_back_sequence_safety` holds on the histories of `BackSafeReachable`. So do the
history clauses of `Goal.inflateBack_safety` and `Goal.inflateBackEnd_safety`, which repeat
clauses of the sequence goal: every row below that names the sequence goal holds for those two
goals as well. `Goal.inflateBackInit__safety` has none of these premises. It covers every call
`zlib.h` allows (`InitArguments`); its only premise that `zlib.h` does not state is the default
allocator ([row "Initial configuration"](#build-and-platform)).

| Premise | What it asks | Goals | Outside the premise |
| --- | --- | --- | --- |
| Callback decoder init (`BackInitArguments` in `BackSafeReachable.init`) | The stream record is readable; `zalloc` and `zfree` are each `NULL` or the default function; `version` points to a readable byte `'1'`; `stream_size = 112`; the call returned `Z_OK`. The record's other fields, `state` included, may hold any value. | `Goal.inflate_back_sequence_safety` | Nothing that `zlib.h` allows, apart from a custom allocator. A call with another version byte or another `stream_size` returns `Z_VERSION_ERROR` (the functional goal `Goal.inflateBackInit_`, which is proved), so it starts no history. An init call that fails or is refused is not a step of a history; its safety is `Goal.inflateBackInit__safety`. |
| Callbacks (`CallbackProtocol`) | The caller supplies a protocol for its `in` and `out` functions; the list below gives its clauses. | `Goal.inflate_back_sequence_safety` | These are contracts of caller code, not assumed library contracts, and stay explicit. Descriptor objects may share the window allocation outside the slice. |
| Caller edits between calls (`BackSafeReachable.caller`) | Between two calls a caller edit is a `Rebuffer` (row "Caller edits between calls") that keeps the window slice and the read-only flag of every block that stays live. | `Goal.inflate_back_sequence_safety` | C code cannot change a read-only flag, so that clause excludes no C caller. The window clause does exclude callers: a history in which the caller writes the window slice between two `inflateBack` calls is outside. When the window pointer is at offset 0 of its block, the stream owns that block in the model (`InflateOwned`), and `Rebuffer` then keeps the whole block between calls, not only the slice. `inflateBack` sets `state->whave = 0` at the start of each call, so the C appears not to read earlier window bytes (**to confirm**); `zlib.h` does not forbid such a write. |
| Callback input total | `protocol.inputBound < 2^48`: one `inflateBack` call is offered fewer than `2^48` input bytes in all. The total counts the first chunk (`next_in`, `avail_in` at the call) and every chunk the `in` calls hand out. | `Goal.inflate_back_sequence_safety` | `zlib.h` puts no limit on the total input of one call. The runtime bounds every loop by `2^64` iterations ([model limits](model-limits.md#conditions-on-the-model-that-goals-state)), and each round of the decoding loop reads at least one bit, so a call offered more input could exhaust the fuel where C would continue. `2^48` bytes is far above any input a call can process in practice. The functional `Goal.inflateBack`, which is not planned and not proved, has no such premise. |
| Callback decoder window | `8 ≤ windowBits ≤ 15` and a non-`NULL` window writable for `2^windowBits` bytes, as `zlib.h` asks, and also: the window is a slice of a heap byte block. | `Goal.inflate_back_sequence_safety`, through `BackSafeReachable.init` | `zlib.h` only asks for a writable window of `2^windowBits` bytes. The model's only other writable byte view is the depth array inside a deflate state, which is library storage that a caller cannot name; a window there is outside the proved domain. |
| Callback decoder input chunks | Every input chunk lies in a heap byte block: the caller's first chunk (`BackFirstChunk`) and each chunk `in` hands out (`BackPlatform`). | `Goal.inflate_back_sequence_safety` | The C handles a chunk in any readable storage. An input chunk in other storage of the model, for example a field of a structure or static data, is outside the proved domain. This is the same restriction as the fast entry of `inflate` ([model limits](model-limits.md#functional-and-model-statements), "Fast decoder helpers"): `inflate_fast` runs on the chunk. Generalising both decoders to any byte reference is not planned; the [callback decoder skeleton record](history/skeleton-inflate-back.md) describes it as a candidate. |

The clauses of `CallbackProtocol`:

- Each of `in` and `out` returns without a fault and changes only the caller's own blocks, which
  exclude the state and the stream record.
- Each keeps the bytes of the window slice.
- `in` hands out a readable chunk that is separate from the window, the state and the stream
  record. `out` keeps the current input chunk readable.
- The total input has a finite bound (`inputBound`).
- Each callback leaves the heap well formed (`Fresh`, `Uniq`), and every block it creates is one
  of the caller's own (`ExternalFrame`).
- The protocol carries an invariant over the heap and the log of bytes supplied and delivered.
  Each callback keeps it. The invariant may depend only
  on the caller's own blocks and on the allocator fields of the heap, and not on the bytes of the
  window slice (`CallbackProtocol.local_`).

Two more premises about the same call are premises of the third clause of the goal, not clauses
of `CallbackProtocol`: the first chunk (`next_in`, `avail_in`) is readable and separate from the
window, and the invariant holds on the heap on which `inflateBack` is called.

## Gzip file interface

`Goal.gz_sequence_safety` holds on every history of one handle (`GzHistory`), for every
file-system world. The safety goal of each gz function (`Goal.<function>_safety`) restricts one
clause of it to that function, with the same premises: a row below that names
`Goal.gz_sequence_safety` holds for the goals of the functions it is about. They are stated for
the patched source ([patches](../patches/README.md) 0002 to
0005). The gz world is trusted semantics beside the heap: the
[external-I/O model](design/external-io.md) describes it, and the [trusted base](trusted-base.md)
says what is assumed of it.

| Premise | What it asks | Goals | Outside the premise |
| --- | --- | --- | --- |
| Gz open arguments (`GzOpenSafe`, `GzDopenSafe`, `GzHistory.open`) | `path` and `mode` are each `NULL` or a NUL-terminated string shorter than `2^64` bytes; the heap is well formed and its byte objects fit; the world is a well-formed file system (`FileSystem`). | `Goal.gz_sequence_safety` | An open with any descriptor, any mode text and any world is covered, including every failure. A path or mode that is not NUL-terminated inside its object is outside, as in C. |
| Gz caller buffers (`GzRange` in `GzArguments`) | The caller buffers of `gzread`, `gzfread`, `gzwrite`, `gzfwrite`, `gzputs`, `gzgets` and `gzerror` are readable (writable for the reading calls and for `gzerror`'s `errnum`) and lie apart from the blocks the handle owns (`GzOwned`). The argument of `gzputs` is a NUL-terminated string (`CString`), through its NUL: readable bytes without a NUL, and `NULL`, are outside. | `Goal.gz_sequence_safety` | See "Why the handle's own strings are excluded" below. Caller buffers and literals are covered. |
| Gz printf strings (`GzArguments`) | The format of `gzprintf` and `gzvprintf` and every string argument (`%s`) lie apart from the blocks the handle owns (`GzOwned`). | `Goal.gz_sequence_safety` | The same reason as the row above. Literals and caller strings are covered. |
| Formatting (`Formatted`) | The format is one the model represents: integer, character and string arguments with the supported flags, widths, precisions and length modifiers. `GzArguments` asks for it at every `gzprintf` and `gzvprintf` step, also on a reader or a handle in error, where the C never reads the format. | `Goal.gz_sequence_safety` | Outside: `%f` and the other floating conversions, `%p`, `%n`, the `h` and `hh` length modifiers (`%hd`, `%hhu`), `*` widths and precisions (`%*d`), `%.3s` on an array without a NUL, and `%c` or `%d` given an `unsigned` argument (which `va_arg` allows when the value is representable). These need a model extension. |
| Gz caller and world steps (`GzCallerFrame`, `GzWorldStep`) | Between two calls the caller may change any block the handle does not own, and may free its own buffers; the heap stays well formed and its byte objects fit. The world may change to any well-formed file system: another party may close or reuse the handle's descriptor. | `Goal.gz_sequence_safety` | Wider than a real system, by design. A caller that writes a block the handle owns is outside the history. `gzbuffer`, `gzclose` and the other calls with no caller memory have no argument premise. |
| Gz reading termination (`ReadsFinite`) | For `gzread`, `gzfread`, `gzgetc`, `gzgetc_`, `gzgets` and `gzungetc`: the handle's descriptor has a finite read budget below `2^61` bytes (`fs.readBudget fd = some b` with `b < 2^61`), the total the descriptor can still deliver. The premise also says that the descriptor number is not negative (`HasBudget`). | The termination half of `Goal.gz_sequence_safety`, for these six calls only | No fault is excluded by the premise: the no-fault half and the post-condition hold for every world, with no budget. `gzdirect`, the write side and `gzseek` do not need it. See "Why a read budget" below. |
| Gz OS facts | A nonempty `write` never returns 0; `close` releases the descriptor also when it fails. | `Goal.gz_sequence_safety`, through the world model | Linux behaviour, trusted, not checked. A `write` returning 0 forever makes `gz_comp` spin in the C ([observation](progress.md#observations)). |

The model of `strerror` ("External error strings") is a limit of the model, not a duty of a
caller: see [model limits](model-limits.md#conditions-on-the-model-that-goals-state).

### Why the handle's own strings are excluded

The string that `gzerror` returns is `state->msg`. The library frees it in `gz_error`, whenever
it clears or replaces the error. The call that clears it is `gz_error(state, Z_OK, NULL)`. When
an entry makes that call differs by family:

| Entries | When they call `gz_error(state, Z_OK, NULL)` |
| --- | --- |
| Writing: `gzwrite`, `gzfwrite`, `gzputc`, `gzputs`, `gzprintf`, `gzvprintf`, `gzflush`, `gzsetparams` | After the test of the mode and of a pending error, which can return first; then before they read their arguments |
| Reading: `gzread`, `gzfread`, `gzgetc`, `gzungetc`, `gzgets` | Only when the previous read stalled (`state->again`); then before they read their arguments |
| `gzclearerr`; a successful `gzrewind`; `gzclose`, `gzclose_r` and `gzclose_w` when they close the file | Always |
| `gzseek`, `gzseek64` | After a successful seek inside transparent data, and through `gzrewind` when a reader seeks backward |
| `gztell`, `gzoffset`, `gzeof`, `gzbuffer`, `gzdirect`, `gzerror` | Never |

Any entry that records a new error also replaces the message. So passing the string back into a
call on the same handle can be a use after free in the C. On a writer whose last write stalled,
`gzprintf(f, "%s", gzerror(f, &e))` frees the message and then reads it in `vsnprintf`:
AddressSanitizer reports a heap use after free
([reproduction](../tests/regression/gzprintf-error-string/README.md)). By the same reading of the
C, `gzputs(f, gzerror(f, &e))` on that writer passes the freed string to `strlen`; no
reproduction of that call is retained. `zlib.h` only warns that later `gzerror` calls may
invalidate the string. The premise excludes the handle's own blocks for every call that takes
caller memory, whether or not that call frees the message.

### Why a read budget

`zlib.h` puts no bound on the input. Two loops of the C do not end on an endless source: a
source that delivers data forever that decodes to nothing (empty gzip members) keeps `gz_fetch`
looping, and `gz_skip` with a huge pending skip on an endless source reads forever. This is real
non-termination of the C, and no finite loop fuel can cover it. With a read budget every loop is
bounded.

The figure `2^61` is the model's limit, not zlib's. A loop of the model has `2^64` iterations of
fuel. The reading loops are bounded by measures built from the input left, the read budget and
the bytes still to deliver (`fetchRank`; the measures of `gz_read` and `gz_skip`). A fetch fills
its buffer unless it fails, ends the input, reaches `GZ_OFF_MAX` or lowers `fetchRank`, so a
budget below `2^61` keeps those measures, and the iterations, below `2^64`.

Evidence that a bound is needed: `tests/verification/regressions/gz-read-budget-fuel.lean`. An
earlier form of the premise asked only for some budget (`HasBudget`). The regression shows that
this form admits a budget of `2^70` bytes, and that `2^70` bytes of empty gzip members, 20 bytes
each, need more rounds than the loop fuel. It supports the need for a bound, not the figure
`2^61`. It is the arithmetic core, not a checked run of `gz_fetch` returning `outOfFuel`.

The budget is keyed by descriptor number: a number reused after `close` inherits the remaining
budget. `gzdopen` refuses a negative descriptor, so no handle comes from one. Termination of the
gz calls rests on two rules about the world: `ReadsFinite` for the reading calls, and the OS fact
that a nonempty `write` never returns 0 (row "Gz OS facts"), which bounds the write side.
