# Deviations: what a call must satisfy

This page is for someone who calls zlib and asks: is my call covered by a safety theorem? The
checklist below answers by function family, in C terms. The tables after it give the Lean
premise behind each line, the goals that state it, and the reason for it.

A call that satisfies the lines for its function is covered. A call outside them is not covered:
it is neither proved safe nor claimed to be unsafe.

The page lists every premise of a safety goal that is narrower than `zlib.h`, or that a reader
could miss. A premise that only repeats `zlib.h` is in the Lean statement of the goal;
[coverage](coverage.md) names the goal of each function. Conditions on the model that a caller
cannot act on are in [model limits](model-limits.md). What is trusted and not proved is in the
[trusted base](trusted-base.md).

## Checklist for a caller

Each line ends with the Lean predicate that states it; a line that no predicate states says so.
`NULL` is allowed wherever a line says so, and only there.

**Every call**

- The library is the default x86_64 Linux build: LP64, static, compiled from zlib 1.4 (upstream
  commit `99623ef7`) with the six [patches](../../patches/README.md).
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

When the call fails, every later call on `s` is refused with an error value, and so is covered,
in two cases: the call returned `Z_VERSION_ERROR`, or you had set `s.state = Z_NULL` before the
call. Otherwise it depends on the failure: [note 2](#note-2-refused-streams) says what each
failure leaves in the record.

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
  the safety goal of every documented stream function except the four init functions.
- A refused call returns an error value and leaves memory as it was, except that `inflateCopy`
  and `deflateCopy` from a refused source set `dest->state` to `Z_NULL`.
  [Note 2](#note-2-refused-streams) gives the values and the exact statements.
- Not covered: a `z_stream` with a set allocator whose `state` holds a stale or garbage pointer.
  This includes a struct copy used after the original was ended.

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
- These buffers, the `int` of `gzerror`, the argument of `gzputs`, and the format and every pointer
  argument of `gzprintf` and `gzvprintf` are memory of your own, not memory that zlib allocated
  for the file. In particular, never pass the string that `gzerror` returned back into a call on
  the same file (`GzRange`, `GzArguments`).
- The argument of `gzputs` is a NUL-terminated string, not `NULL` (`CString`).
- A `gzprintf` or `gzvprintf` call is a call of `vsnprintf` that C defines for its format and
  arguments, and its format has no `%n`. The library does not check this, and no premise states
  it. The model does not read the conversions of the format, so it does not detect a format
  that does not match its arguments: for such a call the theorem holds of the model and says
  nothing about the C. On a file open for writing and not in error, the format is a NUL-terminated string and
  every pointer argument points into memory that is not freed (`GzArguments`).
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
asks; the goals that state it; and the reason for it, with what is not covered.

| Premise | What it asks | Goals | Reason, and what is not covered |
| --- | --- | --- | --- |
| Initial configuration | Default x86_64 Linux, LP64, static build and default allocator: `zalloc` and `zfree` are each `NULL` or the default function (`DefaultOrNull`, `DefAlloc`) | Every goal | The proofs are about this build and this allocator. Not covered: a custom allocator, and any other build configuration ([progress](progress.md)). Failure of the default allocator is covered: the goals hold for every allocation outcome. |
| Platform byte-object scope (`ByteObjectsFit`) | Each byte object has fewer than `2^63` bytes, including caller, static and embedded storage | See the list below | The LP64 limit `PTRDIFF_MAX` on the size of one object ([platform](spec/platform.md)). It limits neither total memory nor the length of a stream. |

Where the goals state `ByteObjectsFit`:

- on the heap of every stream call (`StreamCallDomain`, and clause 2 of `StreamSequenceSafety`);
- for inflate streams, also on every earlier heap of the history, before each call and after each
  caller edit (`StreamReachable.step`, `.rebuffer`); a deflate history carries it only at the call
  a goal states;
- in the `compress*` and `uncompress*` goals (`CompressorSafety`, `UncompressCountedSafe`,
  `UncompressSingleSafe`);
- on the heap of every gz open and after every caller edit of a gz history (`GzHistory`,
  `GzOpenSafe`, `GzDopenSafe`), which covers the caller's path and mode strings;
- for the callback decoder, on the heap of each `inflateBack` call and after each call-back step
  (`BackSafeReachable.step`, `BackPlatform`).

The init, checksum and refusal goals do not state it. The End goals do not state it for the
heap of the call; an inflate history carries it as the second item says. A concrete heap satisfies it
(`inflate_default_witness_platform`).

The conditions that goals put on the model's heap (`Fresh`, `Uniq`, `LibraryGlobals`,
`CrcGlobals`), the loop fuel, the CRC address model and null pointer arithmetic are not duties of
a caller. They are in [model limits](model-limits.md#conditions-on-the-model-that-goals-state).

## Stream calls: inflate and deflate

The safety goal of a stream function holds on every reachable stream (`StreamReachable`) whose
arguments satisfy `StreamArguments`.

| Premise | What it asks | Goals | Reason, and what is not covered |
| --- | --- | --- | --- |
| Stream initialisation (`InitArguments`) | `strm` is `NULL`, or a readable record whose `zalloc` and `zfree` are each `NULL` or the default function (`DefaultOrNull`). `version` is `NULL` or readable for its first byte. The heap is well formed ([model limits](model-limits.md#conditions-on-the-model-that-goals-state)). The other fields of the record, `state` included, the first byte of `version` and `stream_size` are arbitrary. `Goal.inflateBackInit__safety` asks one thing more, which `zlib.h` asks as well: a non-`NULL` window with `windowBits` 8 to 15 is writable for `2^windowBits` bytes. | `Goal.inflateInit2__safety`, `Goal.inflateInit__safety`, `Goal.deflateInit2__safety`, `Goal.deflateInit__safety`, `Goal.inflateBackInit__safety` | Only `DefaultOrNull` is narrower than `zlib.h`. A wrong version, a wrong `stream_size` and a `NULL` stream are covered: the call returns an error code and leaves no block behind (`InitResultSafe`). See [note 1](#note-1-init-and-unset-fields). |
| First call of a history (`StreamReachable.inflateInit`, `.deflateInit`) | A history starts at an init call that returned `Z_OK`, on a readable record with `DefaultOrNull`, a `version` whose first byte is `'1'`, and `stream_size = 112`. | Both sequence goals, and every one-function stream goal through `StreamReachable` | Apart from `DefaultOrNull`, these are the conditions under which the C returns `Z_OK`. There is no clause on `state`. |
| Stream buffers (`StreamBuffers`) | The input range (`next_in`, `avail_in`) and the output range (`next_out`, `avail_out`) are separate, and neither lies in storage the stream owns. Each range is `NULL` or readable, and the output range is writable. | `Goal.inflate_safety`, `Goal.deflate_safety`, `Goal.deflateParams_safety`, and these calls in both sequence goals (`StreamArguments`). The functional `Goal.inflate` and `Goal.deflate` assume it too. | `zlib.h` describes these calls for buffers the caller keeps apart. Not covered: input that overlaps output, and a buffer inside the stream's own state. |
| Caller edits between calls (`Rebuffer`) | Between two calls of a history the caller changes only `next_in`, `avail_in`, `next_out` and `avail_out` of the stream record, and memory the stream does not own. | Both sequence goals; every one-function stream goal through `StreamReachable` | `zlib.h`'s rule: the application updates the buffer fields, and all other fields "must not be updated by the application". Not covered: a history in which the caller writes another field of the record, or a block the stream owns. |
| Other stream arguments (`StreamArguments`) | `inflateSync`: the input range is `NULL` with `avail_in = 0`, or readable and outside the stream's storage. `deflatePrime`: no `deflate` call has started the stream (`DeflateNotStarted`); `deflateSetHeader` has the same ordering rule (row "Header arguments"). The header and dictionary calls have their own rows. The other stream calls have no argument premise. | The function's safety goal, and the same call in a sequence goal | The ordering rule is `zlib.h`'s ("before the first deflate() call"). `deflatePrime` after a `deflate` call is undefined behaviour of the real C (reproduced with the real C under a sanitizer). |
| Dictionary buffers (`CallerRange`) | The dictionary argument is `NULL`, or a readable range (writable for the two `Get` calls) with no byte in a block the stream owns. For `inflateGetDictionary` the range has `whave` bytes; for `deflateGetDictionary`, `min(w_size, strstart + lookahead)` bytes. | `Goal.inflateGetDictionary_safety`, `Goal.deflateGetDictionary_safety`, `Goal.inflateSetDictionary_safety`, `Goal.deflateSetDictionary_safety`, and these calls in the sequence goals | A caller's dictionary has no reason to lie in the stream's storage. Not covered: a dictionary buffer inside the stream's window or other storage. |
| Result cells (`dictLength`, `pending`, `bits`) | No premise, and none can be stated. The translation passes these scalar out-parameters as values, not as memory. `inflateGetDictionary` takes the value of `*dictLength`, or `none` for `NULL` (`Option UInt32`). `deflateGetDictionary`, `deflatePending` and `deflateUsed` take only the fact whether each pointer is `NULL` (`Bool`). Each function returns the value the C stores as a further result. | `Goal.inflateGetDictionary_safety`, `Goal.deflateGetDictionary_safety`, `Goal.deflatePending_safety`, `Goal.deflateUsed_safety`, and these calls in the sequence goals | The goals say nothing about the memory of the result cell, through which the C stores with a plain assignment (`*dictLength = ...`). Covered: a call whose result cell is an ordinary variable of the caller, apart from the dictionary buffer, the stream record and the storage the stream owns. Not covered: any other call. |
| Header arguments (`HeaderMemory`, `DeflateNotStarted`, `DeflateHeaderLive`) | `inflateGetHeader`: the header record is not `NULL`, is not owned by the stream, and its `extra`, `name` and `comment` buffers are `NULL` or writable for `extra_max`, `name_max` and `comm_max` bytes. `deflateSetHeader`: the header is `NULL` or a record the stream does not own, whose non-`NULL` `extra` is readable for `extra_len` bytes and has no byte in a block the stream owns, and whose non-`NULL` `name` and `comment` are NUL-terminated strings shorter than `2^64` bytes; and no `deflate` call has started the stream. `name` and `comment` have no ownership clause at this call; the row "Deflate gzip header regions" has it. `deflateBound`, `deflateBound_z`: `ActiveHeader` (the four rows below) and a set gzip header that is live at any time, not only while it is written. | `Goal.inflateGetHeader_safety`, `Goal.deflateSetHeader_safety`, `Goal.deflateBound_safety`, `Goal.deflateBound_z_safety`, and these calls in the sequence goals | `inflateGetHeader` stores through the pointer (`head->done = 0`), so a `NULL` header is not covered. The ordering rule of `deflateSetHeader` is `zlib.h`'s; a `NULL` header set while the header is being written is dereferenced by the real C (reproduced with the real C under a sanitizer). |
| Attached gzip header stays live (`HeaderMemory` in `ActiveHeader`) | At every `inflate` call, in every mode, also after the header is complete (`done` set): the record given to `inflateGetHeader` is still a live record that the stream does not own, and its non-`NULL` `extra`, `name` and `comment` are still writable for `extra_max`, `name_max` and `comm_max` bytes, outside the stream's storage. For a deflate stream, at every `deflate`, `deflateParams`, `deflateBound` and `deflateBound_z` call while the status is `GZIP_STATE` .. `HCRC_STATE` (`DeflateHeaderWriting`): the record given to `deflateSetHeader` is live and not owned by the stream, its non-`NULL` `extra` is readable for `extra_len` bytes outside the stream's storage, and its non-`NULL` `name` and `comment` are NUL-terminated strings. `GZIP_STATE` is the status of a gzip stream from init or reset on, before any `deflate` call, so the period starts at `deflateSetHeader`. After the header is written the caller may release it, except for `deflateBound` and `deflateBound_z` (row above). A stream made by `inflateCopy` or `deflateCopy` has the header pointer of its source, so the row holds for the calls on the copy too. | `Goal.inflate_safety`, `Goal.deflate_safety`, `Goal.deflateParams_safety`, `Goal.deflateBound_safety`, `Goal.deflateBound_z_safety`, and these calls in both sequence goals | The library keeps the caller's pointer and uses it in later calls. For `inflate` the premise asks more than the C uses: `inflate.c` reads and writes `state->head` only in the header modes (`HEAD` .. `HCRC`). Not covered: an `inflate` call after the caller freed the record or its buffers, also after `done`. For `deflate` the premise asks for `extra_len` readable bytes; the C reads `extra_len mod 2^16`. |
| Inflate gzip extra field (`InflateHeaderProgress`) | While `inflate` reads a gzip header (`HEAD` .. `HCRC`) into an attached `gz_header`, its `extra` buffer (`extra_max` bytes) is separate from the unread input; in `EXTRA`, the record's `extra_len` is not below `state->length`. | `Goal.inflate_safety` and every `inflate` call of `Goal.inflate_sequence_safety`; also the functional `Goal.inflate` and `Goal.inflate_sequence` | Each excluded case is undefined behaviour of the real C in the `zmemcpy` of `EXTRA` (reproduced with the real C under a sanitizer): an overlapping copy, or a write past `extra_max` after the caller lowers `extra_len` inside the extra field. `zlib.h` is silent on both. |
| Deflate gzip header regions (`DeflateHeaderApart`) | While the status is `GZIP_STATE` .. `HCRC_STATE` and a `gz_header` is attached, at every `deflate`, `deflateParams`, `deflateBound` and `deflateBound_z` call: the input range, the output range, the extra field (`extra_len mod 2^16` bytes), the name and the comment (each through its NUL) are pairwise separate byte ranges, which may share a block; the extra field, name and comment lie outside the storage the stream owns. The input and output ranges are the ones the `z_stream` fields name at that call, also for `deflateBound` and `deflateBound_z`, which do not use them. | `Goal.deflate_safety`, `Goal.deflateParams_safety`, `Goal.deflateBound_safety`, `Goal.deflateBound_z_safety` and every such call of `Goal.deflate_sequence_safety`; also the functional `Goal.deflate` and `Goal.deflate_sequence` | These regions have no reason to overlap. A name in the output range or in `pending_buf` is undefined behaviour of the real C: a flush or a header byte overwrites its NUL, and the name loop reads past the buffer (reproduced with the real C under a sanitizer). `zlib.h` is silent on these layouts. |
| Deflate gzip header progress (`DeflateHeaderProgress`) | At each call of the row above, when an earlier `deflate` call returned in the middle of a field of the attached `gz_header`, the caller has kept what was already written: a field still covers the part written (`gzindex`), and in `EXTRA_STATE`, `NAME_STATE` or `COMMENT_STATE` that field is not set to `NULL` part-way (`gzindex = 0` when it is `NULL`). | The same goals as the row above | The excluded edits are undefined behaviour of the real C (reproduced with the real C under a sanitizer): a shortened field is read past its end; a field set to `NULL` part-way is skipped without resetting `gzindex`, and the next string is read from `gzindex` on, past its end. `zlib.h` asks for the header before the first `deflate` call and is silent on changes while it is written. |
| Refused streams (`RefusedInflate`, `RefusedDeflate`) | A refused stream is `NULL`, or a readable record whose state is `NULL`, whose `zalloc` or `zfree` is `NULL`, or whose state is a live state record the check refuses (a wrong back pointer, `mode` or `status`). | The refusal clause of the safety goal of each documented stream function except the four init functions, and of `Goal.inflateCopy_safety` and `Goal.deflateCopy_safety`; `Goal.inflate_refusal`, `Goal.deflate_refusal` | Contains a record after `End`, the destination of a failed copy, a struct copy of a live record, and a record after a failed init as [note 2](#note-2-refused-streams) says. The same note lists the three kinds of record that are not covered. |
| Copy destination | In the clause for a copy from a reachable source: the destination is a readable stream record that is not the source record (`source ≠ dest`), and the source has the default allocator (`DefAlloc`). The refusal clauses ask only for a readable destination record, or for nothing when `dest` is `NULL`; they have no `source ≠ dest` premise. | `Goal.inflateCopy_safety`, `Goal.deflateCopy_safety`, and the functional `Goal.inflateCopy`, `Goal.deflateCopy` | With `dest == source` and a reachable source, the C `zmemcpy(dest, source, sizeof(z_stream))` copies an object onto itself, which is undefined behaviour. With a refused source the C returns before the copy, so `dest == source` is covered there. Not covered, because the model cannot express it: a destination that partly overlaps the source record, a buffer or a state record ([model limits](model-limits.md#how-the-runtime-represents-c), address and layout model). |
| Direct `deflateResetKeep` | A deflate call history (`StreamOperation .deflate`) has no direct `deflateResetKeep` call; `deflateReset` and `deflateInit2_` stay. | `Goal.deflate_sequence_safety` and the one-function deflate goals through `StreamReachable` | `zlib.h` declares `deflateResetKeep` under "undocumented functions (not part of the zlib API)". Not covered: a history that contains a direct call. |

### Note 1: init and unset fields

In C, the fields that the caller of `inflateInit` leaves unset hold indeterminate values. The
model has no such value. An unset integer field has an arbitrary value, and an unset pointer
field has some value the model can express: `NULL` or a reference to a model object. The four
init goals and `Goal.inflateBackInit__safety` hold for every such value, because `InitArguments`
constrains only `zalloc` and `zfree`. The init functions of the C assign `strm->state` and do not
read it. That the model has no "uninitialised pointer" value is a limit of the model
([trusted base](trusted-base.md), item 2).

The three non-vacuity goals of init (`Goal.inflate_initialisation_domain`,
`Goal.deflate_initialisation_domain`, `Goal.inflate_back_initialisation_domain`) are stated for a
record whose `state` is `NULL` before the call (`InitDomain`). They say that init returns `Z_OK`
on every such heap when no allocation fails. They are not premises of a safety goal.

### Note 2: refused streams

**Where the refusal is stated.** The safety goal of every documented inflate and deflate stream
function except the four init functions has two clauses: the refusal of a refused stream
(`RefusedInflate` or `RefusedDeflate`), and the call on a reachable stream. `Goal.inflateCopy_safety`
and `Goal.deflateCopy_safety` have a clause for a refused source, beside their clauses for a
`NULL` argument. `Goal.inflate_refusal` and `Goal.deflate_refusal` state again, in one goal each,
the refusals of `inflate`, `inflateEnd`, `inflateReset`, `inflateReset2`, `inflateGetDictionary`,
`inflateSetDictionary` and `inflateCopy`, and of `deflate`, `deflateSetDictionary`,
`deflateParams`, `deflateGetDictionary` and `deflateCopy`.

**What a refused call returns.** `Z_STREAM_ERROR`, with two exceptions that follow the C.
`inflateMark` returns `-65536`. `deflateBound` and `deflateBound_z` return the bound they give
for a `NULL` stream with the same `sourceLen`, which is not an error value.

**What a refused call changes.** For every function except `inflate`, `inflateSync` and the two
copies, the heap after the call is the heap before it. A copy from a refused source stores `NULL`
in the `state` field of the destination record, as the C does (`dest->state = Z_NULL`), and
changes nothing else; the clause asks that the destination is a readable record and the source
pointer is not `NULL`. For `inflate` and `inflateSync`, on a heap that is `Fresh`, the goal
states that the call writes no block that was live, that every live block is as it was, and that
no block is created or freed. This is not heap equality: each of the two translations allocates
and frees a local four-byte array, so the model's block counters may grow.

**A record after a failed init.** It is refused when its `state` is `NULL`, or when its `zalloc`
or `zfree` is `NULL`. The table says what each failure leaves in the record.

| Failure | `state` after the call | `zalloc`, `zfree` after the call |
| --- | --- | --- |
| `Z_VERSION_ERROR`; `Z_STREAM_ERROR` of `inflateBackInit_` for a `NULL` window or a bad `windowBits` | As before the call | As before the call. When they were `NULL`, as the checklist asks, the record is refused whatever `state` holds |
| `Z_MEM_ERROR` when the state record cannot be allocated | As before the call | Set to the default functions |
| `Z_STREAM_ERROR` of `deflateInit2_` for a bad parameter | As before the call | Set to the default functions |
| `Z_STREAM_ERROR` of `inflateInit2_` for a bad `windowBits` | `NULL` | Set to the default functions |
| `Z_MEM_ERROR` of `deflateInit2_` when one of its four buffers cannot be allocated | `NULL` | Set to the default functions |

In rows 1 to 3 `state` holds what the caller left there. With `zalloc` and `zfree` set, the
record is refused if that value is `NULL`; if it is a stale or garbage pointer, the record is
one of the three kinds below.

**Not covered.** Three kinds of record are outside the refusal domain when `zalloc` and `zfree`
are set. In C the state check reads through the pointer in each of them, which is undefined
behaviour.

1. **A state field that holds a garbage address**, as in a never-initialised automatic
   `z_stream`. The model cannot express it: the field is `NULL`, an inflate state number or a
   deflate state number, and a pointer in fresh memory is `NULL`
   ([model limits](model-limits.md#how-the-runtime-represents-c), row "Uninitialised pointers
   become NULL").
2. **A dangling state**: the field names a state that is not live, as in a struct copy used
   after the original was ended. The predicate excludes it.
3. **A wrongly typed state**: a deflate state passed to an inflate function, or the reverse. The
   predicate excludes it.

## Whole-buffer utilities and checksums

| Premise | What it asks | Goals | Reason, and what is not covered |
| --- | --- | --- | --- |
| Whole-buffer compression (`CompressArguments`) | The source and the destination do not overlap: `Separate source n dest c`. The source is readable and the destination writable for its capacity, unless the call is one the C refuses (`compressRejected`). `compress` and `compress2` take a non-`NULL` length cell; a `NULL` cell is admitted only for the `_z` forms. | `Goal.compress_safety`, `Goal.compress2_safety` and their `_z` forms | Source and destination have no reason to overlap. The length cell `*destLen` is a scalar value in the translation (`Option UInt64`), not memory, so the goals say nothing about its memory. Not covered: overlapping source and destination, and a length cell that is not a writable variable apart from both. |
| Counted decompression (`UtilitySeparation`, `UncompressCountedSafe`, `UncompressSingleSafe`) | Source, destination, the destination-length cell and the source-length cell are pairwise separate. `uncompress` and `uncompress_z` need the source/destination and length-cell/data separations. A length cell is eight readable and writable bytes (`LengthCell`); `uncompress` and `uncompress2` take non-`NULL` cells. | `Goal.uncompress_safe`, `Goal.uncompress2_safe` and their `_z` forms | These regions have no reason to overlap. Here the cells `*destLen` and `*sourceLen` are memory in the translation, so the separation is a stated premise. Not covered: a length cell that aliases a data buffer or the other cell. |
| Adler initialization queries (`AdlerBufferBytes`) | `buf` is `NULL` only with zero length; a non-`NULL` readable buffer has its full length domain. | `Goal.adler32_safety`, `Goal.adler32_z_safety`, and the functional `Goal.adler32`, `Goal.adler32_z` | Narrower than `zlib.h` of zlib 1.4, which allows a `NULL` `buf` without a condition on `len`. With `NULL` and `len = 1` the C reads `buf[0]`, before its test for `NULL`. Not covered: a `NULL` `buf` with a nonzero `len`. The CRC goals keep `BufferBytes`, which admits `NULL` with any length. |
| CRC combination operator | The operator is one that `crc32_combine_gen` or `crc32_combine_gen64` returned. | `Goal.crc32_combine_op_safety` | `zlib.h`'s domain for `crc32_combine_op`. Not covered: an arbitrary `op` value. |

## Callback decoder

`Goal.inflate_back_sequence_safety` holds on the histories of `BackSafeReachable`. So do the
history clauses of `Goal.inflateBack_safety` and `Goal.inflateBackEnd_safety`, which repeat
clauses of the sequence goal: every row below that names the sequence goal holds for those two
goals as well. `Goal.inflateBackInit__safety` has none of these premises; its premises are in
the row "Stream initialisation".

| Premise | What it asks | Goals | Reason, and what is not covered |
| --- | --- | --- | --- |
| Callback decoder init (`BackInitArguments` in `BackSafeReachable.init`) | The stream record is readable; `zalloc` and `zfree` are each `NULL` or the default function; `version` points to a readable byte `'1'`; `stream_size = 112`; the call returned `Z_OK`. The record's other fields, `state` included, may hold any value. | `Goal.inflate_back_sequence_safety` | Apart from the default allocator, these are the conditions under which the C returns `Z_OK`. An init call that fails starts no history; its safety is `Goal.inflateBackInit__safety`. |
| Callbacks (`CallbackProtocol`) | The caller supplies a protocol for its `in` and `out` functions; the list below gives its clauses. | `Goal.inflate_back_sequence_safety` | The callbacks are caller code, so what they do is a premise. Descriptor objects may share the window allocation outside the slice. |
| Caller edits between calls (`BackSafeReachable.caller`) | Between two calls a caller edit is a `Rebuffer` (row "Caller edits between calls") that keeps the window slice and the read-only flag of every block that stays live. | `Goal.inflate_back_sequence_safety` | The window is the decoder's history. Narrower than `zlib.h`, which does not forbid a write to the window between two calls. That the C does not read earlier window bytes (`inflateBack` sets `state->whave = 0` at the start of each call) is **to confirm**. When the window pointer is at offset 0 of its block, the stream owns that block in the model (`InflateOwned`), and `Rebuffer` then keeps the whole block between calls, not only the slice. No C code can change a read-only flag, so that clause excludes no caller. |
| Callback input total | `protocol.inputBound < 2^48`: one `inflateBack` call is offered fewer than `2^48` input bytes in all. The total counts the first chunk (`next_in`, `avail_in` at the call) and every chunk the `in` calls hand out. | `Goal.inflate_back_sequence_safety` | The runtime bounds every loop by `2^64` iterations ([model limits](model-limits.md#conditions-on-the-model-that-goals-state)), and each round of the decoding loop reads at least one bit, so a call offered more input could exhaust the fuel where C would continue. `zlib.h` has no such limit. |
| Callback decoder window | `8 ≤ windowBits ≤ 15` and a non-`NULL` window writable for `2^windowBits` bytes, as `zlib.h` asks, and also: the window is a slice of a heap byte block. | `Goal.inflate_back_sequence_safety`, through `BackSafeReachable.init` | The model's only other writable byte view is the depth array inside a deflate state, which is library storage that a caller cannot name. Not covered: a window there. |
| Callback decoder input chunks | Every input chunk lies in a heap byte block: the caller's first chunk (`BackFirstChunk`) and each chunk `in` hands out (`BackPlatform`). | `Goal.inflate_back_sequence_safety` | `inflate_fast` runs on the chunk, and its proof is for heap byte blocks ([model limits](model-limits.md#functional-and-model-statements), "Fast decoder helpers"). Not covered: a chunk in other storage of the model, such as a field of a structure or static data; the C handles a chunk in any readable storage. |

The clauses of `CallbackProtocol`:

- Each of `in` and `out` returns without a fault and changes only the caller's own blocks, which
  exclude the state and the stream record.
- The clauses about a call of `in` or `out` are required only on a heap in which the stream is a
  valid callback decoder over this window (`CallbackEntry`). The library hands only such heaps
  to the callbacks. Without this restriction no protocol could exist
  ([callbacks](proof/callbacks.md)).
- Each keeps the bytes of the window slice.
- `in` hands out a readable chunk that is separate from the window, the state and the stream
  record. `out` keeps the current input chunk readable.
- The total input has a finite bound (`inputBound`).
- Each callback leaves the heap well formed (`Fresh`, `Uniq`), and every block it creates is one
  of the caller's own (`ExternalFrame`).
- The protocol carries an invariant over the heap and the log of bytes supplied and delivered.
  Each callback keeps it. The invariant may depend only on the caller's own blocks and on the
  allocator fields of the heap, and not on the bytes of the window slice
  (`CallbackProtocol.local_`).

Two more premises about the same call are premises of the third clause of the goal, not clauses
of `CallbackProtocol`: the first chunk (`next_in`, `avail_in`) is readable and separate from the
window, and the invariant holds on the heap on which `inflateBack` is called.
`Goal.inflateBack_call_domain` shows that these premises and a protocol hold together on a
concrete call.

## Gzip file interface

`Goal.gz_sequence_safety` holds on every history of one handle (`GzHistory`), for every
file-system world. The safety goal of each gz function (`Goal.<function>_safety`) restricts one
clause of it to that function, with the same premises: a row below that names
`Goal.gz_sequence_safety` holds for the goals of the functions it is about. The goals are about
the patched source ([patches](../../patches/README.md) 0002 to 0005). The gz world is trusted
semantics beside the heap: the [external-I/O model](design/external-io.md) describes it, and the
[trusted base](trusted-base.md) says what is assumed of it.

| Premise | What it asks | Goals | Reason, and what is not covered |
| --- | --- | --- | --- |
| Gz open arguments (`GzOpenSafe`, `GzDopenSafe`, `GzHistory.open`) | `path` and `mode` are each `NULL` or a NUL-terminated string shorter than `2^64` bytes; the heap is well formed and its byte objects fit; the world is a well-formed file system (`FileSystem`). | `Goal.gz_sequence_safety` | The C reads each string up to its NUL. Covered: every descriptor, every mode text and every world, including every failure. Not covered: a path or mode that is not NUL-terminated inside its object. |
| Gz caller buffers (`GzRange` in `GzArguments`) | The caller buffers of `gzread`, `gzfread`, `gzwrite`, `gzfwrite`, `gzputs`, `gzgets` and `gzerror` are readable (writable for the reading calls and for `gzerror`'s `errnum`) and lie apart from the blocks the handle owns (`GzOwned`). The argument of `gzputs` is a NUL-terminated string (`CString`), through its NUL: readable bytes without a NUL, and `NULL`, are outside. | `Goal.gz_sequence_safety` | The library frees and rewrites its own blocks during a call ([below](#why-the-handles-own-strings-are-excluded)). Not covered: a buffer inside the handle's blocks. |
| Gz printf strings (`GzArguments`) | The format of `gzprintf` and `gzvprintf` and every pointer argument lie apart from the blocks the handle owns (`GzOwned`). | `Goal.gz_sequence_safety` | The same reason as the row above. |
| Gz printf call (caller's obligation; `GzArguments`) | The call of `vsnprintf` is defined in C for the format and the arguments, and the format has no `%n`: no premise states this, the caller ensures it, as for every printf call ([trusted base](trusted-base.md)). `GzArguments` asks, when the file is open for writing and not in error, that the format is a NUL-terminated string and that every pointer argument points into a block that is not freed. It asks this also when `gz_init`, `gz_zero` or `gz_vacate` then fails, where the C returns before it calls `vsnprintf`. | `Goal.gz_sequence_safety` | `vsnprintf` is an external call modelled by its contract, so every valid format is covered, floating point and `%p` included. The model does not read the conversions of the format, so a call that C does not define is no fault in the model, and the goal says nothing about the C for it. Not covered: `%n`, which writes through its argument; a format that does not match its arguments; and a call that returns before `vsnprintf` with a format that is not a string. |
| Gz caller and world steps (`GzCallerFrame`, `GzWorldStep`) | Between two calls the caller may change any block the handle does not own, and may free its own buffers; the heap stays well formed and its byte objects fit. The world may change to any well-formed file system: another party may close or reuse the handle's descriptor. | `Goal.gz_sequence_safety` | The handle's blocks belong to the library. Not covered: a history in which the caller writes a block the handle owns. The world step admits more than a real system does. |
| Gz reading termination (`ReadsFinite`) | For `gzread`, `gzfread`, `gzgetc`, `gzgetc_`, `gzgets` and `gzungetc`: the handle's descriptor has a finite read budget below `2^61` bytes (`fs.readBudget fd = some b` with `b < 2^61`), the total the descriptor can still deliver. The premise also says that the descriptor number is not negative (`HasBudget`). | The termination half of `Goal.gz_sequence_safety`, for these six calls only | On an endless source two loops of the C do not end ([below](#why-a-read-budget)). The premise excludes no fault: the no-fault half and the post-condition hold for every world, with no budget. `gzdirect`, the write side and `gzseek` do not need it. |
| Gz OS facts | A nonempty `write` never returns 0; `close` releases the descriptor also when it fails; `lseek` returns -1 or a non-negative offset. | `Goal.gz_sequence_safety`, through the world model | Assumptions about the system, trusted and not checked. The first two are Linux behaviour. The third does not hold for every file: on Linux, `lseek` on a file with unsigned offsets can return a negative value other than -1. Not covered: a descriptor on which `lseek` returns one. The first bounds the write loops of `gz_comp`. **To confirm**: by a reading of the C, a `write` that returned 0 forever would make `gz_comp` loop forever. The model has no world with such a `write`, so no theorem states this. |

The model of `strerror` is a limit of the model, not a duty of a caller: see
[model limits](model-limits.md#conditions-on-the-model-that-goals-state), row "External error
strings".

### Why the handle's own strings are excluded

The string that `gzerror` returns is `state->msg`. The library frees it in `gz_error` whenever
it clears or replaces the error, which many entries do before they read their arguments. So
passing the string back into a call on the same handle can be a use after free in the C. On a
writer whose last write stalled, `gzprintf(f, "%s", gzerror(f, &e))` frees the message and then
reads it in `vsnprintf`: AddressSanitizer reports a heap use after free. `zlib.h` only warns that
later `gzerror` calls may invalidate the string. The premise excludes the handle's own blocks for
every call that takes caller memory, whether or not that call frees the message.

### Why a read budget

Two loops of the C do not end on an endless source: a source that delivers forever data that
decodes to nothing (empty gzip members) keeps `gz_fetch` looping, and `gz_skip` with a huge
pending skip reads forever. No finite loop fuel covers this. With a read budget every loop is
bounded.

The figure `2^61` is the model's limit, not zlib's. A loop of the model has `2^64` iterations of
fuel. The reading loops are bounded by measures built from the input left, the read budget and
the bytes still to deliver (`fetchRank`; the measures of `gz_read` and `gz_skip`). A fetch fills
its buffer unless it fails, ends the input, reaches `GZ_OFF_MAX` or lowers `fetchRank`, so a
budget below `2^61` keeps those measures, and the iterations, below `2^64`. Some bound is needed:
`2^70` bytes of empty gzip members, 20 bytes each, need more rounds than the loop fuel.

The budget is keyed by descriptor number: a number reused after `close` inherits the remaining
budget. `gzdopen` refuses a negative descriptor, so no handle comes from one.
