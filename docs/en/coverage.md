# Coverage by function

This page answers one question: which theorem proves that function X of `zlib.h` is safe, and on
which domain? There is one row for each documented function. Each row names the safety goal and
the theorem whose type is exactly that goal. A separate column names the functional goal of the
function and, where it is done, its theorem; the safety results do not depend on a functional
goal that is not done.

- **Done.** Every safety goal named on this page is done: every documented function of the
  target build has a safety theorem on the domain its row states.
- **Assumed.** The six items of the [trusted base](trusted-base.md), and the premises in
  [deviations](deviations.md), which the column "domain" refers to.
- **Narrower than `zlib.h`.** Where the domain of a row asks more than `zlib.h` does, the row
  or the section [Domains narrower than `zlib.h`](#domains-narrower-than-zlibh) says so, and
  [deviations](deviations.md) has the premise.

[Progress](progress.md) lists every result with its state.

## How to read a row

- **Safety goal and theorem.** All goals are in the namespace `ZlibF.Spec.Public`, written
  `Goal.…` here. The theorem has the name of its goal unless the row
  names another; the line above each table gives the namespace of the theorems.
- **Domain.** What the goal asks beyond a reachable stream. "None" means no premise on the
  arguments. Three premises are shared by every stream and utility row and are not repeated: the
  default allocator, a well-formed model heap, and byte objects below `2^63` bytes
  ([deviations](deviations.md#build-and-platform)).
- **`NULL` or inconsistent stream.** The call on a `NULL` stream, or on a record that `zlib.h`
  calls inconsistent, is a refusal. The safety goal of every stream function except the four
  init functions has a clause for it, beside the clause for a reachable stream. The column gives
  what that clause states: the value returned and what happens to the heap. The domain of the
  clause is `RefusedInflate` or `RefusedDeflate`
  ([deviations, note 2](deviations.md#note-2-refused-streams)): when `zalloc` and `zfree` are
  set, it leaves out a state pointer that is dangling, of the other stream kind, or garbage.
  Where the column adds "also `Goal.inflate_refusal`" or "also `Goal.deflate_refusal`", that
  goal states the same refusal again; its theorem is `ZlibF.Spec.Public.RefusalProof.inflate_refusal` or
  `ZlibF.Spec.Public.RefusalProof.Deflate.deflate_refusal`.
- **Sequence goal.** Besides its own goal, every stream call except init, End and Copy is a call
  of the sequence goal of its stream kind, so it is also covered at any point of any history:
  - `Goal.inflate_sequence_safety`: theorem `Zlib.Inflate.Proofs.inflate_sequence_safety_public`;
  - `Goal.deflate_sequence_safety`: theorem `Zlib.Deflate.Universal.deflate_sequence_safety`.

  The End call is clause 3 of the sequence goal. A successful init or copy starts a history.

## Inflate streams

Theorems of the safety column: `ZlibF.Spec.Public.StreamCallSafetyProof.<name>`, unless the row
names another. The two init theorems are `ZlibF.Spec.Public.InitSafetyProof.<name>`.

| Function | Safety goal = theorem name | Domain | `NULL` or inconsistent stream | Functional goal, and its theorem where it is done |
| --- | --- | --- | --- | --- |
| `inflateInit_` (macro `inflateInit`) | `Goal.inflateInit__safety` | Every call `zlib.h` allows (`InitArguments`): `strm` `NULL` or a record with the default allocator; any `state`, version byte and `stream_size`; every allocation outcome | Inside the goal | `Goal.inflateInit_`: `init15_public` |
| `inflateInit2_` (macro `inflateInit2`) | `Goal.inflateInit2__safety` | As above, for every `windowBits` | Inside the goal | `Goal.inflateInit2_`: `inflate_init2_public` |
| `inflate` | `Goal.inflate_safety` | `StreamBuffers` and `ActiveHeader` | Inside the goal: `Z_STREAM_ERROR`; on a `Fresh` heap no block that was live is written and the live blocks stay as they were; also `Goal.inflate_refusal` | `Goal.inflate`: `Zlib.Inflate.Proofs.inflate_public` |
| `inflateEnd` | `Goal.inflateEnd_safety` | None | Inside the goal: `Z_STREAM_ERROR`, heap unchanged; also `Goal.inflate_refusal` | `Goal.inflateEnd`: `inflate_end_public` |
| `inflateSetDictionary` | `Goal.inflateSetDictionary_safety` | The dictionary buffer (`CallerRange`) | Inside the goal: `Z_STREAM_ERROR`, heap unchanged; also `Goal.inflate_refusal` | `Goal.inflateSetDictionary`: `inflateSetDictionary_public` |
| `inflateGetDictionary` | `Goal.inflateGetDictionary_safety` | The destination buffer (`CallerRange`). The result cell `*dictLength` is a value in the model ([note](#result-cells)) | Inside the goal: `Z_STREAM_ERROR`, the length value returned as it was passed, heap unchanged; also `Goal.inflate_refusal` | `Goal.inflateGetDictionary`: `inflate_getdict_public` |
| `inflateSync` | `Goal.inflateSync_safety` | The input range | Inside the goal: `Z_STREAM_ERROR`; on a `Fresh` heap no block that was live is written and the live blocks stay as they were | `Goal.inflateSync`: not done, not planned |
| `inflateCopy` | `Goal.inflateCopy_safety`: `ZlibF.Spec.Public.InflateCopySafetyProof.inflateCopy_safety` | `source ≠ dest`; the destination is a readable record | Inside the goal. A `NULL` `dest`: `Z_STREAM_ERROR`, heap unchanged. A `NULL` `source`, or a source record in `RefusedInflate`, with a readable `dest` record: `Z_STREAM_ERROR`, and only `dest->state` is set to `NULL`. The refused source is also in `Goal.inflate_refusal` | `Goal.inflateCopy`: `inflate_copy_public` |
| `inflateReset` | `Goal.inflateReset_safety` | None | Inside the goal: `Z_STREAM_ERROR`, heap unchanged; also `Goal.inflate_refusal` | `Goal.inflateReset`: `reset_public` |
| `inflateReset2` | `Goal.inflateReset2_safety` | None; every `windowBits` | Inside the goal: `Z_STREAM_ERROR`, heap unchanged; also `Goal.inflate_refusal` | `Goal.inflateReset2`: `reset2_public` |
| `inflatePrime` | `Goal.inflatePrime_safety` | None | Inside the goal: `Z_STREAM_ERROR`, heap unchanged | `Goal.inflatePrime`: `prime_public` |
| `inflateMark` | `Goal.inflateMark_safety` | None | Inside the goal: `-65536`, heap unchanged | `Goal.inflateMark`: `mark_public` |
| `inflateGetHeader` | `Goal.inflateGetHeader_safety` | `head` is not `NULL`; the header buffers (`HeaderMemory`) | Inside the goal: `Z_STREAM_ERROR`, heap unchanged | `Goal.inflateGetHeader`: `getheader_public` |

## Deflate streams

Theorems of the safety column: `ZlibF.Spec.Public.StreamCallSafetyProof.<name>`, and
`ZlibF.Spec.Public.InitSafetyProof.<name>` for the two init functions, unless the row names
another.

| Function | Safety goal = theorem name | Domain | `NULL` or inconsistent stream | Functional goal, and its theorem where it is done |
| --- | --- | --- | --- | --- |
| `deflateInit_` (macro `deflateInit`) | `Goal.deflateInit__safety` | Every call `zlib.h` allows (`InitArguments`), every level | Inside the goal | `Goal.deflateInit_`: `deflateInit_proof` |
| `deflateInit2_` (macro `deflateInit2`) | `Goal.deflateInit2__safety` | As above, for every method, `windowBits`, `memLevel` and strategy | Inside the goal | `Goal.deflateInit2_`: `deflateInit2_proof` |
| `deflate` | `Goal.deflate_safety` | `StreamBuffers` and `ActiveHeader` | Inside the goal: `Z_STREAM_ERROR`, heap unchanged; also `Goal.deflate_refusal` | `Goal.deflate`: `Zlib.Deflate.Universal.deflate_safety` |
| `deflateEnd` | `Goal.deflateEnd_safety` | None | Inside the goal: `Z_STREAM_ERROR`, heap unchanged | `Goal.deflateEnd`: `deflate_end_public` |
| `deflateSetDictionary` | `Goal.deflateSetDictionary_safety` | The dictionary buffer (`CallerRange`) | Inside the goal: `Z_STREAM_ERROR`, heap unchanged; also `Goal.deflate_refusal` | `Goal.deflateSetDictionary`: not done, not planned |
| `deflateGetDictionary` | `Goal.deflateGetDictionary_safety` | The destination buffer (`CallerRange`). The result cell `*dictLength` is a value in the model ([note](#result-cells)) | Inside the goal: `Z_STREAM_ERROR`, no length stored, heap unchanged; also `Goal.deflate_refusal` | `Goal.deflateGetDictionary`: `deflate_getdict_public` |
| `deflateCopy` | `Goal.deflateCopy_safety`: `Zlib.Deflate.Universal.deflate_copy_safety` | `source ≠ dest`; the destination is a readable record | Inside the goal. A `NULL` `dest`: `Z_STREAM_ERROR`, heap unchanged. A `NULL` `source`, or a source record in `RefusedDeflate`, with a readable `dest` record: `Z_STREAM_ERROR`, and only `dest->state` is set to `NULL`. The refused source is also in `Goal.deflate_refusal` | `Goal.deflateCopy`: `deflate_copy_public` |
| `deflateReset` | `Goal.deflateReset_safety` | None | Inside the goal: `Z_STREAM_ERROR`, heap unchanged | `Goal.deflateReset`: `deflate_reset_public` |
| `deflateParams` | `Goal.deflateParams_safety` | `StreamBuffers` and `ActiveHeader` | Inside the goal: `Z_STREAM_ERROR`, heap unchanged; also `Goal.deflate_refusal` | `Goal.deflateParams`: not done, not planned |
| `deflateTune` | `Goal.deflateTune_safety` | None | Inside the goal: `Z_STREAM_ERROR`, heap unchanged | `Goal.deflateTune`: `tune_public` |
| `deflateBound` | `Goal.deflateBound_safety` | `ActiveHeader` and `DeflateHeaderLive` | Inside the goal: the value the call returns for a `NULL` stream (a bound, not an error value), heap unchanged | `Goal.deflateBound`: not done, not planned |
| `deflateBound_z` | `Goal.deflateBound_z_safety` | `ActiveHeader` and `DeflateHeaderLive` | Inside the goal: the value the call returns for a `NULL` stream (a bound, not an error value), heap unchanged | `Goal.deflateBound_z`: not done, not planned |
| `deflatePending` | `Goal.deflatePending_safety` | None. The result cells `*pending` and `*bits` are values in the model ([note](#result-cells)) | Inside the goal: `Z_STREAM_ERROR`, neither count stored, heap unchanged | `Goal.deflatePending`: `pending_public` |
| `deflateUsed` | `Goal.deflateUsed_safety` | None. The result cell `*bits` is a value in the model ([note](#result-cells)) | Inside the goal: `Z_STREAM_ERROR`, no count stored, heap unchanged | `Goal.deflateUsed`: `used_public` |
| `deflatePrime` | `Goal.deflatePrime_safety` | Before the first `deflate` call (`DeflateNotStarted`), `zlib.h`'s rule | Inside the goal: `Z_STREAM_ERROR`, heap unchanged | `Goal.deflatePrime`: not done, not planned |
| `deflateSetHeader` | `Goal.deflateSetHeader_safety` | Before the first `deflate` call; the header buffers (`HeaderMemory`) | Inside the goal: `Z_STREAM_ERROR`, heap unchanged | `Goal.deflateSetHeader`: `header_public` |

<a id="result-cells"></a>**Result cells.** `inflateGetDictionary`, `deflateGetDictionary`,
`deflatePending` and `deflateUsed` store a result through a pointer. The translation takes such a
pointer as a value, not as memory, so the safety goals of these four functions say nothing about
the memory of the result cell: not that it is writable, and not that it lies apart from the other
regions. [Deviations](deviations.md#stream-calls-inflate-and-deflate), row "Result cells", says
which calls the model represents. The same holds for the length cell of `compress*`
([whole-buffer utilities](#whole-buffer-utilities)).

## Callback decoder

Theorems of the safety column: `ZlibF.Spec.Public.BackSafetyProof.<name>`.

| Function | Safety goal = theorem name | Domain | `NULL` or inconsistent stream | Functional goal, and its theorem where it is done |
| --- | --- | --- | --- | --- |
| `inflateBackInit_` (macro `inflateBackInit`) | `Goal.inflateBackInit__safety` | Every call `zlib.h` allows (`InitArguments`), for every `windowBits`, `stream_size` and `state`; a non-`NULL` window with `windowBits` 8 to 15 is writable for `2^windowBits` bytes; every allocation outcome | A `NULL` stream is inside the goal | `Goal.inflateBackInit_`: `ZlibF.Spec.Public.InflateBackInitProof.back_init_public`. It says which code a bad version or size, a `NULL` stream, a `NULL` window, a bad `windowBits` and allocation failure return, for every `state`. |
| `inflateBack` | `Goal.inflateBack_safety` | A history of `BackSafeReachable`; `inputBound < 2^48`; the window and every input chunk in a heap byte block; the callback protocol | Inside the goal: a `NULL` stream, and a stream record whose state is `NULL` | `Goal.inflateBack`: not done, not planned |
| `inflateBackEnd` | `Goal.inflateBackEnd_safety` | A history of `BackSafeReachable`; nothing more | Inside the goal: a `NULL` stream, and a stream record whose state or `zfree` is `NULL` | `Goal.inflateBackEnd`: `ZlibF.Spec.Public.InflateBackEndProof.back_end_public` |

- **Sequence goal.** `Goal.inflate_back_sequence_safety`: theorem
  `Zlib.Infback.Safety.inflate_back_sequence_safety`. It
  adds that every history leaves a valid decoder state over the caller's window. Its clauses 1 and
  3 are the first and third clause of `Goal.inflateBack_safety`, and its clause 4 is the third
  clause of `Goal.inflateBackEnd_safety`. A history starts at an `inflateBackInit_` call that
  returned `Z_OK`, with any `state` field before the call (`BackInitArguments`).
- **Non-vacuity.** `Goal.inflate_back_initialisation_domain`: init can succeed.
  `Goal.inflateBack_call_domain`: theorem
  `ZlibF.Spec.Public.BackCallDomainProof.inflateBack_call_domain`. It shows that every premise of
  the call clause of `Goal.inflateBack_safety` holds together on a concrete history with a
  concrete callback protocol.

## Checksums and queries

Theorems of the safety column: `ZlibF.Spec.Public.StatelessSafetyProof.<name>`. These goals say that the call returns and leaves the heap
unchanged. Every CRC goal, the combine goals included, has the premise that the model's two CRC
tables are those of the build (`CrcGlobals`). It is a condition on the model, not on the
arguments ([model limits](model-limits.md#conditions-on-the-model-that-goals-state)), so the
column "Domain" says "None" for a CRC row with no premise on the arguments.

| Function | Safety goal = theorem name | Domain | Functional goal, and its theorem where it is done |
| --- | --- | --- | --- |
| `adler32` | `Goal.adler32_safety` | **Narrower than `zlib.h`**: a `NULL` `buf` only with `len = 0` (`AdlerBufferBytes`). With `len = 1` the C reads `buf[0]`. `NULL` with `len ≥ 2` is safe in C and not covered. | `Goal.adler32`: `adler_public` |
| `adler32_z` | `Goal.adler32_z_safety` | As `adler32` | `Goal.adler32_z`: `adler_z_public` |
| `adler32_combine`, `adler32_combine64` | `Goal.adler32_combine_safety`, `Goal.adler32_combine64_safety` | None | `Goal.adler32_combine`, `Goal.adler32_combine64`: `combine_public`, `combine64_public` |
| `crc32`, `crc32_z` | `Goal.crc32_safety`, `Goal.crc32_z_safety` | `buf` readable or `NULL` with any length (`BufferBytes`) | `Goal.crc32`, `Goal.crc32_z`: `crc32`, `crc32_z` |
| `crc32_combine`, `crc32_combine64` | `Goal.crc32_combine_safety`, `Goal.crc32_combine64_safety` | None | `Goal.crc32_combine`, `Goal.crc32_combine64`: `combine`, `combine64` |
| `crc32_combine_gen`, `crc32_combine_gen64` | `Goal.crc32_combine_gen_safety`, `Goal.crc32_combine_gen64_safety` | None | `Goal.crc32_combine_gen`, `Goal.crc32_combine_gen64`: `gen`, `gen64` |
| `crc32_combine_op` | `Goal.crc32_combine_op_safety` | `op` comes from `crc32_combine_gen` or `crc32_combine_gen64`, as `zlib.h` says | `Goal.crc32_combine_op`: `op` |
| `zlibVersion` | `Goal.zlibVersion_safety` | None | `Goal.zlibVersion`: `zlibVersion` |
| `zlibCompileFlags` | `Goal.zlibCompileFlags_safety` | None | `Goal.zlibCompileFlags`: `zlibCompileFlags` |
| `compressBound`, `compressBound_z` | `Goal.compressBound`, `Goal.compressBound_z`: `ZlibF.Spec.Public.Proofs.compressBound`, `compressBound_z` | None | The same goals. Their translations are pure functions with no heap and no fault, so the full contract stands for both kinds of goal. |

## Whole-buffer utilities

| Function | Safety goal and theorem | Domain | Functional goal, and its theorem where it is done |
| --- | --- | --- | --- |
| `compress`, `compress_z`, `compress2`, `compress2_z` | `Goal.compress_safety`, `Goal.compress_z_safety`, `Goal.compress2_safety`, `Goal.compress2_z_safety`: `ZlibF.Spec.Public.Proofs.Compress.<name>` | Source separate from destination; the length cell is a scalar in the model, so a cell that overlaps the data is not covered ([deviations](deviations.md#whole-buffer-utilities-and-checksums)). Every level. | `Goal.compress*`: not done, not planned |
| `uncompress`, `uncompress_z`, `uncompress2`, `uncompress2_z` | `Goal.uncompress_safe`, `Goal.uncompress_z_safe`, `Goal.uncompress2_safe`, `Goal.uncompress2_z_safe`: `ZlibF.Spec.Public.Proofs.Uncompress.<name>` | Data and length cells pairwise separate (`UtilitySeparation`) | `Goal.uncompress*`: not done, not planned |

## Gzip file interface

Each of the 31 documented gz functions, and `gzvprintf`, has its own safety goal
`Goal.<function>_safety`. The theorem has the name of the goal:
`ZlibF.Spec.Public.GzCallSafetyProof.<function>_safety`.
Each goal is one clause of the sequence goal for the calls of one function. The goal of a
function that takes a handle also has the refusal of a `NULL` handle.

- **Sequence goal.** `Goal.gz_sequence_safety`: theorem
  `ZlibF.Spec.Public.Proofs.gz_sequence_safety_public`. Its
  domain is every history of one handle (`GzHistory`) in every file-system world.
- **Non-vacuity.** `Goal.gz_sequence_nonvacuity`: theorem
  `ZlibF.Spec.Public.Proofs.GzNonvacuity.gz_sequence_nonvacuity_public`.
- **`NULL` handle.** `Goal.gz_refusal`: theorem `ZlibF.Spec.Public.GzRefusalProof.gz_refusal`.
  Each of the 29 gz functions that take a handle, `gzvprintf` included,
  returns its documented value with the heap and the world unchanged. The three open functions
  take no handle. The own goal of each of the 29 repeats its clause.

The table says which clause of the sequence goal the goal of each function restricts. The
premises are the [gz rows of deviations](deviations.md#gzip-file-interface).

| Functions (each with its own `Goal.<function>_safety`) | Part of `Goal.gz_sequence_safety` that the goal restricts | Note |
| --- | --- | --- |
| `gzopen`, `gzopen64` | Open clauses (`GzOpenSafe`) | Every path, mode and world, including every failure |
| `gzdopen` | Open clause (`GzDopenSafe`) | Every `fd`. The functional `Goal.gzdopen` is also done (`Zlib.Gzlib.Proofs.gzdopen_complete`). |
| `gzbuffer`, `gzeof`, `gzerror`, `gzclearerr`, `gztell`, `gztell64`, `gzoffset`, `gzoffset64`, `gzrewind`, `gzseek`, `gzseek64` | Call clause; `gzerror` also the clause about the string it returns | The functional goals of `gzbuffer`, `gzeof`, `gzerror`, `gzclearerr`, `gzoffset`, `gzoffset64` and `gzrewind` are also done. |
| `gzwrite`, `gzfwrite`, `gzputc`, `gzputs`, `gzprintf`, `gzvprintf`, `gzflush`, `gzsetparams` | Call clause | `gzprintf` and `gzvprintf` need a representable format on every call, also on a reader. `zlib.h` lists `gzvprintf` as undocumented; it has a safety goal all the same, because `gzprintf` goes through it. |
| `gzread`, `gzfread`, `gzgetc`, `gzgetc_`, `gzungetc`, `gzgets` | Call clause; termination under `ReadsFinite`. `gzgetc` also the macro clause | No fault in every world; a normal return when the read budget is below `2^61` |
| `gzdirect` | Call clause | Terminates in every world |
| `gzclose`, `gzclose_r`, `gzclose_w` | Close clause | A close of the wrong mode refuses and changes nothing; otherwise every owned block is freed and the descriptor released |
| The `gzgetc()` macro of `zlib.h` (in `Goal.gzgetc_safety`) | Macro clause, and the history step `GzHistory.getcMacro` | With buffered output it is the inline path; with `x.have = 0` it calls the function, covered under `ReadsFinite`. The macro on a `NULL` handle is undefined behaviour in C and is not covered. |
| A second handle on the same descriptor | World step `GzHistory.world` | Any well-formed world may follow a call, so another party may close or reuse the descriptor ([example](../../tests/verification/regressions/gz-world-closes-fd.lean)). |

## Domains narrower than `zlib.h`

Each has a row in [deviations](deviations.md).

- `inflateBack`: `inputBound < 2^48`; the window and every input chunk in a heap byte block; no
  caller write to the window between two calls.
- `inflateCopy` and `deflateCopy`: `source ≠ dest`.
- `adler32` and `adler32_z`: a `NULL` `buf` only with `len = 0`.
- `inflate`, `deflate`, `deflateParams`, `compress*`, `uncompress*`: caller regions that do not
  overlap.
- `compress*`, `inflateGetDictionary`, `deflateGetDictionary`, `deflatePending`, `deflateUsed`:
  the result cell is a value in the model, so the goal says nothing about its memory.
- The gz reading calls: termination under a read budget.
- Every stream: the default allocator.
