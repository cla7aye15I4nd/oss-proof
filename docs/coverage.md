# Coverage by function

This page answers one question: which theorem proves that function X of `zlib.h` is safe, and on
which domain? There is one row for each documented function. Each row names the safety goal, the
registered theorem whose type is exactly that goal, and the file of the proof. A separate column
names the functional theorem, where one exists; functional theorems are kept and not required.

- **Proved.** Every documented function of the target build has a registered safety theorem on
  the domain its row states. The names in the tables were compared with
  `tests/audit/public-api.json`, `tests/audit/theorems.txt` and the proof files.
- **Assumed.** The six items of the [trusted base](trusted-base.md), and the premises in
  [deviations](deviations.md), which the column "domain" refers to.
- **Open.** The gz functions and the three `inflateBack` functions are covered by a sequence
  goal and have no one-function safety goal ([progress](progress.md#ordered-next-work)). Six stream
  functions have their `NULL`-stream refusal proved in the functional goal and not yet in the
  safety goal; their rows say so.

"Registered" means listed in `tests/audit/theorems.txt`. The level and the commit of acceptance
are in [Scope](progress.md#scope).

## How to read a row

- **Safety goal and theorem.** All goals are in the namespace `ZlibF.Spec.Public`, written
  `Goal.…` here. The theorem is given without its namespace; the heading of each table names the
  namespace and the file, in `ZlibF/Proof/`.
- **Domain.** What the goal asks beyond a reachable stream. "None" means no premise on the
  arguments. Three premises are shared by every stream and utility row and are not repeated: the
  default allocator, a well-formed model heap, and byte objects below `2^63` bytes
  ([deviations](deviations.md#build-and-platform)).
- **`NULL` or inconsistent stream.** A one-function stream goal is stated for a reachable stream.
  The call on a `NULL` stream, or on a record that `zlib.h` calls inconsistent, is a refusal with
  `Z_STREAM_ERROR`; this column names the theorem that proves the refusal.
- **Sequence goal.** Besides its own goal, every stream call except init, End and Copy is a call
  of the sequence goal of its stream kind, so it is also covered at any point of any history:
  - `Goal.inflate_sequence_safety`: theorem `Zlib.Inflate.Proofs.inflate_sequence_safety_public`,
    `public-inflate-sequence-safety.lean`;
  - `Goal.deflate_sequence_safety`: theorem `Zlib.Deflate.Universal.deflate_sequence_safety`,
    `public-deflate-goals.lean`.

  The End call is clause 3 of the sequence goal. A successful init or copy starts a history.

## Inflate streams

Theorems of the safety column: `ZlibF.Spec.Public.StreamCallSafetyProof.<name>` in
`public-stream-call-safety.lean`, unless the row names another file. The two init theorems are
`ZlibF.Spec.Public.InitSafetyProof.<name>` in `public-init-safety.lean`.

| Function | Safety goal = theorem name | Domain | `NULL` or inconsistent stream | Functional theorem (kept, not required) |
| --- | --- | --- | --- | --- |
| `inflateInit_` (macro `inflateInit`) | `Goal.inflateInit__safety` | Every call `zlib.h` allows (`InitArguments`): `strm` `NULL` or a record with the default allocator; any `state`, version byte and `stream_size`; every allocation outcome | Inside the goal | `Goal.inflateInit_`: `init15_public`, `public-inflate-init.lean` |
| `inflateInit2_` (macro `inflateInit2`) | `Goal.inflateInit2__safety` | As above, for every `windowBits` | Inside the goal | `Goal.inflateInit2_`: `inflate_init2_public`, `public-inflate-init2.lean` |
| `inflate` | `Goal.inflate_safety` | `StreamBuffers` and `ActiveHeader` | `Goal.inflate_refusal` | `Goal.inflate`: `Zlib.Inflate.Proofs.inflate_public`, `public-inflate.lean` |
| `inflateEnd` | `Goal.inflateEnd_safety` | None | `Goal.inflate_refusal` | `Goal.inflateEnd`: `inflate_end_public`, `public-inflate-end.lean` |
| `inflateSetDictionary` | `Goal.inflateSetDictionary_safety` | The dictionary buffer (`CallerRange`) | `Goal.inflate_refusal` | `Goal.inflateSetDictionary`: `inflateSetDictionary_public`, `public-inflate-setdict.lean` |
| `inflateGetDictionary` | `Goal.inflateGetDictionary_safety` | The destination buffer (`CallerRange`). The result cell `*dictLength` is a value in the model ([note](#result-cells)) | `Goal.inflate_refusal` | `Goal.inflateGetDictionary`: `inflate_getdict_public`, `public-inflate-getdict.lean` |
| `inflateSync` | `Goal.inflateSync_safety` | The input range | `Zlib.Inflate.Proofs.inflateSync_check`, registered, not a goal | None: `Goal.inflateSync` is open and not planned |
| `inflateCopy` | `Goal.inflateCopy_safety`: `ZlibF.Spec.Public.InflateCopySafetyProof.inflateCopy_safety`, `public-inflate-copy-safety.lean` | `source ≠ dest`; the destination is a readable record | `NULL` arguments inside the goal; an inconsistent source in `Goal.inflate_refusal` | `Goal.inflateCopy`: `inflate_copy_public`, `public-inflate-copy.lean` |
| `inflateReset` | `Goal.inflateReset_safety` | None | `Goal.inflate_refusal` | `Goal.inflateReset`: `reset_public`, `public-inflate-reset.lean` |
| `inflateReset2` | `Goal.inflateReset2_safety` | None; every `windowBits` | `Goal.inflate_refusal` | `Goal.inflateReset2`: `reset2_public`, `public-inflate-reset2.lean` |
| `inflatePrime` | `Goal.inflatePrime_safety` | None | In the functional goal only (see below) | `Goal.inflatePrime`: `prime_public`, `public-inflate-prime.lean` |
| `inflateMark` | `Goal.inflateMark_safety` | None | In the functional goal only (see below) | `Goal.inflateMark`: `mark_public`, `public-inflate-mark.lean` |
| `inflateGetHeader` | `Goal.inflateGetHeader_safety` | `head` is not `NULL`; the header buffers (`HeaderMemory`) | `Zlib.Inflate.Proofs.inflateGetHeader_check`, registered, not a goal | `Goal.inflateGetHeader`: `getheader_public`, `public-inflate-header.lean` |

## Deflate streams

Theorems of the safety column: `ZlibF.Spec.Public.StreamCallSafetyProof.<name>` in
`public-stream-call-safety.lean`, and `ZlibF.Spec.Public.InitSafetyProof.<name>` in
`public-init-safety.lean` for the two init functions, unless the row names another file.

| Function | Safety goal = theorem name | Domain | `NULL` or inconsistent stream | Functional theorem (kept, not required) |
| --- | --- | --- | --- | --- |
| `deflateInit_` (macro `deflateInit`) | `Goal.deflateInit__safety` | Every call `zlib.h` allows (`InitArguments`), every level | Inside the goal | `Goal.deflateInit_`: `deflateInit_proof`, `public-deflate-init.lean` |
| `deflateInit2_` (macro `deflateInit2`) | `Goal.deflateInit2__safety` | As above, for every method, `windowBits`, `memLevel` and strategy | Inside the goal | `Goal.deflateInit2_`: `deflateInit2_proof`, `public-deflate-init2.lean` |
| `deflate` | `Goal.deflate_safety` | `StreamBuffers` and `ActiveHeader` | `Goal.deflate_refusal` | `Goal.deflate`: `Zlib.Deflate.Universal.deflate_safety`, `public-deflate-goals.lean` |
| `deflateEnd` | `Goal.deflateEnd_safety` | None | `Zlib.Deflate.Proofs.deflateEnd_reject`, registered, not a goal | `Goal.deflateEnd`: `deflate_end_public`, `public-deflate-end.lean` |
| `deflateSetDictionary` | `Goal.deflateSetDictionary_safety` | The dictionary buffer (`CallerRange`) | `Goal.deflate_refusal` | None: `Goal.deflateSetDictionary` is open and not planned |
| `deflateGetDictionary` | `Goal.deflateGetDictionary_safety` | The destination buffer (`CallerRange`). The result cell `*dictLength` is a value in the model ([note](#result-cells)) | `Goal.deflate_refusal` | `Goal.deflateGetDictionary`: `deflate_getdict_public`, `public-deflate-getdict.lean` |
| `deflateCopy` | `Goal.deflateCopy_safety`: `Zlib.Deflate.Universal.deflate_copy_safety`, `public-deflate-copy.lean` | `source ≠ dest`; the destination is a readable record | `NULL` arguments and a source with a `NULL` allocator or state inside the goal; a source whose state the check refuses in `Goal.deflate_refusal` | `Goal.deflateCopy`: `deflate_copy_public`, `public-deflate-copy.lean` |
| `deflateReset` | `Goal.deflateReset_safety` | None | `Zlib.Deflate.Proofs.deflateReset_reject`, registered, not a goal | `Goal.deflateReset`: `deflate_reset_public`, `public-deflate-reset.lean` |
| `deflateParams` | `Goal.deflateParams_safety` | `StreamBuffers` and `ActiveHeader` | `Goal.deflate_refusal` | None: `Goal.deflateParams` is open and not planned |
| `deflateTune` | `Goal.deflateTune_safety` | None | In the functional goal only (see below) | `Goal.deflateTune`: `tune_public`, `public-deflate-small-queries.lean` |
| `deflateBound` | `Goal.deflateBound_safety` | `ActiveHeader` and `DeflateHeaderLive` | `Zlib.Deflate.Proofs.deflateBound_nostate`, registered, not a goal | None: `Goal.deflateBound` is open and not planned |
| `deflateBound_z` | `Goal.deflateBound_z_safety` | `ActiveHeader` and `DeflateHeaderLive` | `Zlib.Deflate.Proofs.deflateBound_z_nostate`, registered, not a goal | None: `Goal.deflateBound_z` is open and not planned |
| `deflatePending` | `Goal.deflatePending_safety` | None. The result cells `*pending` and `*bits` are values in the model ([note](#result-cells)) | In the functional goal only (see below) | `Goal.deflatePending`: `pending_public`, `public-deflate-small-queries.lean` |
| `deflateUsed` | `Goal.deflateUsed_safety` | None. The result cell `*bits` is a value in the model ([note](#result-cells)) | In the functional goal only (see below) | `Goal.deflateUsed`: `used_public`, `public-deflate-small-queries.lean` |
| `deflatePrime` | `Goal.deflatePrime_safety` | Before the first `deflate` call (`DeflateNotStarted`), `zlib.h`'s rule | `Zlib.Deflate.Proofs.deflatePrime_refused`, registered, not a goal | None: `Goal.deflatePrime` is open and not planned |
| `deflateSetHeader` | `Goal.deflateSetHeader_safety` | Before the first `deflate` call; the header buffers (`HeaderMemory`) | In the functional goal only (see below) | `Goal.deflateSetHeader`: `header_public`, `public-deflate-small-queries.lean` |

**Refusal in the functional goal only.** For `inflatePrime`, `inflateMark`, `deflateTune`,
`deflatePending`, `deflateUsed` and `deflateSetHeader`, the `_safety` goal covers the call on a
reachable stream and says nothing about a `NULL` or inconsistent stream. The refusal of such a
stream is a clause of the registered functional goal of the same function (`CheckedInflate`,
`CheckedDeflate`), so it is proved, and it is not part of a required goal. Adding the refusal
clause to these six safety goals is remaining work.

<a id="result-cells"></a>**Result cells.** `inflateGetDictionary`, `deflateGetDictionary`,
`deflatePending` and `deflateUsed` store a result through a pointer. The translation takes such a
pointer as a value, not as memory, so the safety goals of these four functions say nothing about
the memory of the result cell: not that it is writable, and not that it lies apart from the other
regions. [Deviations](deviations.md#stream-calls-inflate-and-deflate), row "Result cells", says
which calls the model represents. The same holds for the length cell of `compress*`
([whole-buffer utilities](#whole-buffer-utilities)).

## Callback decoder

The three functions are proved safe through the sequence goal and have no one-function safety
goal ([progress](progress.md#ordered-next-work)).

| Function | Safety goal and theorem | Domain | `NULL` or inconsistent stream | Functional theorem (kept, not required) |
| --- | --- | --- | --- | --- |
| `inflateBackInit_` (macro `inflateBackInit`) | `Goal.inflate_back_sequence_safety`: `Zlib.Infback.Safety.inflate_back_sequence_safety`, `infback.c.safety-fast.lean`. The init is the first step of every history. | The [callback decoder rows](deviations.md#callback-decoder), which include `state == NULL` before the call | In the functional goal | `Goal.inflateBackInit_`: `ZlibF.Spec.Public.InflateBackInitProof.back_init_public`, `public-infback-init.lean`. It covers a bad version or size, a `NULL` stream, a `NULL` window, a bad `windowBits` and allocation failure, for every `state`. |
| `inflateBack` | The same goal and theorem, clause 3 | `inputBound < 2^48`; the window and every input chunk in a heap byte block; the callback protocol | A `NULL` stream is clause 1 of the goal. A `NULL` state: `Zlib.Infback.Proofs.inflateBack_nostate`, registered, not a goal | None: `Goal.inflateBack` is open and not planned |
| `inflateBackEnd` | The same goal and theorem, clause 4 | None beyond the history | In the functional goal | `Goal.inflateBackEnd`: `ZlibF.Spec.Public.InflateBackEndProof.back_end_public`, `public-infback-end.lean`. It covers `NULL`, a `NULL` state and a `NULL` `zfree`. |

The sequence theorem has eleven proof mutants of `inflateBack`, `inflateBackInit_` and
`inflateBackEnd` (`tests/proof-mutants/infback-sequence.tsv`).

## Checksums and queries

Theorems of the safety column: `ZlibF.Spec.Public.StatelessSafetyProof.<name>` in
`public-stateless-safety.lean`. These goals say that the call returns and leaves the heap
unchanged. Every CRC goal, the combine goals included, has the premise that the model's two CRC
tables are those of the build (`CrcGlobals`). It is a condition on the model, not on the
arguments ([model limits](model-limits.md#conditions-on-the-model-that-goals-state)), so the
column "Domain" says "None" for a CRC row with no premise on the arguments.

| Function | Safety goal = theorem name | Domain | Functional theorem (kept, not required) |
| --- | --- | --- | --- |
| `adler32` | `Goal.adler32_safety` | **Narrower than `zlib.h`**: a `NULL` `buf` only with `len = 0` (`AdlerBufferBytes`). With `len = 1` the C reads `buf[0]`. `NULL` with `len ≥ 2` is safe in C and not proved. | `Goal.adler32`: `adler_public`, `public-adler-update.lean` |
| `adler32_z` | `Goal.adler32_z_safety` | As `adler32` | `Goal.adler32_z`: `adler_z_public`, `public-adler-update.lean` |
| `adler32_combine`, `adler32_combine64` | `Goal.adler32_combine_safety`, `Goal.adler32_combine64_safety` | None | `Goal.adler32_combine`, `Goal.adler32_combine64`: `combine_public`, `combine64_public`, `public-adler-combine.lean` |
| `crc32`, `crc32_z` | `Goal.crc32_safety`, `Goal.crc32_z_safety` | `buf` readable or `NULL` with any length (`BufferBytes`) | `Goal.crc32`, `Goal.crc32_z`: `crc32`, `crc32_z`, `public-crc-updates.lean` |
| `crc32_combine`, `crc32_combine64` | `Goal.crc32_combine_safety`, `Goal.crc32_combine64_safety` | None | `Goal.crc32_combine`, `Goal.crc32_combine64`: `combine`, `combine64`, `public-crc-combine.lean` |
| `crc32_combine_gen`, `crc32_combine_gen64` | `Goal.crc32_combine_gen_safety`, `Goal.crc32_combine_gen64_safety` | None | `Goal.crc32_combine_gen`, `Goal.crc32_combine_gen64`: `gen`, `gen64`, `public-crc-combine.lean` |
| `crc32_combine_op` | `Goal.crc32_combine_op_safety` | `op` comes from `crc32_combine_gen` or `crc32_combine_gen64`, as `zlib.h` says | `Goal.crc32_combine_op`: `op`, `public-crc-combine.lean` |
| `zlibVersion` | `Goal.zlibVersion_safety` | None | `Goal.zlibVersion`: `zlibVersion`, `public-zlib-version.lean` |
| `zlibCompileFlags` | `Goal.zlibCompileFlags_safety` | None | `Goal.zlibCompileFlags`: `zlibCompileFlags`, `public-zlib-compile-flags.lean` |
| `compressBound`, `compressBound_z` | `Goal.compressBound`, `Goal.compressBound_z`: `ZlibF.Spec.Public.Proofs.compressBound`, `compressBound_z`, `public-compress-bound.lean` | None | The same goals. Their translations are pure functions with no heap and no fault, so the full contract stands for both kinds of goal. |

## Whole-buffer utilities

| Function | Safety goal and theorem | Domain | Functional theorem (kept, not required) |
| --- | --- | --- | --- |
| `compress`, `compress_z`, `compress2`, `compress2_z` | `Goal.compress_safety`, `Goal.compress_z_safety`, `Goal.compress2_safety`, `Goal.compress2_z_safety`: `ZlibF.Spec.Public.Proofs.Compress.<name>`, `public-compress-safe-mid.lean` | Source separate from destination; the length cell is a scalar in the model, so a cell that overlaps the data is not covered ([deviations](deviations.md#whole-buffer-utilities-and-checksums)). Every level. | None: `Goal.compress*` are open and not planned |
| `uncompress`, `uncompress_z`, `uncompress2`, `uncompress2_z` | `Goal.uncompress_safe`, `Goal.uncompress_z_safe`, `Goal.uncompress2_safe`, `Goal.uncompress2_z_safe`: `ZlibF.Spec.Public.Proofs.Uncompress.<name>`, `public-uncompress-safe.lean` | Data and length cells pairwise separate (`UtilitySeparation`) | None: `Goal.uncompress*` are open and not planned |

## Gzip file interface

The 31 documented gz functions are proved safe through the sequence goal and have no one-function
safety goal ([progress](progress.md#ordered-next-work)).

- **Sequence goal.** `Goal.gz_sequence_safety` (`ZlibF/Spec/Public/GzSafety.lean`): theorem
  `ZlibF.Spec.Public.Proofs.gz_sequence_safety_public`, `public-gz-sequence-safety.lean`. Its
  domain is every history of one handle (`GzHistory`) in every file-system world.
- **Non-vacuity.** `Goal.gz_sequence_nonvacuity`: theorem
  `ZlibF.Spec.Public.Proofs.GzNonvacuity.gz_sequence_nonvacuity_public`,
  `public-gz-sequence-nonvacuity.lean`.
- **`NULL` handle.** `Goal.gz_refusal`: theorem `ZlibF.Spec.Public.GzRefusalProof.gz_refusal`,
  `public-gz-refusal.lean`. Each of the 29 gz functions that take a handle, `gzvprintf` included,
  returns its documented value with the heap and the world unchanged. The three open functions
  take no handle.
- **Proof mutants.** Every gz function group and each hunk of patches 0002 to 0005 has mutants
  (`gz-sequence.tsv`, `gz-read.tsv`, `gz-refusal.tsv`;
  [mutant guide](checking/proof-mutants.md)).

The table says which part of the sequence goal covers each function. The premises are the
[gz rows of deviations](deviations.md#gzip-file-interface).

| Functions | Part of `Goal.gz_sequence_safety` | Note |
| --- | --- | --- |
| `gzopen`, `gzopen64` | Open clauses (`GzOpenSafe`) | Every path, mode and world, including every failure |
| `gzdopen` | Open clause (`GzDopenSafe`) | Every `fd`. The functional `Goal.gzdopen` is also registered (`Zlib.Gzlib.Proofs.gzdopen_complete`). |
| `gzbuffer`, `gzeof`, `gzerror`, `gzclearerr`, `gztell`, `gztell64`, `gzoffset`, `gzoffset64`, `gzrewind`, `gzseek`, `gzseek64` | Call clause | The functional goals of `gzbuffer`, `gzeof`, `gzerror`, `gzclearerr`, `gzoffset`, `gzoffset64` and `gzrewind` are also registered. |
| `gzwrite`, `gzfwrite`, `gzputc`, `gzputs`, `gzprintf`, `gzflush`, `gzsetparams` | Call clause | `gzprintf` needs a representable format on every call, also on a reader. The undocumented `gzvprintf` is a call of the goal as well. |
| `gzread`, `gzfread`, `gzgetc`, `gzgetc_`, `gzungetc`, `gzgets` | Call clause; termination under `ReadsFinite` | No fault in every world; a normal return when the read budget is below `2^61` |
| `gzdirect` | Call clause | Terminates in every world |
| `gzclose`, `gzclose_r`, `gzclose_w` | Close clause | A close of the wrong mode refuses and changes nothing; otherwise every owned block is freed and the descriptor released |
| The `gzgetc()` macro of `zlib.h` | Macro clause, and the history step `GzHistory.getcMacro` | With buffered output it is the inline path; with `x.have = 0` it calls the function, covered under `ReadsFinite`. The macro on a `NULL` handle is undefined behaviour in C and is not covered. |
| A second handle on the same descriptor | World step `GzHistory.world` | Any well-formed world may follow a call, so another party may close or reuse the descriptor ([regression](../tests/verification/regressions/gz-world-closes-fd.lean)). |

## Domains narrower than `zlib.h`

Each has a row in [deviations](deviations.md).

- `inflateBack`: `inputBound < 2^48`; the window and every input chunk in a heap byte block;
  `state == NULL` before `inflateBackInit_`.
- `inflateCopy` and `deflateCopy`: `source ≠ dest`.
- `adler32` and `adler32_z`: a `NULL` `buf` only with `len = 0`.
- `inflate`, `deflate`, `deflateParams`, `compress*`, `uncompress*`: caller regions that do not
  overlap.
- `compress*`, `inflateGetDictionary`, `deflateGetDictionary`, `deflatePending`, `deflateUsed`:
  the result cell is a value in the model, so the goal says nothing about its memory.
- The gz reading calls: termination under a read budget.
- Every stream: the default allocator.

The record of how the gz coverage was reviewed and corrected is in
[coverage: review record](history/coverage-review-record.md), and the earlier list of open items
in [coverage: earlier open items](history/coverage-open-items.md).
