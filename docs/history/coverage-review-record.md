# Coverage: review record

This page is history. It keeps, unchanged, the section "No-fault coverage of zlib.h functions"
that `docs/progress.md` held until the table moved to [coverage by function](../coverage.md).
The rows were last compared with `dev` at `6a097d3b`, 2026-11-14. Its states and levels describe
that time: for example it writes "(checked)" for refusal goals that are registered, and it names
the functional theorem of `inflate` in the column of the safety theorem. The current table
corrects both.

The labels in the text name review passes and work batches of that time: "audit A1", "A2", "B1"
and "B3" are findings of an adversarial reading of the gz safety goal on 2026-11-14, and
"batch C" is the batch of work that proved the `gzgetc`, `gzungetc`, `gzgets` and `gzdirect`
steps.


One row for each function that zlib.h documents. Each row names the checked theorem that shows the
call does not fault, and the route: its own goal, a sequence goal (the call is a `StreamOperation`),
the End clause of `StreamSequenceSafety`, or open. The rows were last checked against `dev` at
`6a097d3b`, 2026-11-14. "Registered" means listed in `tests/audit/theorems.txt`. The acceptance
suite is green on the later commit `bde170e9` (see [Scope](../progress.md#scope)). Re-check a row when its
theorem or goal changes.

Model-wide premises that every stream or utility route shares, which are not repeated per row:
the default allocator (`DefaultOrNull`/`DefAlloc`/`zfree = zcfree`; a declared target
restriction), heap well-formedness (`Fresh`, `Uniq`, `LibraryGlobals`), and, for inflate, the
utilities and inflateBack, `ByteObjectsFit` (the platform row in `docs/deviations.md`).

Abbreviations:
- **SeqI** = `Goal.inflate_sequence_safety`: `Zlib.Inflate.Proofs.inflate_sequence_safety_public`
  (`public-inflate-sequence-safety.lean`, registered).
- **SeqD** = `Goal.deflate_sequence_safety`: `Zlib.Deflate.Universal.deflate_sequence_safety`
  (`public-deflate-goals.lean`, registered).
- Both cover only `p = some r` with `StreamReachable r` (and `StreamArguments`). Neither covers a
  NULL stream or an inconsistent stream (zalloc/zfree NULL, state NULL, or a state the check
  refuses). zlib.h documents those as `Z_STREAM_ERROR` refusals, and `docs/spec/safety.md` A1
  keeps documented null refusals in scope. The column "refusal" says whether any theorem
  covers that case.

## Stream: deflate

| function | route | theorem (Lean name, file) | registered? | domain gap or note |
| --- | --- | --- | --- | --- |
| deflateInit_ (macro deflateInit) | own goal | `ZlibF.Spec.Public.Proofs.DeflateInit.deflateInit_proof`, `public-deflate-init.lean` | yes | Full: bad version (`VersionValue`, NULL or a readable first byte), wrong `stream_size` (any `p`), NULL strm, every level, allocation failures. |
| deflateInit2_ (macro deflateInit2) | own goal | `ZlibF.Spec.Public.Proofs.DeflateInit2.deflateInit2_proof`, `public-deflate-init2.lean` | yes | Full, as for deflateInit_, plus every method/windowBits/memLevel/strategy. `Goal.deflate_initialisation_domain` (nonvacuity) is registered (`DeflateInitDomain.deflate_initialisation_domain_public`). |
| deflate | own goal + SeqD | `Zlib.Deflate.Universal.deflate_safety`, `public-deflate-goals.lean` | yes | Reachable + `DGood` + `StreamBuffers` + `ActiveHeader` (separation rows). Refusal: `Goal.deflate_refusal` (checked) covers NULL and inconsistent streams. |
| deflateEnd | own goal + End clause of SeqD | `ZlibF.Spec.Public.DeflateEndProof.deflate_end_public`, `public-deflate-end.lean`; clause 3 of SeqD | yes | Own goal needs `DGood`. Refusal: `Zlib.Deflate.Proofs.deflateEnd_reject` (`deflate.c.life.end.lean`, registered) covers NULL, zalloc/zfree NULL, state NULL and a refused live state. So it is covered: never initialised (model pointers are NULL), NULL, state NULL, and after a failed copy. It is not a goal-typed theorem. |
| deflateSetDictionary | safety goal + SeqD | `Goal.deflateSetDictionary_safety` (registered); SeqD | yes | Own functional `Goal.deflateSetDictionary` (not planned): no theorem. Refusal: `Goal.deflate_refusal` (checked) covers NULL and inconsistent streams. |
| deflateGetDictionary | own goal + SeqD | `ZlibF.Spec.Public.DeflateDictionaryProof.deflate_getdict_public`, `public-deflate-getdict.lean` | yes | Own goal needs `DGood` and a destination separate from the window. Refusal: `Zlib.Deflate.Proofs.deflateGetDictionary_reject` (`deflate.c.life.getdict.lean`) is registered. |
| deflateCopy | own goal | `Zlib.Deflate.Universal.deflate_copy_public` / `deflate_copy_safety`, `public-deflate-copy.lean` | yes | Not a `StreamOperation`; `StreamReachable.deflateCopy` only feeds clause 1 of SeqD. Gap: `source ≠ dest` (deviation row). An inconsistent source is covered by `Goal.deflate_refusal` (checked). |
| deflateReset | own goal + SeqD | `ZlibF.Spec.Public.DeflateResetProof.deflate_reset_public`, `public-deflate-reset.lean` | yes | Refusal: `Zlib.Deflate.Proofs.deflateReset_reject` (registered). |
| deflateParams | safety goal + SeqD | `Goal.deflateParams_safety` (registered); SeqD | yes | Own functional `Goal.deflateParams` (not planned): no theorem. Refusal: `Goal.deflate_refusal` (checked) covers NULL and inconsistent streams. |
| deflateTune | own goal + SeqD | `ZlibF.Spec.Public.DeflateQueryProof.tune_public`, `public-deflate-small-queries.lean` | yes | Full (`CheckedDeflate` includes the refusals). |
| deflateBound | safety goal + SeqD | `Goal.deflateBound_safety` (registered); SeqD | yes | Own functional `Goal.deflateBound` (not planned): no theorem. SeqD needs `ActiveHeader ∧ DeflateHeaderLive`. Refusal: `deflateBound_nostate` (registered). |
| deflateBound_z | safety goal + SeqD | `Goal.deflateBound_z_safety` (registered); SeqD | yes | Same as deflateBound (`deflateBound_z_nostate`, registered). |
| deflatePending | own goal + SeqD | `ZlibF.Spec.Public.DeflateQueryProof.pending_public` | yes | Full. |
| deflateUsed | own goal + SeqD | `ZlibF.Spec.Public.DeflateQueryProof.used_public` | yes | Full. |
| deflatePrime | safety goal + SeqD | `Goal.deflatePrime_safety` (registered); SeqD | yes | Own functional `Goal.deflatePrime` (not planned): no theorem. SeqD needs `DeflateNotStarted`, which is zlib.h's own ordering rule. Refusal: `deflatePrime_refused` (registered). |
| deflateSetHeader | own goal + SeqD | `ZlibF.Spec.Public.DeflateQueryProof.header_public` | yes | Full. SeqD needs `DeflateNotStarted` (zlib.h order). |

## Stream: inflate

| function | route | theorem (Lean name, file) | registered? | domain gap or note |
| --- | --- | --- | --- | --- |
| inflateInit_ (macro inflateInit) | own goal | `ZlibF.Spec.Public.Proofs.InflateInit.init15_public`, `public-inflate-init.lean` | yes | Full: bad version or size, NULL strm, allocation failure. |
| inflateInit2_ (macro inflateInit2) | own goal | `ZlibF.Spec.Public.Proofs.InflateInit.inflate_init2_public`, `public-inflate-init2.lean` | yes | Full, every `windowBits`. |
| inflate | own goal + SeqI | `Zlib.Inflate.Proofs.inflate_public`, `public-inflate.lean` | yes | Reachable + `Good` + `ByteObjectsFit` + `StreamBuffers` + `ActiveHeader`. Refusal: `Goal.inflate_refusal` (checked) covers NULL and inconsistent streams. |
| inflateEnd | own goal + End clause of SeqI | `ZlibF.Spec.Public.InflateEndProof.inflate_end_public`, `public-inflate-end.lean`; clause 3 of SeqI | yes | Own goal needs `Good`. Refusal: `Goal.inflate_refusal` (checked) covers NULL and inconsistent streams. |
| inflateSetDictionary | own goal + SeqI | `ZlibF.Spec.Public.Proofs.inflateSetDictionary_public`, `public-inflate-setdict.lean` | yes | Own goal needs `Good`, `zalloc = zcalloc`, and a dictionary separate from the window (deviation row). Refusal: `Goal.inflate_refusal` (checked) covers NULL and inconsistent streams. |
| inflateGetDictionary | own goal + SeqI | `ZlibF.Spec.Public.InflateDictionaryProof.inflate_getdict_public` | yes | Own goal needs `Good` and a destination separate from the window. Refusal: `Goal.inflate_refusal` (checked) covers NULL and inconsistent streams. |
| inflateSync | safety goal + SeqI | `Goal.inflateSync_safety` (registered); SeqI | yes | Own functional `Goal.inflateSync` (not planned): no theorem. Refusal: `inflateSync_check` (registered). |
| inflateCopy | own goal | `Zlib.Inflate.Proofs.inflate_copy_public`, `public-inflate-copy.lean` | yes | Not a `StreamOperation`. Gap: `source ≠ dest` (deviation row). An inconsistent source is covered by `Goal.inflate_refusal` (checked). |
| inflateReset | own goal + SeqI | `ZlibF.Spec.Public.InflateResetProof.reset_public` | yes | Own goal needs `InflateView`. Refusal: `Goal.inflate_refusal` (checked) covers NULL and inconsistent streams. |
| inflateReset2 | own goal + SeqI | `ZlibF.Spec.Public.InflateReset2Proof.reset2_public` | yes | Every `windowBits`. Refusal: `Goal.inflate_refusal` (checked) covers NULL and inconsistent streams. |
| inflatePrime | own goal + SeqI | `ZlibF.Spec.Public.InflatePrimeProof.prime_public` | yes | Full (`CheckedInflate`). The accepted branch needs `s.bits ≤ 39`, a fact of the invariant. |
| inflateMark | own goal + SeqI | `ZlibF.Spec.Public.InflateMarkProof.mark_public` | yes | Full. |
| inflateGetHeader | own goal + SeqI | `ZlibF.Spec.Public.InflateHeaderProof.getheader_public` | yes | Full on `InflateView`. A gzip-capable stream needs `head ≠ NULL`: C dereferences it, and zlib.h does not offer NULL. SeqI also needs `p ≠ none`. Refusal: `inflateGetHeader_check` (registered). |

## Callback decoder

The three functions have no safety goal of their own yet: the sequence goal carries their safety
([Ordered next work](../progress.md#ordered-next-work)).

| function | route | theorem (Lean name, file) | registered? | domain gap or note |
| --- | --- | --- | --- | --- |
| inflateBackInit_ (macro inflateBackInit) | own goal | `ZlibF.Spec.Public.InflateBackInitProof.back_init_public`, `public-infback-init.lean` | yes | Full: bad version or size, NULL strm, NULL window, bad `windowBits`, allocation failure. The success branch needs a writable window of `2^wb` bytes (zlib.h's own rule). |
| inflateBack | sequence (`Goal.inflate_back_sequence_safety`) | `Zlib.Infback.Safety.inflate_back_sequence_safety`, `infback.c.safety-fast.lean` (checked, c7169b54) | yes | Registered, with eleven structural proof mutants of `inflateBack`, `inflateBackInit_` and `inflateBackEnd` (`tests/proof-mutants/infback-sequence.tsv`), each killed and rejected by the kernel replay of the goal theorem. Own `Goal.inflateBack` (functional) is not planned. NULL strm and state NULL are covered (`inflateBack_nullstream`, `inflateBack_nostate`, registered). The goal also narrows: `inputBound < 2^48`, the window is a slice of a heap byte block, every input chunk lies in a heap byte block (deviation rows). |
| inflateBackEnd | own goal | `ZlibF.Spec.Public.InflateBackEndProof.back_end_public`, `public-infback-end.lean` | yes | Full: NULL, state NULL or zfree NULL, and `BackValid`. Clause 4 of the inflateBack sequence goal is proved in `inflate_back_sequence_safety` (`back_end_blk`). |

## Checksums

| function | route | theorem | registered? | domain gap or note |
| --- | --- | --- | --- | --- |
| adler32 | own goal | `ZlibF.Spec.Public.AdlerUpdateProof.adler_public`, `public-adler-update.lean` | yes | **Narrower**: NULL `buf` only with `len = 0` (`AdlerBufferBytes`, deviation row). With `len = 1`, C reads `buf[0]`, a real fault (upstream PR #1364 was closed and a zlib.h restriction was announced). NULL with `len ≥ 2` is safe in C but unproved. |
| adler32_z | own goal | `...AdlerUpdateProof.adler_z_public` | yes | Same as adler32. |
| adler32_combine / _combine64 | own goal | `...AdlerCombineProof.combine_public` / `combine64_public` | yes | Full. |
| crc32 / crc32_z | own goal | `ZlibF.Spec.Public.Proofs.crc32` / `crc32_z`, `public-crc-updates.lean` | yes | Full (`BufferBytes` includes NULL with any length). `CrcGlobals` is a premise of the model's static data. |
| crc32_combine / _combine64 | own goal | `...CrcCombineProof.combine` / `combine64` | yes | Full. |
| crc32_combine_gen / _gen64 | own goal | `...CrcCombineProof.gen` / `gen64` | yes | Full. |
| crc32_combine_op | own goal | `...CrcCombineProof.op` | yes | `op` must come from `crc32_combine_gen` (matches zlib.h). |
| get_crc_table | own goal | `ZlibF.Spec.Public.Proofs.get_crc_table` | yes | Undocumented in zlib.h (not required). |

## Utilities

| function | route | theorem | registered? | domain gap or note |
| --- | --- | --- | --- | --- |
| compress / compress_z / compress2 / compress2_z | safety goals `Goal.compress*_safety` | `ZlibF.Spec.Public.Proofs.Compress.compress_safety`, `compress_z_safety`, `compress2_safety`, `compress2_z_safety`, `public-compress-safe-mid.lean` | yes | Source separate from dest (deviation row). The length cell is modelled as an `Option` scalar, so aliasing the cell with data is outside the model (deviation row). Every level. The functional `Goal.compress*` (not planned) have no theorem. |
| uncompress / uncompress_z / uncompress2 / uncompress2_z | safety goals `Goal.uncompress*_safe` | `ZlibF.Spec.Public.Proofs.Uncompress.uncompress_safe` etc., `public-uncompress-safe.lean` | yes | `UtilitySeparation`: data and length cells pairwise separate (deviation row). The functional `Goal.uncompress*` (not planned) have no theorem. |
| compressBound / compressBound_z | own goal | `ZlibF.Spec.Public.Proofs.compressBound` / `compressBound_z` | yes | Full. |
| zlibVersion | own goal | `ZlibF.Spec.Public.Proofs.zlibVersion` | yes | Full. |
| zlibCompileFlags | own goal | `ZlibF.Spec.Public.Proofs.zlibCompileFlags` | yes | Full. |
| zError | own goal | `ZlibF.Spec.Public.Proofs.zError` | yes | Undocumented (not required). |

## Gzip file interface

The gz functions have no safety goal of their own yet: the sequence goal carries their safety
([Ordered next work](../progress.md#ordered-next-work)).

`Goal.gz_sequence_safety` (`ZlibF/Spec/Public/GzSafety.lean`) is the safety goal of the gzip interface. It is
registered in `goals.txt` and in `safety_goals`, checked with no premise (`gz_sequence_safety_public`,
`public-gz-sequence-safety.lean`) and registered in `theorems.txt`, with proof mutants of every gz function group and of
each hunk of patches 0002 to 0005 (`gz-sequence.tsv`, `gz-read.tsv`, `docs/checking/proof-mutants.md`). Its non-vacuity
goal `Goal.gz_sequence_nonvacuity` (`gz_sequence_nonvacuity_public`) is registered too. `gz_sequence_safety_of (L : GzReadLeaves)`
(`gz.sequence-safety.lean`) proves it from six read leaves, all proved. Every other call is proved directly: the open calls,
the close calls, the write calls and the queries. `gzread_step` and `gzfread_step` close with the read side's
`gz.read-assembly`. `gzgetc_step`, `gzungetc_step`, `gzgets_step` and `gzdirect_step` are batch C's. The goal's
domain is every history of one handle (`GzHistory`) in every OS world (`GzWorldStep`). An adversarial reading
(2026-11-14) found no false clause and three gaps: the `gzgetc` macro's inline path, `NULL`
handles, and an unlisted fd rule (rows below). All three are closed: the macro step is in the goal (A1), `NULL`
handles have `Goal.gz_refusal` (A2), and the fd rule is removed from the goal (B1).

| function | route | theorem | registered? | domain gap or note |
| --- | --- | --- | --- | --- |
| gzopen, gzopen64 | open leaf | `gzopen_safe` (`gz.inv-open-fresh`), `gzopen64_safe` | through `gz_sequence_safety_public` | Every path, mode and world. |
| gzdopen | open leaf + own goal | `gzdopen_safe` (`gz.inv-open`); `gzdopen_complete` (`Goal.gzdopen`) | yes (own goal) | Every `fd`. |
| gzbuffer, gzeof, gzerror, gzclearerr, gztell, gztell64, gzoffset, gzoffset64, gzrewind, gzseek, gzseek64 | sequence leaf | `gzbuffer_step`, `gzeof_step`, `gzerror_step`, `gzclearerr_step`, `gztell*_step`, `gzoffset*_step`, `gzrewind_step`, `gzseek*_step` (`gz.inv-*`) | through `gz_sequence_safety_public` | Own functional goals of gzbuffer, gzeof, gzerror, gzclearerr, gzoffset and gzrewind are registered separately. |
| gzwrite, gzfwrite, gzputc, gzputs, gzprintf, gzvprintf, gzflush, gzsetparams | sequence leaf | `gzwrite.c.safety` (`gzwrite_step` …) | through `gz_sequence_safety_public` | `gzprintf`/`gzvprintf`: `GzArguments` asks for a representable format on every call, even on a reader (audit B3). |
| gzclose, gzclose_w, gzclose_r | close leaf | `gzclose_step`, `gzclose_w_step`, `gzclose_r_step_safe` | through `gz_sequence_safety_public` | |
| gzread, gzfread | read leaf | `GzRead.gzread_step`, `GzRead.gzfread_step` (`gz.read-assembly`) | through `gz_sequence_safety_public` | |
| gzgetc, gzgetc_, gzungetc, gzgets, gzdirect | read leaf | `GzRead.gzgetc_step`, `GzRead.gzungetc_step` (`gz.read-getc-step`), `GzRead.gzgets_step`, `GzRead.gzdirect_step` | through `gz_sequence_safety_public` | |
| the `gzgetc()` macro of zlib.h | history step + goal conjunct | `GzMacro.gzgetc_macro_safe` (`zlib.h.gzgetc-macro`) | through `gz_sequence_safety_public` | Closed (audit A1; corrected in 3c5292f7 after the proof mutant `macro-have-guard-dropped` survived): every macro call is `GzHistory.getcMacro`; with buffered output it is the inline path, and with `x.have = 0` the call of the function, covered through `gzgetc_step` under `ReadsFinite`. Differential test: op `getcm` of `tests/gen/gz.py` (also at `x.have = 0`: right after an open, on a writer, on an empty file). |
| all gz functions on a `NULL` handle | own safety goal | `ZlibF.Spec.Public.GzRefusalProof.gz_refusal` (`Goal.gz_refusal`, `public-gz-refusal.lean`) | yes, with proof mutants (`gz-refusal.tsv`) | Closed (audit A2): each of the 29 functions returns its documented value with the heap and the world unchanged. C test `tests/goals/gz-refusal`: 204 calls, no violation. The `gzgetc` macro on `NULL` is undefined behaviour in C; the goal states the function. |
| a second handle on the same fd | world step | `GzHistory.world` | no | Covered (audit B1, corrected): `GzWorldStep` is any well-formed world, so another party may close or reuse the handle's fd ([regression](../../tests/verification/regressions/gz-world-closes-fd.lean)). |

## Miscounts and open items

Every function that zlib.h documents has a registered no-fault theorem on the domain its row
states. What is open or narrower:

1. **Per-function safety goals** for the gz functions and for `inflateBackInit_`, `inflateBack`
   and `inflateBackEnd` are not stated yet. `Goal.gz_sequence_safety` and
   `Goal.inflate_back_sequence_safety` carry their safety.
2. **Domains narrower than zlib.h**, each with a row in [deviations](../deviations.md):
   `inflateBack` (`inputBound < 2^48`; the window and every input chunk in a heap byte block);
   `inflateCopy` and `deflateCopy` (`source ≠ dest`); `adler32` and `adler32_z` (a NULL `buf`
   only with `len = 0`: `len = 1` is a real C fault, and NULL with `len ≥ 2` is safe in C but
   unproved).
3. **Functional own goals** of `deflateParams`, `deflateSetDictionary`, `deflatePrime`,
   `deflateBound`, `deflateBound_z` and `inflateSync` have no theorem and are not planned.
   Their safety goals are registered.

The earlier numbered list, with the items since closed, is in
[coverage: earlier open items](coverage-open-items.md).

