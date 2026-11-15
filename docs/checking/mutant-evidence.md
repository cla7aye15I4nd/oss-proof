# Mutant evidence record

> **Dated record.** Written from 2026-11-12 to 2026-11-14, at the runs that registered the goals
> named here. It says which mutant rows carried the evidence of each group of goals and where
> they were killed. The times, memory peaks and counts are those of these runs. The authority
> on which rows a goal needs is the lists and `tests/audit/public-mutants.json`; the terms and
> the rules are in [proof mutants](proof-mutants.md). The acceptance suite runs the lists named
> here; it is green on commit `bde170e9`.

The record has one section per group of goals. "Structural", "restatement", "script row", "key"
and "semantic list" are defined in [proof mutants, Terms](proof-mutants.md#terms).

## `Goal.deflate`

The keyed rows of `Goal.deflate` (`tests/proof-mutants/public-deflate.tsv`) are one-file edits of
the body of `deflate`. Each is rejected first at `deflate_phases`, the `rfl` equation that splits
`deflate` into its phases; any edit of the body fails there. So these rows show that the
registered proof is tied to the translation, not that it depends on the mutated check. They are
acceptable for the exact replay only because the semantic kills are covered by the script-row
lists that every mutant shard runs: `deflate-header.tsv` (header stages and `_tr_flush_block`),
`deflate-strategies.tsv` (`fill_window`, `longest_match` and the strategies) and `deflate-ops.tsv`
(the stream operations). Each script row makes the edit in the translation and in every proof
restatement of it, and is killed in its semantic lemma.

## `Goal.deflateCopy` and the refusal goals

The five rows of `Goal.deflateCopy` in `tests/proof-mutants/public-streams.tsv` are all structural:
- a null destination returns `Z_OK`;
- the state-allocation failure returns `Z_OK`;
- the buffer-failure path keeps `dest->state`;
- the buffer-failure path skips the free of `pending_buf`;
- the copy's back pointer is set to the source.

Each is rejected by the replay; the replay of `deflate_copy_public`
(`ZlibF/Proof/public-deflate-copy.lean`) peaks at about 10.4 GB. The
refusal goals `Goal.inflate_refusal` and `Goal.deflate_refusal` have no key. Their rows are in
`tests/proof-mutants/stream-refusal.tsv`, which the mutation shards check by re-elaboration: each
row turns a refusal into `Z_OK`.

## Per-function safety goals

For most functions the rows of the safety goal are the rows of the functional goal: the safety
proofs of the stream calls are corollaries of the sequence theorems
(`inflate_sequence_safety_public`, `deflate_sequence_safety`, clause 2 for a call and clause 3 for
`End`), and those of the init, copy and stateless functions are corollaries of their functional
proofs, so the same translation edits break them. Functions without such rows have rows in
`tests/proof-mutants/public-safety.tsv`, all structural:
- `compress`, `compress_z`, `compress2`: the length pointer is not passed on (`NULL` instead). The
  row of `api-boundary.tsv` that makes `compress2` return on a `NULL` `destLen` is not a mutant of
  `Goal.compress2_safety`: the C reads `*destLen` first, so the goal excludes a `NULL` length
  (`CompressorSafety` with `nullableLength = false`), and the replay accepts that row;
- `uncompress2`: the destination length is read from `sourceLen`; the free of a local cell is dropped;
- `uncompress_z`, `uncompress`: the source-length cell is passed as the destination length; the free
  of the local cell is dropped;
- `deflateBound`: the result is dropped; `deflateBound_z`: the state check is dropped;
- `deflatePrime`: the `bits > 16` test is dropped; the pending room test is dropped;
- `inflateSync`: the local buffer has three bytes, not four.

`deflateParams` and `deflateSetDictionary` use their refusal rows of `stream-refusal.tsv`. A dropped
`deflateEnd` or `inflateEnd` call is a row of `compress2_z` and `uncompress2_z`, the functions that
make the call. `Goal.deflate_initialisation_domain` has no key: it states the successful
runs of `deflateInit2_`, and the four `deflateInit2_` rows are its mutants: a kernel replay of
`deflate_initialisation_domain_public` rejects all four (peak about 3.4 GB).

## `Goal.inflate_back_sequence_safety`

Its eleven rows are in `tests/proof-mutants/infback-sequence.tsv`: four of `inflateBack`, four of
`inflateBackInit_` and three of `inflateBackEnd`, all structural:
- `inflateBack`: a null stream returns `Z_OK`; the mode is not reset to `TYPE`; the output starts at
  `NULL`, not the window; a refused last window after the end returns `Z_OK`;
- `inflateBackInit_`: the state is not stored in the stream; the window is not stored; an allocation
  failure returns `Z_OK`; `sane` is cleared;
- `inflateBackEnd`: the free of the state is skipped; `strm->state` is kept; it returns `Z_STREAM_ERROR`.

The row of the epilogue is a script (`infback-sequence.py`) that makes the same edit in the restatement
`backTail`, so that a semantic lemma fails and not the `rfl` of `inflateBack_eq`. The mutation shards
check the rows by re-elaboration. A kernel replay of `inflate_back_sequence_safety` with the
translation edit of each row also rejects all eleven; the replay of the original peaks at about 9.8 GB.

## The gz goals

The gz goals have no key; their rows are three semantic lists.
- `tests/proof-mutants/gz-refusal.tsv`, for `Goal.gz_refusal`: nineteen rows, each a different return value on a
  `NULL` handle or a dropped `NULL` test, of every gz function except `gzread` and `gzfread` (in `gz-read.tsv`) and
  `gzbuffer`, `gzeof` and `gzoffset64` (in `public-streams.tsv`). The goal's clauses hold by evaluation, so each row
  fails in `public-gz-refusal`.
- `tests/proof-mutants/gz-sequence.tsv`, for `Goal.gz_sequence_safety`: the write calls (`gzwrite`, `gzfwrite`,
  `gzputc`, `gzputs`, `gzvprintf` and so `gzprintf`, `gzflush`, `gzsetparams`), the closes (`gzclose_w`, `gzclose_r`,
  the dispatch of `gzclose`), the opens (`gz_open`, `gzdopen`), `gzseek64` and `gztell64`, `gz_error` (a skipped free;
  a message allocated for `Z_MEM_ERROR`), both branches of the `gzgetc()` macro (`zlib.h.lean`: the `have` test dropped;
  `pos` not advanced), the read leaves `gzgetc`, `gzungetc`, `gzgets` and `gzdirect`, and one row per hunk of
  patches 0002 to 0005 that removes the hunk (the unpatched C). Most rows are script rows (`gz-sequence.py`) that make
  the same edit in each `rfl` restatement of the code (`gzwrite_eq`, `putcSlow`, `closeTail`, `pfFmt`, `gTail`,
  `seekTail`, `openAfterMode`, `fetchBody`, `restK`, `getsRest`, the private copies of `gz_error`), so that a semantic
  lemma fails, not the restatement.
- `tests/proof-mutants/gz-read.tsv` (with `gz-read.py`), from the read side: `gzread` and `gzfread`, the refusal
  cases of `gzgetc` and `gzungetc`, and `gzclose_r`. Its two `gzungetc` rows `gzungetc-mode-check` and
  `gzungetc-skip-dropped` name the step lemma's module `gz.read-getc-step` as well: with `gzread.c.getc-ungetc`
  alone the proof of `gzungetc_step` is not built, and both rows built; with it both are killed there.

**Where the first error lands.** Each row is killed in a proof of the mutated function: its step lemma, the exact run
of its body, or (for a callee) the proof of that callee. Five rows name modules beyond the step lemma, all proofs of
the mutated function:
- the three `gz_open` rows fail in the exact runs of `gz_open` (`gz_open_empty_mode` in `gzlib.c.open-init`,
  `openAfterPath_writer` in `gzlib.c.open-io`: the I/O tail of `gz_open`, which frees the path and calls `gz_reset`);
- the `gzdopen` row fails in the run of `gzdopen` (`gzdopen_writer_regular_run`, `gzlib.c.dopen-entry`);
- the `gztell64` row fails in the run of `gztell64` (`gztell64_run`, `gzlib.c.simple`).

The `gzclose_w` rows fail in `closeTail_ok` (`gzwrite.c.close`), the release proof of `gzclose_w`; the dispatch row
of `gzclose` in `gzclose_dispatch`. One row is killed by a heartbeat timeout, not a type error:
`patch0004-fetch-copy-room-removed` in `fetch_look` (`gz.read-fetch`), a proof of the same function `gz_fetch`.

**A row that found a wrong goal.** The row `macro-have-guard-dropped` survived at first: the goal ran the macro only
with `x.have ≠ 0`, so its `have = 0` branch was never run. The goal was corrected (3c5292f7; regression
`tests/verification/regressions/gz-macro-have-zero.lean`) and the row is killed in `zlib.h.gzgetc-macro`.

**Kernel replay of the gz lists.** The mutation shards check the three lists by re-elaboration. A kernel replay of
`gz_refusal` rejects all nineteen refusal rows (each replay ends within two seconds). A second kernel replay took
`gz_sequence_safety_public` with the translation edit of each structural row. The rows in a loop body or in machine
arithmetic were left out: `patch0003-*`, the three `patch0004` rows of `gz_fetch` and `gz_read`,
`patch0004-gets-room-removed`, `gzgets-left-whole-length` and `gztell64-adds-max`. The replay accepts the original
(51615 dependencies, peak about 10.7 GB). It rejects 29 of the 36 rows it was given, most at the restatement of the
mutated function (`gzwrite_eq`, `gzclose_w_eq`, `gzgetc_macro_eq`, ...), with peaks of 10.7 GB. Seven rows reach the
12 GiB budget before a verdict: `gzvprintf-length-check-dropped`, `gz_open-open-failure-path-leak`,
`gz_open-reset-skipped`, `gzseek64-have-not-consumed`, `gzseek64-skip-wrong`, `patch0005-seek-next-unconditional` and
`patch0004-printf-position-check-removed`. Their functions (`gzvprintf`, `gz_open`, `gzseek64`) contain a loop, and
the kernel unfolds it when the bodies differ; for these rows the re-elaboration kill is the evidence.
