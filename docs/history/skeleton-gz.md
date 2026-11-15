# Gzip file interface proof skeleton (historical)

This page keeps the gz part of the section "Core proof skeletons" of [progress](../progress.md), as it stood
after the required goals were accepted on `bde170e9`. The text is unchanged apart from relative links. It is a historical
record: states such as "open" and "checked", hours, counts and dates describe the time each
entry was written. They are not current status. Current status and remaining work are only in
[progress](../progress.md).

#### gz

Safety of the gzip file interface (result 5, owner's decision of 2026-11-12): no undefined
behaviour, no memory error, no leak of a block or of the descriptor, and termination, on every
history of a handle. The goal `Goal.gz_sequence_safety` and its definitions (`GzHistory`,
`GzCloseSafe`, `GzOpenSafe`, `GzDopenSafe`) are on `dev` in `ZlibF/Spec/Public/GzSafety.lean`
(`61fc2678`), over `GzInv` and `GzCallSafe` of `gz.inv-model`. The assembly is on `dev`:
`gz_sequence_safety_of` (`gz.sequence-safety`) has the conclusion `Goal.gz_sequence_safety`
and one premise, `GzReadLeaves`: the six read leaves `gzread_step`, `gzfread_step`, `gzgetc_step`,
`gzungetc_step`, `gzgets_step`, `gzdirect_step`, each with the skeleton's exact statement. All six are
checked on `dev` with no premise, so `Goal.gz_sequence_safety` is checked: `gz_sequence_safety_public`
(`public-gz-sequence-safety`). It is registered in `tests/audit/theorems.txt`, with proof mutants (`gz-sequence.tsv`,
`gz-read.tsv`); `Goal.gz_sequence_nonvacuity` (`gz_sequence_nonvacuity_public`) and `Goal.gz_refusal` (`gz_refusal`) are
registered with it.
Audit A1 added the inline path of the `gzgetc()` macro of `zlib.h` to `GzHistory` (`getcMacro`) and to the
goal (one conjunct); `GzMacro.gzgetc_macro_safe` proves it. Goal correction (3c5292f7): the step and the conjunct
covered only `x.have ≠ 0`, so the macro's `have = 0` branch was never run by the goal (the proof mutant
`macro-have-guard-dropped` survived). Both now cover every macro call; with `x.have = 0` the macro is the call of
`gzgetc`, which returns under `ReadsFinite` (regression `tests/verification/regressions/gz-macro-have-zero.lean`). Every other
leaf is used from `dev` directly; no loop rule is used. The skeleton is on the branch `skeleton/gz`,
commit `17770416`, after a merge of `dev`: files `gz.skeleton-model.lean` (the two loop rules only),
`gz.skeleton-read.lean` (the open read leaves) and `gz.skeleton.lean` (`gz_sequence_safety_of` applied to
the read leaves). It type-checks: `Goal.gz_sequence_safety` is proved there from the open lemmas below. A skeleton leaf that `dev` proves with exactly its
statement is deleted from the skeleton (or closed by the `dev` theorem) and listed as checked.
The goal ranges over every open (`gzopen`, `gzopen64`, `gzdopen`), every public call of
`GzOperation`, every close, caller edits outside the handle and changes of the file-system world
between calls, for every value of the OS-call oracle.

A read leaf is open while `dev`'s theorem differs from the skeleton statement. The column
"Difference" names what differs, so that the read side can align the statement (a correction of
the skeleton statement, with evidence) or add an adapter lemma.

Statement corrections of `GzInv` against the skeleton text. Both make a clause weaker, because the
skeleton's clause was false; each has a checked regression. The no-fault and frame clauses of the goal
are unchanged.
- `GzCommon.next` constrains `x.next` only while output is buffered (`x.have ≠ 0`) (`7c32d275`;
  regression `tests/verification/regressions/gz-next-caller.c`, with patch 0005).
- `GzReadInv.copyDirect` allows `direct = 0 ∨ direct = 1` under `how = COPY` (`a351cd66`; regression
  `tests/verification/regressions/gz-copy-direct.c`).

| Lemma | Meaning | State | Hours | Owner |
| --- | --- | --- | ---: | --- |
| `GzInv.caller`, `GzInv.gz_error`, `GzInv.gz_reset`, `GzInv.put_scalars` | Interface lemmas of `GzInv`. | checked: `gz.inv-frame`, `gzlib.c.error-inv-premises`, `gz.inv-reset`, `gz.inv-put-scalars` | 0 | batch 1, deflate owner |
| `gwhile_partial`, `gdoWhile_partial` | Partial-correctness loop rules (`gz.skeleton-model`); no proof uses them yet. | open | 2 | unassigned |
| `gzopen_safe` | `gzopen` returns; NULL leaves nothing; a handle is in `GzInv` with only its descriptor new. | checked: `gzopen_safe` (`gz.inv-open-fresh`, `5252a412`) | 0 | batch C |
| `gzopen64_safe` | `gzopen64` is `gzopen`. | checked: `gzopen64_safe` (`gz.inv-open-fresh`, `5252a412`) | 0 | batch C |
| `gzdopen_safe` | As `gzopen_safe`, with no descriptor opened or closed. | checked: `gzdopen_safe` (`gz.inv-open`, `8c2bba51`) | 0 | batch C |
| `gzclose_dispatch_inv` | `gzclose` is `gzclose_r` or `gzclose_w` by mode. | checked: `gzclose_dispatch_inv` (`gz.inv-queries`) | 0 | batch 1 |
| `gzclose_step` | `gzclose` from the dispatch and the two close steps. | checked: `gzclose_step` (`gz.inv-close`, `fdb8c613`) | 0 | batch C |
| `gzseek64_step`, `gzseek_step` | Seek is safe on `GzInv`. | checked: `gzseek64_step`, `gzseek_step` (`gz.inv-seek`) | 0 | batch 1 |
| `gztell64_step`, `gztell_step`, `gzeof_step`, `gzbuffer_step` | Tell, eof and buffer; with `post_unchanged`, `safe_of_unchanged`. | checked: same names (`gz.inv-queries`) | 0 | batch 1 |
| `gzerror_step` | `gzerror` stores the code in the caller's cell. | checked: `gzerror_step` (`gz.inv-frame`) | 0 | batch 1 |
| `gzerror_string` | The pointer `gzerror` returns is a C string after the call (goal conjunct added by audit C1). | checked: `gzerror_string` (`gz.inv-frame`) | 0 | batch C |
| `gzclearerr_step` | `gzclearerr` through `gz_error`. | checked: `gzclearerr_step` (`gz.inv-clearerr`) | 0 | batch 1 |
| `gzoffset64_step`, `gzoffset_step` | One `lseek` (M3); nothing else changes. | checked: same names (`gz.inv-offset-rewind`, `646b1ab6`) | 0 | batch C |
| `gzrewind_step` | `lseek` (M3) and `gz_reset`. | checked: `gzrewind_step` (`gz.inv-offset-rewind`, `646b1ab6`) | 0 | batch C |
| `history_inv`, `operation_safe`, `close_safe`, `gz_sequence_safety` | Assembly, re-checked under `dev`'s `GzInv` and `GzSafety`. | checked: `gz_sequence_safety_of` (`gz.sequence-safety`), premise `GzReadLeaves`, all six fields proved (`gz_read_leaves`); `Goal.gz_sequence_safety` checked with no premise as `gz_sequence_safety_public` (`public-gz-sequence-safety`); registered in `theorems.txt` | 0 | batch C |
| `gz_init_safe`, `gz_comp_safe`, `gz_zero_safe`, `gz_write_safe`, `gz_vacate_safe` | Write-side helpers. | checked: same names (`gzwrite.c.safety`) | 0 | batch C |
| `gzwrite_step`, `gzfwrite_step`, `gzputc_step`, `gzputs_step`, `gzvprintf_step`, `gzprintf_step`, `gzflush_step`, `gzsetparams_step` | Write-side public calls. | checked: same names (`gzwrite.c.safety`) | 0 | batch C |
| `gzclose_w_step` | Finish, `deflateEnd`, frees, descriptor released. | checked: `gzclose_w_step` (`gzwrite.c.safety`, stated with `GzCloseSafe`) | 0 | batch C |
| `deflate_quiet` | `deflate` with no input stops (`DeflateQuiet`). Used by the write proofs on `dev` directly; no skeleton leaf is left. | checked: `Zlib.Deflate.Universal.Quiet.deflate_quiet_holds` | 0 | batch 3 |
| `gzclose_r_step` | `inflateEnd`, frees, descriptor released. | checked: `GzRead.gzclose_r_step_safe` (`gz.read-close`), the statement written out; `GzRead.Close.Released` is `GzReleased` by `rfl` | 0 | read side (deflate owner) |
| `gz_skip_have_safe` | Skip consumption of buffered bytes. | checked: `gz_skip_have_safe` (`gzread.c.skip-have`) | 0 | read side (deflate owner) |
| `gz_load_safe` | The `read` loop (M1). Difference: `GzRead.gz_load_safe` (`gz.read-load-error`) has the extra hypotheses `hm` (`mode = GZ_READ`), `hsz` (`size ≠ 0`), `hroot` (the buffer is a data buffer or not owned) and `heofin` (`eof ≠ 0 → avail_in = 0`), and a stronger conclusion. | open (align) | 1 | read side (deflate owner) |
| `gz_avail_safe` | Refill `in`. Difference: `GzRead.gz_avail_safe` (`gz.read-avail`) has the extra hypothesis `hm` (`mode = GZ_READ`), and a stronger conclusion. | open (align) | 0.5 | read side (deflate owner) |
| `gz_look_safe` | Lazy buffers, `inflateInit2`, COPY. Difference: `GzRead.gz_look_safe : GzLookSpec` takes `GzInvUpToOutput` (weaker than `GzInv`) and the premises `how = LOOK` and `MsgLit s`; its post is over `GzInvOut`, not `GzInv`. | open (align) | 2 | read side (deflate owner) |
| `gz_decomp_safe` | Inflate steps. Difference: `gz_decomp_safe_of` needs one premise, `InflateStuckNoOutput` (a call from `BAD` or `MEM` returns an error with no output and no input used), proved by batch 3 (`inflateStuckNoOutput_holds`, `inflate.c.stuck-no-output`); the HEAD fact is proved (`inflateHeadUsesInputR_holds`, `inflate.c.head-uses-input`); `GzDecompSpec` adds the premises `MsgLit s` and `out.length ≠ 0`, replaces the separation premise (`out` not owned, or `out = s.out`), and terminates under `ReadsFinite`, not unconditionally. | open (align, one premise) | 3 | read side (deflate owner) |
| `gz_fetch_safe` | The dispatcher. Difference: `gz_fetch_safe_of` needs `GzLookSpec` and `GzDecompSpec`; `GzFetchSafe` takes `GzInvUpToOutput` and the premises `err ≠ Z_STREAM_END`, `how = COPY → avail_in = 0`, `MsgLit s`; post over `GzInvOut`; termination under `ReadsFinite`. Its post carries the progress clauses that `gz_read` and `gz_skip` need for their fuel bound (`fetchRank`: a fetch fills its buffer unless it fails, ends the input, reaches `GZ_OFF_MAX`, or lowers the rank by 2; a bad error stays bad, and a `Stuck` stream gives no output). | open (align, callee premises) | 2 | read side (deflate owner) |
| `gz_skip_safe` | The skip loop. Difference: `gz_skip_safe_of` needs `GzFetchSpec`, `GzFetchProgress` (and `GzErrorSpec`, `GzErrorOwn`, proved); it takes `GzInvUpToSkip` (weaker than `GzInv`). | open (callee premises) | 1 | read side (deflate owner) |
| `gz_read_safe` | Three paths, caller range, `x.pos` (F-1). Checked as `gz_read_safe_of (skip : GzSkipRead) (fetch : GzFetchSafe) (decomp : GzDecompSpec) : GzReadSafe` (`gz.read-read`). `GzReadSafe` is the skeleton statement plus the premises `err ≠ Z_STREAM_END`, `how = COPY → avail_in = 0` and `MsgLit s` (clauses of `GzReadInv`), kept in the post. Termination: the measure `min(len, GZ_OFF_MAX - pos)/8 + fetchRank + phase terms` stays below `2^64` under `ReadsFinite`. `GzSkipRead` is `gzSkipRead_holds` (`gzread.c.skip-fetch`). Closed with no premise as `gz_read_safe : GzReadSafe` (`gz.read-assembly`). | checked | 0 | read side (deflate owner) |
| `gzread_step`, `gzfread_step` | Wrappers of `gz_read`. Checked as `gzread_step_of_read` (`gz.read-gzread`) and `gzfread_step_of_read` (`gzread.c.fread`) from `GzReadSafe`, and closed with no premise as `gzread_step` and `gzfread_step` (`gz.read-assembly`): the skeleton leaves. | checked | 0 | read side (deflate owner) |
| `gzgetc_step` (`gzgetc__step` from it) | One byte. | checked: `GzRead.gzgetc_step` (`gz.read-getc-step`), no premise | 0 | batch C |
| `gzungetc_step` | Push back inside `out`. | checked: `GzRead.gzungetc_step` (`gz.read-getc-step`), no premise: `GzSkipTerminates` is `gzSkipTerminates_holds` (`gzread.c.skip-terminates`) | 0 | batch C |
| `gzgets_step` | Bounded `memchr`, copy, NUL. | checked: `GzRead.gzgets_step` (`gz.read-gets-step`), no premise | 0 | batch C |
| `gzdirect_step` | One `gz_look` and `gz_skip_have`. | checked: `GzRead.gzdirect_step` (`gz.read-direct-step`), no premise | 0 | batch C |
| `gzgetc_macro_safe` | A call of the `gzgetc()` macro of `zlib.h` (`Zlib.ZlibH.gzgetc`) keeps `GzInv`: the inline path (`x.have ≠ 0`) returns with no premise, and with `x.have = 0` the macro is the function, through `gzgetc_step`; the history step `GzHistory.getcMacro` and the goal conjunct added by audit A1, corrected in 3c5292f7. | checked: `GzMacro.gzgetc_macro_safe` (`zlib.h.gzgetc-macro`), used in `history_inv` and `gz_sequence_safety_of` | 0 | batch C |
| Merge the `deflate.c.quiet-*` restated copies | Cleanup, not on the critical path. | open | 4 | later |
| **Total remaining** | batch C 0; read side 9.5 (alignment of internal helper statements with the skeleton text; the goal no longer needs them); unassigned 2; later 4 | | **15.5** | |
