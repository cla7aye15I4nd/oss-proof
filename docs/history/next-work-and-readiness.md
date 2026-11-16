# Earlier work order and readiness notes (historical)

This page keeps the earlier text of the sections "Remaining work", "Ordered next work" and "Public API proof readiness", with the introduction of "Core proof skeletons" of [progress](../progress.md), as it stood
after the required goals were accepted on `bde170e9`. The text is unchanged apart from relative links. It is a historical
record: states such as "open" and "checked", hours, counts and dates describe the time each
entry was written. They are not current status. Current status and remaining work are only in
[progress](../progress.md).

## Remaining work

Targets with red borders have a documented blocker with evidence and a next step below.
A long proof attempt alone does not establish a blocker. Gray targets may be started;
their missing internal lemmas and history invariants are not all drawn in the graph.

### Core proof skeletons

Scope change of 2026-11-11: only safety is planned (see [Scope](../progress.md#scope)). Functional rows that
were still open are marked "not planned" and carry no hours; checked rows stay as they are.

### Ordered next work

Every required goal is registered (63 required goals, none open; 2026-11-14). Of the planned rows 9 to 12, the targets now
registered are `deflateInit2_`, `deflate_initialisation_domain`, `inflateCopy`, `deflateCopy`, `inflate`, `deflate` and the
safety goals of the other calls listed (`inflate_sequence_safety`, `deflate_sequence_safety`, `inflateSync_safety`,
`deflateParams_safety`, `uncompress*_safe`, `compress*_safety`, `inflate_back_sequence_safety`). What is left in them is
functional and not planned: `inflate_sequence`, `deflate_sequence`, `uncompress*`, `compress*`, `inflateBack`,
`inflate_back_sequence` and the functional own goals.
Rows 1 to 5 and 13 are the gzip file interface: their safety is planned (result 5) and follows
the [gz skeleton](skeleton-gz.md#gz), not this table; their functional contracts are not planned. Rows 6 to 8 and 10 are done
only when a sequence goal needs them.

Ordered. "Prerequisite" is what must be proved first; it is never an assumed contract.
"Owner PR" is the pull request that carries the work once one exists.

| # | Target | Prerequisite | Owner PR |
| ---: | --- | --- | --- |
| 1 | `gzopen`, `gzopen64`, `gz_initialisation_domain` | Functional contracts, not planned; `gz_initialisation_domain` is not required (see [Scope](../progress.md#scope)). Statement corrected (see [gzip open path length](specification-review.md#gzip-open-path-length)). Next: the path-open (`fd = -1`) branch of `gz_open`: `fsOpen` outcomes and the append/read seeks, reusing the `gzdopen` composition | — |
| 2 | `gztell`, `gztell64` | `PosInv` from every permitted gz history (open, read, write, seek, pushback) | — |
| 3 | `gzclose_r` | Reader buffer ownership over histories, then `inflateEnd` on an initialized reader | — |
| 4 | `gzseek`, `gzseek64` | `PosInv` and buffer invariants from item 2; transparent and buffered paths | — |
| 5 | Transparent paths of `gzread`, `gzfread`, `gzgetc`, `gzgetc_`, `gzgets`, `gzungetc`, `gzdirect`, `gzwrite`, `gzfwrite`, `gzputc`, `gzputs`, `gzprintf`, `gzvprintf`, `gzflush`, `gzsetparams` | Lazy setup and buffer invariants; compressed paths wait for items 12–13 | — |
| 6 | `deflatePrime` | Pending-byte compaction and bit insertion under `DGood` | — |
| 7 | `deflateBound`, `deflateBound_z` | Execution formulas against the saturated bound, including header strings | — |
| 8 | `deflateSetDictionary` | Window fill, hash insertion and input restoration under `DGood` | — |
| 9 | `deflateInit2_`, `deflate_initialisation_domain` | Registered. Was: parameter normalization, five allocations, cleanup, `DGood` establishment for every parameter tuple | — |
| 10 | `inflateCopy`, `deflateCopy` | Registered. Was: allocation failures, buffer copies, pointer relocation, independent ownership | — |
| 11 | `inflate` → `inflate_sequence` → `inflateSync`, `uncompress*`, `inflateBack`, `inflate_back_sequence` | Table meaning from actual `inflate_table`; one dispatch-loop invariant over every mode | — |
| 12 | `deflate` → `deflate_sequence` → `deflateParams`, `compress*` | `fill_window`/sliding; one strategy-loop invariant parametric in level, `memLevel`, `windowBits`; block emission | — |
| 13 | Compressed gz paths, `gzclose_w`, `gzclose`, `gz_sequence` | Items 11 and 12 | — |

Statement corrections come first when they change what must be proved. Open:
`Api.Goal.inflate_rejects_invalid`, which rests on `detectLag = 8` (a checked counterexample shows
the constant is wrong; [API model](../design/api-model.md)). The gzip open path length question below is corrected.
`inflateInit2_` and `Api.Goal.gz_seek_read` are corrected and checked; they await registration.

Earlier narrative checkpoints (per-area notes on inflate, deflate, trees, CRC, the harness and
integration) are kept in [progress checkpoints](progress-checkpoints.md). They are
historical; the counts in them are not current.

### Public API proof readiness

**Gray means unproved, not blocked. Start independent work now.** Green callees do not
establish the caller's own preconditions, loops, results or memory effects. A directly
callable API can still have a false contract or a confirmed source defect; only evidence
of that kind warrants a blocker border. Do not infer readiness solely from missing arrows.

The [evidence index](../progress.md) separates proof references, C calls and specification
references. The work below names composition obligations, **to confirm** against
the exact targets. It does not introduce public assumptions or grant input coverage.

#### Open, query and close prerequisites

Opening a file does not require the complete engine. Its main work is the common `gz_open`
mode loop, real allocations, string copying, descriptor effects and invariant establishment.
For a tell query, the missing producer is the position invariant over permitted histories.
For close, it is ownership over those histories, including allocation failures.

Local execution proofs now cover:

- [Open entries](../../ZlibF/Proof/gzlib.c.open.lean): NULL arguments, negative descriptors
  and first-allocation failure. They give the unchanged file system and exact heap,
  including the allocation-attempt counter.
- [Reader close](../../ZlibF/Proof/gzread.c.close.lean): NULL, wrong mode and complete
  unbuffered execution under `GzGood`, including descriptor errors, freeing the message,
  path and handle, and a frame over unrelated allocations.
- [Priming entry](../../ZlibF/Proof/deflate.c.prime.lean): refused streams and invalid bit
  counts, before pending-byte compaction.

These are scoped internal results, not proofs of the complete public targets. In particular,
`GzGood` still has to be derived from the permitted public histories. Do not replace a gray
public node with green on the strength of one branch.

#### Next work for every unfinished public target

"Start" means work can begin without a complete engine theorem. "Compose" names a
prerequisite for full closure; independent branches can still proceed. No row grants
checked status or assumes a callee's specification.

<!-- proof-readiness:start -->
| Public targets | Proof work shown in graph | Next work and missing prerequisite |
| --- | --- | --- |
| `gzopen`, `gzopen64`, `gz_initialisation_domain`  | Start: open and cleanup | <a id="readiness-gzopen"></a> **Statement corrected:** see [gzip open path length](specification-review.md#gzip-open-path-length). **Start:** the path-open branch of `gz_open` (`fsOpen` outcomes, append and read seeks), reusing the registered `gzdopen` mode loop, allocation and `OpenState` composition. Entry/failure branches are locally checked above. |
| `gztell64`, `gztell`  | Needs: position history | <a id="readiness-gztell64"></a> **Compose:** derive `PosInv` from reads, writes, seeking and pushback; then reuse the existing arithmetic execution proof. |
| `gzclose_r`  | Needs: resource history | <a id="readiness-gzclose-r"></a> **Start:** initialized-buffer cleanup and its ownership producer over histories. Unbuffered execution and frame are locally checked; `inflateEnd` alone is insufficient. |
| `gzclose_w`, `gzclose`  | Needs: flush and cleanup | <a id="readiness-gzclose-w"></a> **Compose:** actual zero-fill/final compression and file writes, all cleanup/error paths, then dispatch using both complete close results. |
| `gzseek64`, `gzseek`  | Needs: seek and history | <a id="readiness-gzseek64"></a> **Start:** position/pointer history invariants, buffered and transparent paths, exact error frames. Negative-position reachability and historical overflow reports remain **to confirm**. |
| `gzdirect`, `gzread`, `gzfread`, `gzgetc`, `gzgetc_`, `gzgets`, `gzungetc`  | Needs: reader path proofs | <a id="readiness-gzdirect"></a> **Start:** common lazy setup, transparent reads and buffer/history invariants. **Compose:** actual decoder execution for compressed paths, then EOF/count/pushback/error clauses. `gzdirect` needs detection and init, not the full data-decoding loop. |
| `gzwrite`, `gzfwrite`, `gzputc`, `gzputs`, `gzvprintf`, `gzprintf`, `gzflush`, `gzsetparams`  | Needs: writer path proofs | <a id="readiness-gzwrite"></a> **Start:** buffering, formatting, transparent writes and failures. **Compose:** actual compressor execution for compressed output and parameter changes. |
| `deflateInit2_`, `deflate_initialisation_domain`  | Start: init and allocation | <a id="readiness-deflateinit2"></a> **Start:** parameter normalization, five allocations, all failure cleanup, actual `DGood`/tree establishment and witnesses. Reset proofs require the invariant; they do not establish it for fresh storage. |
| `deflatePrime`  | Start: compaction and bits | <a id="readiness-deflateprime"></a> **Start:** pending-byte compaction, checked shifts, bit insertion/flush and invariant/frame preservation. Refusal branches are locally checked; accepted counts remain open. |
| `deflateBound_z`, `deflateBound`  | Start: bound and header review | <a id="readiness-deflatebound-z"></a> **Start:** connect existing execution formulas to the saturated mathematical bound, including header strings and extra lengths. The historical extra-length report is **to confirm**, not a newly confirmed blocker. |
| `deflateSetDictionary`  | Start: window and hash | <a id="readiness-deflatesetdictionary"></a> **Start:** window fill, hash-chain insertion, saved-input restoration, then checksum and exact state/frame effects. Green checksum calls cover only that part. |
| `inflateCopy`, `deflateCopy`  | Start: copy and relocation | <a id="readiness-inflatecopy"></a> **Start:** allocation failures, buffer copies, pointer relocation and independent ownership. Resolve the recorded copy/history investigations before claiming the full domain; do not add silent premises. |
| `deflateParams` | Needs: block flush and parameter state | <a id="readiness-deflateparams"></a> **Compose:** actual old-block flushing, return-code handling and canonical tuning-row updates. Check exact state preservation on refusal before full closure. |
| `inflateSync`  | Needs: scan and history | <a id="readiness-inflatesync"></a> **Start:** compose existing first/resume scans, held bits, marker search, reset and accounting/frame results. Derive window/reset premises from histories. |
| `compress2_z`, `compress2`, `compress_z`, `compress`  | Needs: compressor execution | <a id="readiness-compress2-z"></a> **Start:** arguments, scalar lengths and cleanup. **Compose:** actual init/compress/end with exact output, then wrappers. Abstract roundtrip is insufficient. |
| `uncompress2_z`, `uncompress2`, `uncompress_z`, `uncompress`  | Needs: decoder execution | <a id="readiness-uncompress2-z"></a> **Start:** scalar results, insufficient space and cleanup. **Compose:** actual init/decompress/end, exact consumption/output, then wrappers. |
| `inflate`, `deflate`  | Needs: dispatch invariants | <a id="readiness-inflate"></a> **Compose:** decoder-table or hash-chain meaning, dispatch invariants, loop termination and output/accounting. Green checksums do not establish these premises. |
| `inflate_sequence`, `deflate_sequence`, `inflate_back_sequence`, `gz_sequence`  | Needs: execution and format | <a id="readiness-inflate-sequence"></a> **Compose:** actual per-call safety, history preservation, independent format refinement and completion across input/output splits. |
| `inflateBack` | Needs: tables, window and callbacks | <a id="readiness-inflateback"></a> **Compose:** compressed TABLE/LEN execution, output inside the window, public callback ownership, loop termination and exact input/output accounting. Existing stored and entry paths can progress independently. |
<!-- proof-readiness:end -->

The immediate order is independent entry/cleanup and arithmetic paths, then common open,
position and ownership invariants, then complete function composition. Callback compressed
blocks can progress alongside these. Record an unknown prerequisite here with its exact
question; do not invent a dependency or treat elapsed time as evidence of a blocker.
