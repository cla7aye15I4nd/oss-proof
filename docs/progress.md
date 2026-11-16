# Proof progress and remaining work

This page records the level of every result and the work that remains. It is the only page that
does: the other pages say what a theorem states and link here for its level. Its first section,
Scope, says what is planned, what is accepted and on which commit, and what is not planned. The
long middle part is generated from the proof records: one entry for each goal, with its
statement, proof and dependencies. For what the results mean, read [the overview](overview.md).
For the theorem that covers one function, read [coverage by function](coverage.md): it is the
map from each function to its theorem, and it carries no level.

## Scope

The project is finished when the three safety results below are accepted, in this order.
Everything listed under "Not planned" gets no work.

**Planned: three safety results.** Safety means no undefined behaviour, no memory error, no leak,
and termination. The third result has four parts.

| # | Result | Required goals |
| ---: | --- | --- |
| 1 | `inflate` is safe on every input and every split of the buffers, also over its call sequences. | `Goal.inflate_safety`, `Goal.inflate_sequence_safety` |
| 2 | `deflate` is safe on every input and every split of the buffers, also over its call sequences. | `Goal.deflate_safety`, `Goal.deflate_sequence_safety` |
| 3a | The whole-buffer functions are safe: compositions of 1 and 2. | `Goal.compress_safety`, `Goal.compress2_safety`, `Goal.uncompress_safe`, `Goal.uncompress2_safe` and their `_z` forms |
| 3b | The callback decoder is safe on every input and every caller protocol, also over its call sequences. | `Goal.inflateBackInit__safety`, `Goal.inflateBack_safety`, `Goal.inflateBackEnd_safety`, `Goal.inflate_back_sequence_safety`, `Goal.inflate_back_initialisation_domain` |
| 3c | The gzip file interface is safe on every history of a handle, for every file-system world. | The 32 one-function safety goals of the 31 documented gz functions and of `gzvprintf`; `Goal.gz_sequence_safety`; `Goal.gz_refusal` (a `NULL` handle); `Goal.gz_sequence_nonvacuity` |
| 3d | Every other documented function is safe: the other stream calls with init, End and Copy, the checksums, `compressBound*`, `zlibVersion` and `zlibCompileFlags`. | Their 42 one-function safety goals, `Goal.inflate_refusal`, `Goal.deflate_refusal`, `Goal.inflate_initialisation_domain`, `Goal.deflate_initialisation_domain` |

The six rows hold all 98 required goals: 2 + 2 + 8 + 5 + 35 + 46. The 98 are computed from
`tests/audit/public-api.json` by `scripts/verification.py`; [coverage](coverage.md) names the
theorem of each.

By kind they are 87 one-function safety goals, 4 sequence safety goals, 3 refusal goals and 4
non-vacuity goals. In the manifest, 92 are in the group `safety_goals`, 4 in `nonvacuity_goals`,
and 2 are the full contracts of `compressBound` and `compressBound_z`, which stand for the safety
goals of these two pure functions.

Three notes on the table:

- In 3c, termination is proved for every call in every world, except `gzread`, `gzfread`,
  `gzgetc`, `gzgetc_`, `gzgets` and `gzungetc`. These six need a read budget below `2^61`
  (`ReadsFinite`), also where the C returns at once.
- `gzvprintf` is undocumented in `zlib.h`, but `gzprintf` goes through it, so it is planned
  with 3c, and its goal `Goal.gzvprintf_safety` is required.
- A functional fact is in scope exactly when a planned proof depends on it.

**Level of each result.** The three levels, checked, registered and accepted, are defined in the
[glossary](glossary.md#status). A result is accepted when its theorem is registered and the
acceptance suite is green on a named commit. The suite is the axiom gate, the exact goal match,
the self tests and the differential tests. Proof mutants are not part of it; their runs are
recorded separately below.

| # | Registered | Accepted on commit |
| ---: | --- | --- |
| 1 | Yes, both goals | `bde170e9` for the sequence goal, and for `Goal.inflate_safety` in its earlier form. Registered, not accepted: `Goal.inflate_safety` in its present form |
| 2 | Yes, both goals | `bde170e9` for the sequence goal, and for `Goal.deflate_safety` in its earlier form. Registered, not accepted: `Goal.deflate_safety` in its present form |
| 3a | Yes, all eight | `bde170e9` |
| 3b | Yes, all five | `bde170e9` for the non-vacuity goal, and for the sequence goal in its earlier form. Registered, not accepted: the three one-function goals, and the sequence goal in its present form |
| 3c | Yes, all 35 | `bde170e9` for the sequence, refusal and non-vacuity goals. Registered, not accepted: the 32 one-function goals |
| 3d | Yes, all 46 | `bde170e9`, except these goals in their present form, which are registered, not accepted: the four init safety goals; the 21 goals of `ZlibF/Spec/Safety/Streams.lean` other than `Goal.inflate_safety` and `Goal.deflate_safety` (rows 1 and 2); `Goal.inflateCopy_safety` and `Goal.deflateCopy_safety` |

"Registered, not accepted" means that no acceptance run that covers the goal in its present form
has finished green.

**Acceptance runs.** Each line is a run of the workflow `lean`, read from the record of the run.

- **`bde170e9`, green.** Manual run 43671067586 of 2026-11-15. Every job was green: `build`,
  `no-sorry`, `audit_core`, both `audit_selftest` shards, `diff_core`, all eight `diff_harness`
  shards, and the results `audit` and `difftest`. All 63 goals that were required then were
  registered. The commit of `main` with the same tree, `74a2097c`, was green in the nightly run
  43735018381 of the same day.
- **`3fdbbc38`, cancelled: not an accepted commit.** Manual run 43763696005 of 2026-11-15, on a
  commit that holds all 98 required goals in the form they had at that commit; 25 of them were
  changed afterwards (the refusal clauses, below). It was started when the mutant
  shards were still part of `audit`, and it was cancelled while only those shards were running.
  Green before the cancellation: `build`, `no-sorry`, `audit_core`, both `audit_selftest`
  shards, `diff_core`, all eight `diff_harness` shards, and the result `difftest`. The twenty
  mutant shards were cancelled, so the result `audit` failed, and the run as a whole is recorded
  as cancelled. The parts that now make up the acceptance suite were all green in this run. It
  is not counted because the result `audit` of the run is red and acceptance is read from that
  result. No result is accepted on the strength of this run.
- **Next run: commit not yet named.** <a id="next-acceptance-run"></a>A clean run of the
  acceptance suite on a later commit will accept the goals that the table marks "registered, not
  accepted". This line is the one place to record it: the commit, the run, and the date. Until it
  is filled in, those goals stay registered.

The differential tests are evidence of fidelity, not proof.

**Proof mutant runs.** Proof mutants are additional evidence. They run only on request, gate
nothing, and are reported here with their commit, apart from acceptance.

- **`bde170e9`, green.** All twenty mutant shards of run 43671067586 were green. So were the
  twenty shards of the nightly run 43735018381 on `74a2097c`, the commit of `main` with the same
  tree.
- **No mutant run has finished on a later commit.** The shards of the run on `3fdbbc38` were
  cancelled. The mutant rows of the 35 goals registered after `bde170e9` exist
  (`tests/audit/public-mutants.json`), and the audit checked that on `3fdbbc38`; no finished run
  has executed them.

Between `bde170e9` and this page, these things changed:

- **Each gz function and each callback-decoder function has its own safety goal.** There are 35
  new goals: one for each of the 31 documented gz functions, one for `gzvprintf`, and one each for
  `inflateBackInit_`, `inflateBack` and `inflateBackEnd` (`ZlibF/Spec/Safety/GzCalls.lean`,
  `ZlibF/Spec/Safety/Back.lean`; proofs in `ZlibF/Proof/public-gz-call-safety.lean` and
  `ZlibF/Proof/public-back-safety.lean`). They were registered in commit `0cdd7bdd`: the
  registries under `tests/audit/` gained the 35 goals and their 35 theorems, the manifest names
  each function's own goal, and `scripts/verification.py` no longer lets functions share a safety
  goal. The required set grew from 63 goals to 98. Before, the gz functions named
  `Goal.gz_sequence_safety` and the three callback functions named
  `Goal.inflate_back_sequence_safety`. The 35 goals are registered, not accepted: the
  fast gate is green on `3fdbbc38`.
- **The histories of the callback decoder were widened.** The first step of a history
  (`BackSafeReachable.init`) no longer asks for a `NULL` `state` field before `inflateBackInit_`
  (commit `874a9398`, `BackInitArguments` in `ZlibF/Spec/Common/Sequences.lean`). So
  `Goal.inflate_back_sequence_safety` covers more histories than it did on `bde170e9`. In this
  form it is registered, not accepted.

- **The four init safety goals were widened.** `Goal.inflateInit__safety`,
  `Goal.inflateInit2__safety`, `Goal.deflateInit__safety` and `Goal.deflateInit2__safety` hold for
  every call `zlib.h` allows (commit `101c6ab3`, `ZlibF/Spec/Safety/Initialisation.lean`; proofs in
  `8642e435`, `ZlibF/Proof/public-init-safety.lean`). Before, they asked for a record with a
  `NULL` `state`, the matching version and the matching `stream_size`. In the wider form the four
  goals are checked and registered, and not yet accepted: the fast gate is green on `8642e435`,
  and no acceptance run covers a commit that contains them. They are accepted on `bde170e9` only
  in the narrower form.
- **The stream safety goals state the refusal of a `NULL` or inconsistent stream.** Each of the
  23 one-function stream safety goals of `ZlibF/Spec/Safety/Streams.lean` gained a refusal
  clause: the ten inflate goals and the thirteen deflate goals, among them `Goal.inflate_safety`,
  `Goal.deflate_safety`, `Goal.inflateEnd_safety` and `Goal.deflateEnd_safety`. The two copy
  goals `Goal.inflateCopy_safety` and `Goal.deflateCopy_safety` (`ZlibF/Spec/Safety/Copy.lean`)
  state the refusal of every refused source (commit `71188823`; proofs in `0c45d863`,
  `ZlibF/Proof/public-stream-call-safety.lean`, `ZlibF/Proof/public-inflate-copy-safety.lean` and
  `ZlibF/Proof/public-deflate-copy.lean`). Before, a stream goal covered only the call on a
  reachable stream; `Goal.inflateCopy_safety` had no clause for an inconsistent source, and the
  clause of `Goal.deflateCopy_safety` covered only a source whose `zalloc`, `zfree` or `state` is
  `NULL`. Each goal in its present form implies its earlier form
  (`ZlibF/Proof/public-stream-refusal-strengthening.lean`). The names of the goals and of their
  theorems are unchanged, so the registries are unchanged. In the present form the 25 goals are
  checked and registered, and not yet accepted: the fast gate is green on `2ef5694c`, and no
  acceptance run covers a commit that contains them. They are accepted on `bde170e9` only in the
  earlier form.
- **Statements that are not required goals changed.** The specifications of the fast decoder take
  the input and the output in any byte view, not only in a heap block (commit `4ed7315e`;
  the modules are now `InflateFast*.lean` under `ZlibF/Spec/Common/Inflate/` and
  `ZlibF/Spec/Functional/Inflate/`); a regression derives each earlier statement from the present one
  (`tests/verification/regressions/inffast-byte-views-old-from-new.lean`). Two functional
  definitions were changed: `WrapperLength` (commit `ac0fccc5`) and `DeflateCompletes` (commit
  `a2cf8723`). Registered goals among these statements have, in their present form, no finished
  acceptance run either.
- **Proof modules of functional work changed.** Modules about the meaning of the output of
  `inflate` (`ZlibF/Proof/inflate.c.meaning*.lean`) were added or changed. None of their theorems
  is registered.

The lists `goals.txt`, `proved-goals.txt` and `theorems.txt` changed only by the 35 goals and 35
theorems of the first item; `public-mutants.json` gained the keys of the 35 goals. The complete list
of changes is the difference between `bde170e9` and this commit under `ZlibF/Spec/`,
`tests/audit/` and `scripts/`.

**Open.** Nothing that a safety result needs. Every required goal is registered. What remains
is acceptance of the goals that the table marks "registered, not accepted"
([Ordered next work](#ordered-next-work)).

**Planned after the safety results: the round trip of the default zlib stream.** The default
stream is `deflateInit` at the default level with `inflateInit`. The order is: first the
conditional form (when a `deflate` call sequence and an `inflate` call sequence both reach
`Z_STREAM_END`, the bytes `inflate` writes are the bytes `deflate` read); then completeness (with
enough output room and successful allocation both sides reach `Z_STREAM_END`); then the
unconditional round trip and `uncompress(compress(x)) = x`. The conditional form is checked on
`dev` for the translated C: the theorem `deflate_inflate_roundtrip`
(`ZlibF/Proof/public-deflate-inflate-roundtrip.lean`), which is not registered. Completeness and
the unconditional form are open. The registered goal `Api.Goal.roundtrip` is a model-only statement: it is about the
abstract API model. Earlier work on the deflate side of the round trip (`Ledger`, `ledger_*`,
`completes`, `bound_before_output`, the decoding part of `deflate_sequence`) is kept; which of
it the default-stream round trip needs is not settled on this page.

**Not planned.** No work goes to these. Results already registered for them stay.

| Group | Targets | Reason |
| --- | --- | --- |
| Gzip file interface, functional | `gz_sequence`, `gz_initialisation_domain`, and the functional clauses of the gz calls (the bytes read or written, the return values beyond safety) | Functional. These theorems depend on a hand-made model of the file system, descriptors and `printf` formatting. The safety of the gz calls is planned (3c). |
| Undocumented functions | `zError`, `inflateSyncPoint`, `get_crc_table`, `inflateUndermine`, `inflateValidate`, `inflateCodesUsed`, `inflateResetKeep`, `deflateResetKeep`, `gzopen_w` | Nine of the ten functions that `zlib.h` declares under "undocumented functions (not part of the zlib API)" (`tests/audit/public-api.json`, `undocumented`); the tenth, `gzvprintf`, is planned with 3c. They are not required public targets, and a direct call of one is not a required operation of a sequence goal; the deflate stream domain excludes a direct `deflateResetKeep` ([deviations](deviations.md#stream-calls-inflate-and-deflate)). Their registered proofs stay registered and audited. Internal use is unchanged: `deflateReset` and `inflateReset` go through the `ResetKeep` lemmas. |
| Callback decoder, decoding | the decoding clauses of `inflateBack` and `inflate_back_sequence` (what reaches `out`, `Decodes`) | Functional. The safety of the callback decoder is planned (3b). |
| Model-only statements | `Api.Goal.inflate_rejects_invalid`, the unregistered `*_refines` goals | They speak about the abstract model, not about the C. The first also rests on a detection lag of eight bytes that a counterexample refutes. Rejection of invalid input is stated against the C in the format part of `inflate_sequence` (row "Functional correctness" below). |
| Other build configurations | every configuration except the default x86_64 Linux build | Each one repeats the whole proof for a different platform model. The default build carries the result. |
| More proof mutants for query functions | getters and constant queries | Mutants defend against a wrong proof setup. For a one-line query they add nothing to the planned results. |
| Functional correctness, except the round trip above | the format part of `inflate_sequence` (`inflate` output equals the format: `ParseMeaning` and its stream and decoding sides), the `DecoderFacts` format facts behind `InflateCompletes` and the format clauses of `uncompress*`; the round trip for other levels, strategies, window sizes and wrappers, with preset dictionaries, through the gzip file interface or through `inflateBack` | Not required for the safety results. A functional fact that a planned proof depends on stays in scope. What is already proved is kept and listed as checked; the archived skeleton tables mark the open rows not planned ([inflate](history/skeleton-inflate.md), [deflate](history/skeleton-deflate.md)). |

`Goal.gz_initialisation_domain` is not a required non-vacuity goal. It states the functional
contract of `gzopen` (`OpenState`, `GzReachable`), which the first row above lists as not
planned. No planned safety proof depends on it: `Goal.gz_sequence_safety` starts each history at
the open call and proves `GzInv` along it. In the import closure of the registered gz safety
theorems (`gz_sequence_safety_public`, `gz_sequence_nonvacuity_public`, `gz_refusal`) the goal
occurs only in its own definition, and `GzReachable` is never a premise. That the premises of the
gz safety goal can be met is the registered `Goal.gz_sequence_nonvacuity`. The statement stays in
`tests/audit/goals.txt` as an open, not-planned goal.

A not-planned target is not claimed. Reports say "not planned", never "proved".

**Decisions of the owner.** This list is the dated record; other pages state the result without
the date.

| Date | Decision |
| --- | --- |
| 2026-11-11 | The scope is safety only, to finish sooner. Before it, the functional correctness of `inflate` was result 2. |
| 2026-11-12 | The callback decoder (3b) and the gzip file interface (3c) are planned, safety only. `gzvprintf` moves from the undocumented group to 3c. Patches 0004 and 0005 may land before their upstream submission. |
| 2026-11-14 | `Goal.gz_initialisation_domain` is not a required goal. |
| 2026-11-15 | The round trip of the default zlib stream, with completeness, is planned after the safety results. Four normalisations of the translation are accepted (`AGENTS.md`, section Translation). Proof mutants are additional evidence and no longer part of acceptance: a full run takes several hours. They run on request and gate no merge, no acceptance and no milestone. Status is kept on this page only: other pages do not name a level, an acceptance commit or a count of goals. |

## Contents

- [Scope: planned and not planned](#scope)
- [All targets and dependencies](#proof-progress-graph)
- [Exact target evidence](#target-evidence)
- [Remaining work](#remaining-work)
  - [Core proof skeletons](#core-proof-skeletons)
  - [Ordered next work](#ordered-next-work)
  - [Public API prerequisites](#public-api-proof-readiness)
  - [Specification review](#specification-review)
  - [Translation review](#translation-review)
  - [Reports to recheck](#historical-reports-to-recheck)
- [Earlier checkpoints (historical)](history/progress-checkpoints.md)

The counts in the generated block below are the only current counts. Counts in review
records and in `docs/history/` describe the state when they were written.

<!-- proof-progress:start -->
## Proof progress graph

**274 fixed targets: 196 public and 78 supporting.**
Exact proofs: 228 registered and 1 local only.
These counts are not a percentage of verification effort or a final CI result.

**Input coverage colours:** ⬜ not proved · 🟦 default inputs · 🟨 common inputs · 🟩 all stated inputs.
The input ranges are defined once in [input configurations](spec/input-configurations.md).
A complete fixed-goal proof covers all inputs admitted by that exact statement.
Default/common coverage requires an exact checked scoped contract; branch lemmas
and manually assigned labels cannot grant it. Registration and CI remain separate.
A red border marks a recorded blocker without erasing other established coverage.

Every current fixed target appears once. Public APIs, internal obligations and
abstract models stay in separate groups. Solid arrows show actual proof reuse
between fixed targets, following references through auxiliary lemmas. Dotted
arrows show C calls from callee to caller. They do not make the callee's complete
API contract a proof premise: default Init can be proved independently of
universal Init2. Redundant arrows are omitted only when a path of the same kind
remains. The [evidence index](progress.md) retains every observed connection,
specification references and supporting proof families. These helpers are not
extra final targets. Missing arrows do not establish independence or enumerate
future proof obligations.

```mermaid
flowchart LR
  subgraph queries["Library queries"]
    n19["compressBound"]:::all
    n20["compressBound_z"]:::all
    n21["zlibVersion"]:::all
    n22["zlibCompileFlags"]:::all
    n23["zError"]:::all
    n30["get_crc_table"]:::all
  end
  style queries fill:#f9fafb,stroke:#9ca3af,color:#111827
  subgraph checksums["Checksums"]
    n24["adler32"]:::all
    n25["adler32_z"]:::all
    n26["adler32_combine"]:::all
    n27["adler32_combine64"]:::all
    n28["crc32"]:::all
    n29["crc32_z"]:::all
    n31["crc32_combine_gen"]:::all
    n32["crc32_combine_gen64"]:::all
    n33["crc32_combine_op"]:::all
    n34["crc32_combine"]:::all
    n35["crc32_combine64"]:::all
    n161["adler32_safety"]:::all
    n162["adler32_z_safety"]:::all
    n163["adler32_combine_safety"]:::all
    n164["adler32_combine64_safety"]:::all
    n165["crc32_safety"]:::all
    n166["crc32_z_safety"]:::all
    n167["crc32_combine_gen_safety"]:::all
    n168["crc32_combine_gen64_<br/>safety"]:::all
    n169["crc32_combine_op_safety"]:::all
    n170["crc32_combine_safety"]:::all
    n171["crc32_combine64_safety"]:::all
  end
  style checksums fill:#f9fafb,stroke:#9ca3af,color:#111827
  subgraph addresses["Byte-address model"]
    n181["ByteAddress<br/>address_read_is_pure"]:::all
    n182["ByteAddress<br/>raw_block_unchanged"]:::all
    n183["ByteAddress<br/>every_layout_is_<br/>representable"]:::all
    n184["ByteAddress<br/>every_existing_heap_<br/>accepts_layout"]:::all
    n185["ByteAddress<br/>mask_refines_base_plus_<br/>offset"]:::all
    n186["ByteAddress<br/>pointer_advance_<br/>preserves_low_bits"]:::all
    n187["ByteAddress<br/>first_aligned_offset"]:::all
    n188["ByteAddress<br/>byte_stores_preserve_<br/>bases"]:::all
    n189["ByteAddress<br/>byte_modifies_preserve_<br/>bases"]:::all
  end
  style addresses fill:#f9fafb,stroke:#9ca3af,color:#111827
  subgraph inflate["Inflate streams"]
    n39["inflateCopy"]:::all
    n73["inflateInit2_"]:::all
    n74["inflateInit_"]:::all
    n77["inflateResetKeep"]:::all
    n78["inflateReset"]:::all
    n79["inflateReset2"]:::all
    n80["inflateEnd"]:::all
    n81["inflateGetDictionary"]:::all
    n82["inflateGetHeader"]:::all
    n87["inflateSetDictionary"]:::all
    n89["inflateSyncPoint"]:::all
    n90["inflateMark"]:::all
    n91["inflateCodesUsed"]:::all
    n92["inflateUndermine"]:::all
    n93["inflateValidate"]:::all
    n94["inflatePrime"]:::all
    n99["inflate"]:::all
    n105["inflateSync"]:::unproved
    n123["inflate_sequence_safety"]:::all
    n127["inflate_back_sequence_<br/>safety"]:::all
    n129["inflate_refusal"]:::all
    n133["inflate_safety"]:::all
    n134["inflateSetDictionary_<br/>safety"]:::all
    n135["inflateGetDictionary_<br/>safety"]:::all
    n136["inflateSync_safety"]:::all
    n137["inflateReset_safety"]:::all
    n138["inflateReset2_safety"]:::all
    n139["inflatePrime_safety"]:::all
    n140["inflateMark_safety"]:::all
    n141["inflateGetHeader_safety"]:::all
    n154["inflateEnd_safety"]:::all
    n156["inflateInit2__safety"]:::all
    n157["inflateInit__safety"]:::all
    n160["inflateCopy_safety"]:::all
  end
  style inflate fill:#f9fafb,stroke:#9ca3af,color:#111827
  subgraph fast["Fast decoder obligations"]
    n192["InflateFastBodyOrigin<br/>actual_body_preserves_<br/>origin"]:::all
    n193["InflateFastBodyToken<br/>actual_body_refines_token"]:::all
    n194["InflateFastCallOrigin<br/>actual_fast_preserves_<br/>origin"]:::all
    n195["InflateFastDistanceOrigin<br/>actual_distance_block_<br/>preserves_origin"]:::all
    n196["InflateFastDistanceResult<br/>actual_distance_refines_<br/>lz77"]:::all
    n197["InflateFastDistance<br/>Semantics<br/>distance_lookup_matches_<br/>format"]:::all
    n198["InflateFast<br/>fast_safe"]:::all
    n199["InflateFast<br/>step_safe"]:::all
    n200["InflateFastLength<br/>Semantics<br/>length_lookup_matches_<br/>format"]:::all
    n201["InflateFastLengthTrace<br/>actual_body_retains_<br/>selected_length"]:::all
    n202["InflateFastMatchHistory<br/>actual_copy_match_<br/>refines_lz77"]:::all
    n203["InflateFastMatchHistory<br/>match_array_refines_lz77"]:::all
    n204["InflateFastOrigin<br/>actual_drop_preserves_<br/>origin"]:::all
    n205["InflateFastOrigin<br/>actual_pull_preserves_<br/>origin"]:::all
    n206["InflateFastOrigin<br/>actual_rollback_<br/>preserves_origin"]:::all
    n207["InflateFastOrigin<br/>drop_preserves_origin"]:::all
    n208["InflateFastOrigin<br/>initial_origin"]:::all
    n209["InflateFastOrigin<br/>pull_preserves_origin"]:::all
    n210["InflateFastOrigin<br/>rollback_preserves_origin"]:::all
  end
  style fast fill:#f9fafb,stroke:#9ca3af,color:#111827
  subgraph tables["Decode-table obligations"]
    n211["InflateDecodeTable<br/>Rejection<br/>decode_table_classifies_<br/>input"]:::all
    n212["InflateDecodeTable<br/>Semantics<br/>decode_table_matches_<br/>format"]:::all
    n213["InflateDecodeTableShort<br/>short_decode_table_leaf_<br/>sound"]:::all
    n214["InflateDecodeTable<br/>Soundness<br/>decode_table_leaf_sound"]:::all
    n215["InflateDecodeTableFrame<br/>decode_table_read_<br/>preserved"]:::all
    n216["InflateDecodeTable<br/>Invariant<br/>constructor_establishes_<br/>decode_table_invariant"]:::all
    n217["InflateDecodeTable<br/>Invariant<br/>decode_table_invariant_<br/>of_prefix"]:::all
    n218["InflateDecodeTable<br/>Stability<br/>constructor_establishes_<br/>query_stability"]:::all
    n219["InflateDecodeTable<br/>Stability<br/>query_stability_of_prefix"]:::all
    n220["InflateDecodeTable<br/>Stability<br/>short_rejected_leaf_<br/>stays_invalid"]:::all
    n221["InflateFastTableFlags<br/>constructor_establishes_<br/>fast_leaf_flags"]:::all
    n222["InflateFastTableFlags<br/>fast_leaf_flags_of_prefix"]:::all
    n223["InflateFastTableFlags<br/>fixed_tables_have_fast_<br/>leaf_flags"]:::all
    n224["InflateFastTableFlags<br/>leaf_classification_<br/>agrees"]:::all
    n225["InflateTableContent<br/>inflate_table_content"]:::all
    n226["InflateTableSafety<br/>inflate_table_decoder_<br/>safe"]:::all
    n227["InflateTableExtent<br/>inflate_table_read_extent"]:::all
    n228["InflateRootTable<br/>constructor_root_bits"]:::all
    n229["InflateSubtable<br/>constructor_subtable_bits"]:::all
  end
  style tables fill:#f9fafb,stroke:#9ca3af,color:#111827
  subgraph copy["Match-copy mathematics"]
    n230["LZ77CopySpec<br/>output_copy_refines_lz77"]:::all
    n231["LZ77CopySpec<br/>window_copy_refines_lz77"]:::all
    n232["LZ77HistorySpec<br/>copy_back_compose"]:::all
    n233["LZ77HistorySpec<br/>copy_back_extends_history"]:::all
    n234["LZ77HistorySpec<br/>retained_history_agrees"]:::all
    n235["LZ77HistorySpec<br/>window_distance_check_<br/>agrees"]:::all
  end
  style copy fill:#f9fafb,stroke:#9ca3af,color:#111827
  subgraph deflate["Deflate streams"]
    n40["deflateCopy"]:::all
    n75["deflateInit2_"]:::all
    n76["deflateInit_"]:::all
    n83["deflateGetDictionary"]:::all
    n84["deflateEnd"]:::all
    n85["deflateResetKeep"]:::all
    n86["deflateReset"]:::all
    n88["deflateSetDictionary"]:::unproved
    n95["deflatePending"]:::all
    n96["deflateUsed"]:::all
    n97["deflateTune"]:::all
    n98["deflateSetHeader"]:::all
    n100["deflate"]:::all
    n101["deflateBound_z"]:::unproved
    n102["deflateBound"]:::unproved
    n103["deflatePrime"]:::unproved
    n104["deflateParams"]:::unproved
    n125["deflate_sequence_safety"]:::all
    n128["deflateCopy_safety"]:::all
    n130["deflate_refusal"]:::all
    n142["deflate_safety"]:::all
    n143["deflateSetDictionary_<br/>safety"]:::all
    n144["deflateGetDictionary_<br/>safety"]:::all
    n145["deflateReset_safety"]:::all
    n146["deflateParams_safety"]:::all
    n147["deflateTune_safety"]:::all
    n148["deflateBound_safety"]:::all
    n149["deflateBound_z_safety"]:::all
    n150["deflatePending_safety"]:::all
    n151["deflateUsed_safety"]:::all
    n152["deflatePrime_safety"]:::all
    n153["deflateSetHeader_safety"]:::all
    n155["deflateEnd_safety"]:::all
    n158["deflateInit2__safety"]:::all
    n159["deflateInit__safety"]:::all
  end
  style deflate fill:#f9fafb,stroke:#9ca3af,color:#111827
  subgraph back["Callback decoding"]
    n36["inflateBackInit_"]:::all
    n37["inflateBack"]:::unproved
    n38["inflateBackEnd"]:::all
    n271["inflateBack_safety"]:::all
    n272["inflateBackEnd_safety"]:::all
    n273["inflateBackInit__safety"]:::all
  end
  style back fill:#f9fafb,stroke:#9ca3af,color:#111827
  subgraph gzip["Gzip files"]
    n41["gzclose_r"]:::unproved
    n42["gzclose_w"]:::unproved
    n43["gzclose"]:::unproved
    n44["gzbuffer"]:::all
    n45["gzeof"]:::all
    n46["gztell64"]:::unproved
    n47["gztell"]:::unproved
    n48["gzoffset64"]:::all
    n49["gzoffset"]:::all
    n50["gzerror"]:::all
    n51["gzclearerr"]:::all
    n52["gzrewind"]:::all
    n53["gzseek64"]:::unproved
    n54["gzseek"]:::unproved
    n55["gzopen"]:::unproved
    n56["gzopen64"]:::unproved
    n57["gzdopen"]:::all
    n58["gzread"]:::unproved
    n59["gzfread"]:::unproved
    n60["gzgetc"]:::unproved
    n61["gzgetc_"]:::unproved
    n62["gzungetc"]:::unproved
    n63["gzgets"]:::unproved
    n64["gzdirect"]:::unproved
    n65["gzwrite"]:::unproved
    n66["gzfwrite"]:::unproved
    n67["gzputc"]:::unproved
    n68["gzputs"]:::unproved
    n69["gzvprintf"]:::unproved
    n70["gzprintf"]:::unproved
    n71["gzflush"]:::unproved
    n72["gzsetparams"]:::unproved
    n131["gz_sequence_safety"]:::all
    n132["gz_refusal"]:::all
    n179["gz_sequence_nonvacuity"]:::all
    n239["gzbuffer_safety"]:::all
    n240["gzclearerr_safety"]:::all
    n241["gzclose_safety"]:::all
    n242["gzclose_r_safety"]:::all
    n243["gzclose_w_safety"]:::all
    n244["gzdirect_safety"]:::all
    n245["gzdopen_safety"]:::all
    n246["gzeof_safety"]:::all
    n247["gzerror_safety"]:::all
    n248["gzflush_safety"]:::all
    n249["gzfread_safety"]:::all
    n250["gzfwrite_safety"]:::all
    n251["gzgetc_safety"]:::all
    n252["gzgetc__safety"]:::all
    n253["gzgets_safety"]:::all
    n254["gzoffset_safety"]:::all
    n255["gzoffset64_safety"]:::all
    n256["gzopen_safety"]:::all
    n257["gzopen64_safety"]:::all
    n258["gzprintf_safety"]:::all
    n259["gzvprintf_safety"]:::all
    n260["gzputc_safety"]:::all
    n261["gzputs_safety"]:::all
    n262["gzread_safety"]:::all
    n263["gzrewind_safety"]:::all
    n264["gzseek_safety"]:::all
    n265["gzseek64_safety"]:::all
    n266["gzsetparams_safety"]:::all
    n267["gztell_safety"]:::all
    n268["gztell64_safety"]:::all
    n269["gzungetc_safety"]:::all
    n270["gzwrite_safety"]:::all
  end
  style gzip fill:#f9fafb,stroke:#9ca3af,color:#111827
  subgraph buffers["Whole-buffer operations"]
    n106["compress2_z"]:::unproved
    n107["compress2"]:::unproved
    n108["compress_z"]:::unproved
    n109["compress"]:::unproved
    n110["uncompress2_z"]:::unproved
    n111["uncompress2"]:::unproved
    n112["uncompress_z"]:::unproved
    n113["uncompress"]:::unproved
    n114["uncompress2_z_safe"]:::all
    n115["uncompress2_safe"]:::all
    n116["uncompress_z_safe"]:::all
    n117["uncompress_safe"]:::all
    n118["compress2_z_safety"]:::all
    n119["compress2_safety"]:::all
    n120["compress_z_safety"]:::all
    n121["compress_safety"]:::all
    n172["zlibVersion_safety"]:::all
    n173["zlibCompileFlags_safety"]:::all
  end
  style buffers fill:#f9fafb,stroke:#9ca3af,color:#111827
  subgraph models["Format and API models"]
    n0["Goals<br/>format_deterministic"]:::all
    n1["Goals<br/>format_prefix_free"]:::all
    n2["Goals<br/>inflate_decodes"]:::all
    n3["Goals<br/>inflate_completes"]:::all
    n4["Goals<br/>inflate_rejects_invalid"]:::unproved
    n5["Goals<br/>deflate_valid"]:::all
    n6["Goals<br/>deflate_completes"]:::all
    n7["Goals<br/>deflate_full_flush_resync"]:::all
    n8["Goals<br/>roundtrip"]:::all
    n9["Goals<br/>roundtrip_completes"]:::all
    n10["Goals<br/>dict_roundtrip"]:::all
    n11["Goals<br/>header_roundtrip"]:::all
    n12["Goals<br/>deflate_bound_adequate"]:::all
    n13["Goals<br/>compress_bound_adequate"]:::all
    n14["Goals<br/>compress_roundtrip"]:::all
    n15["Goals<br/>gz_roundtrip"]:::all
    n16["Goals<br/>gz_seek_read<br/>Local exact proof"]:::all
    n17["Concrete<br/>compress_bound_value"]:::all
    n18["Concrete<br/>compress2_z_first_alloc_<br/>failure"]:::all
    n180["Inflate<br/>inflate_deferred_distance"]:::all
  end
  style models fill:#f9fafb,stroke:#9ca3af,color:#111827
  subgraph lifecycle["Lifecycles and call sequences"]
    n122["inflate_sequence"]:::unproved
    n124["deflate_sequence"]:::unproved
    n126["inflate_back_sequence"]:::unproved
    n174["gz_sequence"]:::unproved
    n175["inflate_initialisation_<br/>domain"]:::all
    n176["deflate_initialisation_<br/>domain"]:::all
    n177["inflate_back_<br/>initialisation_domain"]:::all
    n178["gz_initialisation_domain"]:::unproved
  end
  style lifecycle fill:#f9fafb,stroke:#9ca3af,color:#111827
  subgraph internal["Internal proof obligations"]
    n190["Crc32ByteViews<br/>crc32_z_all_byte_views"]:::all
    n191["Crc32ByteViews<br/>crc32_all_byte_views"]:::all
    n236["Token<br/>rejected_has_no_symbols"]:::all
    n237["Token<br/>step_composes_symbols"]:::all
    n238["Token<br/>symbols_exposes_step"]:::all
  end
  style internal fill:#f9fafb,stroke:#9ca3af,color:#111827
  n186 --> n187
  n191 --> n28
  n191 --> n99
  n191 --> n39
  n191 --> n123
  n190 --> n29
  n192 --> n194
  n194 --> n99
  n194 --> n39
  n194 --> n123
  n195 --> n192
  n196 --> n193
  n197 --> n196
  n198 --> n194
  n199 --> n193
  n199 --> n201
  n200 --> n193
  n202 --> n196
  n203 --> n202
  n204 --> n192
  n206 --> n194
  n207 --> n195
  n207 --> n204
  n208 --> n194
  n209 --> n195
  n209 --> n205
  n210 --> n206
  n211 --> n216
  n212 --> n211
  n213 --> n216
  n214 --> n211
  n214 --> n213
  n215 --> n217
  n215 --> n219
  n215 --> n222
  n216 --> n99
  n216 --> n39
  n216 --> n127
  n216 --> n123
  n217 --> n99
  n217 --> n39
  n217 --> n127
  n217 --> n123
  n218 --> n127
  n219 --> n127
  n220 --> n197
  n220 --> n200
  n225 --> n226
  n226 --> n227
  n226 --> n228
  n227 --> n216
  n229 --> n216
  n229 --> n228
  n230 --> n203
  n231 --> n203
  n232 --> n203
  n234 --> n8
  n234 --> n9
  n5 --> n10
  n5 --> n11
  n5 --> n8
  n5 --> n9
  n3 --> n9
  n2 --> n8
  n24 --> n161
  n26 --> n163
  n27 --> n164
  n25 --> n24
  n25 --> n162
  n28 --> n119
  n28 --> n118
  n28 --> n121
  n28 --> n120
  n28 --> n165
  n28 --> n100
  n28 --> n40
  n28 --> n125
  n28 --> n131
  n34 --> n170
  n35 --> n171
  n31 --> n167
  n31 --> n169
  n32 --> n168
  n32 --> n169
  n33 --> n169
  n29 --> n166
  n40 --> n128
  n84 --> n119
  n84 --> n118
  n84 --> n121
  n84 --> n120
  n84 --> n125
  n84 --> n131
  n75 --> n158
  n158 --> n159
  n95 --> n150
  n98 --> n153
  n97 --> n147
  n96 --> n151
  n130 --> n128
  n130 --> n144
  n130 --> n146
  n130 --> n143
  n130 --> n142
  n125 --> n148
  n125 --> n149
  n125 --> n155
  n125 --> n144
  n125 --> n146
  n125 --> n150
  n125 --> n152
  n125 --> n145
  n125 --> n143
  n125 --> n153
  n125 --> n147
  n125 --> n151
  n125 --> n142
  n131 --> n239
  n131 --> n240
  n131 --> n242
  n131 --> n241
  n131 --> n243
  n131 --> n244
  n131 --> n245
  n131 --> n246
  n131 --> n247
  n131 --> n248
  n131 --> n249
  n131 --> n250
  n131 --> n252
  n131 --> n251
  n131 --> n253
  n131 --> n255
  n131 --> n254
  n131 --> n257
  n131 --> n256
  n131 --> n258
  n131 --> n260
  n131 --> n261
  n131 --> n262
  n131 --> n263
  n131 --> n265
  n131 --> n264
  n131 --> n266
  n131 --> n268
  n131 --> n267
  n131 --> n269
  n131 --> n259
  n131 --> n270
  n45 --> n131
  n99 --> n131
  n99 --> n115
  n99 --> n114
  n99 --> n117
  n99 --> n116
  n38 --> n127
  n36 --> n273
  n36 --> n177
  n36 --> n127
  n39 --> n160
  n80 --> n123
  n73 --> n99
  n73 --> n39
  n73 --> n156
  n73 --> n123
  n156 --> n157
  n90 --> n140
  n94 --> n139
  n87 --> n123
  n127 --> n272
  n127 --> n271
  n129 --> n160
  n129 --> n154
  n129 --> n135
  n129 --> n138
  n129 --> n137
  n129 --> n134
  n129 --> n133
  n123 --> n154
  n123 --> n135
  n123 --> n141
  n123 --> n140
  n123 --> n139
  n123 --> n138
  n123 --> n137
  n123 --> n134
  n123 --> n136
  n123 --> n133
  n22 --> n173
  n21 --> n172
  n24 -.-> n100
  n24 -.-> n85
  n24 -.-> n88
  n24 -.-> n99
  n24 -.-> n87
  n25 -.-> n24
  n107 -.-> n109
  n106 -.-> n107
  n106 -.-> n108
  n20 -.-> n19
  n28 -.-> n100
  n28 -.-> n85
  n28 -.-> n88
  n28 -.-> n99
  n35 -.-> n34
  n32 -.-> n35
  n32 -.-> n31
  n33 -.-> n35
  n29 -.-> n28
  n100 -.-> n106
  n100 -.-> n104
  n100 -.-> n42
  n100 -.-> n71
  n100 -.-> n66
  n100 -.-> n67
  n100 -.-> n68
  n100 -.-> n69
  n100 -.-> n65
  n101 -.-> n102
  n84 -.-> n75
  n75 -.-> n76
  n75 -.-> n42
  n75 -.-> n71
  n75 -.-> n66
  n75 -.-> n67
  n75 -.-> n68
  n75 -.-> n72
  n75 -.-> n69
  n75 -.-> n65
  n76 -.-> n106
  n104 -.-> n72
  n86 -.-> n75
  n85 -.-> n86
  n41 -.-> n43
  n42 -.-> n43
  n60 -.-> n61
  n48 -.-> n49
  n52 -.-> n53
  n53 -.-> n54
  n46 -.-> n47
  n69 -.-> n70
  n99 -.-> n59
  n99 -.-> n60
  n99 -.-> n63
  n99 -.-> n58
  n99 -.-> n62
  n99 -.-> n110
  n80 -.-> n41
  n80 -.-> n110
  n73 -.-> n64
  n73 -.-> n59
  n73 -.-> n60
  n73 -.-> n63
  n73 -.-> n58
  n73 -.-> n62
  n73 -.-> n74
  n74 -.-> n110
  n78 -.-> n79
  n78 -.-> n105
  n79 -.-> n73
  n77 -.-> n78
  n111 -.-> n113
  n110 -.-> n111
  n110 -.-> n112
  n23 -.-> n100
  n23 -.-> n75
  n21 -.-> n106
  click n0 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Api/Goals.lean#L42" _blank
  click n1 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Api/Goals.lean#L47" _blank
  click n2 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Api/Goals.lean#L58" _blank
  click n3 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Api/Goals.lean#L69" _blank
  click n4 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Api/Goals.lean#L84" _blank
  click n5 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Api/Goals.lean#L99" _blank
  click n6 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Api/Goals.lean#L106" _blank
  click n7 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Api/Goals.lean#L116" _blank
  click n8 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Api/Goals.lean#L134" _blank
  click n9 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Api/Goals.lean#L143" _blank
  click n10 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Api/Goals.lean#L162" _blank
  click n11 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Api/Goals.lean#L180" _blank
  click n12 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Api/Goals.lean#L189" _blank
  click n13 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Api/Goals.lean#L196" _blank
  click n14 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Api/Goals.lean#L203" _blank
  click n15 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Api/Goals.lean#L214" _blank
  click n16 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Api/Goals.lean#L221" _blank
  click n17 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Api/Concrete.lean#L57" _blank
  click n18 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Api/Concrete.lean#L67" _blank
  click n19 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Queries.lean#L16" _blank
  click n20 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Queries.lean#L21" _blank
  click n21 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Queries.lean#L27" _blank
  click n22 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Queries.lean#L34" _blank
  click n23 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Queries.lean#L40" _blank
  click n24 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Checksums.lean#L41" _blank
  click n25 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Checksums.lean#L36" _blank
  click n26 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Checksums.lean#L62" _blank
  click n27 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Checksums.lean#L66" _blank
  click n28 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Checksums.lean#L93" _blank
  click n29 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Checksums.lean#L85" _blank
  click n30 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Checksums.lean#L102" _blank
  click n31 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Checksums.lean#L116" _blank
  click n32 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Checksums.lean#L119" _blank
  click n33 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Checksums.lean#L126" _blank
  click n34 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Checksums.lean#L138" _blank
  click n35 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Checksums.lean#L141" _blank
  click n36 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Common/Back.lean#L22" _blank
  click n37 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Back.lean#L19" _blank
  click n38 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Common/Back.lean#L116" _blank
  click n39 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Copy.lean#L16" _blank
  click n40 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Copy.lean#L46" _blank
  click n41 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/GzClose.lean#L35" _blank
  click n42 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/GzClose.lean#L40" _blank
  click n43 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/GzClose.lean#L44" _blank
  click n44 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/GzControl.lean#L9" _blank
  click n45 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/GzControl.lean#L19" _blank
  click n46 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/GzControl.lean#L33" _blank
  click n47 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/GzControl.lean#L36" _blank
  click n48 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/GzControl.lean#L50" _blank
  click n49 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/GzControl.lean#L53" _blank
  click n50 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/GzControl.lean#L60" _blank
  click n51 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/GzControl.lean#L71" _blank
  click n52 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/GzControl.lean#L88" _blank
  click n53 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/GzControl.lean#L113" _blank
  click n54 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/GzControl.lean#L116" _blank
  click n55 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/GzOpen.lean#L65" _blank
  click n56 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/GzOpen.lean#L70" _blank
  click n57 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/GzOpen.lean#L75" _blank
  click n58 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/GzRead.lean#L22" _blank
  click n59 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/GzRead.lean#L37" _blank
  click n60 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/GzRead.lean#L58" _blank
  click n61 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/GzRead.lean#L61" _blank
  click n62 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/GzRead.lean#L66" _blank
  click n63 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/GzRead.lean#L80" _blank
  click n64 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/GzRead.lean#L103" _blank
  click n65 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/GzWrite.lean#L28" _blank
  click n66 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/GzWrite.lean#L43" _blank
  click n67 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/GzWrite.lean#L59" _blank
  click n68 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/GzWrite.lean#L71" _blank
  click n69 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/GzWrite.lean#L108" _blank
  click n70 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/GzWrite.lean#L112" _blank
  click n71 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/GzWrite.lean#L117" _blank
  click n72 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/GzWrite.lean#L134" _blank
  click n73 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Initialisation.lean#L15" _blank
  click n74 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Initialisation.lean#L20" _blank
  click n75 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Initialisation.lean#L25" _blank
  click n76 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Initialisation.lean#L32" _blank
  click n77 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Lifecycle.lean#L16" _blank
  click n78 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Lifecycle.lean#L23" _blank
  click n79 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Lifecycle.lean#L34" _blank
  click n80 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Lifecycle.lean#L51" _blank
  click n81 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Lifecycle.lean#L61" _blank
  click n82 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Lifecycle.lean#L71" _blank
  click n83 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Lifecycle.lean#L82" _blank
  click n84 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Lifecycle.lean#L92" _blank
  click n85 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Lifecycle.lean#L102" _blank
  click n86 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Lifecycle.lean#L105" _blank
  click n87 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Lifecycle.lean#L109" _blank
  click n88 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Lifecycle.lean#L131" _blank
  click n89 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/StreamQueries.lean#L15" _blank
  click n90 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/StreamQueries.lean#L24" _blank
  click n91 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/StreamQueries.lean#L35" _blank
  click n92 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/StreamQueries.lean#L43" _blank
  click n93 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/StreamQueries.lean#L51" _blank
  click n94 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/StreamQueries.lean#L62" _blank
  click n95 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/StreamQueries.lean#L75" _blank
  click n96 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/StreamQueries.lean#L86" _blank
  click n97 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/StreamQueries.lean#L94" _blank
  click n98 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/StreamQueries.lean#L107" _blank
  click n99 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Streams.lean#L28" _blank
  click n100 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Streams.lean#L68" _blank
  click n101 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Streams.lean#L105" _blank
  click n102 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Streams.lean#L109" _blank
  click n103 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Streams.lean#L114" _blank
  click n104 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Streams.lean#L132" _blank
  click n105 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Streams.lean#L151" _blank
  click n106 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Utilities.lean#L43" _blank
  click n107 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Utilities.lean#L48" _blank
  click n108 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Utilities.lean#L55" _blank
  click n109 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Utilities.lean#L60" _blank
  click n110 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Utilities.lean#L101" _blank
  click n111 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Utilities.lean#L105" _blank
  click n112 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Utilities.lean#L133" _blank
  click n113 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Utilities.lean#L137" _blank
  click n114 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Utilities.lean#L34" _blank
  click n115 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Utilities.lean#L37" _blank
  click n116 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Utilities.lean#L40" _blank
  click n117 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Utilities.lean#L43" _blank
  click n118 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Utilities.lean#L14" _blank
  click n119 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Utilities.lean#L18" _blank
  click n120 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Utilities.lean#L24" _blank
  click n121 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Utilities.lean#L28" _blank
  click n122 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Sequences.lean#L173" _blank
  click n123 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Sequences.lean#L28" _blank
  click n124 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Sequences.lean#L193" _blank
  click n125 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Sequences.lean#L19" _blank
  click n126 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Sequences.lean#L230" _blank
  click n127 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Common/Sequences.lean#L184" _blank
  click n128 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Copy.lean#L24" _blank
  click n129 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Refusals.lean#L30" _blank
  click n130 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Refusals.lean#L50" _blank
  click n131 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/GzSafety.lean#L144" _blank
  click n132 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Common/GzRefusal.lean#L39" _blank
  click n133 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Streams.lean#L48" _blank
  click n134 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Streams.lean#L60" _blank
  click n135 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Streams.lean#L71" _blank
  click n136 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Streams.lean#L84" _blank
  click n137 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Streams.lean#L96" _blank
  click n138 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Streams.lean#L106" _blank
  click n139 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Streams.lean#L117" _blank
  click n140 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Streams.lean#L128" _blank
  click n141 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Streams.lean#L138" _blank
  click n142 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Streams.lean#L149" _blank
  click n143 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Streams.lean#L160" _blank
  click n144 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Streams.lean#L171" _blank
  click n145 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Streams.lean#L183" _blank
  click n146 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Streams.lean#L193" _blank
  click n147 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Streams.lean#L204" _blank
  click n148 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Streams.lean#L217" _blank
  click n149 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Streams.lean#L229" _blank
  click n150 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Streams.lean#L240" _blank
  click n151 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Streams.lean#L252" _blank
  click n152 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Streams.lean#L263" _blank
  click n153 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Streams.lean#L274" _blank
  click n154 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Streams.lean#L286" _blank
  click n155 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Streams.lean#L300" _blank
  click n156 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Initialisation.lean#L52" _blank
  click n157 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Initialisation.lean#L60" _blank
  click n158 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Initialisation.lean#L70" _blank
  click n159 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Initialisation.lean#L78" _blank
  click n160 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Copy.lean#L58" _blank
  click n161 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Checksums.lean#L20" _blank
  click n162 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Checksums.lean#L27" _blank
  click n163 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Checksums.lean#L35" _blank
  click n164 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Checksums.lean#L41" _blank
  click n165 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Checksums.lean#L48" _blank
  click n166 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Checksums.lean#L55" _blank
  click n167 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Checksums.lean#L62" _blank
  click n168 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Checksums.lean#L68" _blank
  click n169 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Checksums.lean#L75" _blank
  click n170 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Checksums.lean#L83" _blank
  click n171 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Checksums.lean#L89" _blank
  click n172 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Queries.lean#L18" _blank
  click n173 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Queries.lean#L23" _blank
  click n174 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/GzSequence.lean#L48" _blank
  click n175 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Domains.lean#L15" _blank
  click n176 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Domains.lean#L28" _blank
  click n177 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Common/Domains.lean#L24" _blank
  click n178 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/GzSequence.lean#L28" _blank
  click n179 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/GzSafety.lean#L179" _blank
  click n180 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Api/Inflate.lean#L267" _blank
  click n181 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Common/ByteAddress.lean#L39" _blank
  click n182 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Common/ByteAddress.lean#L43" _blank
  click n183 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Common/ByteAddress.lean#L50" _blank
  click n184 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Common/ByteAddress.lean#L57" _blank
  click n185 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Common/ByteAddress.lean#L65" _blank
  click n186 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Common/ByteAddress.lean#L70" _blank
  click n187 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Common/ByteAddress.lean#L77" _blank
  click n188 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Common/ByteAddress.lean#L83" _blank
  click n189 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Common/ByteAddress.lean#L87" _blank
  click n190 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Crc32ByteViews.lean#L18" _blank
  click n191 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Crc32ByteViews.lean#L29" _blank
  click n192 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Common/Inflate/InflateFastBodyOrigin.lean#L18" _blank
  click n193 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Inflate/InflateFastBodyToken.lean#L73" _blank
  click n194 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Common/Inflate/InflateFastCallOrigin.lean#L24" _blank
  click n195 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Inflate/InflateFastDistanceOrigin.lean#L19" _blank
  click n196 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Inflate/InflateFastDistanceResult.lean#L102" _blank
  click n197 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Inflate/InflateFastDistanceSemantics.lean#L20" _blank
  click n198 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Common/Inflate/InflateFast.lean#L70" _blank
  click n199 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Common/Inflate/InflateFast.lean#L42" _blank
  click n200 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Inflate/InflateFastLengthSemantics.lean#L34" _blank
  click n201 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Inflate/InflateFastLengthTrace.lean#L52" _blank
  click n202 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Inflate/InflateFastMatchHistory.lean#L39" _blank
  click n203 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Inflate/InflateFastMatchHistory.lean#L25" _blank
  click n204 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Common/Inflate/InflateFastOrigin.lean#L68" _blank
  click n205 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Common/Inflate/InflateFastOrigin.lean#L57" _blank
  click n206 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Common/Inflate/InflateFastOrigin.lean#L81" _blank
  click n207 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Common/Inflate/InflateFastOrigin.lean#L38" _blank
  click n208 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Common/Inflate/InflateFastOrigin.lean#L27" _blank
  click n209 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Common/Inflate/InflateFastOrigin.lean#L32" _blank
  click n210 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Common/Inflate/InflateFastOrigin.lean#L46" _blank
  click n211 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Inflate/InflateDecodeTableRejection.lean#L19" _blank
  click n212 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Inflate/InflateDecodeTableSemantics.lean#L51" _blank
  click n213 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Inflate/InflateDecodeTableShort.lean#L26" _blank
  click n214 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Inflate/InflateDecodeTableSoundness.lean#L31" _blank
  click n215 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Inflate/InflateDecodeTableFrame.lean#L20" _blank
  click n216 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Inflate/InflateDecodeTableInvariant.lean#L52" _blank
  click n217 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Inflate/InflateDecodeTableInvariant.lean#L69" _blank
  click n218 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Inflate/InflateDecodeTableStability.lean#L30" _blank
  click n219 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Inflate/InflateDecodeTableStability.lean#L43" _blank
  click n220 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Inflate/InflateDecodeTableStability.lean#L54" _blank
  click n221 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Inflate/InflateFastTableFlags.lean#L52" _blank
  click n222 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Inflate/InflateFastTableFlags.lean#L66" _blank
  click n223 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Inflate/InflateFastTableFlags.lean#L76" _blank
  click n224 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Inflate/InflateFastTableFlags.lean#L42" _blank
  click n225 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Common/Inflate/InflateTableContent.lean#L32" _blank
  click n226 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Common/Inflate/InflateTableSafety.lean#L28" _blank
  click n227 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Common/Inflate/InflateTableExtent.lean#L28" _blank
  click n228 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Common/Inflate/InflateRootTable.lean#L21" _blank
  click n229 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Common/Inflate/InflateSubtable.lean#L26" _blank
  click n230 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Math/LZ77CopySpec.lean#L22" _blank
  click n231 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Math/LZ77CopySpec.lean#L32" _blank
  click n232 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Math/LZ77HistorySpec.lean#L21" _blank
  click n233 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Math/LZ77HistorySpec.lean#L15" _blank
  click n234 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Math/LZ77HistorySpec.lean#L29" _blank
  click n235 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Math/LZ77HistorySpec.lean#L39" _blank
  click n236 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Format/Token.lean#L84" _blank
  click n237 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Format/Token.lean#L62" _blank
  click n238 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Functional/Format/Token.lean#L73" _blank
  click n239 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/GzCalls.lean#L45" _blank
  click n240 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/GzCalls.lean#L52" _blank
  click n241 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/GzCalls.lean#L252" _blank
  click n242 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/GzCalls.lean#L260" _blank
  click n243 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/GzCalls.lean#L268" _blank
  click n244 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/GzCalls.lean#L59" _blank
  click n245 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/GzCalls.lean#L286" _blank
  click n246 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/GzCalls.lean#L66" _blank
  click n247 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/GzCalls.lean#L239" _blank
  click n248 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/GzCalls.lean#L73" _blank
  click n249 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/GzCalls.lean#L81" _blank
  click n250 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/GzCalls.lean#L89" _blank
  click n251 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/GzCalls.lean#L224" _blank
  click n252 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/GzCalls.lean#L97" _blank
  click n253 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/GzCalls.lean#L104" _blank
  click n254 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/GzCalls.lean#L111" _blank
  click n255 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/GzCalls.lean#L118" _blank
  click n256 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/GzCalls.lean#L276" _blank
  click n257 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/GzCalls.lean#L281" _blank
  click n258 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/GzCalls.lean#L125" _blank
  click n259 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/GzCalls.lean#L134" _blank
  click n260 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/GzCalls.lean#L142" _blank
  click n261 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/GzCalls.lean#L149" _blank
  click n262 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/GzCalls.lean#L156" _blank
  click n263 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/GzCalls.lean#L163" _blank
  click n264 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/GzCalls.lean#L170" _blank
  click n265 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/GzCalls.lean#L178" _blank
  click n266 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/GzCalls.lean#L186" _blank
  click n267 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/GzCalls.lean#L194" _blank
  click n268 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/GzCalls.lean#L201" _blank
  click n269 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/GzCalls.lean#L208" _blank
  click n270 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/GzCalls.lean#L215" _blank
  click n271 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Back.lean#L46" _blank
  click n272 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Back.lean#L72" _blank
  click n273 "https://github.com/cla7aye15I4nd/zlib-f/blob/4d6796f/ZlibF/Spec/Safety/Back.lean#L30" _blank
  classDef unproved fill:#e5e7eb,color:#374151,stroke:#374151
  classDef default fill:#dbeafe,color:#1d4ed8,stroke:#1d4ed8
  classDef common fill:#fef3c7,color:#92400e,stroke:#92400e
  classDef all fill:#dcfce7,color:#166534,stroke:#166534
  classDef obstacle stroke:#b91c1c,stroke-width:3px
```

Each node opens its exact target or blocker at the fixed source snapshot
`4d6796f`. Some viewers disable diagram links; the
[evidence index](progress.md) provides ordinary links and all proof references.

No documented blockers in this snapshot.


## Target evidence

<!-- proof-link-revision: 4d6796fbf3cab93d0dd09f6fb4bc380f9657e9c6 -->

[Proof narrative](overview.md) · [All-target graph](#proof-progress-graph) · [Input configurations](spec/input-configurations.md)

This index contains **274 fixed targets**: public execution,
sequence and initialization targets, internal obligations and abstract models.
There is one status graph, in progress. A model result is not implementation refinement.
Input coverage and proof registration are separate. An exact local proof can
cover its complete stated domain while still awaiting registration and CI.
Internal premises remain part of the statement; green does not remove them.
A source-only candidate never grants coverage. Disallowed axioms stop generation.

Why can an isolated node be unfinished? Its proof dependencies have not been
established. Missing arrows neither prove independence nor supply a proof plan.
Some Markdown viewers disable diagram links; use these ordinary source links.

## Status key

<a id="status-registered"></a>Registered proof: an exact checked theorem is listed.
<a id="status-local"></a>Locally checked: an exact theorem exists but is not listed.
<a id="status-open"></a>Not proved: no exact theorem covers this target.
<a id="status-blocked"></a>Blocked: a documented obstacle applies to the target.
<a id="status-not-planned"></a>Not planned: the target stays registered but is not planned and not required (see Scope).
These labels do not assign input coverage or replace named-commit CI acceptance.
"All stated inputs" means every input the goal itself states. A goal can state less than zlib.h
allows: [No-fault coverage of zlib.h functions](#no-fault-coverage-of-zlibh-functions) lists the gaps.

<a id="group-queries"></a>

## Library queries

| Target statement | Coverage / evidence state | Contract / input range | Proof evidence | Reviewed next work |
| --- | --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-compressbound"></a>[compressBound](../ZlibF/Spec/Functional/Queries.lean#L16) | All stated inputs / Registered proof | [Contract](../docs/spec/api/utility.md#compressbound); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.compressBound](../ZlibF/Proof/public-compress-bound.lean#L50) | — |
| <a id="target-zlibf-spec-public-goal-compressbound-z"></a>[compressBound_z](../ZlibF/Spec/Functional/Queries.lean#L21) | All stated inputs / Registered proof | [Contract](../docs/spec/api/utility.md#compressbound_z); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.compressBound_z](../ZlibF/Proof/public-compress-bound.lean#L47) | — |
| <a id="target-zlibf-spec-public-goal-zlibversion"></a>[zlibVersion](../ZlibF/Spec/Functional/Queries.lean#L27) | All stated inputs / Registered proof | [Contract](../docs/spec/api/utility.md#zlibversion); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.zlibVersion](../ZlibF/Proof/public-zlib-version.lean#L9) | — |
| <a id="target-zlibf-spec-public-goal-zlibcompileflags"></a>[zlibCompileFlags](../ZlibF/Spec/Functional/Queries.lean#L34) | All stated inputs / Registered proof | [Contract](../docs/spec/api/utility.md#zlibcompileflags); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.zlibCompileFlags](../ZlibF/Proof/public-zlib-compile-flags.lean#L7) | — |
| <a id="target-zlibf-spec-public-goal-zerror"></a>[zError](../ZlibF/Spec/Functional/Queries.lean#L40) | All stated inputs / Registered proof | [Contract](../docs/spec/api/utility.md#zerror); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.zError](../ZlibF/Proof/public-zerror.lean#L38) | — |
| <a id="target-zlibf-spec-public-goal-get-crc-table"></a>[get_crc_table](../ZlibF/Spec/Functional/Checksums.lean#L102) | All stated inputs / Registered proof | [Contract](../docs/spec/api/checksums.md#get_crc_table); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.get_crc_table](../ZlibF/Proof/public-get-crc-table.lean#L14) | — |

<a id="group-checksums"></a>

## Checksums

| Target statement | Coverage / evidence state | Contract / input range | Proof evidence | Reviewed next work |
| --- | --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-adler32"></a>[adler32](../ZlibF/Spec/Functional/Checksums.lean#L41) | All stated inputs / Registered proof | [Contract](../docs/spec/api/checksums.md#adler32); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.AdlerUpdateProof.adler_public](../ZlibF/Proof/public-adler-update.lean#L47) | — |
| <a id="target-zlibf-spec-public-goal-adler32-z"></a>[adler32_z](../ZlibF/Spec/Functional/Checksums.lean#L36) | All stated inputs / Registered proof | [Contract](../docs/spec/api/checksums.md#adler32_z); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.AdlerUpdateProof.adler_z_public](../ZlibF/Proof/public-adler-update.lean#L37) | — |
| <a id="target-zlibf-spec-public-goal-adler32-combine"></a>[adler32_combine](../ZlibF/Spec/Functional/Checksums.lean#L62) | All stated inputs / Registered proof | [Contract](../docs/spec/api/checksums.md#adler32_combine); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.AdlerCombineProof.combine_public](../ZlibF/Proof/public-adler-combine.lean#L119) | — |
| <a id="target-zlibf-spec-public-goal-adler32-combine64"></a>[adler32_combine64](../ZlibF/Spec/Functional/Checksums.lean#L66) | All stated inputs / Registered proof | [Contract](../docs/spec/api/checksums.md#adler32_combine64); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.AdlerCombineProof.combine64_public](../ZlibF/Proof/public-adler-combine.lean#L122) | — |
| <a id="target-zlibf-spec-public-goal-crc32"></a>[crc32](../ZlibF/Spec/Functional/Checksums.lean#L93) | All stated inputs / Registered proof | [Contract](../docs/spec/api/checksums.md#crc32); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.crc32](../ZlibF/Proof/public-crc-updates.lean#L29) | — |
| <a id="target-zlibf-spec-public-goal-crc32-z"></a>[crc32_z](../ZlibF/Spec/Functional/Checksums.lean#L85) | All stated inputs / Registered proof | [Contract](../docs/spec/api/checksums.md#crc32_z); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.crc32_z](../ZlibF/Proof/public-crc-updates.lean#L19) | — |
| <a id="target-zlibf-spec-public-goal-crc32-combine-gen"></a>[crc32_combine_gen](../ZlibF/Spec/Functional/Checksums.lean#L116) | All stated inputs / Registered proof | [Contract](../docs/spec/api/checksums.md#crc32_combine_gen); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.CrcCombineProof.gen](../ZlibF/Proof/public-crc-combine.lean#L77) | — |
| <a id="target-zlibf-spec-public-goal-crc32-combine-gen64"></a>[crc32_combine_gen64](../ZlibF/Spec/Functional/Checksums.lean#L119) | All stated inputs / Registered proof | [Contract](../docs/spec/api/checksums.md#crc32_combine_gen64); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.CrcCombineProof.gen64](../ZlibF/Proof/public-crc-combine.lean#L83) | — |
| <a id="target-zlibf-spec-public-goal-crc32-combine-op"></a>[crc32_combine_op](../ZlibF/Spec/Functional/Checksums.lean#L126) | All stated inputs / Registered proof | [Contract](../docs/spec/api/checksums.md#crc32_combine_op); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.CrcCombineProof.op](../ZlibF/Proof/public-crc-combine.lean#L89) | — |
| <a id="target-zlibf-spec-public-goal-crc32-combine"></a>[crc32_combine](../ZlibF/Spec/Functional/Checksums.lean#L138) | All stated inputs / Registered proof | [Contract](../docs/spec/api/checksums.md#crc32_combine); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.CrcCombineProof.combine](../ZlibF/Proof/public-crc-combine.lean#L95) | — |
| <a id="target-zlibf-spec-public-goal-crc32-combine64"></a>[crc32_combine64](../ZlibF/Spec/Functional/Checksums.lean#L141) | All stated inputs / Registered proof | [Contract](../docs/spec/api/checksums.md#crc32_combine64); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.CrcCombineProof.combine64](../ZlibF/Proof/public-crc-combine.lean#L101) | — |
| <a id="target-zlibf-spec-public-goal-adler32-safety"></a>[adler32_safety](../ZlibF/Spec/Safety/Checksums.lean#L20) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.StatelessSafetyProof.adler32_safety](../ZlibF/Proof/public-stateless-safety.lean#L21) | — |
| <a id="target-zlibf-spec-public-goal-adler32-z-safety"></a>[adler32_z_safety](../ZlibF/Spec/Safety/Checksums.lean#L27) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.StatelessSafetyProof.adler32_z_safety](../ZlibF/Proof/public-stateless-safety.lean#L25) | — |
| <a id="target-zlibf-spec-public-goal-adler32-combine-safety"></a>[adler32_combine_safety](../ZlibF/Spec/Safety/Checksums.lean#L35) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.StatelessSafetyProof.adler32_combine_safety](../ZlibF/Proof/public-stateless-safety.lean#L29) | — |
| <a id="target-zlibf-spec-public-goal-adler32-combine64-safety"></a>[adler32_combine64_safety](../ZlibF/Spec/Safety/Checksums.lean#L41) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.StatelessSafetyProof.adler32_combine64_safety](../ZlibF/Proof/public-stateless-safety.lean#L34) | — |
| <a id="target-zlibf-spec-public-goal-crc32-safety"></a>[crc32_safety](../ZlibF/Spec/Safety/Checksums.lean#L48) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.StatelessSafetyProof.crc32_safety](../ZlibF/Proof/public-stateless-safety.lean#L39) | — |
| <a id="target-zlibf-spec-public-goal-crc32-z-safety"></a>[crc32_z_safety](../ZlibF/Spec/Safety/Checksums.lean#L55) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.StatelessSafetyProof.crc32_z_safety](../ZlibF/Proof/public-stateless-safety.lean#L43) | — |
| <a id="target-zlibf-spec-public-goal-crc32-combine-gen-safety"></a>[crc32_combine_gen_safety](../ZlibF/Spec/Safety/Checksums.lean#L62) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.StatelessSafetyProof.crc32_combine_gen_safety](../ZlibF/Proof/public-stateless-safety.lean#L47) | — |
| <a id="target-zlibf-spec-public-goal-crc32-combine-gen64-safety"></a>[crc32_combine_gen64_safety](../ZlibF/Spec/Safety/Checksums.lean#L68) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.StatelessSafetyProof.crc32_combine_gen64_safety](../ZlibF/Proof/public-stateless-safety.lean#L51) | — |
| <a id="target-zlibf-spec-public-goal-crc32-combine-op-safety"></a>[crc32_combine_op_safety](../ZlibF/Spec/Safety/Checksums.lean#L75) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.StatelessSafetyProof.crc32_combine_op_safety](../ZlibF/Proof/public-stateless-safety.lean#L55) | — |
| <a id="target-zlibf-spec-public-goal-crc32-combine-safety"></a>[crc32_combine_safety](../ZlibF/Spec/Safety/Checksums.lean#L83) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.StatelessSafetyProof.crc32_combine_safety](../ZlibF/Proof/public-stateless-safety.lean#L67) | — |
| <a id="target-zlibf-spec-public-goal-crc32-combine64-safety"></a>[crc32_combine64_safety](../ZlibF/Spec/Safety/Checksums.lean#L89) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.StatelessSafetyProof.crc32_combine64_safety](../ZlibF/Proof/public-stateless-safety.lean#L71) | — |

<a id="group-addresses"></a>

## Byte-address model

| Target statement | Coverage / evidence state | Contract / input range | Proof evidence | Reviewed next work |
| --- | --- | --- | --- | --- |
| <a id="target-c-byteaddress-spec-goal-address-read-is-pure"></a>[address_read_is_pure](../ZlibF/Spec/Common/ByteAddress.lean#L39) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [C.ByteAddress.Proofs.address_read_is_pure](../ZlibF/Proof/ByteAddress.lean#L28) | — |
| <a id="target-c-byteaddress-spec-goal-raw-block-unchanged"></a>[raw_block_unchanged](../ZlibF/Spec/Common/ByteAddress.lean#L43) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [C.ByteAddress.Proofs.raw_block_unchanged](../ZlibF/Proof/ByteAddress.lean#L33) | — |
| <a id="target-c-byteaddress-spec-goal-every-layout-is-representable"></a>[every_layout_is_representable](../ZlibF/Spec/Common/ByteAddress.lean#L50) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [C.ByteAddress.Proofs.every_layout_is_representable](../ZlibF/Proof/ByteAddress.lean#L39) | — |
| <a id="target-c-byteaddress-spec-goal-every-existing-heap-accepts-layout"></a>[every_existing_heap_accepts_layout](../ZlibF/Spec/Common/ByteAddress.lean#L57) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [C.ByteAddress.Proofs.every_existing_heap_accepts_layout](../ZlibF/Proof/ByteAddress.lean#L94) | — |
| <a id="target-c-byteaddress-spec-goal-mask-refines-base-plus-offset"></a>[mask_refines_base_plus_offset](../ZlibF/Spec/Common/ByteAddress.lean#L65) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [C.ByteAddress.Proofs.mask_refines_base_plus_offset](../ZlibF/Proof/ByteAddress.lean#L54) | — |
| <a id="target-c-byteaddress-spec-goal-pointer-advance-preserves-low-bits"></a>[pointer_advance_preserves_low_bits](../ZlibF/Spec/Common/ByteAddress.lean#L70) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [C.ByteAddress.Proofs.pointer_advance_preserves_low_bits](../ZlibF/Proof/ByteAddress.lean#L60) | — |
| <a id="target-c-byteaddress-spec-goal-first-aligned-offset"></a>[first_aligned_offset](../ZlibF/Spec/Common/ByteAddress.lean#L77) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [C.ByteAddress.Proofs.first_aligned_offset](../ZlibF/Proof/ByteAddress.lean#L67) | — |
| <a id="target-c-byteaddress-spec-goal-byte-stores-preserve-bases"></a>[byte_stores_preserve_bases](../ZlibF/Spec/Common/ByteAddress.lean#L83) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [C.ByteAddress.Proofs.byte_stores_preserve_bases](../ZlibF/Proof/ByteAddress.lean#L81) | — |
| <a id="target-c-byteaddress-spec-goal-byte-modifies-preserve-bases"></a>[byte_modifies_preserve_bases](../ZlibF/Spec/Common/ByteAddress.lean#L87) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [C.ByteAddress.Proofs.byte_modifies_preserve_bases](../ZlibF/Proof/ByteAddress.lean#L88) | — |

<a id="group-inflate"></a>

## Inflate streams

| Target statement | Coverage / evidence state | Contract / input range | Proof evidence | Reviewed next work |
| --- | --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-inflatecopy"></a>[inflateCopy](../ZlibF/Spec/Functional/Copy.lean#L16) | All stated inputs / Registered proof | [Contract](../docs/spec/api/inflate-stream.md#inflatecopy); [input range](spec/input-configurations.md#inflate-inputs) | [Zlib.Inflate.Proofs.inflate_copy_public](../ZlibF/Proof/public-inflate-copy.lean#L13) | — |
| <a id="target-zlibf-spec-public-goal-inflateinit2"></a>[inflateInit2_](../ZlibF/Spec/Functional/Initialisation.lean#L15) | All stated inputs / Registered proof | [Contract](../docs/spec/api/inflate-stream.md#inflateinit2_); [input range](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.Proofs.InflateInit.inflate_init2_public](../ZlibF/Proof/public-inflate-init2.lean#L20) | — |
| <a id="target-zlibf-spec-public-goal-inflateinit"></a>[inflateInit_](../ZlibF/Spec/Functional/Initialisation.lean#L20) | All stated inputs / Registered proof | [Contract](../docs/spec/api/inflate-stream.md#inflateinit_); [input range](spec/input-configurations.md#inflate-inputs) | [Zlib.Inflate.Proofs.inflate_default_init_contract](../ZlibF/Proof/inflate.c.default-entry.lean#L59); [ZlibF.Spec.Public.Proofs.InflateInit.init15_public](../ZlibF/Proof/public-inflate-init.lean#L86) | — |
| <a id="target-zlibf-spec-public-goal-inflateresetkeep"></a>[inflateResetKeep](../ZlibF/Spec/Functional/Lifecycle.lean#L16) | All stated inputs / Registered proof | [Contract](../docs/spec/api/inflate-stream.md#inflateresetkeep); [input range](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflateResetKeepProof.resetkeep_public](../ZlibF/Proof/public-inflate-reset-keep.lean#L10) | — |
| <a id="target-zlibf-spec-public-goal-inflatereset"></a>[inflateReset](../ZlibF/Spec/Functional/Lifecycle.lean#L23) | All stated inputs / Registered proof | [Contract](../docs/spec/api/inflate-stream.md#inflatereset); [input range](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflateResetProof.reset_public](../ZlibF/Proof/public-inflate-reset.lean#L18) | — |
| <a id="target-zlibf-spec-public-goal-inflatereset2"></a>[inflateReset2](../ZlibF/Spec/Functional/Lifecycle.lean#L34) | All stated inputs / Registered proof | [Contract](../docs/spec/api/inflate-stream.md#inflatereset2); [input range](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflateReset2Proof.reset2_public](../ZlibF/Proof/public-inflate-reset2.lean#L63) | — |
| <a id="target-zlibf-spec-public-goal-inflateend"></a>[inflateEnd](../ZlibF/Spec/Functional/Lifecycle.lean#L51) | All stated inputs / Registered proof | [Contract](../docs/spec/api/inflate-stream.md#inflateend); [input range](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflateEndProof.inflate_end_public](../ZlibF/Proof/public-inflate-end.lean#L57) | — |
| <a id="target-zlibf-spec-public-goal-inflategetdictionary"></a>[inflateGetDictionary](../ZlibF/Spec/Functional/Lifecycle.lean#L61) | All stated inputs / Registered proof | [Contract](../docs/spec/api/inflate-stream.md#inflategetdictionary); [input range](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflateDictionaryProof.inflate_getdict_public](../ZlibF/Proof/public-inflate-getdict.lean#L12) | — |
| <a id="target-zlibf-spec-public-goal-inflategetheader"></a>[inflateGetHeader](../ZlibF/Spec/Functional/Lifecycle.lean#L71) | All stated inputs / Registered proof | [Contract](../docs/spec/api/inflate-stream.md#inflategetheader); [input range](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflateHeaderProof.getheader_public](../ZlibF/Proof/public-inflate-header.lean#L36) | — |
| <a id="target-zlibf-spec-public-goal-inflatesetdictionary"></a>[inflateSetDictionary](../ZlibF/Spec/Functional/Lifecycle.lean#L109) | All stated inputs / Registered proof | [Contract](../docs/spec/api/inflate-stream.md#inflatesetdictionary); [input range](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.Proofs.inflateSetDictionary_public](../ZlibF/Proof/public-inflate-setdict.lean#L94) | — |
| <a id="target-zlibf-spec-public-goal-inflatesyncpoint"></a>[inflateSyncPoint](../ZlibF/Spec/Functional/StreamQueries.lean#L15) | All stated inputs / Registered proof | [Contract](../docs/spec/api/inflate-stream.md#inflatesyncpoint); [input range](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflateQueryProof.syncpoint_public](../ZlibF/Proof/public-inflate-small-queries.lean#L46) | — |
| <a id="target-zlibf-spec-public-goal-inflatemark"></a>[inflateMark](../ZlibF/Spec/Functional/StreamQueries.lean#L24) | All stated inputs / Registered proof | [Contract](../docs/spec/api/inflate-stream.md#inflatemark); [input range](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflateMarkProof.mark_public](../ZlibF/Proof/public-inflate-mark.lean#L72) | — |
| <a id="target-zlibf-spec-public-goal-inflatecodesused"></a>[inflateCodesUsed](../ZlibF/Spec/Functional/StreamQueries.lean#L35) | All stated inputs / Registered proof | [Contract](../docs/spec/api/inflate-stream.md#inflatecodesused); [input range](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.Proofs.inflate_codes_used](../ZlibF/Proof/Api/QueryLayout.lean#L73) | — |
| <a id="target-zlibf-spec-public-goal-inflateundermine"></a>[inflateUndermine](../ZlibF/Spec/Functional/StreamQueries.lean#L43) | All stated inputs / Registered proof | [Contract](../docs/spec/api/inflate-stream.md#inflateundermine); [input range](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflateQueryProof.undermine_public](../ZlibF/Proof/public-inflate-small-queries.lean#L62) | — |
| <a id="target-zlibf-spec-public-goal-inflatevalidate"></a>[inflateValidate](../ZlibF/Spec/Functional/StreamQueries.lean#L51) | All stated inputs / Registered proof | [Contract](../docs/spec/api/inflate-stream.md#inflatevalidate); [input range](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflateQueryProof.validate_public](../ZlibF/Proof/public-inflate-small-queries.lean#L77) | — |
| <a id="target-zlibf-spec-public-goal-inflateprime"></a>[inflatePrime](../ZlibF/Spec/Functional/StreamQueries.lean#L62) | All stated inputs / Registered proof | [Contract](../docs/spec/api/inflate-stream.md#inflateprime); [input range](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflatePrimeProof.prime_public](../ZlibF/Proof/public-inflate-prime.lean#L118) | — |
| <a id="target-zlibf-spec-public-goal-inflate"></a>[inflate](../ZlibF/Spec/Functional/Streams.lean#L28) | All stated inputs / Registered proof | [Contract](../docs/spec/api/inflate-stream.md#inflate); [input range](spec/input-configurations.md#inflate-inputs) | [Zlib.Inflate.Proofs.inflate_public](../ZlibF/Proof/public-inflate.lean#L11) | — |
| <a id="target-zlibf-spec-public-goal-inflatesync"></a>[inflateSync](../ZlibF/Spec/Functional/Streams.lean#L151) | Not proved / Not proved | [Contract](../docs/spec/api/inflate-stream.md#inflatesync); [input range](spec/input-configurations.md#inflate-inputs) | — | [Needs: scan and history](progress.md#readiness-inflatesync) |
| <a id="target-zlibf-spec-public-goal-inflate-sequence-safety"></a>[inflate_sequence_safety](../ZlibF/Spec/Safety/Sequences.lean#L28) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#inflate-inputs) | [Zlib.Inflate.Proofs.inflate_sequence_safety_public](../ZlibF/Proof/public-inflate-sequence-safety.lean#L11) | — |
| <a id="target-zlibf-spec-public-goal-inflate-back-sequence-safety"></a>[inflate_back_sequence_safety](../ZlibF/Spec/Common/Sequences.lean#L184) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#inflate-inputs) | [Zlib.Infback.Safety.inflate_back_sequence_safety](../ZlibF/Proof/infback.c.safety-fast.lean#L438) | — |
| <a id="target-zlibf-spec-public-goal-inflate-refusal"></a>[inflate_refusal](../ZlibF/Spec/Safety/Refusals.lean#L30) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.RefusalProof.inflate_refusal](../ZlibF/Proof/public-stream-refusal.lean#L46) | — |
| <a id="target-zlibf-spec-public-goal-inflate-safety"></a>[inflate_safety](../ZlibF/Spec/Safety/Streams.lean#L48) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.StreamCallSafetyProof.inflate_safety](../ZlibF/Proof/public-stream-call-safety.lean#L65) | — |
| <a id="target-zlibf-spec-public-goal-inflatesetdictionary-safety"></a>[inflateSetDictionary_safety](../ZlibF/Spec/Safety/Streams.lean#L60) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.StreamCallSafetyProof.inflateSetDictionary_safety](../ZlibF/Proof/public-stream-call-safety.lean#L70) | — |
| <a id="target-zlibf-spec-public-goal-inflategetdictionary-safety"></a>[inflateGetDictionary_safety](../ZlibF/Spec/Safety/Streams.lean#L71) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.StreamCallSafetyProof.inflateGetDictionary_safety](../ZlibF/Proof/public-stream-call-safety.lean#L75) | — |
| <a id="target-zlibf-spec-public-goal-inflatesync-safety"></a>[inflateSync_safety](../ZlibF/Spec/Safety/Streams.lean#L84) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.StreamCallSafetyProof.inflateSync_safety](../ZlibF/Proof/public-stream-call-safety.lean#L80) | — |
| <a id="target-zlibf-spec-public-goal-inflatereset-safety"></a>[inflateReset_safety](../ZlibF/Spec/Safety/Streams.lean#L96) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.StreamCallSafetyProof.inflateReset_safety](../ZlibF/Proof/public-stream-call-safety.lean#L85) | — |
| <a id="target-zlibf-spec-public-goal-inflatereset2-safety"></a>[inflateReset2_safety](../ZlibF/Spec/Safety/Streams.lean#L106) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.StreamCallSafetyProof.inflateReset2_safety](../ZlibF/Proof/public-stream-call-safety.lean#L90) | — |
| <a id="target-zlibf-spec-public-goal-inflateprime-safety"></a>[inflatePrime_safety](../ZlibF/Spec/Safety/Streams.lean#L117) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.StreamCallSafetyProof.inflatePrime_safety](../ZlibF/Proof/public-stream-call-safety.lean#L95) | — |
| <a id="target-zlibf-spec-public-goal-inflatemark-safety"></a>[inflateMark_safety](../ZlibF/Spec/Safety/Streams.lean#L128) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.StreamCallSafetyProof.inflateMark_safety](../ZlibF/Proof/public-stream-call-safety.lean#L100) | — |
| <a id="target-zlibf-spec-public-goal-inflategetheader-safety"></a>[inflateGetHeader_safety](../ZlibF/Spec/Safety/Streams.lean#L138) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.StreamCallSafetyProof.inflateGetHeader_safety](../ZlibF/Proof/public-stream-call-safety.lean#L105) | — |
| <a id="target-zlibf-spec-public-goal-inflateend-safety"></a>[inflateEnd_safety](../ZlibF/Spec/Safety/Streams.lean#L286) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.StreamCallSafetyProof.inflateEnd_safety](../ZlibF/Proof/public-stream-call-safety.lean#L172) | — |
| <a id="target-zlibf-spec-public-goal-inflateinit2-safety"></a>[inflateInit2__safety](../ZlibF/Spec/Safety/Initialisation.lean#L52) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InitSafetyProof.inflateInit2__safety](../ZlibF/Proof/public-init-safety.lean#L112) | — |
| <a id="target-zlibf-spec-public-goal-inflateinit-safety"></a>[inflateInit__safety](../ZlibF/Spec/Safety/Initialisation.lean#L60) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InitSafetyProof.inflateInit__safety](../ZlibF/Proof/public-init-safety.lean#L132) | — |
| <a id="target-zlibf-spec-public-goal-inflatecopy-safety"></a>[inflateCopy_safety](../ZlibF/Spec/Safety/Copy.lean#L58) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#inflate-inputs) | [ZlibF.Spec.Public.InflateCopySafetyProof.inflateCopy_safety](../ZlibF/Proof/public-inflate-copy-safety.lean#L17) | — |

<a id="group-fast"></a>

## Fast decoder obligations

| Target statement | Coverage / evidence state | Contract / input range | Proof evidence | Reviewed next work |
| --- | --- | --- | --- | --- |
| <a id="target-zlib-inffast-spec-bodyorigin-goal-actual-body-preserves-origin"></a>[actual_body_preserves_origin](../ZlibF/Spec/Common/Inflate/InflateFastBodyOrigin.lean#L18) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.BodyOriginProof.actual_body_preserves_origin](../ZlibF/Proof/inffast.c.body-origin.lean#L380); [Zlib.Inffast.Proofs.actual_body_preserves_origin](../ZlibF/Proof/inffast.c.body-origin.lean#L380) | — |
| <a id="target-zlib-inffast-spec-bodytoken-goal-actual-body-refines-token"></a>[actual_body_refines_token](../ZlibF/Spec/Functional/Inflate/InflateFastBodyToken.lean#L73) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.BodyTokenProof.actual_body_refines_token](../ZlibF/Proof/inffast.c.body-token.lean#L571); [Zlib.Inffast.Proofs.actual_body_refines_token](../ZlibF/Proof/inffast.c.body-token.lean#L571) | — |
| <a id="target-zlib-inffast-spec-callorigin-goal-actual-fast-preserves-origin"></a>[actual_fast_preserves_origin](../ZlibF/Spec/Common/Inflate/InflateFastCallOrigin.lean#L24) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.actual_fast_preserves_origin](../ZlibF/Proof/inffast.c.call-origin.lean#L180); [ZlibF.Proof.Registration.fast_call_origin](../ZlibF/Proof/proof-registrations.lean#L14) | — |
| <a id="target-zlib-inffast-spec-distanceorigin-goal-actual-distance-block-preserves-origin"></a>[actual_distance_block_preserves_origin](../ZlibF/Spec/Functional/Inflate/InflateFastDistanceOrigin.lean#L19) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.actual_distance_block_preserves_origin](../ZlibF/Proof/inffast.c.distance-origin.lean#L327) | — |
| <a id="target-zlib-inffast-spec-distanceresult-goal-actual-distance-refines-lz77"></a>[actual_distance_refines_lz77](../ZlibF/Spec/Functional/Inflate/InflateFastDistanceResult.lean#L102) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.actual_distance_refines_lz77](../ZlibF/Proof/inffast.c.distance-result.lean#L386) | — |
| <a id="target-zlib-inffast-spec-distancesemantics-goal-distance-lookup-matches-format"></a>[distance_lookup_matches_format](../ZlibF/Spec/Functional/Inflate/InflateFastDistanceSemantics.lean#L20) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.distance_lookup_matches_format](../ZlibF/Proof/inffast.c.distance-semantics.lean#L25) | — |
| <a id="target-zlib-inffast-spec-goal-fast-safe"></a>[fast_safe](../ZlibF/Spec/Common/Inflate/InflateFast.lean#L70) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.inflate_fast_safe](../ZlibF/Proof/inffast.c.final.lean#L253) | — |
| <a id="target-zlib-inffast-spec-goal-step-safe"></a>[step_safe](../ZlibF/Spec/Common/Inflate/InflateFast.lean#L42) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.inflate_fast_body_step_safe](../ZlibF/Proof/inffast.c.body.lean#L350) | — |
| <a id="target-zlib-inffast-spec-lengthsemantics-goal-length-lookup-matches-format"></a>[length_lookup_matches_format](../ZlibF/Spec/Functional/Inflate/InflateFastLengthSemantics.lean#L34) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.length_lookup_matches_format](../ZlibF/Proof/inffast.c.length-semantics.lean#L25) | — |
| <a id="target-zlib-inffast-spec-lengthtrace-goal-actual-body-retains-selected-length"></a>[actual_body_retains_selected_length](../ZlibF/Spec/Functional/Inflate/InflateFastLengthTrace.lean#L52) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.LengthTraceProof.actual_body_retains_selected_length](../ZlibF/Proof/inffast.c.length-trace.lean#L250); [Zlib.Inffast.Proofs.actual_body_retains_selected_length](../ZlibF/Proof/inffast.c.length-trace.lean#L250) | — |
| <a id="target-zlib-inffast-spec-matchhistory-goal-actual-copy-match-refines-lz77"></a>[actual_copy_match_refines_lz77](../ZlibF/Spec/Functional/Inflate/InflateFastMatchHistory.lean#L39) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.actual_copy_match_refines_lz77](../ZlibF/Proof/inffast.c.match-history.lean#L328) | — |
| <a id="target-zlib-inffast-spec-matchhistory-goal-match-array-refines-lz77"></a>[match_array_refines_lz77](../ZlibF/Spec/Functional/Inflate/InflateFastMatchHistory.lean#L25) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.fast_match_array_refines_lz77](../ZlibF/Math/InflateFastMatchHistory.lean#L59) | — |
| <a id="target-zlib-inffast-spec-origin-goal-actual-drop-preserves-origin"></a>[actual_drop_preserves_origin](../ZlibF/Spec/Common/Inflate/InflateFastOrigin.lean#L68) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.actual_drop_preserves_origin](../ZlibF/Proof/inffast.c.origin.lean#L138) | — |
| <a id="target-zlib-inffast-spec-origin-goal-actual-pull-preserves-origin"></a>[actual_pull_preserves_origin](../ZlibF/Spec/Common/Inflate/InflateFastOrigin.lean#L57) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.actual_pull_preserves_origin](../ZlibF/Proof/inffast.c.origin.lean#L127) | — |
| <a id="target-zlib-inffast-spec-origin-goal-actual-rollback-preserves-origin"></a>[actual_rollback_preserves_origin](../ZlibF/Spec/Common/Inflate/InflateFastOrigin.lean#L81) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.actual_rollback_preserves_origin](../ZlibF/Proof/inffast.c.origin.lean#L150) | — |
| <a id="target-zlib-inffast-spec-origin-goal-drop-preserves-origin"></a>[drop_preserves_origin](../ZlibF/Spec/Common/Inflate/InflateFastOrigin.lean#L38) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.drop_preserves_origin](../ZlibF/Proof/inffast.c.origin.lean#L41) | — |
| <a id="target-zlib-inffast-spec-origin-goal-initial-origin"></a>[initial_origin](../ZlibF/Spec/Common/Inflate/InflateFastOrigin.lean#L27) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.initial_origin](../ZlibF/Proof/inffast.c.origin.lean#L16) | — |
| <a id="target-zlib-inffast-spec-origin-goal-pull-preserves-origin"></a>[pull_preserves_origin](../ZlibF/Spec/Common/Inflate/InflateFastOrigin.lean#L32) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.pull_preserves_origin](../ZlibF/Proof/inffast.c.origin.lean#L21) | — |
| <a id="target-zlib-inffast-spec-origin-goal-rollback-preserves-origin"></a>[rollback_preserves_origin](../ZlibF/Spec/Common/Inflate/InflateFastOrigin.lean#L46) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inffast.Proofs.rollback_preserves_origin](../ZlibF/Proof/inffast.c.origin.lean#L83) | — |

<a id="group-tables"></a>

## Decode-table obligations

| Target statement | Coverage / evidence state | Contract / input range | Proof evidence | Reviewed next work |
| --- | --- | --- | --- | --- |
| <a id="target-zlib-inftrees-spec-decoderejection-goal-decode-table-classifies-input"></a>[decode_table_classifies_input](../ZlibF/Spec/Functional/Inflate/InflateDecodeTableRejection.lean#L19) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.decode_table_classifies_input](../ZlibF/Proof/inftrees.c.decode.short.lean#L62) | — |
| <a id="target-zlib-inftrees-spec-decodesemantics-goal-decode-table-matches-format"></a>[decode_table_matches_format](../ZlibF/Spec/Functional/Inflate/InflateDecodeTableSemantics.lean#L51) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.decode_table_matches_format](../ZlibF/Proof/inftrees.c.decode.semantics.lean#L327) | — |
| <a id="target-zlib-inftrees-spec-decodeshort-goal-short-decode-table-leaf-sound"></a>[short_decode_table_leaf_sound](../ZlibF/Spec/Functional/Inflate/InflateDecodeTableShort.lean#L26) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.short_decode_table_leaf_sound](../ZlibF/Proof/inftrees.c.decode.short.lean#L33) | — |
| <a id="target-zlib-inftrees-spec-decodesoundness-goal-decode-table-leaf-sound"></a>[decode_table_leaf_sound](../ZlibF/Spec/Functional/Inflate/InflateDecodeTableSoundness.lean#L31) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.decode_table_leaf_sound](../ZlibF/Proof/inftrees.c.decode.soundness.lean#L244) | — |
| <a id="target-zlib-inftrees-spec-decodetableframe-goal-decode-table-read-preserved"></a>[decode_table_read_preserved](../ZlibF/Spec/Functional/Inflate/InflateDecodeTableFrame.lean#L20) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.decode_table_read_preserved](../ZlibF/Proof/inftrees.c.decode.frame.lean#L55) | — |
| <a id="target-zlib-inftrees-spec-decodetableinvariant-goal-constructor-establishes-decode-table-invariant"></a>[constructor_establishes_decode_table_invariant](../ZlibF/Spec/Functional/Inflate/InflateDecodeTableInvariant.lean#L52) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.constructor_establishes_decode_table_invariant](../ZlibF/Proof/inftrees.c.decode.invariant.lean#L13) | — |
| <a id="target-zlib-inftrees-spec-decodetableinvariant-goal-decode-table-invariant-of-prefix"></a>[decode_table_invariant_of_prefix](../ZlibF/Spec/Functional/Inflate/InflateDecodeTableInvariant.lean#L69) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.decode_table_invariant_of_prefix](../ZlibF/Proof/inftrees.c.decode.invariant-prefix.lean#L22) | — |
| <a id="target-zlib-inftrees-spec-decodetablestability-goal-constructor-establishes-query-stability"></a>[constructor_establishes_query_stability](../ZlibF/Spec/Functional/Inflate/InflateDecodeTableStability.lean#L30) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.constructor_establishes_query_stability](../ZlibF/Proof/inftrees.c.decode.stability.lean#L190) | — |
| <a id="target-zlib-inftrees-spec-decodetablestability-goal-query-stability-of-prefix"></a>[query_stability_of_prefix](../ZlibF/Spec/Functional/Inflate/InflateDecodeTableStability.lean#L43) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.query_stability_of_prefix](../ZlibF/Proof/inftrees.c.decode.stability-rejection.lean#L20) | — |
| <a id="target-zlib-inftrees-spec-decodetablestability-goal-short-rejected-leaf-stays-invalid"></a>[short_rejected_leaf_stays_invalid](../ZlibF/Spec/Functional/Inflate/InflateDecodeTableStability.lean#L54) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.short_rejected_leaf_stays_invalid](../ZlibF/Proof/inftrees.c.decode.stability-rejection.lean#L31) | — |
| <a id="target-zlib-inftrees-spec-fasttableflags-goal-constructor-establishes-fast-leaf-flags"></a>[constructor_establishes_fast_leaf_flags](../ZlibF/Spec/Functional/Inflate/InflateFastTableFlags.lean#L52) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.constructor_establishes_fast_leaf_flags](../ZlibF/Proof/inftrees.c.decode.fast-flags.lean#L125) | — |
| <a id="target-zlib-inftrees-spec-fasttableflags-goal-fast-leaf-flags-of-prefix"></a>[fast_leaf_flags_of_prefix](../ZlibF/Spec/Functional/Inflate/InflateFastTableFlags.lean#L66) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.fast_leaf_flags_of_prefix](../ZlibF/Proof/inftrees.c.decode.fast-flags-frame.lean#L48); [ZlibF.Proof.Registration.fast_leaf_flags_of_prefix](../ZlibF/Proof/proof-registrations.lean#L20) | — |
| <a id="target-zlib-inftrees-spec-fasttableflags-goal-fixed-tables-have-fast-leaf-flags"></a>[fixed_tables_have_fast_leaf_flags](../ZlibF/Spec/Functional/Inflate/InflateFastTableFlags.lean#L76) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.fixed_tables_have_fast_leaf_flags](../ZlibF/Proof/inffixed.h.fast-flags.lean#L55); [ZlibF.Proof.Registration.fixed_tables_fast_leaf_flags](../ZlibF/Proof/proof-registrations.lean#L26) | — |
| <a id="target-zlib-inftrees-spec-fasttableflags-goal-leaf-classification-agrees"></a>[leaf_classification_agrees](../ZlibF/Spec/Functional/Inflate/InflateFastTableFlags.lean#L42) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.leaf_classification_agrees](../ZlibF/Proof/inftrees.c.decode.fast-flags-frame.lean#L9); [ZlibF.Proof.Registration.leaf_classification_agrees](../ZlibF/Proof/proof-registrations.lean#L32) | — |
| <a id="target-zlib-inftrees-spec-goal-inflate-table-content"></a>[inflate_table_content](../ZlibF/Spec/Common/Inflate/InflateTableContent.lean#L32) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.inflate_table_content](../ZlibF/Proof/inftrees.c.content.lean#L328) | — |
| <a id="target-zlib-inftrees-spec-goal-inflate-table-decoder-safe"></a>[inflate_table_decoder_safe](../ZlibF/Spec/Common/Inflate/InflateTableSafety.lean#L28) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.inflate_table_decoder_safe](../ZlibF/Proof/inftrees.c.decoder-safe.lean#L143) | — |
| <a id="target-zlib-inftrees-spec-goal-inflate-table-read-extent"></a>[inflate_table_read_extent](../ZlibF/Spec/Common/Inflate/InflateTableExtent.lean#L28) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.inflate_table_read_extent](../ZlibF/Proof/inftrees.c.read-extent.lean#L139) | — |
| <a id="target-zlib-inftrees-spec-roottable-goal-constructor-root-bits"></a>[constructor_root_bits](../ZlibF/Spec/Common/Inflate/InflateRootTable.lean#L21) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.constructor_root_bits](../ZlibF/Proof/inftrees.c.decode.bits.lean#L260) | — |
| <a id="target-zlib-inftrees-spec-subtable-goal-constructor-subtable-bits"></a>[constructor_subtable_bits](../ZlibF/Spec/Common/Inflate/InflateSubtable.lean#L26) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Inftrees.Proofs.constructor_subtable_bits](../ZlibF/Proof/inftrees.c.decode.bits.lean#L221) | — |

<a id="group-copy"></a>

## Match-copy mathematics

| Target statement | Coverage / evidence state | Contract / input range | Proof evidence | Reviewed next work |
| --- | --- | --- | --- | --- |
| <a id="target-zlibf-math-lz77copy-goal-output-copy-refines-lz77"></a>[output_copy_refines_lz77](../ZlibF/Math/LZ77CopySpec.lean#L22) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Math.LZ77Copy.output_copy_refines_lz77](../ZlibF/Math/LZ77Copy.lean#L65) | — |
| <a id="target-zlibf-math-lz77copy-goal-window-copy-refines-lz77"></a>[window_copy_refines_lz77](../ZlibF/Math/LZ77CopySpec.lean#L32) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Math.LZ77Copy.window_copy_refines_lz77](../ZlibF/Math/LZ77Copy.lean#L124) | — |
| <a id="target-zlibf-math-lz77history-goal-copy-back-compose"></a>[copy_back_compose](../ZlibF/Math/LZ77HistorySpec.lean#L21) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Math.LZ77History.copy_back_compose](../ZlibF/Math/LZ77History.lean#L31) | — |
| <a id="target-zlibf-math-lz77history-goal-copy-back-extends-history"></a>[copy_back_extends_history](../ZlibF/Math/LZ77HistorySpec.lean#L15) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Math.LZ77History.copy_back_extends_history](../ZlibF/Math/LZ77History.lean#L17) | — |
| <a id="target-zlibf-math-lz77history-goal-retained-history-agrees"></a>[retained_history_agrees](../ZlibF/Math/LZ77HistorySpec.lean#L29) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Math.LZ77History.retained_history_agrees](../ZlibF/Math/LZ77History.lean#L59) | — |
| <a id="target-zlibf-math-lz77history-goal-window-distance-check-agrees"></a>[window_distance_check_agrees](../ZlibF/Math/LZ77HistorySpec.lean#L39) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Math.LZ77History.window_distance_check_agrees](../ZlibF/Math/LZ77History.lean#L72) | — |

<a id="group-deflate"></a>

## Deflate streams

| Target statement | Coverage / evidence state | Contract / input range | Proof evidence | Reviewed next work |
| --- | --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-deflatecopy"></a>[deflateCopy](../ZlibF/Spec/Functional/Copy.lean#L46) | All stated inputs / Registered proof | [Contract](../docs/spec/api/deflate-stream.md#deflatecopy); [input range](spec/input-configurations.md#deflate-inputs) | [Zlib.Deflate.Universal.deflate_copy_public](../ZlibF/Proof/public-deflate-copy.lean#L68) | — |
| <a id="target-zlibf-spec-public-goal-deflateinit2"></a>[deflateInit2_](../ZlibF/Spec/Functional/Initialisation.lean#L25) | All stated inputs / Registered proof | [Contract](../docs/spec/api/deflate-stream.md#deflateinit2_); [input range](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.Proofs.DeflateInit2.deflateInit2_proof](../ZlibF/Proof/public-deflate-init2.lean#L18) | — |
| <a id="target-zlibf-spec-public-goal-deflateinit"></a>[deflateInit_](../ZlibF/Spec/Functional/Initialisation.lean#L32) | All stated inputs / Registered proof | [Contract](../docs/spec/api/deflate-stream.md#deflateinit_); [input range](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.Proofs.DeflateInit.deflateInit_proof](../ZlibF/Proof/public-deflate-init.lean#L162) | — |
| <a id="target-zlibf-spec-public-goal-deflategetdictionary"></a>[deflateGetDictionary](../ZlibF/Spec/Functional/Lifecycle.lean#L82) | All stated inputs / Registered proof | [Contract](../docs/spec/api/deflate-stream.md#deflategetdictionary); [input range](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.DeflateDictionaryProof.deflate_getdict_public](../ZlibF/Proof/public-deflate-getdict.lean#L12) | — |
| <a id="target-zlibf-spec-public-goal-deflateend"></a>[deflateEnd](../ZlibF/Spec/Functional/Lifecycle.lean#L92) | All stated inputs / Registered proof | [Contract](../docs/spec/api/deflate-stream.md#deflateend); [input range](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.DeflateEndProof.deflate_end_public](../ZlibF/Proof/public-deflate-end.lean#L12) | — |
| <a id="target-zlibf-spec-public-goal-deflateresetkeep"></a>[deflateResetKeep](../ZlibF/Spec/Functional/Lifecycle.lean#L102) | All stated inputs / Registered proof | [Contract](../docs/spec/api/deflate-stream.md#deflateresetkeep); [input range](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.DeflateResetKeepProof.deflate_resetkeep_public](../ZlibF/Proof/public-deflate-reset-keep.lean#L21) | — |
| <a id="target-zlibf-spec-public-goal-deflatereset"></a>[deflateReset](../ZlibF/Spec/Functional/Lifecycle.lean#L105) | All stated inputs / Registered proof | [Contract](../docs/spec/api/deflate-stream.md#deflatereset); [input range](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.DeflateResetProof.deflate_reset_public](../ZlibF/Proof/public-deflate-reset.lean#L54) | — |
| <a id="target-zlibf-spec-public-goal-deflatesetdictionary"></a>[deflateSetDictionary](../ZlibF/Spec/Functional/Lifecycle.lean#L131) | Not proved / Not proved | [Contract](../docs/spec/api/deflate-stream.md#deflatesetdictionary); [input range](spec/input-configurations.md#deflate-inputs) | — | [Start: window and hash](progress.md#readiness-deflatesetdictionary) |
| <a id="target-zlibf-spec-public-goal-deflatepending"></a>[deflatePending](../ZlibF/Spec/Functional/StreamQueries.lean#L75) | All stated inputs / Registered proof | [Contract](../docs/spec/api/deflate-stream.md#deflatepending); [input range](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.DeflateQueryProof.pending_public](../ZlibF/Proof/public-deflate-small-queries.lean#L147) | — |
| <a id="target-zlibf-spec-public-goal-deflateused"></a>[deflateUsed](../ZlibF/Spec/Functional/StreamQueries.lean#L86) | All stated inputs / Registered proof | [Contract](../docs/spec/api/deflate-stream.md#deflateused); [input range](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.DeflateQueryProof.used_public](../ZlibF/Proof/public-deflate-small-queries.lean#L50) | — |
| <a id="target-zlibf-spec-public-goal-deflatetune"></a>[deflateTune](../ZlibF/Spec/Functional/StreamQueries.lean#L94) | All stated inputs / Registered proof | [Contract](../docs/spec/api/deflate-stream.md#deflatetune); [input range](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.DeflateQueryProof.tune_public](../ZlibF/Proof/public-deflate-small-queries.lean#L63) | — |
| <a id="target-zlibf-spec-public-goal-deflatesetheader"></a>[deflateSetHeader](../ZlibF/Spec/Functional/StreamQueries.lean#L107) | All stated inputs / Registered proof | [Contract](../docs/spec/api/deflate-stream.md#deflatesetheader); [input range](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.DeflateQueryProof.header_public](../ZlibF/Proof/public-deflate-small-queries.lean#L76) | — |
| <a id="target-zlibf-spec-public-goal-deflate"></a>[deflate](../ZlibF/Spec/Functional/Streams.lean#L68) | All stated inputs / Registered proof | [Contract](../docs/spec/api/deflate-stream.md#deflate); [input range](spec/input-configurations.md#deflate-inputs) | [Zlib.Deflate.Universal.deflate_safety](../ZlibF/Proof/public-deflate-goals.lean#L21) | — |
| <a id="target-zlibf-spec-public-goal-deflatebound-z"></a>[deflateBound_z](../ZlibF/Spec/Functional/Streams.lean#L105) | Not proved / Not proved | [Contract](../docs/spec/api/deflate-stream.md#deflatebound_z); [input range](spec/input-configurations.md#deflate-inputs) | — | [Start: bound and header review](progress.md#readiness-deflatebound-z) |
| <a id="target-zlibf-spec-public-goal-deflatebound"></a>[deflateBound](../ZlibF/Spec/Functional/Streams.lean#L109) | Not proved / Not proved | [Contract](../docs/spec/api/deflate-stream.md#deflatebound); [input range](spec/input-configurations.md#deflate-inputs) | — | [Start: bound and header review](progress.md#readiness-deflatebound-z) |
| <a id="target-zlibf-spec-public-goal-deflateprime"></a>[deflatePrime](../ZlibF/Spec/Functional/Streams.lean#L114) | Not proved / Not proved | [Contract](../docs/spec/api/deflate-stream.md#deflateprime); [input range](spec/input-configurations.md#deflate-inputs) | — | [Start: compaction and bits](progress.md#readiness-deflateprime) |
| <a id="target-zlibf-spec-public-goal-deflateparams"></a>[deflateParams](../ZlibF/Spec/Functional/Streams.lean#L132) | Not proved / Not proved | [Contract](../docs/spec/api/deflate-stream.md#deflateparams); [input range](spec/input-configurations.md#deflate-inputs) | — | [Needs: block flush and parameter state](progress.md#readiness-deflateparams) |
| <a id="target-zlibf-spec-public-goal-deflate-sequence-safety"></a>[deflate_sequence_safety](../ZlibF/Spec/Safety/Sequences.lean#L19) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#deflate-inputs) | [Zlib.Deflate.Universal.deflate_sequence_safety](../ZlibF/Proof/public-deflate-goals.lean#L26) | — |
| <a id="target-zlibf-spec-public-goal-deflatecopy-safety"></a>[deflateCopy_safety](../ZlibF/Spec/Safety/Copy.lean#L24) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#deflate-inputs) | [Zlib.Deflate.Universal.deflate_copy_safety](../ZlibF/Proof/public-deflate-copy.lean#L85) | — |
| <a id="target-zlibf-spec-public-goal-deflate-refusal"></a>[deflate_refusal](../ZlibF/Spec/Safety/Refusals.lean#L50) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.RefusalProof.Deflate.deflate_refusal](../ZlibF/Proof/public-stream-refusal.lean#L89) | — |
| <a id="target-zlibf-spec-public-goal-deflate-safety"></a>[deflate_safety](../ZlibF/Spec/Safety/Streams.lean#L149) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.StreamCallSafetyProof.deflate_safety](../ZlibF/Proof/public-stream-call-safety.lean#L111) | — |
| <a id="target-zlibf-spec-public-goal-deflatesetdictionary-safety"></a>[deflateSetDictionary_safety](../ZlibF/Spec/Safety/Streams.lean#L160) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.StreamCallSafetyProof.deflateSetDictionary_safety](../ZlibF/Proof/public-stream-call-safety.lean#L116) | — |
| <a id="target-zlibf-spec-public-goal-deflategetdictionary-safety"></a>[deflateGetDictionary_safety](../ZlibF/Spec/Safety/Streams.lean#L171) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.StreamCallSafetyProof.deflateGetDictionary_safety](../ZlibF/Proof/public-stream-call-safety.lean#L121) | — |
| <a id="target-zlibf-spec-public-goal-deflatereset-safety"></a>[deflateReset_safety](../ZlibF/Spec/Safety/Streams.lean#L183) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.StreamCallSafetyProof.deflateReset_safety](../ZlibF/Proof/public-stream-call-safety.lean#L126) | — |
| <a id="target-zlibf-spec-public-goal-deflateparams-safety"></a>[deflateParams_safety](../ZlibF/Spec/Safety/Streams.lean#L193) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.StreamCallSafetyProof.deflateParams_safety](../ZlibF/Proof/public-stream-call-safety.lean#L132) | — |
| <a id="target-zlibf-spec-public-goal-deflatetune-safety"></a>[deflateTune_safety](../ZlibF/Spec/Safety/Streams.lean#L204) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.StreamCallSafetyProof.deflateTune_safety](../ZlibF/Proof/public-stream-call-safety.lean#L137) | — |
| <a id="target-zlibf-spec-public-goal-deflatebound-safety"></a>[deflateBound_safety](../ZlibF/Spec/Safety/Streams.lean#L217) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.StreamCallSafetyProof.deflateBound_safety](../ZlibF/Proof/public-stream-call-safety.lean#L142) | — |
| <a id="target-zlibf-spec-public-goal-deflatebound-z-safety"></a>[deflateBound_z_safety](../ZlibF/Spec/Safety/Streams.lean#L229) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.StreamCallSafetyProof.deflateBound_z_safety](../ZlibF/Proof/public-stream-call-safety.lean#L147) | — |
| <a id="target-zlibf-spec-public-goal-deflatepending-safety"></a>[deflatePending_safety](../ZlibF/Spec/Safety/Streams.lean#L240) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.StreamCallSafetyProof.deflatePending_safety](../ZlibF/Proof/public-stream-call-safety.lean#L152) | — |
| <a id="target-zlibf-spec-public-goal-deflateused-safety"></a>[deflateUsed_safety](../ZlibF/Spec/Safety/Streams.lean#L252) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.StreamCallSafetyProof.deflateUsed_safety](../ZlibF/Proof/public-stream-call-safety.lean#L157) | — |
| <a id="target-zlibf-spec-public-goal-deflateprime-safety"></a>[deflatePrime_safety](../ZlibF/Spec/Safety/Streams.lean#L263) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.StreamCallSafetyProof.deflatePrime_safety](../ZlibF/Proof/public-stream-call-safety.lean#L162) | — |
| <a id="target-zlibf-spec-public-goal-deflatesetheader-safety"></a>[deflateSetHeader_safety](../ZlibF/Spec/Safety/Streams.lean#L274) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.StreamCallSafetyProof.deflateSetHeader_safety](../ZlibF/Proof/public-stream-call-safety.lean#L167) | — |
| <a id="target-zlibf-spec-public-goal-deflateend-safety"></a>[deflateEnd_safety](../ZlibF/Spec/Safety/Streams.lean#L300) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.StreamCallSafetyProof.deflateEnd_safety](../ZlibF/Proof/public-stream-call-safety.lean#L183) | — |
| <a id="target-zlibf-spec-public-goal-deflateinit2-safety"></a>[deflateInit2__safety](../ZlibF/Spec/Safety/Initialisation.lean#L70) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.InitSafetyProof.deflateInit2__safety](../ZlibF/Proof/public-init-safety.lean#L175) | — |
| <a id="target-zlibf-spec-public-goal-deflateinit-safety"></a>[deflateInit__safety](../ZlibF/Spec/Safety/Initialisation.lean#L78) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#deflate-inputs) | [ZlibF.Spec.Public.InitSafetyProof.deflateInit__safety](../ZlibF/Proof/public-init-safety.lean#L195) | — |

<a id="group-back"></a>

## Callback decoding

| Target statement | Coverage / evidence state | Contract / input range | Proof evidence | Reviewed next work |
| --- | --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-inflatebackinit"></a>[inflateBackInit_](../ZlibF/Spec/Common/Back.lean#L22) | All stated inputs / Registered proof | [Contract](../docs/spec/api/inflate-back.md#inflatebackinit_); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.InflateBackInitProof.back_init_public](../ZlibF/Proof/public-infback-init.lean#L136) | — |
| <a id="target-zlibf-spec-public-goal-inflateback"></a>[inflateBack](../ZlibF/Spec/Functional/Back.lean#L19) | Not proved / Not proved | [Contract](../docs/spec/api/inflate-back.md#inflateback); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: tables, window and callbacks](progress.md#readiness-inflateback) |
| <a id="target-zlibf-spec-public-goal-inflatebackend"></a>[inflateBackEnd](../ZlibF/Spec/Common/Back.lean#L116) | All stated inputs / Registered proof | [Contract](../docs/spec/api/inflate-back.md#inflatebackend); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.InflateBackEndProof.back_end_public](../ZlibF/Proof/public-infback-end.lean#L21) | — |
| <a id="target-zlibf-spec-public-goal-inflateback-safety"></a>[inflateBack_safety](../ZlibF/Spec/Safety/Back.lean#L46) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.BackSafetyProof.inflateBack_safety](../ZlibF/Proof/public-back-safety.lean#L24) | — |
| <a id="target-zlibf-spec-public-goal-inflatebackend-safety"></a>[inflateBackEnd_safety](../ZlibF/Spec/Safety/Back.lean#L72) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.BackSafetyProof.inflateBackEnd_safety](../ZlibF/Proof/public-back-safety.lean#L32) | — |
| <a id="target-zlibf-spec-public-goal-inflatebackinit-safety"></a>[inflateBackInit__safety](../ZlibF/Spec/Safety/Back.lean#L30) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.BackSafetyProof.inflateBackInit__safety](../ZlibF/Proof/public-back-safety.lean#L47) | — |

<a id="group-gzip"></a>

## Gzip files

| Target statement | Coverage / evidence state | Contract / input range | Proof evidence | Reviewed next work |
| --- | --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-gzclose-r"></a>[gzclose_r](../ZlibF/Spec/Functional/GzClose.lean#L35) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gzclose_r); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: resource history](progress.md#readiness-gzclose-r) |
| <a id="target-zlibf-spec-public-goal-gzclose-w"></a>[gzclose_w](../ZlibF/Spec/Functional/GzClose.lean#L40) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gzclose_w); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: flush and cleanup](progress.md#readiness-gzclose-w) |
| <a id="target-zlibf-spec-public-goal-gzclose"></a>[gzclose](../ZlibF/Spec/Functional/GzClose.lean#L44) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gzclose); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: flush and cleanup](progress.md#readiness-gzclose-w) |
| <a id="target-zlibf-spec-public-goal-gzbuffer"></a>[gzbuffer](../ZlibF/Spec/Functional/GzControl.lean#L9) | All stated inputs / Registered proof | [Contract](../docs/spec/api/gz-file.md#gzbuffer); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.gzbuffer_public](../ZlibF/Proof/public-gzbuffer.lean#L50) | — |
| <a id="target-zlibf-spec-public-goal-gzeof"></a>[gzeof](../ZlibF/Spec/Functional/GzControl.lean#L19) | All stated inputs / Registered proof | [Contract](../docs/spec/api/gz-file.md#gzeof); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.gzeof_public](../ZlibF/Proof/public-gzeof.lean#L19) | — |
| <a id="target-zlibf-spec-public-goal-gztell64"></a>[gztell64](../ZlibF/Spec/Functional/GzControl.lean#L33) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gztell64); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: position history](progress.md#readiness-gztell64) |
| <a id="target-zlibf-spec-public-goal-gztell"></a>[gztell](../ZlibF/Spec/Functional/GzControl.lean#L36) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gztell); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: position history](progress.md#readiness-gztell64) |
| <a id="target-zlibf-spec-public-goal-gzoffset64"></a>[gzoffset64](../ZlibF/Spec/Functional/GzControl.lean#L50) | All stated inputs / Registered proof | [Contract](../docs/spec/api/gz-file.md#gzoffset64); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.OffsetProof.gzoffset64_public_goal](../ZlibF/Proof/public-gz-offset.lean#L232) | — |
| <a id="target-zlibf-spec-public-goal-gzoffset"></a>[gzoffset](../ZlibF/Spec/Functional/GzControl.lean#L53) | All stated inputs / Registered proof | [Contract](../docs/spec/api/gz-file.md#gzoffset); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.OffsetProof.gzoffset_public_goal](../ZlibF/Proof/public-gz-offset.lean#L245) | — |
| <a id="target-zlibf-spec-public-goal-gzerror"></a>[gzerror](../ZlibF/Spec/Functional/GzControl.lean#L60) | All stated inputs / Registered proof | [Contract](../docs/spec/api/gz-file.md#gzerror); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzErrorProof.gzerror](../ZlibF/Proof/public-gz-error.lean#L207) | — |
| <a id="target-zlibf-spec-public-goal-gzclearerr"></a>[gzclearerr](../ZlibF/Spec/Functional/GzControl.lean#L71) | All stated inputs / Registered proof | [Contract](../docs/spec/api/gz-file.md#gzclearerr); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.gzclearerr](../ZlibF/Proof/gzlib.c.public-clearerr.lean#L29) | — |
| <a id="target-zlibf-spec-public-goal-gzrewind"></a>[gzrewind](../ZlibF/Spec/Functional/GzControl.lean#L88) | All stated inputs / Registered proof | [Contract](../docs/spec/api/gz-file.md#gzrewind); [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzRewindProof.rewind_public](../ZlibF/Proof/public-gz-rewind.lean#L76) | — |
| <a id="target-zlibf-spec-public-goal-gzseek64"></a>[gzseek64](../ZlibF/Spec/Functional/GzControl.lean#L113) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gzseek64); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: seek and history](progress.md#readiness-gzseek64) |
| <a id="target-zlibf-spec-public-goal-gzseek"></a>[gzseek](../ZlibF/Spec/Functional/GzControl.lean#L116) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gzseek); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: seek and history](progress.md#readiness-gzseek64) |
| <a id="target-zlibf-spec-public-goal-gzopen"></a>[gzopen](../ZlibF/Spec/Functional/GzOpen.lean#L65) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gzopen); [input range](spec/input-configurations.md#entry-inputs) | — | [Start: open and cleanup](progress.md#readiness-gzopen) |
| <a id="target-zlibf-spec-public-goal-gzopen64"></a>[gzopen64](../ZlibF/Spec/Functional/GzOpen.lean#L70) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gzopen64); [input range](spec/input-configurations.md#entry-inputs) | — | [Start: open and cleanup](progress.md#readiness-gzopen) |
| <a id="target-zlibf-spec-public-goal-gzdopen"></a>[gzdopen](../ZlibF/Spec/Functional/GzOpen.lean#L75) | All stated inputs / Registered proof | [Contract](../docs/spec/api/gz-file.md#gzdopen); [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Gzlib.Proofs.gzdopen_complete](../ZlibF/Proof/gzlib.c.dopen-complete.lean#L28) | — |
| <a id="target-zlibf-spec-public-goal-gzread"></a>[gzread](../ZlibF/Spec/Functional/GzRead.lean#L22) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gzread); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: reader path proofs](progress.md#readiness-gzdirect) |
| <a id="target-zlibf-spec-public-goal-gzfread"></a>[gzfread](../ZlibF/Spec/Functional/GzRead.lean#L37) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gzfread); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: reader path proofs](progress.md#readiness-gzdirect) |
| <a id="target-zlibf-spec-public-goal-gzgetc"></a>[gzgetc](../ZlibF/Spec/Functional/GzRead.lean#L58) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gzgetc); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: reader path proofs](progress.md#readiness-gzdirect) |
| <a id="target-zlibf-spec-public-goal-gzgetc"></a>[gzgetc_](../ZlibF/Spec/Functional/GzRead.lean#L61) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gzgetc_); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: reader path proofs](progress.md#readiness-gzdirect) |
| <a id="target-zlibf-spec-public-goal-gzungetc"></a>[gzungetc](../ZlibF/Spec/Functional/GzRead.lean#L66) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gzungetc); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: reader path proofs](progress.md#readiness-gzdirect) |
| <a id="target-zlibf-spec-public-goal-gzgets"></a>[gzgets](../ZlibF/Spec/Functional/GzRead.lean#L80) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gzgets); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: reader path proofs](progress.md#readiness-gzdirect) |
| <a id="target-zlibf-spec-public-goal-gzdirect"></a>[gzdirect](../ZlibF/Spec/Functional/GzRead.lean#L103) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gzdirect); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: reader path proofs](progress.md#readiness-gzdirect) |
| <a id="target-zlibf-spec-public-goal-gzwrite"></a>[gzwrite](../ZlibF/Spec/Functional/GzWrite.lean#L28) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gzwrite); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: writer path proofs](progress.md#readiness-gzwrite) |
| <a id="target-zlibf-spec-public-goal-gzfwrite"></a>[gzfwrite](../ZlibF/Spec/Functional/GzWrite.lean#L43) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gzfwrite); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: writer path proofs](progress.md#readiness-gzwrite) |
| <a id="target-zlibf-spec-public-goal-gzputc"></a>[gzputc](../ZlibF/Spec/Functional/GzWrite.lean#L59) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gzputc); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: writer path proofs](progress.md#readiness-gzwrite) |
| <a id="target-zlibf-spec-public-goal-gzputs"></a>[gzputs](../ZlibF/Spec/Functional/GzWrite.lean#L71) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gzputs); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: writer path proofs](progress.md#readiness-gzwrite) |
| <a id="target-zlibf-spec-public-goal-gzvprintf"></a>[gzvprintf](../ZlibF/Spec/Functional/GzWrite.lean#L108) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gzvprintf); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: writer path proofs](progress.md#readiness-gzwrite) |
| <a id="target-zlibf-spec-public-goal-gzprintf"></a>[gzprintf](../ZlibF/Spec/Functional/GzWrite.lean#L112) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gzprintf); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: writer path proofs](progress.md#readiness-gzwrite) |
| <a id="target-zlibf-spec-public-goal-gzflush"></a>[gzflush](../ZlibF/Spec/Functional/GzWrite.lean#L117) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gzflush); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: writer path proofs](progress.md#readiness-gzwrite) |
| <a id="target-zlibf-spec-public-goal-gzsetparams"></a>[gzsetparams](../ZlibF/Spec/Functional/GzWrite.lean#L134) | Not proved / Not proved | [Contract](../docs/spec/api/gz-file.md#gzsetparams); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: writer path proofs](progress.md#readiness-gzwrite) |
| <a id="target-zlibf-spec-public-goal-gz-sequence-safety"></a>[gz_sequence_safety](../ZlibF/Spec/Safety/GzSafety.lean#L144) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.gz_sequence_safety_public](../ZlibF/Proof/public-gz-sequence-safety.lean#L25) | — |
| <a id="target-zlibf-spec-public-goal-gz-refusal"></a>[gz_refusal](../ZlibF/Spec/Common/GzRefusal.lean#L39) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzRefusalProof.gz_refusal](../ZlibF/Proof/public-gz-refusal.lean#L17) | — |
| <a id="target-zlibf-spec-public-goal-gz-sequence-nonvacuity"></a>[gz_sequence_nonvacuity](../ZlibF/Spec/Safety/GzSafety.lean#L179) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.GzNonvacuity.gz_sequence_nonvacuity_public](../ZlibF/Proof/public-gz-sequence-nonvacuity.lean#L268) | — |
| <a id="target-zlibf-spec-public-goal-gzbuffer-safety"></a>[gzbuffer_safety](../ZlibF/Spec/Safety/GzCalls.lean#L45) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzbuffer_safety](../ZlibF/Proof/public-gz-call-safety.lean#L26) | — |
| <a id="target-zlibf-spec-public-goal-gzclearerr-safety"></a>[gzclearerr_safety](../ZlibF/Spec/Safety/GzCalls.lean#L52) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzclearerr_safety](../ZlibF/Proof/public-gz-call-safety.lean#L30) | — |
| <a id="target-zlibf-spec-public-goal-gzclose-safety"></a>[gzclose_safety](../ZlibF/Spec/Safety/GzCalls.lean#L252) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzclose_safety](../ZlibF/Proof/public-gz-call-safety.lean#L130) | — |
| <a id="target-zlibf-spec-public-goal-gzclose-r-safety"></a>[gzclose_r_safety](../ZlibF/Spec/Safety/GzCalls.lean#L260) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzclose_r_safety](../ZlibF/Proof/public-gz-call-safety.lean#L134) | — |
| <a id="target-zlibf-spec-public-goal-gzclose-w-safety"></a>[gzclose_w_safety](../ZlibF/Spec/Safety/GzCalls.lean#L268) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzclose_w_safety](../ZlibF/Proof/public-gz-call-safety.lean#L138) | — |
| <a id="target-zlibf-spec-public-goal-gzdirect-safety"></a>[gzdirect_safety](../ZlibF/Spec/Safety/GzCalls.lean#L59) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzdirect_safety](../ZlibF/Proof/public-gz-call-safety.lean#L34) | — |
| <a id="target-zlibf-spec-public-goal-gzdopen-safety"></a>[gzdopen_safety](../ZlibF/Spec/Safety/GzCalls.lean#L286) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzdopen_safety](../ZlibF/Proof/public-gz-call-safety.lean#L147) | — |
| <a id="target-zlibf-spec-public-goal-gzeof-safety"></a>[gzeof_safety](../ZlibF/Spec/Safety/GzCalls.lean#L66) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzeof_safety](../ZlibF/Proof/public-gz-call-safety.lean#L38) | — |
| <a id="target-zlibf-spec-public-goal-gzerror-safety"></a>[gzerror_safety](../ZlibF/Spec/Safety/GzCalls.lean#L239) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzerror_safety](../ZlibF/Proof/public-gz-call-safety.lean#L126) | — |
| <a id="target-zlibf-spec-public-goal-gzflush-safety"></a>[gzflush_safety](../ZlibF/Spec/Safety/GzCalls.lean#L73) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzflush_safety](../ZlibF/Proof/public-gz-call-safety.lean#L42) | — |
| <a id="target-zlibf-spec-public-goal-gzfread-safety"></a>[gzfread_safety](../ZlibF/Spec/Safety/GzCalls.lean#L81) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzfread_safety](../ZlibF/Proof/public-gz-call-safety.lean#L46) | — |
| <a id="target-zlibf-spec-public-goal-gzfwrite-safety"></a>[gzfwrite_safety](../ZlibF/Spec/Safety/GzCalls.lean#L89) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzfwrite_safety](../ZlibF/Proof/public-gz-call-safety.lean#L50) | — |
| <a id="target-zlibf-spec-public-goal-gzgetc-safety"></a>[gzgetc_safety](../ZlibF/Spec/Safety/GzCalls.lean#L224) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzgetc_safety](../ZlibF/Proof/public-gz-call-safety.lean#L122) | — |
| <a id="target-zlibf-spec-public-goal-gzgetc-safety"></a>[gzgetc__safety](../ZlibF/Spec/Safety/GzCalls.lean#L97) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzgetc__safety](../ZlibF/Proof/public-gz-call-safety.lean#L54) | — |
| <a id="target-zlibf-spec-public-goal-gzgets-safety"></a>[gzgets_safety](../ZlibF/Spec/Safety/GzCalls.lean#L104) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzgets_safety](../ZlibF/Proof/public-gz-call-safety.lean#L58) | — |
| <a id="target-zlibf-spec-public-goal-gzoffset-safety"></a>[gzoffset_safety](../ZlibF/Spec/Safety/GzCalls.lean#L111) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzoffset_safety](../ZlibF/Proof/public-gz-call-safety.lean#L62) | — |
| <a id="target-zlibf-spec-public-goal-gzoffset64-safety"></a>[gzoffset64_safety](../ZlibF/Spec/Safety/GzCalls.lean#L118) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzoffset64_safety](../ZlibF/Proof/public-gz-call-safety.lean#L66) | — |
| <a id="target-zlibf-spec-public-goal-gzopen-safety"></a>[gzopen_safety](../ZlibF/Spec/Safety/GzCalls.lean#L276) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzopen_safety](../ZlibF/Proof/public-gz-call-safety.lean#L141) | — |
| <a id="target-zlibf-spec-public-goal-gzopen64-safety"></a>[gzopen64_safety](../ZlibF/Spec/Safety/GzCalls.lean#L281) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzopen64_safety](../ZlibF/Proof/public-gz-call-safety.lean#L144) | — |
| <a id="target-zlibf-spec-public-goal-gzprintf-safety"></a>[gzprintf_safety](../ZlibF/Spec/Safety/GzCalls.lean#L125) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzprintf_safety](../ZlibF/Proof/public-gz-call-safety.lean#L70) | — |
| <a id="target-zlibf-spec-public-goal-gzvprintf-safety"></a>[gzvprintf_safety](../ZlibF/Spec/Safety/GzCalls.lean#L134) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzvprintf_safety](../ZlibF/Proof/public-gz-call-safety.lean#L74) | — |
| <a id="target-zlibf-spec-public-goal-gzputc-safety"></a>[gzputc_safety](../ZlibF/Spec/Safety/GzCalls.lean#L142) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzputc_safety](../ZlibF/Proof/public-gz-call-safety.lean#L78) | — |
| <a id="target-zlibf-spec-public-goal-gzputs-safety"></a>[gzputs_safety](../ZlibF/Spec/Safety/GzCalls.lean#L149) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzputs_safety](../ZlibF/Proof/public-gz-call-safety.lean#L82) | — |
| <a id="target-zlibf-spec-public-goal-gzread-safety"></a>[gzread_safety](../ZlibF/Spec/Safety/GzCalls.lean#L156) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzread_safety](../ZlibF/Proof/public-gz-call-safety.lean#L86) | — |
| <a id="target-zlibf-spec-public-goal-gzrewind-safety"></a>[gzrewind_safety](../ZlibF/Spec/Safety/GzCalls.lean#L163) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzrewind_safety](../ZlibF/Proof/public-gz-call-safety.lean#L90) | — |
| <a id="target-zlibf-spec-public-goal-gzseek-safety"></a>[gzseek_safety](../ZlibF/Spec/Safety/GzCalls.lean#L170) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzseek_safety](../ZlibF/Proof/public-gz-call-safety.lean#L94) | — |
| <a id="target-zlibf-spec-public-goal-gzseek64-safety"></a>[gzseek64_safety](../ZlibF/Spec/Safety/GzCalls.lean#L178) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzseek64_safety](../ZlibF/Proof/public-gz-call-safety.lean#L98) | — |
| <a id="target-zlibf-spec-public-goal-gzsetparams-safety"></a>[gzsetparams_safety](../ZlibF/Spec/Safety/GzCalls.lean#L186) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzsetparams_safety](../ZlibF/Proof/public-gz-call-safety.lean#L102) | — |
| <a id="target-zlibf-spec-public-goal-gztell-safety"></a>[gztell_safety](../ZlibF/Spec/Safety/GzCalls.lean#L194) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gztell_safety](../ZlibF/Proof/public-gz-call-safety.lean#L106) | — |
| <a id="target-zlibf-spec-public-goal-gztell64-safety"></a>[gztell64_safety](../ZlibF/Spec/Safety/GzCalls.lean#L201) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gztell64_safety](../ZlibF/Proof/public-gz-call-safety.lean#L110) | — |
| <a id="target-zlibf-spec-public-goal-gzungetc-safety"></a>[gzungetc_safety](../ZlibF/Spec/Safety/GzCalls.lean#L208) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzungetc_safety](../ZlibF/Proof/public-gz-call-safety.lean#L114) | — |
| <a id="target-zlibf-spec-public-goal-gzwrite-safety"></a>[gzwrite_safety](../ZlibF/Spec/Safety/GzCalls.lean#L215) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.GzCallSafetyProof.gzwrite_safety](../ZlibF/Proof/public-gz-call-safety.lean#L118) | — |

<a id="group-buffers"></a>

## Whole-buffer operations

| Target statement | Coverage / evidence state | Contract / input range | Proof evidence | Reviewed next work |
| --- | --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-compress2-z"></a>[compress2_z](../ZlibF/Spec/Functional/Utilities.lean#L43) | Not proved / Not proved | [Contract](../docs/spec/api/utility.md#compress2_z); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: compressor execution](progress.md#readiness-compress2-z) |
| <a id="target-zlibf-spec-public-goal-compress2"></a>[compress2](../ZlibF/Spec/Functional/Utilities.lean#L48) | Not proved / Not proved | [Contract](../docs/spec/api/utility.md#compress2); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: compressor execution](progress.md#readiness-compress2-z) |
| <a id="target-zlibf-spec-public-goal-compress-z"></a>[compress_z](../ZlibF/Spec/Functional/Utilities.lean#L55) | Not proved / Not proved | [Contract](../docs/spec/api/utility.md#compress_z); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: compressor execution](progress.md#readiness-compress2-z) |
| <a id="target-zlibf-spec-public-goal-compress"></a>[compress](../ZlibF/Spec/Functional/Utilities.lean#L60) | Not proved / Not proved | [Contract](../docs/spec/api/utility.md#compress); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: compressor execution](progress.md#readiness-compress2-z) |
| <a id="target-zlibf-spec-public-goal-uncompress2-z"></a>[uncompress2_z](../ZlibF/Spec/Functional/Utilities.lean#L101) | Not proved / Not proved | [Contract](../docs/spec/api/utility.md#uncompress2_z); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: decoder execution](progress.md#readiness-uncompress2-z) |
| <a id="target-zlibf-spec-public-goal-uncompress2"></a>[uncompress2](../ZlibF/Spec/Functional/Utilities.lean#L105) | Not proved / Not proved | [Contract](../docs/spec/api/utility.md#uncompress2); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: decoder execution](progress.md#readiness-uncompress2-z) |
| <a id="target-zlibf-spec-public-goal-uncompress-z"></a>[uncompress_z](../ZlibF/Spec/Functional/Utilities.lean#L133) | Not proved / Not proved | [Contract](../docs/spec/api/utility.md#uncompress_z); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: decoder execution](progress.md#readiness-uncompress2-z) |
| <a id="target-zlibf-spec-public-goal-uncompress"></a>[uncompress](../ZlibF/Spec/Functional/Utilities.lean#L137) | Not proved / Not proved | [Contract](../docs/spec/api/utility.md#uncompress); [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: decoder execution](progress.md#readiness-uncompress2-z) |
| <a id="target-zlibf-spec-public-goal-uncompress2-z-safe"></a>[uncompress2_z_safe](../ZlibF/Spec/Safety/Utilities.lean#L34) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.Uncompress.uncompress2_z_safe](../ZlibF/Proof/public-uncompress-safe.lean#L300) | — |
| <a id="target-zlibf-spec-public-goal-uncompress2-safe"></a>[uncompress2_safe](../ZlibF/Spec/Safety/Utilities.lean#L37) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.Uncompress.uncompress2_safe](../ZlibF/Proof/public-uncompress-safe.lean#L304) | — |
| <a id="target-zlibf-spec-public-goal-uncompress-z-safe"></a>[uncompress_z_safe](../ZlibF/Spec/Safety/Utilities.lean#L40) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.Uncompress.uncompress_z_safe](../ZlibF/Proof/public-uncompress-safe.lean#L308) | — |
| <a id="target-zlibf-spec-public-goal-uncompress-safe"></a>[uncompress_safe](../ZlibF/Spec/Safety/Utilities.lean#L43) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.Uncompress.uncompress_safe](../ZlibF/Proof/public-uncompress-safe.lean#L314) | — |
| <a id="target-zlibf-spec-public-goal-compress2-z-safety"></a>[compress2_z_safety](../ZlibF/Spec/Safety/Utilities.lean#L14) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.Compress.compress2_z_safety](../ZlibF/Proof/public-compress-safe-mid.lean#L116) | — |
| <a id="target-zlibf-spec-public-goal-compress2-safety"></a>[compress2_safety](../ZlibF/Spec/Safety/Utilities.lean#L18) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.Compress.compress2_safety](../ZlibF/Proof/public-compress-safe-mid.lean#L124) | — |
| <a id="target-zlibf-spec-public-goal-compress-z-safety"></a>[compress_z_safety](../ZlibF/Spec/Safety/Utilities.lean#L24) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.Compress.compress_z_safety](../ZlibF/Proof/public-compress-safe-mid.lean#L120) | — |
| <a id="target-zlibf-spec-public-goal-compress-safety"></a>[compress_safety](../ZlibF/Spec/Safety/Utilities.lean#L28) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.Compress.compress_safety](../ZlibF/Proof/public-compress-safe-mid.lean#L128) | — |
| <a id="target-zlibf-spec-public-goal-zlibversion-safety"></a>[zlibVersion_safety](../ZlibF/Spec/Safety/Queries.lean#L18) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.StatelessSafetyProof.zlibVersion_safety](../ZlibF/Proof/public-stateless-safety.lean#L75) | — |
| <a id="target-zlibf-spec-public-goal-zlibcompileflags-safety"></a>[zlibCompileFlags_safety](../ZlibF/Spec/Safety/Queries.lean#L23) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.StatelessSafetyProof.zlibCompileFlags_safety](../ZlibF/Proof/public-stateless-safety.lean#L80) | — |

<a id="group-models"></a>

## Format and API models

| Target statement | Coverage / evidence state | Contract / input range | Proof evidence | Reviewed next work |
| --- | --- | --- | --- | --- |
| <a id="target-zlibf-spec-api-goal-format-deterministic"></a>[format_deterministic](../ZlibF/Spec/Functional/Api/Goals.lean#L42) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.format_deterministic](../ZlibF/Proof/Format/Api.lean#L51) | — |
| <a id="target-zlibf-spec-api-goal-format-prefix-free"></a>[format_prefix_free](../ZlibF/Spec/Functional/Api/Goals.lean#L47) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.format_prefix_free](../ZlibF/Proof/Format/Api.lean#L56) | — |
| <a id="target-zlibf-spec-api-goal-inflate-decodes"></a>[inflate_decodes](../ZlibF/Spec/Functional/Api/Goals.lean#L58) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.inflate_decodes](../ZlibF/Proof/Api/Inflate.lean#L346) | — |
| <a id="target-zlibf-spec-api-goal-inflate-completes"></a>[inflate_completes](../ZlibF/Spec/Functional/Api/Goals.lean#L69) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.inflate_completes](../ZlibF/Proof/Api/Inflate.lean#L353) | — |
| <a id="target-zlibf-spec-api-goal-inflate-rejects-invalid"></a>[inflate_rejects_invalid](../ZlibF/Spec/Functional/Api/Goals.lean#L84) | Not proved / Not proved | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | — | Prerequisites unreviewed |
| <a id="target-zlibf-spec-api-goal-deflate-valid"></a>[deflate_valid](../ZlibF/Spec/Functional/Api/Goals.lean#L99) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.deflate_valid](../ZlibF/Proof/Api/Deflate.lean#L181) | — |
| <a id="target-zlibf-spec-api-goal-deflate-completes"></a>[deflate_completes](../ZlibF/Spec/Functional/Api/Goals.lean#L106) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.deflate_completes](../ZlibF/Proof/Api/DeflateBounds.lean#L164) | — |
| <a id="target-zlibf-spec-api-goal-deflate-full-flush-resync"></a>[deflate_full_flush_resync](../ZlibF/Spec/Functional/Api/Goals.lean#L116) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.deflate_full_flush_resync](../ZlibF/Proof/Api/DeflateFlush.lean#L169) | — |
| <a id="target-zlibf-spec-api-goal-roundtrip"></a>[roundtrip](../ZlibF/Spec/Functional/Api/Goals.lean#L134) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.roundtrip](../ZlibF/Proof/Api/GzipRoundtrip.lean#L177) | — |
| <a id="target-zlibf-spec-api-goal-roundtrip-completes"></a>[roundtrip_completes](../ZlibF/Spec/Functional/Api/Goals.lean#L143) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.roundtrip_completes](../ZlibF/Proof/Api/GzipRoundtrip.lean#L186) | — |
| <a id="target-zlibf-spec-api-goal-dict-roundtrip"></a>[dict_roundtrip](../ZlibF/Spec/Functional/Api/Goals.lean#L162) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.dict_roundtrip](../ZlibF/Proof/Api/DictionaryRoundtrip.lean#L121) | — |
| <a id="target-zlibf-spec-api-goal-header-roundtrip"></a>[header_roundtrip](../ZlibF/Spec/Functional/Api/Goals.lean#L180) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.header_roundtrip](../ZlibF/Proof/Api/HeaderRoundtrip.lean#L89) | — |
| <a id="target-zlibf-spec-api-goal-deflate-bound-adequate"></a>[deflate_bound_adequate](../ZlibF/Spec/Functional/Api/Goals.lean#L189) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.deflate_bound_adequate](../ZlibF/Proof/Api/DeflateBounds.lean#L103) | — |
| <a id="target-zlibf-spec-api-goal-compress-bound-adequate"></a>[compress_bound_adequate](../ZlibF/Spec/Functional/Api/Goals.lean#L196) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.compress_bound_adequate](../ZlibF/Proof/Api/Compress.lean#L8) | — |
| <a id="target-zlibf-spec-api-goal-compress-roundtrip"></a>[compress_roundtrip](../ZlibF/Spec/Functional/Api/Goals.lean#L203) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.compress_roundtrip](../ZlibF/Proof/Api/CompressRoundtrip.lean#L32) | — |
| <a id="target-zlibf-spec-api-goal-gz-roundtrip"></a>[gz_roundtrip](../ZlibF/Spec/Functional/Api/Goals.lean#L214) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.gz_roundtrip](../ZlibF/Proof/Api/GzRoundtrip.lean#L15) | — |
| <a id="target-zlibf-spec-api-goal-gz-seek-read"></a>[gz_seek_read](../ZlibF/Spec/Functional/Api/Goals.lean#L221) | All stated inputs / Locally checked | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.gz_seek_read](../ZlibF/Proof/Api/GzSeekRead.lean#L15) | — |
| <a id="target-zlibf-spec-api-goal-compress-bound-value"></a>[compress_bound_value](../ZlibF/Spec/Functional/Api/Concrete.lean#L57) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.compress_bound_value](../ZlibF/Proof/Api/Concrete.lean#L57) | — |
| <a id="target-zlibf-spec-api-goal-compress2-z-first-alloc-failure"></a>[compress2_z_first_alloc_failure](../ZlibF/Spec/Functional/Api/Concrete.lean#L67) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.compress2_z_first_alloc_failure](../ZlibF/Proof/Api/CompressFailure.lean#L29) | — |
| <a id="target-zlibf-spec-api-goal-inflate-deferred-distance"></a>[inflate_deferred_distance](../ZlibF/Spec/Functional/Api/Inflate.lean#L267) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Api.Proofs.inflate_deferred_distance](../ZlibF/Proof/Api/InflateCausality.lean#L244) | — |

<a id="group-lifecycle"></a>

## Lifecycles and call sequences

| Target statement | Coverage / evidence state | Contract / input range | Proof evidence | Reviewed next work |
| --- | --- | --- | --- | --- |
| <a id="target-zlibf-spec-public-goal-inflate-sequence"></a>[inflate_sequence](../ZlibF/Spec/Functional/Sequences.lean#L173) | Not proved / Not proved | Exact target statement; [input range](spec/input-configurations.md#inflate-inputs) | — | [Needs: execution and format](progress.md#readiness-inflate-sequence) |
| <a id="target-zlibf-spec-public-goal-deflate-sequence"></a>[deflate_sequence](../ZlibF/Spec/Functional/Sequences.lean#L193) | Not proved / Not proved | Exact target statement; [input range](spec/input-configurations.md#deflate-inputs) | — | [Needs: execution and format](progress.md#readiness-inflate-sequence) |
| <a id="target-zlibf-spec-public-goal-inflate-back-sequence"></a>[inflate_back_sequence](../ZlibF/Spec/Functional/Sequences.lean#L230) | Not proved / Not proved | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: execution and format](progress.md#readiness-inflate-sequence) |
| <a id="target-zlibf-spec-public-goal-gz-sequence"></a>[gz_sequence](../ZlibF/Spec/Functional/GzSequence.lean#L48) | Not proved / Not proved | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | — | [Needs: execution and format](progress.md#readiness-inflate-sequence) |
| <a id="target-zlibf-spec-public-goal-inflate-initialisation-domain"></a>[inflate_initialisation_domain](../ZlibF/Spec/Safety/Domains.lean#L15) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.InflateInit.inflate_initialisation_domain_public](../ZlibF/Proof/public-inflate-init.lean#L266) | — |
| <a id="target-zlibf-spec-public-goal-deflate-initialisation-domain"></a>[deflate_initialisation_domain](../ZlibF/Spec/Safety/Domains.lean#L28) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.Proofs.DeflateInitDomain.deflate_initialisation_domain_public](../ZlibF/Proof/public-deflate-init-domain.lean#L39) | — |
| <a id="target-zlibf-spec-public-goal-inflate-back-initialisation-domain"></a>[inflate_back_initialisation_domain](../ZlibF/Spec/Common/Domains.lean#L24) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Public.InflateBackInitProof.back_init_domain_public](../ZlibF/Proof/public-infback-init.lean#L231) | — |
| <a id="target-zlibf-spec-public-goal-gz-initialisation-domain"></a>[gz_initialisation_domain](../ZlibF/Spec/Functional/GzSequence.lean#L28) | Not proved / Not planned | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | — | [Not planned](#scope) |

<a id="group-internal"></a>

## Internal proof obligations

| Target statement | Coverage / evidence state | Contract / input range | Proof evidence | Reviewed next work |
| --- | --- | --- | --- | --- |
| <a id="target-zlib-crc32-spec-byteviews-goal-crc32-z-all-byte-views"></a>[crc32_z_all_byte_views](../ZlibF/Spec/Functional/Crc32ByteViews.lean#L18) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Crc32.Proofs.crc32_z_all_byte_views](../ZlibF/Proof/crc32.c.views.lean#L568) | — |
| <a id="target-zlib-crc32-spec-byteviews-goal-crc32-all-byte-views"></a>[crc32_all_byte_views](../ZlibF/Spec/Functional/Crc32ByteViews.lean#L29) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [Zlib.Crc32.Proofs.crc32_all_byte_views](../ZlibF/Proof/crc32.c.views.lean#L574) | — |
| <a id="target-zlibf-spec-token-goal-rejected-has-no-symbols"></a>[rejected_has_no_symbols](../ZlibF/Spec/Functional/Format/Token.lean#L84) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Token.rejected_has_no_symbols](../ZlibF/Proof/Format/Token.lean#L49) | — |
| <a id="target-zlibf-spec-token-goal-step-composes-symbols"></a>[step_composes_symbols](../ZlibF/Spec/Functional/Format/Token.lean#L62) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Token.step_composes_symbols](../ZlibF/Proof/Format/Token.lean#L15) | — |
| <a id="target-zlibf-spec-token-goal-symbols-exposes-step"></a>[symbols_exposes_step](../ZlibF/Spec/Functional/Format/Token.lean#L73) | All stated inputs / Registered proof | Exact target statement; [input range](spec/input-configurations.md#entry-inputs) | [ZlibF.Spec.Token.symbols_exposes_step](../ZlibF/Proof/Format/Token.lean#L35) | — |

## Observed proof dependencies

A theorem for the destination actually uses a proof of the source target.

| Source | Destination |
| --- | --- |
| [pointer_advance_preserves_low_bits](#target-c-byteaddress-spec-goal-pointer-advance-preserves-low-bits) | [first_aligned_offset](#target-c-byteaddress-spec-goal-first-aligned-offset) |
| [crc32_all_byte_views](#target-zlib-crc32-spec-byteviews-goal-crc32-all-byte-views) | [crc32](#target-zlibf-spec-public-goal-crc32) |
| [crc32_all_byte_views](#target-zlib-crc32-spec-byteviews-goal-crc32-all-byte-views) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [crc32_all_byte_views](#target-zlib-crc32-spec-byteviews-goal-crc32-all-byte-views) | [inflate](#target-zlibf-spec-public-goal-inflate) |
| [crc32_all_byte_views](#target-zlib-crc32-spec-byteviews-goal-crc32-all-byte-views) | [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy) |
| [crc32_all_byte_views](#target-zlib-crc32-spec-byteviews-goal-crc32-all-byte-views) | [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety) |
| [crc32_all_byte_views](#target-zlib-crc32-spec-byteviews-goal-crc32-all-byte-views) | [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe) |
| [crc32_all_byte_views](#target-zlib-crc32-spec-byteviews-goal-crc32-all-byte-views) | [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe) |
| [crc32_all_byte_views](#target-zlib-crc32-spec-byteviews-goal-crc32-all-byte-views) | [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe) |
| [crc32_all_byte_views](#target-zlib-crc32-spec-byteviews-goal-crc32-all-byte-views) | [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [crc32_z_all_byte_views](#target-zlib-crc32-spec-byteviews-goal-crc32-z-all-byte-views) | [crc32_z](#target-zlibf-spec-public-goal-crc32-z) |
| [actual_body_preserves_origin](#target-zlib-inffast-spec-bodyorigin-goal-actual-body-preserves-origin) | [actual_fast_preserves_origin](#target-zlib-inffast-spec-callorigin-goal-actual-fast-preserves-origin) |
| [actual_fast_preserves_origin](#target-zlib-inffast-spec-callorigin-goal-actual-fast-preserves-origin) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [actual_fast_preserves_origin](#target-zlib-inffast-spec-callorigin-goal-actual-fast-preserves-origin) | [inflate](#target-zlibf-spec-public-goal-inflate) |
| [actual_fast_preserves_origin](#target-zlib-inffast-spec-callorigin-goal-actual-fast-preserves-origin) | [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy) |
| [actual_fast_preserves_origin](#target-zlib-inffast-spec-callorigin-goal-actual-fast-preserves-origin) | [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety) |
| [actual_fast_preserves_origin](#target-zlib-inffast-spec-callorigin-goal-actual-fast-preserves-origin) | [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe) |
| [actual_fast_preserves_origin](#target-zlib-inffast-spec-callorigin-goal-actual-fast-preserves-origin) | [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe) |
| [actual_fast_preserves_origin](#target-zlib-inffast-spec-callorigin-goal-actual-fast-preserves-origin) | [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe) |
| [actual_fast_preserves_origin](#target-zlib-inffast-spec-callorigin-goal-actual-fast-preserves-origin) | [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [actual_distance_block_preserves_origin](#target-zlib-inffast-spec-distanceorigin-goal-actual-distance-block-preserves-origin) | [actual_body_preserves_origin](#target-zlib-inffast-spec-bodyorigin-goal-actual-body-preserves-origin) |
| [actual_distance_refines_lz77](#target-zlib-inffast-spec-distanceresult-goal-actual-distance-refines-lz77) | [actual_body_refines_token](#target-zlib-inffast-spec-bodytoken-goal-actual-body-refines-token) |
| [distance_lookup_matches_format](#target-zlib-inffast-spec-distancesemantics-goal-distance-lookup-matches-format) | [actual_distance_refines_lz77](#target-zlib-inffast-spec-distanceresult-goal-actual-distance-refines-lz77) |
| [fast_safe](#target-zlib-inffast-spec-goal-fast-safe) | [actual_fast_preserves_origin](#target-zlib-inffast-spec-callorigin-goal-actual-fast-preserves-origin) |
| [step_safe](#target-zlib-inffast-spec-goal-step-safe) | [actual_body_refines_token](#target-zlib-inffast-spec-bodytoken-goal-actual-body-refines-token) |
| [step_safe](#target-zlib-inffast-spec-goal-step-safe) | [actual_body_retains_selected_length](#target-zlib-inffast-spec-lengthtrace-goal-actual-body-retains-selected-length) |
| [length_lookup_matches_format](#target-zlib-inffast-spec-lengthsemantics-goal-length-lookup-matches-format) | [actual_body_refines_token](#target-zlib-inffast-spec-bodytoken-goal-actual-body-refines-token) |
| [actual_copy_match_refines_lz77](#target-zlib-inffast-spec-matchhistory-goal-actual-copy-match-refines-lz77) | [actual_distance_refines_lz77](#target-zlib-inffast-spec-distanceresult-goal-actual-distance-refines-lz77) |
| [match_array_refines_lz77](#target-zlib-inffast-spec-matchhistory-goal-match-array-refines-lz77) | [actual_copy_match_refines_lz77](#target-zlib-inffast-spec-matchhistory-goal-actual-copy-match-refines-lz77) |
| [actual_drop_preserves_origin](#target-zlib-inffast-spec-origin-goal-actual-drop-preserves-origin) | [actual_body_preserves_origin](#target-zlib-inffast-spec-bodyorigin-goal-actual-body-preserves-origin) |
| [actual_rollback_preserves_origin](#target-zlib-inffast-spec-origin-goal-actual-rollback-preserves-origin) | [actual_fast_preserves_origin](#target-zlib-inffast-spec-callorigin-goal-actual-fast-preserves-origin) |
| [drop_preserves_origin](#target-zlib-inffast-spec-origin-goal-drop-preserves-origin) | [actual_distance_block_preserves_origin](#target-zlib-inffast-spec-distanceorigin-goal-actual-distance-block-preserves-origin) |
| [drop_preserves_origin](#target-zlib-inffast-spec-origin-goal-drop-preserves-origin) | [actual_drop_preserves_origin](#target-zlib-inffast-spec-origin-goal-actual-drop-preserves-origin) |
| [initial_origin](#target-zlib-inffast-spec-origin-goal-initial-origin) | [actual_fast_preserves_origin](#target-zlib-inffast-spec-callorigin-goal-actual-fast-preserves-origin) |
| [pull_preserves_origin](#target-zlib-inffast-spec-origin-goal-pull-preserves-origin) | [actual_body_preserves_origin](#target-zlib-inffast-spec-bodyorigin-goal-actual-body-preserves-origin) |
| [pull_preserves_origin](#target-zlib-inffast-spec-origin-goal-pull-preserves-origin) | [actual_distance_block_preserves_origin](#target-zlib-inffast-spec-distanceorigin-goal-actual-distance-block-preserves-origin) |
| [pull_preserves_origin](#target-zlib-inffast-spec-origin-goal-pull-preserves-origin) | [actual_pull_preserves_origin](#target-zlib-inffast-spec-origin-goal-actual-pull-preserves-origin) |
| [rollback_preserves_origin](#target-zlib-inffast-spec-origin-goal-rollback-preserves-origin) | [actual_rollback_preserves_origin](#target-zlib-inffast-spec-origin-goal-actual-rollback-preserves-origin) |
| [decode_table_classifies_input](#target-zlib-inftrees-spec-decoderejection-goal-decode-table-classifies-input) | [constructor_establishes_decode_table_invariant](#target-zlib-inftrees-spec-decodetableinvariant-goal-constructor-establishes-decode-table-invariant) |
| [decode_table_matches_format](#target-zlib-inftrees-spec-decodesemantics-goal-decode-table-matches-format) | [decode_table_classifies_input](#target-zlib-inftrees-spec-decoderejection-goal-decode-table-classifies-input) |
| [short_decode_table_leaf_sound](#target-zlib-inftrees-spec-decodeshort-goal-short-decode-table-leaf-sound) | [constructor_establishes_decode_table_invariant](#target-zlib-inftrees-spec-decodetableinvariant-goal-constructor-establishes-decode-table-invariant) |
| [decode_table_leaf_sound](#target-zlib-inftrees-spec-decodesoundness-goal-decode-table-leaf-sound) | [decode_table_classifies_input](#target-zlib-inftrees-spec-decoderejection-goal-decode-table-classifies-input) |
| [decode_table_leaf_sound](#target-zlib-inftrees-spec-decodesoundness-goal-decode-table-leaf-sound) | [short_decode_table_leaf_sound](#target-zlib-inftrees-spec-decodeshort-goal-short-decode-table-leaf-sound) |
| [decode_table_read_preserved](#target-zlib-inftrees-spec-decodetableframe-goal-decode-table-read-preserved) | [decode_table_invariant_of_prefix](#target-zlib-inftrees-spec-decodetableinvariant-goal-decode-table-invariant-of-prefix) |
| [decode_table_read_preserved](#target-zlib-inftrees-spec-decodetableframe-goal-decode-table-read-preserved) | [query_stability_of_prefix](#target-zlib-inftrees-spec-decodetablestability-goal-query-stability-of-prefix) |
| [decode_table_read_preserved](#target-zlib-inftrees-spec-decodetableframe-goal-decode-table-read-preserved) | [fast_leaf_flags_of_prefix](#target-zlib-inftrees-spec-fasttableflags-goal-fast-leaf-flags-of-prefix) |
| [decode_table_read_preserved](#target-zlib-inftrees-spec-decodetableframe-goal-decode-table-read-preserved) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [decode_table_read_preserved](#target-zlib-inftrees-spec-decodetableframe-goal-decode-table-read-preserved) | [inflate](#target-zlibf-spec-public-goal-inflate) |
| [decode_table_read_preserved](#target-zlib-inftrees-spec-decodetableframe-goal-decode-table-read-preserved) | [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy) |
| [decode_table_read_preserved](#target-zlib-inftrees-spec-decodetableframe-goal-decode-table-read-preserved) | [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety) |
| [decode_table_read_preserved](#target-zlib-inftrees-spec-decodetableframe-goal-decode-table-read-preserved) | [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety) |
| [decode_table_read_preserved](#target-zlib-inftrees-spec-decodetableframe-goal-decode-table-read-preserved) | [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe) |
| [decode_table_read_preserved](#target-zlib-inftrees-spec-decodetableframe-goal-decode-table-read-preserved) | [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe) |
| [decode_table_read_preserved](#target-zlib-inftrees-spec-decodetableframe-goal-decode-table-read-preserved) | [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe) |
| [decode_table_read_preserved](#target-zlib-inftrees-spec-decodetableframe-goal-decode-table-read-preserved) | [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [constructor_establishes_decode_table_invariant](#target-zlib-inftrees-spec-decodetableinvariant-goal-constructor-establishes-decode-table-invariant) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [constructor_establishes_decode_table_invariant](#target-zlib-inftrees-spec-decodetableinvariant-goal-constructor-establishes-decode-table-invariant) | [inflate](#target-zlibf-spec-public-goal-inflate) |
| [constructor_establishes_decode_table_invariant](#target-zlib-inftrees-spec-decodetableinvariant-goal-constructor-establishes-decode-table-invariant) | [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy) |
| [constructor_establishes_decode_table_invariant](#target-zlib-inftrees-spec-decodetableinvariant-goal-constructor-establishes-decode-table-invariant) | [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety) |
| [constructor_establishes_decode_table_invariant](#target-zlib-inftrees-spec-decodetableinvariant-goal-constructor-establishes-decode-table-invariant) | [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety) |
| [constructor_establishes_decode_table_invariant](#target-zlib-inftrees-spec-decodetableinvariant-goal-constructor-establishes-decode-table-invariant) | [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe) |
| [constructor_establishes_decode_table_invariant](#target-zlib-inftrees-spec-decodetableinvariant-goal-constructor-establishes-decode-table-invariant) | [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe) |
| [constructor_establishes_decode_table_invariant](#target-zlib-inftrees-spec-decodetableinvariant-goal-constructor-establishes-decode-table-invariant) | [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe) |
| [constructor_establishes_decode_table_invariant](#target-zlib-inftrees-spec-decodetableinvariant-goal-constructor-establishes-decode-table-invariant) | [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [decode_table_invariant_of_prefix](#target-zlib-inftrees-spec-decodetableinvariant-goal-decode-table-invariant-of-prefix) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [decode_table_invariant_of_prefix](#target-zlib-inftrees-spec-decodetableinvariant-goal-decode-table-invariant-of-prefix) | [inflate](#target-zlibf-spec-public-goal-inflate) |
| [decode_table_invariant_of_prefix](#target-zlib-inftrees-spec-decodetableinvariant-goal-decode-table-invariant-of-prefix) | [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy) |
| [decode_table_invariant_of_prefix](#target-zlib-inftrees-spec-decodetableinvariant-goal-decode-table-invariant-of-prefix) | [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety) |
| [decode_table_invariant_of_prefix](#target-zlib-inftrees-spec-decodetableinvariant-goal-decode-table-invariant-of-prefix) | [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety) |
| [decode_table_invariant_of_prefix](#target-zlib-inftrees-spec-decodetableinvariant-goal-decode-table-invariant-of-prefix) | [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe) |
| [decode_table_invariant_of_prefix](#target-zlib-inftrees-spec-decodetableinvariant-goal-decode-table-invariant-of-prefix) | [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe) |
| [decode_table_invariant_of_prefix](#target-zlib-inftrees-spec-decodetableinvariant-goal-decode-table-invariant-of-prefix) | [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe) |
| [decode_table_invariant_of_prefix](#target-zlib-inftrees-spec-decodetableinvariant-goal-decode-table-invariant-of-prefix) | [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [constructor_establishes_query_stability](#target-zlib-inftrees-spec-decodetablestability-goal-constructor-establishes-query-stability) | [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety) |
| [query_stability_of_prefix](#target-zlib-inftrees-spec-decodetablestability-goal-query-stability-of-prefix) | [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety) |
| [short_rejected_leaf_stays_invalid](#target-zlib-inftrees-spec-decodetablestability-goal-short-rejected-leaf-stays-invalid) | [distance_lookup_matches_format](#target-zlib-inffast-spec-distancesemantics-goal-distance-lookup-matches-format) |
| [short_rejected_leaf_stays_invalid](#target-zlib-inftrees-spec-decodetablestability-goal-short-rejected-leaf-stays-invalid) | [length_lookup_matches_format](#target-zlib-inffast-spec-lengthsemantics-goal-length-lookup-matches-format) |
| [inflate_table_content](#target-zlib-inftrees-spec-goal-inflate-table-content) | [inflate_table_decoder_safe](#target-zlib-inftrees-spec-goal-inflate-table-decoder-safe) |
| [inflate_table_content](#target-zlib-inftrees-spec-goal-inflate-table-content) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [inflate_table_content](#target-zlib-inftrees-spec-goal-inflate-table-content) | [inflate](#target-zlibf-spec-public-goal-inflate) |
| [inflate_table_content](#target-zlib-inftrees-spec-goal-inflate-table-content) | [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy) |
| [inflate_table_content](#target-zlib-inftrees-spec-goal-inflate-table-content) | [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety) |
| [inflate_table_content](#target-zlib-inftrees-spec-goal-inflate-table-content) | [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety) |
| [inflate_table_content](#target-zlib-inftrees-spec-goal-inflate-table-content) | [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe) |
| [inflate_table_content](#target-zlib-inftrees-spec-goal-inflate-table-content) | [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe) |
| [inflate_table_content](#target-zlib-inftrees-spec-goal-inflate-table-content) | [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe) |
| [inflate_table_content](#target-zlib-inftrees-spec-goal-inflate-table-content) | [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [inflate_table_decoder_safe](#target-zlib-inftrees-spec-goal-inflate-table-decoder-safe) | [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent) |
| [inflate_table_decoder_safe](#target-zlib-inftrees-spec-goal-inflate-table-decoder-safe) | [constructor_root_bits](#target-zlib-inftrees-spec-roottable-goal-constructor-root-bits) |
| [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent) | [constructor_establishes_decode_table_invariant](#target-zlib-inftrees-spec-decodetableinvariant-goal-constructor-establishes-decode-table-invariant) |
| [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent) | [inflate](#target-zlibf-spec-public-goal-inflate) |
| [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent) | [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy) |
| [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent) | [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety) |
| [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent) | [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety) |
| [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent) | [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe) |
| [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent) | [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe) |
| [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent) | [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe) |
| [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent) | [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [constructor_subtable_bits](#target-zlib-inftrees-spec-subtable-goal-constructor-subtable-bits) | [constructor_establishes_decode_table_invariant](#target-zlib-inftrees-spec-decodetableinvariant-goal-constructor-establishes-decode-table-invariant) |
| [constructor_subtable_bits](#target-zlib-inftrees-spec-subtable-goal-constructor-subtable-bits) | [constructor_root_bits](#target-zlib-inftrees-spec-roottable-goal-constructor-root-bits) |
| [output_copy_refines_lz77](#target-zlibf-math-lz77copy-goal-output-copy-refines-lz77) | [match_array_refines_lz77](#target-zlib-inffast-spec-matchhistory-goal-match-array-refines-lz77) |
| [window_copy_refines_lz77](#target-zlibf-math-lz77copy-goal-window-copy-refines-lz77) | [match_array_refines_lz77](#target-zlib-inffast-spec-matchhistory-goal-match-array-refines-lz77) |
| [copy_back_compose](#target-zlibf-math-lz77history-goal-copy-back-compose) | [match_array_refines_lz77](#target-zlib-inffast-spec-matchhistory-goal-match-array-refines-lz77) |
| [retained_history_agrees](#target-zlibf-math-lz77history-goal-retained-history-agrees) | [roundtrip](#target-zlibf-spec-api-goal-roundtrip) |
| [retained_history_agrees](#target-zlibf-math-lz77history-goal-retained-history-agrees) | [roundtrip_completes](#target-zlibf-spec-api-goal-roundtrip-completes) |
| [deflate_valid](#target-zlibf-spec-api-goal-deflate-valid) | [dict_roundtrip](#target-zlibf-spec-api-goal-dict-roundtrip) |
| [deflate_valid](#target-zlibf-spec-api-goal-deflate-valid) | [header_roundtrip](#target-zlibf-spec-api-goal-header-roundtrip) |
| [deflate_valid](#target-zlibf-spec-api-goal-deflate-valid) | [roundtrip](#target-zlibf-spec-api-goal-roundtrip) |
| [deflate_valid](#target-zlibf-spec-api-goal-deflate-valid) | [roundtrip_completes](#target-zlibf-spec-api-goal-roundtrip-completes) |
| [inflate_completes](#target-zlibf-spec-api-goal-inflate-completes) | [roundtrip_completes](#target-zlibf-spec-api-goal-roundtrip-completes) |
| [inflate_decodes](#target-zlibf-spec-api-goal-inflate-decodes) | [roundtrip](#target-zlibf-spec-api-goal-roundtrip) |
| [adler32](#target-zlibf-spec-public-goal-adler32) | [adler32_safety](#target-zlibf-spec-public-goal-adler32-safety) |
| [adler32_combine](#target-zlibf-spec-public-goal-adler32-combine) | [adler32_combine_safety](#target-zlibf-spec-public-goal-adler32-combine-safety) |
| [adler32_combine64](#target-zlibf-spec-public-goal-adler32-combine64) | [adler32_combine64_safety](#target-zlibf-spec-public-goal-adler32-combine64-safety) |
| [adler32_z](#target-zlibf-spec-public-goal-adler32-z) | [adler32](#target-zlibf-spec-public-goal-adler32) |
| [adler32_z](#target-zlibf-spec-public-goal-adler32-z) | [adler32_z_safety](#target-zlibf-spec-public-goal-adler32-z-safety) |
| [crc32](#target-zlibf-spec-public-goal-crc32) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety) |
| [crc32](#target-zlibf-spec-public-goal-crc32) | [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety) |
| [crc32](#target-zlibf-spec-public-goal-crc32) | [compress_safety](#target-zlibf-spec-public-goal-compress-safety) |
| [crc32](#target-zlibf-spec-public-goal-crc32) | [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety) |
| [crc32](#target-zlibf-spec-public-goal-crc32) | [crc32_safety](#target-zlibf-spec-public-goal-crc32-safety) |
| [crc32](#target-zlibf-spec-public-goal-crc32) | [deflate](#target-zlibf-spec-public-goal-deflate) |
| [crc32](#target-zlibf-spec-public-goal-crc32) | [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy) |
| [crc32](#target-zlibf-spec-public-goal-crc32) | [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) |
| [crc32](#target-zlibf-spec-public-goal-crc32) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [crc32_combine](#target-zlibf-spec-public-goal-crc32-combine) | [crc32_combine_safety](#target-zlibf-spec-public-goal-crc32-combine-safety) |
| [crc32_combine64](#target-zlibf-spec-public-goal-crc32-combine64) | [crc32_combine64_safety](#target-zlibf-spec-public-goal-crc32-combine64-safety) |
| [crc32_combine_gen](#target-zlibf-spec-public-goal-crc32-combine-gen) | [crc32_combine_gen_safety](#target-zlibf-spec-public-goal-crc32-combine-gen-safety) |
| [crc32_combine_gen](#target-zlibf-spec-public-goal-crc32-combine-gen) | [crc32_combine_op_safety](#target-zlibf-spec-public-goal-crc32-combine-op-safety) |
| [crc32_combine_gen64](#target-zlibf-spec-public-goal-crc32-combine-gen64) | [crc32_combine_gen64_safety](#target-zlibf-spec-public-goal-crc32-combine-gen64-safety) |
| [crc32_combine_gen64](#target-zlibf-spec-public-goal-crc32-combine-gen64) | [crc32_combine_op_safety](#target-zlibf-spec-public-goal-crc32-combine-op-safety) |
| [crc32_combine_op](#target-zlibf-spec-public-goal-crc32-combine-op) | [crc32_combine_op_safety](#target-zlibf-spec-public-goal-crc32-combine-op-safety) |
| [crc32_z](#target-zlibf-spec-public-goal-crc32-z) | [crc32_z_safety](#target-zlibf-spec-public-goal-crc32-z-safety) |
| [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy) | [deflateCopy_safety](#target-zlibf-spec-public-goal-deflatecopy-safety) |
| [deflateEnd](#target-zlibf-spec-public-goal-deflateend) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety) |
| [deflateEnd](#target-zlibf-spec-public-goal-deflateend) | [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety) |
| [deflateEnd](#target-zlibf-spec-public-goal-deflateend) | [compress_safety](#target-zlibf-spec-public-goal-compress-safety) |
| [deflateEnd](#target-zlibf-spec-public-goal-deflateend) | [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety) |
| [deflateEnd](#target-zlibf-spec-public-goal-deflateend) | [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) |
| [deflateEnd](#target-zlibf-spec-public-goal-deflateend) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) | [deflateInit2__safety](#target-zlibf-spec-public-goal-deflateinit2-safety) |
| [deflateInit2__safety](#target-zlibf-spec-public-goal-deflateinit2-safety) | [deflateInit__safety](#target-zlibf-spec-public-goal-deflateinit-safety) |
| [deflatePending](#target-zlibf-spec-public-goal-deflatepending) | [deflatePending_safety](#target-zlibf-spec-public-goal-deflatepending-safety) |
| [deflateSetHeader](#target-zlibf-spec-public-goal-deflatesetheader) | [deflateSetHeader_safety](#target-zlibf-spec-public-goal-deflatesetheader-safety) |
| [deflateTune](#target-zlibf-spec-public-goal-deflatetune) | [deflateTune_safety](#target-zlibf-spec-public-goal-deflatetune-safety) |
| [deflateUsed](#target-zlibf-spec-public-goal-deflateused) | [deflateUsed_safety](#target-zlibf-spec-public-goal-deflateused-safety) |
| [deflate_refusal](#target-zlibf-spec-public-goal-deflate-refusal) | [deflateCopy_safety](#target-zlibf-spec-public-goal-deflatecopy-safety) |
| [deflate_refusal](#target-zlibf-spec-public-goal-deflate-refusal) | [deflateGetDictionary_safety](#target-zlibf-spec-public-goal-deflategetdictionary-safety) |
| [deflate_refusal](#target-zlibf-spec-public-goal-deflate-refusal) | [deflateParams_safety](#target-zlibf-spec-public-goal-deflateparams-safety) |
| [deflate_refusal](#target-zlibf-spec-public-goal-deflate-refusal) | [deflateSetDictionary_safety](#target-zlibf-spec-public-goal-deflatesetdictionary-safety) |
| [deflate_refusal](#target-zlibf-spec-public-goal-deflate-refusal) | [deflate_safety](#target-zlibf-spec-public-goal-deflate-safety) |
| [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) | [deflateBound_safety](#target-zlibf-spec-public-goal-deflatebound-safety) |
| [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) | [deflateBound_z_safety](#target-zlibf-spec-public-goal-deflatebound-z-safety) |
| [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) | [deflateEnd_safety](#target-zlibf-spec-public-goal-deflateend-safety) |
| [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) | [deflateGetDictionary_safety](#target-zlibf-spec-public-goal-deflategetdictionary-safety) |
| [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) | [deflateParams_safety](#target-zlibf-spec-public-goal-deflateparams-safety) |
| [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) | [deflatePending_safety](#target-zlibf-spec-public-goal-deflatepending-safety) |
| [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) | [deflatePrime_safety](#target-zlibf-spec-public-goal-deflateprime-safety) |
| [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) | [deflateReset_safety](#target-zlibf-spec-public-goal-deflatereset-safety) |
| [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) | [deflateSetDictionary_safety](#target-zlibf-spec-public-goal-deflatesetdictionary-safety) |
| [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) | [deflateSetHeader_safety](#target-zlibf-spec-public-goal-deflatesetheader-safety) |
| [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) | [deflateTune_safety](#target-zlibf-spec-public-goal-deflatetune-safety) |
| [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) | [deflateUsed_safety](#target-zlibf-spec-public-goal-deflateused-safety) |
| [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety) | [deflate_safety](#target-zlibf-spec-public-goal-deflate-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzbuffer_safety](#target-zlibf-spec-public-goal-gzbuffer-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzclearerr_safety](#target-zlibf-spec-public-goal-gzclearerr-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzclose_r_safety](#target-zlibf-spec-public-goal-gzclose-r-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzclose_safety](#target-zlibf-spec-public-goal-gzclose-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzclose_w_safety](#target-zlibf-spec-public-goal-gzclose-w-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzdirect_safety](#target-zlibf-spec-public-goal-gzdirect-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzdopen_safety](#target-zlibf-spec-public-goal-gzdopen-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzeof_safety](#target-zlibf-spec-public-goal-gzeof-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzerror_safety](#target-zlibf-spec-public-goal-gzerror-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzflush_safety](#target-zlibf-spec-public-goal-gzflush-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzfread_safety](#target-zlibf-spec-public-goal-gzfread-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzfwrite_safety](#target-zlibf-spec-public-goal-gzfwrite-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzgetc__safety](#target-zlibf-spec-public-goal-gzgetc-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzgetc_safety](#target-zlibf-spec-public-goal-gzgetc-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzgets_safety](#target-zlibf-spec-public-goal-gzgets-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzoffset64_safety](#target-zlibf-spec-public-goal-gzoffset64-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzoffset_safety](#target-zlibf-spec-public-goal-gzoffset-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzopen64_safety](#target-zlibf-spec-public-goal-gzopen64-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzopen_safety](#target-zlibf-spec-public-goal-gzopen-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzprintf_safety](#target-zlibf-spec-public-goal-gzprintf-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzputc_safety](#target-zlibf-spec-public-goal-gzputc-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzputs_safety](#target-zlibf-spec-public-goal-gzputs-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzread_safety](#target-zlibf-spec-public-goal-gzread-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzrewind_safety](#target-zlibf-spec-public-goal-gzrewind-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzseek64_safety](#target-zlibf-spec-public-goal-gzseek64-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzseek_safety](#target-zlibf-spec-public-goal-gzseek-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzsetparams_safety](#target-zlibf-spec-public-goal-gzsetparams-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gztell64_safety](#target-zlibf-spec-public-goal-gztell64-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gztell_safety](#target-zlibf-spec-public-goal-gztell-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzungetc_safety](#target-zlibf-spec-public-goal-gzungetc-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzvprintf_safety](#target-zlibf-spec-public-goal-gzvprintf-safety) |
| [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) | [gzwrite_safety](#target-zlibf-spec-public-goal-gzwrite-safety) |
| [gzeof](#target-zlibf-spec-public-goal-gzeof) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [inflate](#target-zlibf-spec-public-goal-inflate) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [inflate](#target-zlibf-spec-public-goal-inflate) | [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe) |
| [inflate](#target-zlibf-spec-public-goal-inflate) | [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe) |
| [inflate](#target-zlibf-spec-public-goal-inflate) | [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe) |
| [inflate](#target-zlibf-spec-public-goal-inflate) | [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [inflateBackEnd](#target-zlibf-spec-public-goal-inflatebackend) | [inflateBackEnd_safety](#target-zlibf-spec-public-goal-inflatebackend-safety) |
| [inflateBackEnd](#target-zlibf-spec-public-goal-inflatebackend) | [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety) |
| [inflateBackInit_](#target-zlibf-spec-public-goal-inflatebackinit) | [inflateBackInit__safety](#target-zlibf-spec-public-goal-inflatebackinit-safety) |
| [inflateBackInit_](#target-zlibf-spec-public-goal-inflatebackinit) | [inflate_back_initialisation_domain](#target-zlibf-spec-public-goal-inflate-back-initialisation-domain) |
| [inflateBackInit_](#target-zlibf-spec-public-goal-inflatebackinit) | [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety) |
| [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy) | [inflateCopy_safety](#target-zlibf-spec-public-goal-inflatecopy-safety) |
| [inflateEnd](#target-zlibf-spec-public-goal-inflateend) | [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [inflate](#target-zlibf-spec-public-goal-inflate) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [inflateInit2__safety](#target-zlibf-spec-public-goal-inflateinit2-safety) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [inflateInit2__safety](#target-zlibf-spec-public-goal-inflateinit2-safety) | [inflateInit__safety](#target-zlibf-spec-public-goal-inflateinit-safety) |
| [inflateMark](#target-zlibf-spec-public-goal-inflatemark) | [inflateMark_safety](#target-zlibf-spec-public-goal-inflatemark-safety) |
| [inflatePrime](#target-zlibf-spec-public-goal-inflateprime) | [inflatePrime_safety](#target-zlibf-spec-public-goal-inflateprime-safety) |
| [inflateSetDictionary](#target-zlibf-spec-public-goal-inflatesetdictionary) | [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety) |
| [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety) | [inflateBackEnd_safety](#target-zlibf-spec-public-goal-inflatebackend-safety) |
| [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety) | [inflateBack_safety](#target-zlibf-spec-public-goal-inflateback-safety) |
| [inflate_refusal](#target-zlibf-spec-public-goal-inflate-refusal) | [inflateCopy_safety](#target-zlibf-spec-public-goal-inflatecopy-safety) |
| [inflate_refusal](#target-zlibf-spec-public-goal-inflate-refusal) | [inflateEnd_safety](#target-zlibf-spec-public-goal-inflateend-safety) |
| [inflate_refusal](#target-zlibf-spec-public-goal-inflate-refusal) | [inflateGetDictionary_safety](#target-zlibf-spec-public-goal-inflategetdictionary-safety) |
| [inflate_refusal](#target-zlibf-spec-public-goal-inflate-refusal) | [inflateReset2_safety](#target-zlibf-spec-public-goal-inflatereset2-safety) |
| [inflate_refusal](#target-zlibf-spec-public-goal-inflate-refusal) | [inflateReset_safety](#target-zlibf-spec-public-goal-inflatereset-safety) |
| [inflate_refusal](#target-zlibf-spec-public-goal-inflate-refusal) | [inflateSetDictionary_safety](#target-zlibf-spec-public-goal-inflatesetdictionary-safety) |
| [inflate_refusal](#target-zlibf-spec-public-goal-inflate-refusal) | [inflate_safety](#target-zlibf-spec-public-goal-inflate-safety) |
| [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety) | [inflateEnd_safety](#target-zlibf-spec-public-goal-inflateend-safety) |
| [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety) | [inflateGetDictionary_safety](#target-zlibf-spec-public-goal-inflategetdictionary-safety) |
| [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety) | [inflateGetHeader_safety](#target-zlibf-spec-public-goal-inflategetheader-safety) |
| [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety) | [inflateMark_safety](#target-zlibf-spec-public-goal-inflatemark-safety) |
| [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety) | [inflatePrime_safety](#target-zlibf-spec-public-goal-inflateprime-safety) |
| [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety) | [inflateReset2_safety](#target-zlibf-spec-public-goal-inflatereset2-safety) |
| [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety) | [inflateReset_safety](#target-zlibf-spec-public-goal-inflatereset-safety) |
| [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety) | [inflateSetDictionary_safety](#target-zlibf-spec-public-goal-inflatesetdictionary-safety) |
| [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety) | [inflateSync_safety](#target-zlibf-spec-public-goal-inflatesync-safety) |
| [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety) | [inflate_safety](#target-zlibf-spec-public-goal-inflate-safety) |
| [zlibCompileFlags](#target-zlibf-spec-public-goal-zlibcompileflags) | [zlibCompileFlags_safety](#target-zlibf-spec-public-goal-zlibcompileflags-safety) |
| [zlibVersion](#target-zlibf-spec-public-goal-zlibversion) | [zlibVersion_safety](#target-zlibf-spec-public-goal-zlibversion-safety) |

## C function calls

The destination implementation calls the source entry. This does not require the complete source-entry contract as a proof premise.

| Source | Destination |
| --- | --- |
| [adler32](#target-zlibf-spec-public-goal-adler32) | [deflate](#target-zlibf-spec-public-goal-deflate) |
| [adler32](#target-zlibf-spec-public-goal-adler32) | [deflateResetKeep](#target-zlibf-spec-public-goal-deflateresetkeep) |
| [adler32](#target-zlibf-spec-public-goal-adler32) | [deflateSetDictionary](#target-zlibf-spec-public-goal-deflatesetdictionary) |
| [adler32](#target-zlibf-spec-public-goal-adler32) | [inflate](#target-zlibf-spec-public-goal-inflate) |
| [adler32](#target-zlibf-spec-public-goal-adler32) | [inflateSetDictionary](#target-zlibf-spec-public-goal-inflatesetdictionary) |
| [adler32_z](#target-zlibf-spec-public-goal-adler32-z) | [adler32](#target-zlibf-spec-public-goal-adler32) |
| [compress2](#target-zlibf-spec-public-goal-compress2) | [compress](#target-zlibf-spec-public-goal-compress) |
| [compress2_z](#target-zlibf-spec-public-goal-compress2-z) | [compress2](#target-zlibf-spec-public-goal-compress2) |
| [compress2_z](#target-zlibf-spec-public-goal-compress2-z) | [compress_z](#target-zlibf-spec-public-goal-compress-z) |
| [compressBound_z](#target-zlibf-spec-public-goal-compressbound-z) | [compressBound](#target-zlibf-spec-public-goal-compressbound) |
| [crc32](#target-zlibf-spec-public-goal-crc32) | [deflate](#target-zlibf-spec-public-goal-deflate) |
| [crc32](#target-zlibf-spec-public-goal-crc32) | [deflateResetKeep](#target-zlibf-spec-public-goal-deflateresetkeep) |
| [crc32](#target-zlibf-spec-public-goal-crc32) | [deflateSetDictionary](#target-zlibf-spec-public-goal-deflatesetdictionary) |
| [crc32](#target-zlibf-spec-public-goal-crc32) | [inflate](#target-zlibf-spec-public-goal-inflate) |
| [crc32_combine64](#target-zlibf-spec-public-goal-crc32-combine64) | [crc32_combine](#target-zlibf-spec-public-goal-crc32-combine) |
| [crc32_combine_gen64](#target-zlibf-spec-public-goal-crc32-combine-gen64) | [crc32_combine64](#target-zlibf-spec-public-goal-crc32-combine64) |
| [crc32_combine_gen64](#target-zlibf-spec-public-goal-crc32-combine-gen64) | [crc32_combine_gen](#target-zlibf-spec-public-goal-crc32-combine-gen) |
| [crc32_combine_op](#target-zlibf-spec-public-goal-crc32-combine-op) | [crc32_combine64](#target-zlibf-spec-public-goal-crc32-combine64) |
| [crc32_z](#target-zlibf-spec-public-goal-crc32-z) | [crc32](#target-zlibf-spec-public-goal-crc32) |
| [crc32_z](#target-zlibf-spec-public-goal-crc32-z) | [deflate](#target-zlibf-spec-public-goal-deflate) |
| [deflate](#target-zlibf-spec-public-goal-deflate) | [compress2_z](#target-zlibf-spec-public-goal-compress2-z) |
| [deflate](#target-zlibf-spec-public-goal-deflate) | [deflateParams](#target-zlibf-spec-public-goal-deflateparams) |
| [deflate](#target-zlibf-spec-public-goal-deflate) | [gzclose_w](#target-zlibf-spec-public-goal-gzclose-w) |
| [deflate](#target-zlibf-spec-public-goal-deflate) | [gzflush](#target-zlibf-spec-public-goal-gzflush) |
| [deflate](#target-zlibf-spec-public-goal-deflate) | [gzfwrite](#target-zlibf-spec-public-goal-gzfwrite) |
| [deflate](#target-zlibf-spec-public-goal-deflate) | [gzputc](#target-zlibf-spec-public-goal-gzputc) |
| [deflate](#target-zlibf-spec-public-goal-deflate) | [gzputs](#target-zlibf-spec-public-goal-gzputs) |
| [deflate](#target-zlibf-spec-public-goal-deflate) | [gzsetparams](#target-zlibf-spec-public-goal-gzsetparams) |
| [deflate](#target-zlibf-spec-public-goal-deflate) | [gzvprintf](#target-zlibf-spec-public-goal-gzvprintf) |
| [deflate](#target-zlibf-spec-public-goal-deflate) | [gzwrite](#target-zlibf-spec-public-goal-gzwrite) |
| [deflateBound_z](#target-zlibf-spec-public-goal-deflatebound-z) | [deflateBound](#target-zlibf-spec-public-goal-deflatebound) |
| [deflateEnd](#target-zlibf-spec-public-goal-deflateend) | [compress2_z](#target-zlibf-spec-public-goal-compress2-z) |
| [deflateEnd](#target-zlibf-spec-public-goal-deflateend) | [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) |
| [deflateEnd](#target-zlibf-spec-public-goal-deflateend) | [gzclose_w](#target-zlibf-spec-public-goal-gzclose-w) |
| [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) | [deflateInit_](#target-zlibf-spec-public-goal-deflateinit) |
| [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) | [gzclose_w](#target-zlibf-spec-public-goal-gzclose-w) |
| [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) | [gzflush](#target-zlibf-spec-public-goal-gzflush) |
| [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) | [gzfwrite](#target-zlibf-spec-public-goal-gzfwrite) |
| [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) | [gzputc](#target-zlibf-spec-public-goal-gzputc) |
| [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) | [gzputs](#target-zlibf-spec-public-goal-gzputs) |
| [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) | [gzsetparams](#target-zlibf-spec-public-goal-gzsetparams) |
| [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) | [gzvprintf](#target-zlibf-spec-public-goal-gzvprintf) |
| [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) | [gzwrite](#target-zlibf-spec-public-goal-gzwrite) |
| [deflateInit_](#target-zlibf-spec-public-goal-deflateinit) | [compress2_z](#target-zlibf-spec-public-goal-compress2-z) |
| [deflateParams](#target-zlibf-spec-public-goal-deflateparams) | [gzsetparams](#target-zlibf-spec-public-goal-gzsetparams) |
| [deflateReset](#target-zlibf-spec-public-goal-deflatereset) | [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) |
| [deflateReset](#target-zlibf-spec-public-goal-deflatereset) | [gzclose_w](#target-zlibf-spec-public-goal-gzclose-w) |
| [deflateReset](#target-zlibf-spec-public-goal-deflatereset) | [gzflush](#target-zlibf-spec-public-goal-gzflush) |
| [deflateReset](#target-zlibf-spec-public-goal-deflatereset) | [gzfwrite](#target-zlibf-spec-public-goal-gzfwrite) |
| [deflateReset](#target-zlibf-spec-public-goal-deflatereset) | [gzputc](#target-zlibf-spec-public-goal-gzputc) |
| [deflateReset](#target-zlibf-spec-public-goal-deflatereset) | [gzputs](#target-zlibf-spec-public-goal-gzputs) |
| [deflateReset](#target-zlibf-spec-public-goal-deflatereset) | [gzsetparams](#target-zlibf-spec-public-goal-gzsetparams) |
| [deflateReset](#target-zlibf-spec-public-goal-deflatereset) | [gzvprintf](#target-zlibf-spec-public-goal-gzvprintf) |
| [deflateReset](#target-zlibf-spec-public-goal-deflatereset) | [gzwrite](#target-zlibf-spec-public-goal-gzwrite) |
| [deflateResetKeep](#target-zlibf-spec-public-goal-deflateresetkeep) | [deflateReset](#target-zlibf-spec-public-goal-deflatereset) |
| [gzclose_r](#target-zlibf-spec-public-goal-gzclose-r) | [gzclose](#target-zlibf-spec-public-goal-gzclose) |
| [gzclose_w](#target-zlibf-spec-public-goal-gzclose-w) | [gzclose](#target-zlibf-spec-public-goal-gzclose) |
| [gzgetc](#target-zlibf-spec-public-goal-gzgetc) | [gzgetc_](#target-zlibf-spec-public-goal-gzgetc) |
| [gzoffset64](#target-zlibf-spec-public-goal-gzoffset64) | [gzoffset](#target-zlibf-spec-public-goal-gzoffset) |
| [gzrewind](#target-zlibf-spec-public-goal-gzrewind) | [gzseek64](#target-zlibf-spec-public-goal-gzseek64) |
| [gzseek64](#target-zlibf-spec-public-goal-gzseek64) | [gzseek](#target-zlibf-spec-public-goal-gzseek) |
| [gztell64](#target-zlibf-spec-public-goal-gztell64) | [gztell](#target-zlibf-spec-public-goal-gztell) |
| [gzvprintf](#target-zlibf-spec-public-goal-gzvprintf) | [gzprintf](#target-zlibf-spec-public-goal-gzprintf) |
| [inflate](#target-zlibf-spec-public-goal-inflate) | [gzfread](#target-zlibf-spec-public-goal-gzfread) |
| [inflate](#target-zlibf-spec-public-goal-inflate) | [gzgetc](#target-zlibf-spec-public-goal-gzgetc) |
| [inflate](#target-zlibf-spec-public-goal-inflate) | [gzgets](#target-zlibf-spec-public-goal-gzgets) |
| [inflate](#target-zlibf-spec-public-goal-inflate) | [gzread](#target-zlibf-spec-public-goal-gzread) |
| [inflate](#target-zlibf-spec-public-goal-inflate) | [gzungetc](#target-zlibf-spec-public-goal-gzungetc) |
| [inflate](#target-zlibf-spec-public-goal-inflate) | [uncompress2_z](#target-zlibf-spec-public-goal-uncompress2-z) |
| [inflateEnd](#target-zlibf-spec-public-goal-inflateend) | [gzclose_r](#target-zlibf-spec-public-goal-gzclose-r) |
| [inflateEnd](#target-zlibf-spec-public-goal-inflateend) | [uncompress2_z](#target-zlibf-spec-public-goal-uncompress2-z) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [gzdirect](#target-zlibf-spec-public-goal-gzdirect) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [gzfread](#target-zlibf-spec-public-goal-gzfread) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [gzgetc](#target-zlibf-spec-public-goal-gzgetc) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [gzgets](#target-zlibf-spec-public-goal-gzgets) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [gzread](#target-zlibf-spec-public-goal-gzread) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [gzungetc](#target-zlibf-spec-public-goal-gzungetc) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [inflateInit_](#target-zlibf-spec-public-goal-inflateinit) |
| [inflateInit_](#target-zlibf-spec-public-goal-inflateinit) | [uncompress2_z](#target-zlibf-spec-public-goal-uncompress2-z) |
| [inflateReset](#target-zlibf-spec-public-goal-inflatereset) | [gzdirect](#target-zlibf-spec-public-goal-gzdirect) |
| [inflateReset](#target-zlibf-spec-public-goal-inflatereset) | [gzfread](#target-zlibf-spec-public-goal-gzfread) |
| [inflateReset](#target-zlibf-spec-public-goal-inflatereset) | [gzgetc](#target-zlibf-spec-public-goal-gzgetc) |
| [inflateReset](#target-zlibf-spec-public-goal-inflatereset) | [gzgets](#target-zlibf-spec-public-goal-gzgets) |
| [inflateReset](#target-zlibf-spec-public-goal-inflatereset) | [gzread](#target-zlibf-spec-public-goal-gzread) |
| [inflateReset](#target-zlibf-spec-public-goal-inflatereset) | [gzungetc](#target-zlibf-spec-public-goal-gzungetc) |
| [inflateReset](#target-zlibf-spec-public-goal-inflatereset) | [inflateReset2](#target-zlibf-spec-public-goal-inflatereset2) |
| [inflateReset](#target-zlibf-spec-public-goal-inflatereset) | [inflateSync](#target-zlibf-spec-public-goal-inflatesync) |
| [inflateReset2](#target-zlibf-spec-public-goal-inflatereset2) | [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) |
| [inflateResetKeep](#target-zlibf-spec-public-goal-inflateresetkeep) | [inflateReset](#target-zlibf-spec-public-goal-inflatereset) |
| [uncompress2](#target-zlibf-spec-public-goal-uncompress2) | [uncompress](#target-zlibf-spec-public-goal-uncompress) |
| [uncompress2_z](#target-zlibf-spec-public-goal-uncompress2-z) | [uncompress2](#target-zlibf-spec-public-goal-uncompress2) |
| [uncompress2_z](#target-zlibf-spec-public-goal-uncompress2-z) | [uncompress_z](#target-zlibf-spec-public-goal-uncompress-z) |
| [zError](#target-zlibf-spec-public-goal-zerror) | [deflate](#target-zlibf-spec-public-goal-deflate) |
| [zError](#target-zlibf-spec-public-goal-zerror) | [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) |
| [zlibVersion](#target-zlibf-spec-public-goal-zlibversion) | [compress2_z](#target-zlibf-spec-public-goal-compress2-z) |

## Specification references

The destination target definition references the source target or implementation. This is not a proof dependency.

| Source | Destination |
| --- | --- |
| [adler32](#target-zlibf-spec-public-goal-adler32) | [adler32_safety](#target-zlibf-spec-public-goal-adler32-safety) |
| [adler32_combine](#target-zlibf-spec-public-goal-adler32-combine) | [adler32_combine_safety](#target-zlibf-spec-public-goal-adler32-combine-safety) |
| [adler32_combine64](#target-zlibf-spec-public-goal-adler32-combine64) | [adler32_combine64_safety](#target-zlibf-spec-public-goal-adler32-combine64-safety) |
| [adler32_z](#target-zlibf-spec-public-goal-adler32-z) | [adler32_z_safety](#target-zlibf-spec-public-goal-adler32-z-safety) |
| [compress](#target-zlibf-spec-public-goal-compress) | [compress_safety](#target-zlibf-spec-public-goal-compress-safety) |
| [compress2](#target-zlibf-spec-public-goal-compress2) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety) |
| [compress2_z](#target-zlibf-spec-public-goal-compress2-z) | [compress2_z_first_alloc_failure](#target-zlibf-spec-api-goal-compress2-z-first-alloc-failure) |
| [compress2_z](#target-zlibf-spec-public-goal-compress2-z) | [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety) |
| [compressBound](#target-zlibf-spec-public-goal-compressbound) | [compress_bound_value](#target-zlibf-spec-api-goal-compress-bound-value) |
| [compressBound_z](#target-zlibf-spec-public-goal-compressbound-z) | [compress_bound_value](#target-zlibf-spec-api-goal-compress-bound-value) |
| [compress_z](#target-zlibf-spec-public-goal-compress-z) | [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety) |
| [crc32](#target-zlibf-spec-public-goal-crc32) | [crc32_all_byte_views](#target-zlib-crc32-spec-byteviews-goal-crc32-all-byte-views) |
| [crc32](#target-zlibf-spec-public-goal-crc32) | [crc32_safety](#target-zlibf-spec-public-goal-crc32-safety) |
| [crc32_combine](#target-zlibf-spec-public-goal-crc32-combine) | [crc32_combine_safety](#target-zlibf-spec-public-goal-crc32-combine-safety) |
| [crc32_combine64](#target-zlibf-spec-public-goal-crc32-combine64) | [crc32_combine64_safety](#target-zlibf-spec-public-goal-crc32-combine64-safety) |
| [crc32_combine_gen](#target-zlibf-spec-public-goal-crc32-combine-gen) | [crc32_combine_gen_safety](#target-zlibf-spec-public-goal-crc32-combine-gen-safety) |
| [crc32_combine_gen](#target-zlibf-spec-public-goal-crc32-combine-gen) | [crc32_combine_op_safety](#target-zlibf-spec-public-goal-crc32-combine-op-safety) |
| [crc32_combine_gen64](#target-zlibf-spec-public-goal-crc32-combine-gen64) | [crc32_combine_gen64_safety](#target-zlibf-spec-public-goal-crc32-combine-gen64-safety) |
| [crc32_combine_gen64](#target-zlibf-spec-public-goal-crc32-combine-gen64) | [crc32_combine_op_safety](#target-zlibf-spec-public-goal-crc32-combine-op-safety) |
| [crc32_combine_op](#target-zlibf-spec-public-goal-crc32-combine-op) | [crc32_combine_op_safety](#target-zlibf-spec-public-goal-crc32-combine-op-safety) |
| [crc32_z](#target-zlibf-spec-public-goal-crc32-z) | [crc32_z_all_byte_views](#target-zlib-crc32-spec-byteviews-goal-crc32-z-all-byte-views) |
| [crc32_z](#target-zlibf-spec-public-goal-crc32-z) | [crc32_z_safety](#target-zlibf-spec-public-goal-crc32-z-safety) |
| [deflate](#target-zlibf-spec-public-goal-deflate) | [deflate_refusal](#target-zlibf-spec-public-goal-deflate-refusal) |
| [deflate](#target-zlibf-spec-public-goal-deflate) | [deflate_safety](#target-zlibf-spec-public-goal-deflate-safety) |
| [deflateBound](#target-zlibf-spec-public-goal-deflatebound) | [deflateBound_safety](#target-zlibf-spec-public-goal-deflatebound-safety) |
| [deflateBound](#target-zlibf-spec-public-goal-deflatebound) | [deflate_sequence](#target-zlibf-spec-public-goal-deflate-sequence) |
| [deflateBound_z](#target-zlibf-spec-public-goal-deflatebound-z) | [deflateBound_z_safety](#target-zlibf-spec-public-goal-deflatebound-z-safety) |
| [deflateBound_z](#target-zlibf-spec-public-goal-deflatebound-z) | [deflate_sequence](#target-zlibf-spec-public-goal-deflate-sequence) |
| [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy) | [deflateCopy_safety](#target-zlibf-spec-public-goal-deflatecopy-safety) |
| [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy) | [deflate_refusal](#target-zlibf-spec-public-goal-deflate-refusal) |
| [deflateEnd](#target-zlibf-spec-public-goal-deflateend) | [deflateEnd_safety](#target-zlibf-spec-public-goal-deflateend-safety) |
| [deflateGetDictionary](#target-zlibf-spec-public-goal-deflategetdictionary) | [deflateGetDictionary_safety](#target-zlibf-spec-public-goal-deflategetdictionary-safety) |
| [deflateGetDictionary](#target-zlibf-spec-public-goal-deflategetdictionary) | [deflate_refusal](#target-zlibf-spec-public-goal-deflate-refusal) |
| [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) | [deflateInit2__safety](#target-zlibf-spec-public-goal-deflateinit2-safety) |
| [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2) | [deflate_initialisation_domain](#target-zlibf-spec-public-goal-deflate-initialisation-domain) |
| [deflateInit_](#target-zlibf-spec-public-goal-deflateinit) | [deflateInit__safety](#target-zlibf-spec-public-goal-deflateinit-safety) |
| [deflateParams](#target-zlibf-spec-public-goal-deflateparams) | [deflateParams_safety](#target-zlibf-spec-public-goal-deflateparams-safety) |
| [deflateParams](#target-zlibf-spec-public-goal-deflateparams) | [deflate_refusal](#target-zlibf-spec-public-goal-deflate-refusal) |
| [deflatePending](#target-zlibf-spec-public-goal-deflatepending) | [deflatePending_safety](#target-zlibf-spec-public-goal-deflatepending-safety) |
| [deflatePrime](#target-zlibf-spec-public-goal-deflateprime) | [deflatePrime_safety](#target-zlibf-spec-public-goal-deflateprime-safety) |
| [deflateReset](#target-zlibf-spec-public-goal-deflatereset) | [deflateReset_safety](#target-zlibf-spec-public-goal-deflatereset-safety) |
| [deflateSetDictionary](#target-zlibf-spec-public-goal-deflatesetdictionary) | [deflateSetDictionary_safety](#target-zlibf-spec-public-goal-deflatesetdictionary-safety) |
| [deflateSetDictionary](#target-zlibf-spec-public-goal-deflatesetdictionary) | [deflate_refusal](#target-zlibf-spec-public-goal-deflate-refusal) |
| [deflateSetHeader](#target-zlibf-spec-public-goal-deflatesetheader) | [deflateSetHeader_safety](#target-zlibf-spec-public-goal-deflatesetheader-safety) |
| [deflateTune](#target-zlibf-spec-public-goal-deflatetune) | [deflateTune_safety](#target-zlibf-spec-public-goal-deflatetune-safety) |
| [deflateUsed](#target-zlibf-spec-public-goal-deflateused) | [deflateUsed_safety](#target-zlibf-spec-public-goal-deflateused-safety) |
| [gzbuffer](#target-zlibf-spec-public-goal-gzbuffer) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gzbuffer](#target-zlibf-spec-public-goal-gzbuffer) | [gzbuffer_safety](#target-zlibf-spec-public-goal-gzbuffer-safety) |
| [gzclearerr](#target-zlibf-spec-public-goal-gzclearerr) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gzclearerr](#target-zlibf-spec-public-goal-gzclearerr) | [gzclearerr_safety](#target-zlibf-spec-public-goal-gzclearerr-safety) |
| [gzclose](#target-zlibf-spec-public-goal-gzclose) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gzclose](#target-zlibf-spec-public-goal-gzclose) | [gz_sequence](#target-zlibf-spec-public-goal-gz-sequence) |
| [gzclose](#target-zlibf-spec-public-goal-gzclose) | [gzclose_safety](#target-zlibf-spec-public-goal-gzclose-safety) |
| [gzclose_r](#target-zlibf-spec-public-goal-gzclose-r) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gzclose_r](#target-zlibf-spec-public-goal-gzclose-r) | [gzclose_r_safety](#target-zlibf-spec-public-goal-gzclose-r-safety) |
| [gzclose_w](#target-zlibf-spec-public-goal-gzclose-w) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gzclose_w](#target-zlibf-spec-public-goal-gzclose-w) | [gzclose_w_safety](#target-zlibf-spec-public-goal-gzclose-w-safety) |
| [gzdirect](#target-zlibf-spec-public-goal-gzdirect) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gzdirect](#target-zlibf-spec-public-goal-gzdirect) | [gzdirect_safety](#target-zlibf-spec-public-goal-gzdirect-safety) |
| [gzdopen](#target-zlibf-spec-public-goal-gzdopen) | [gz_sequence_nonvacuity](#target-zlibf-spec-public-goal-gz-sequence-nonvacuity) |
| [gzeof](#target-zlibf-spec-public-goal-gzeof) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gzeof](#target-zlibf-spec-public-goal-gzeof) | [gzeof_safety](#target-zlibf-spec-public-goal-gzeof-safety) |
| [gzerror](#target-zlibf-spec-public-goal-gzerror) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gzerror](#target-zlibf-spec-public-goal-gzerror) | [gzerror_safety](#target-zlibf-spec-public-goal-gzerror-safety) |
| [gzflush](#target-zlibf-spec-public-goal-gzflush) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gzflush](#target-zlibf-spec-public-goal-gzflush) | [gz_sequence](#target-zlibf-spec-public-goal-gz-sequence) |
| [gzflush](#target-zlibf-spec-public-goal-gzflush) | [gzflush_safety](#target-zlibf-spec-public-goal-gzflush-safety) |
| [gzfread](#target-zlibf-spec-public-goal-gzfread) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gzfread](#target-zlibf-spec-public-goal-gzfread) | [gz_sequence](#target-zlibf-spec-public-goal-gz-sequence) |
| [gzfread](#target-zlibf-spec-public-goal-gzfread) | [gzfread_safety](#target-zlibf-spec-public-goal-gzfread-safety) |
| [gzfwrite](#target-zlibf-spec-public-goal-gzfwrite) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gzfwrite](#target-zlibf-spec-public-goal-gzfwrite) | [gz_sequence](#target-zlibf-spec-public-goal-gz-sequence) |
| [gzfwrite](#target-zlibf-spec-public-goal-gzfwrite) | [gzfwrite_safety](#target-zlibf-spec-public-goal-gzfwrite-safety) |
| [gzgetc](#target-zlibf-spec-public-goal-gzgetc) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gzgetc](#target-zlibf-spec-public-goal-gzgetc) | [gz_sequence](#target-zlibf-spec-public-goal-gz-sequence) |
| [gzgetc](#target-zlibf-spec-public-goal-gzgetc) | [gzgetc_safety](#target-zlibf-spec-public-goal-gzgetc-safety) |
| [gzgetc_](#target-zlibf-spec-public-goal-gzgetc) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gzgetc_](#target-zlibf-spec-public-goal-gzgetc) | [gzgetc__safety](#target-zlibf-spec-public-goal-gzgetc-safety) |
| [gzgets](#target-zlibf-spec-public-goal-gzgets) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gzgets](#target-zlibf-spec-public-goal-gzgets) | [gz_sequence](#target-zlibf-spec-public-goal-gz-sequence) |
| [gzgets](#target-zlibf-spec-public-goal-gzgets) | [gzgets_safety](#target-zlibf-spec-public-goal-gzgets-safety) |
| [gzoffset](#target-zlibf-spec-public-goal-gzoffset) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gzoffset](#target-zlibf-spec-public-goal-gzoffset) | [gzoffset_safety](#target-zlibf-spec-public-goal-gzoffset-safety) |
| [gzoffset64](#target-zlibf-spec-public-goal-gzoffset64) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gzoffset64](#target-zlibf-spec-public-goal-gzoffset64) | [gzoffset64_safety](#target-zlibf-spec-public-goal-gzoffset64-safety) |
| [gzopen](#target-zlibf-spec-public-goal-gzopen) | [gz_initialisation_domain](#target-zlibf-spec-public-goal-gz-initialisation-domain) |
| [gzopen](#target-zlibf-spec-public-goal-gzopen) | [gz_sequence_nonvacuity](#target-zlibf-spec-public-goal-gz-sequence-nonvacuity) |
| [gzopen](#target-zlibf-spec-public-goal-gzopen) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [gzopen](#target-zlibf-spec-public-goal-gzopen) | [gzopen_safety](#target-zlibf-spec-public-goal-gzopen-safety) |
| [gzopen64](#target-zlibf-spec-public-goal-gzopen64) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [gzopen64](#target-zlibf-spec-public-goal-gzopen64) | [gzopen64_safety](#target-zlibf-spec-public-goal-gzopen64-safety) |
| [gzprintf](#target-zlibf-spec-public-goal-gzprintf) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gzprintf](#target-zlibf-spec-public-goal-gzprintf) | [gzprintf_safety](#target-zlibf-spec-public-goal-gzprintf-safety) |
| [gzputc](#target-zlibf-spec-public-goal-gzputc) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gzputc](#target-zlibf-spec-public-goal-gzputc) | [gzputc_safety](#target-zlibf-spec-public-goal-gzputc-safety) |
| [gzputs](#target-zlibf-spec-public-goal-gzputs) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gzputs](#target-zlibf-spec-public-goal-gzputs) | [gzputs_safety](#target-zlibf-spec-public-goal-gzputs-safety) |
| [gzread](#target-zlibf-spec-public-goal-gzread) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gzread](#target-zlibf-spec-public-goal-gzread) | [gz_sequence](#target-zlibf-spec-public-goal-gz-sequence) |
| [gzread](#target-zlibf-spec-public-goal-gzread) | [gzread_safety](#target-zlibf-spec-public-goal-gzread-safety) |
| [gzrewind](#target-zlibf-spec-public-goal-gzrewind) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gzrewind](#target-zlibf-spec-public-goal-gzrewind) | [gzrewind_safety](#target-zlibf-spec-public-goal-gzrewind-safety) |
| [gzseek](#target-zlibf-spec-public-goal-gzseek) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gzseek](#target-zlibf-spec-public-goal-gzseek) | [gzseek_safety](#target-zlibf-spec-public-goal-gzseek-safety) |
| [gzseek64](#target-zlibf-spec-public-goal-gzseek64) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gzseek64](#target-zlibf-spec-public-goal-gzseek64) | [gzseek64_safety](#target-zlibf-spec-public-goal-gzseek64-safety) |
| [gzsetparams](#target-zlibf-spec-public-goal-gzsetparams) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gzsetparams](#target-zlibf-spec-public-goal-gzsetparams) | [gzsetparams_safety](#target-zlibf-spec-public-goal-gzsetparams-safety) |
| [gztell](#target-zlibf-spec-public-goal-gztell) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gztell](#target-zlibf-spec-public-goal-gztell) | [gztell_safety](#target-zlibf-spec-public-goal-gztell-safety) |
| [gztell64](#target-zlibf-spec-public-goal-gztell64) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gztell64](#target-zlibf-spec-public-goal-gztell64) | [gztell64_safety](#target-zlibf-spec-public-goal-gztell64-safety) |
| [gzungetc](#target-zlibf-spec-public-goal-gzungetc) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gzungetc](#target-zlibf-spec-public-goal-gzungetc) | [gzungetc_safety](#target-zlibf-spec-public-goal-gzungetc-safety) |
| [gzvprintf](#target-zlibf-spec-public-goal-gzvprintf) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gzvprintf](#target-zlibf-spec-public-goal-gzvprintf) | [gzvprintf_safety](#target-zlibf-spec-public-goal-gzvprintf-safety) |
| [gzwrite](#target-zlibf-spec-public-goal-gzwrite) | [gz_refusal](#target-zlibf-spec-public-goal-gz-refusal) |
| [gzwrite](#target-zlibf-spec-public-goal-gzwrite) | [gz_sequence](#target-zlibf-spec-public-goal-gz-sequence) |
| [gzwrite](#target-zlibf-spec-public-goal-gzwrite) | [gzwrite_safety](#target-zlibf-spec-public-goal-gzwrite-safety) |
| [inflate](#target-zlibf-spec-public-goal-inflate) | [inflate_refusal](#target-zlibf-spec-public-goal-inflate-refusal) |
| [inflate](#target-zlibf-spec-public-goal-inflate) | [inflate_safety](#target-zlibf-spec-public-goal-inflate-safety) |
| [inflateBack](#target-zlibf-spec-public-goal-inflateback) | [inflateBack_safety](#target-zlibf-spec-public-goal-inflateback-safety) |
| [inflateBack](#target-zlibf-spec-public-goal-inflateback) | [inflate_back_sequence](#target-zlibf-spec-public-goal-inflate-back-sequence) |
| [inflateBack](#target-zlibf-spec-public-goal-inflateback) | [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety) |
| [inflateBackEnd](#target-zlibf-spec-public-goal-inflatebackend) | [inflateBackEnd_safety](#target-zlibf-spec-public-goal-inflatebackend-safety) |
| [inflateBackEnd](#target-zlibf-spec-public-goal-inflatebackend) | [inflate_back_sequence](#target-zlibf-spec-public-goal-inflate-back-sequence) |
| [inflateBackEnd](#target-zlibf-spec-public-goal-inflatebackend) | [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety) |
| [inflateBackInit_](#target-zlibf-spec-public-goal-inflatebackinit) | [inflateBackInit__safety](#target-zlibf-spec-public-goal-inflatebackinit-safety) |
| [inflateBackInit_](#target-zlibf-spec-public-goal-inflatebackinit) | [inflate_back_initialisation_domain](#target-zlibf-spec-public-goal-inflate-back-initialisation-domain) |
| [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy) | [inflateCopy_safety](#target-zlibf-spec-public-goal-inflatecopy-safety) |
| [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy) | [inflate_refusal](#target-zlibf-spec-public-goal-inflate-refusal) |
| [inflateEnd](#target-zlibf-spec-public-goal-inflateend) | [inflateEnd_safety](#target-zlibf-spec-public-goal-inflateend-safety) |
| [inflateEnd](#target-zlibf-spec-public-goal-inflateend) | [inflate_refusal](#target-zlibf-spec-public-goal-inflate-refusal) |
| [inflateGetDictionary](#target-zlibf-spec-public-goal-inflategetdictionary) | [inflateGetDictionary_safety](#target-zlibf-spec-public-goal-inflategetdictionary-safety) |
| [inflateGetDictionary](#target-zlibf-spec-public-goal-inflategetdictionary) | [inflate_refusal](#target-zlibf-spec-public-goal-inflate-refusal) |
| [inflateGetHeader](#target-zlibf-spec-public-goal-inflategetheader) | [inflateGetHeader_safety](#target-zlibf-spec-public-goal-inflategetheader-safety) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [inflateInit2__safety](#target-zlibf-spec-public-goal-inflateinit2-safety) |
| [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2) | [inflate_initialisation_domain](#target-zlibf-spec-public-goal-inflate-initialisation-domain) |
| [inflateInit_](#target-zlibf-spec-public-goal-inflateinit) | [inflateInit__safety](#target-zlibf-spec-public-goal-inflateinit-safety) |
| [inflateMark](#target-zlibf-spec-public-goal-inflatemark) | [inflateMark_safety](#target-zlibf-spec-public-goal-inflatemark-safety) |
| [inflatePrime](#target-zlibf-spec-public-goal-inflateprime) | [inflatePrime_safety](#target-zlibf-spec-public-goal-inflateprime-safety) |
| [inflateReset](#target-zlibf-spec-public-goal-inflatereset) | [inflateReset_safety](#target-zlibf-spec-public-goal-inflatereset-safety) |
| [inflateReset](#target-zlibf-spec-public-goal-inflatereset) | [inflate_refusal](#target-zlibf-spec-public-goal-inflate-refusal) |
| [inflateReset2](#target-zlibf-spec-public-goal-inflatereset2) | [inflateReset2_safety](#target-zlibf-spec-public-goal-inflatereset2-safety) |
| [inflateReset2](#target-zlibf-spec-public-goal-inflatereset2) | [inflate_refusal](#target-zlibf-spec-public-goal-inflate-refusal) |
| [inflateSetDictionary](#target-zlibf-spec-public-goal-inflatesetdictionary) | [inflateSetDictionary_safety](#target-zlibf-spec-public-goal-inflatesetdictionary-safety) |
| [inflateSetDictionary](#target-zlibf-spec-public-goal-inflatesetdictionary) | [inflate_refusal](#target-zlibf-spec-public-goal-inflate-refusal) |
| [inflateSync](#target-zlibf-spec-public-goal-inflatesync) | [inflateSync_safety](#target-zlibf-spec-public-goal-inflatesync-safety) |
| [uncompress](#target-zlibf-spec-public-goal-uncompress) | [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe) |
| [uncompress2](#target-zlibf-spec-public-goal-uncompress2) | [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe) |
| [uncompress2_z](#target-zlibf-spec-public-goal-uncompress2-z) | [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe) |
| [uncompress_z](#target-zlibf-spec-public-goal-uncompress-z) | [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [zlibCompileFlags](#target-zlibf-spec-public-goal-zlibcompileflags) | [zlibCompileFlags_safety](#target-zlibf-spec-public-goal-zlibcompileflags-safety) |
| [zlibVersion](#target-zlibf-spec-public-goal-zlibversion) | [zlibVersion_safety](#target-zlibf-spec-public-goal-zlibversion-safety) |

## Proof support relationships

These are observed theorem references grouped by source family. Groups carry no whole-file proof status.
Every direct grouped connection is retained here, including arrows reduced in the graph.

| Supporting source | Direct destinations |
| --- | --- |
| API-model lemmas | dict_roundtrip, gz_roundtrip, gz_seek_read, inflate_completes, inflate_deferred_distance, roundtrip_completes, gzdopen, api-model proofs, gz.inv-open proofs, gz.inv-open-fresh proofs, gz.inv-open-path proofs, gzlib.c proofs, heap-free mathematics |
| ByteAddress proofs | first_aligned_offset, mask_refines_base_plus_offset, pointer_advance_preserves_low_bits |
| LibcBorrow proofs | LibcBorrowLoops proofs, LibcBorrowPrimitives proofs, PlatformMemory proofs, borrowed-byte-frame proofs, checksum.borrow-stable proofs, deflate lifecycle proofs, deflate window and match proofs, gz.inv-open proofs, gzfs.borrow-stable proofs, gzlib.c proofs, inflate mode and exit proofs, inflate storage and bit proofs, libc-errno-cstring proofs, public entry composition, tree construction and emission proofs |
| LibcBorrowLoops proofs | checksum.borrow-stable proofs, deflate lifecycle proofs, inflate storage and bit proofs, tree construction and emission proofs |
| LibcBorrowPrimitives proofs | checksum.borrow-stable proofs, deflate lifecycle proofs, gzfs.borrow-stable proofs, gzlib.c proofs, inflate storage and bit proofs, public entry composition, tree construction and emission proofs |
| LibcStrings proofs | LibcBorrow proofs, gzfs.error-message-store proofs, gzlib.c proofs, heap-free mathematics, libc-errno-cstring proofs |
| PlatformMemory proofs | gz.inv-frame proofs, gz.read-avail proofs, gz.read-gzread proofs, gz.read-load-error proofs, gz.read-look proofs, gz.read-store proofs, gzread.c proofs, gzwrite.c proofs, inffast.c proofs, inflate storage and bit proofs |
| crc32_all_byte_views | inflate storage and bit proofs |
| actual_body_preserves_origin | inffast.c proofs |
| actual_fast_preserves_origin | inffast.c proofs |
| actual_distance_block_preserves_origin | inffast.c proofs |
| actual_copy_match_refines_lz77 | inffast.c proofs |
| actual_drop_preserves_origin | inffast.c proofs |
| actual_rollback_preserves_origin | inffast.c proofs |
| drop_preserves_origin | inffast.c proofs |
| pull_preserves_origin | inffast.c proofs |
| decode_table_read_preserved | inftrees.c proofs |
| constructor_establishes_decode_table_invariant | infback.c proofs, inflate storage and bit proofs, inftrees.c proofs |
| decode_table_invariant_of_prefix | infback.c proofs, inftrees.c proofs |
| constructor_establishes_query_stability | infback.c proofs |
| query_stability_of_prefix | infback.c proofs |
| inflate_table_content | inftrees.c proofs |
| inflate_table_read_extent | infback.c proofs, inflate storage and bit proofs |
| retained_history_agrees | format proofs |
| deflate_valid | api-model proofs |
| inflate_completes | api-model proofs |
| inflate_decodes | api-model proofs |
| crc32 | deflate lifecycle proofs |
| deflateEnd | deflate lifecycle proofs, public entry composition |
| deflateInit2_ | public entry composition |
| gz_sequence_safety | public entry composition |
| gzeof | gz.inv-queries proofs |
| inflate | gz.read-decomp proofs, public entry composition |
| inflateBackEnd | infback.c proofs |
| inflateBackInit_ | infback.c proofs, public entry composition |
| inflateEnd | inflate storage and bit proofs |
| inflateInit2_ | inflate storage and bit proofs, public entry composition |
| inflateSetDictionary | inflate storage and bit proofs |
| adler32.c proofs | inflateSetDictionary, deflate lifecycle proofs, inflate entry composition, inflate storage and bit proofs, public entry composition |
| api-model proofs | compress2_z_first_alloc_failure, compress_bound_adequate, compress_bound_value, compress_roundtrip, deflate_bound_adequate, deflate_completes, deflate_full_flush_resync, deflate_valid, dict_roundtrip, gz_roundtrip, gz_seek_read, header_roundtrip, inflate_completes, inflate_decodes, inflate_deferred_distance, roundtrip, roundtrip_completes, inflateCodesUsed, gzlib.c proofs |
| borrowed-byte-frame proofs | inflate storage and bit proofs |
| checksum.borrow-stable proofs | deflate lifecycle proofs, inflate storage and bit proofs, tree construction and emission proofs |
| crc32.c proofs | crc32_all_byte_views, crc32_z_all_byte_views, crc32, crc32_z, deflate lifecycle proofs, inflate storage and bit proofs, public entry composition |
| deflate construction proofs | deflateInit2_, deflateInit_, deflate_initialisation_domain, deflate lifecycle proofs, deflate window and match proofs, gzwrite.c proofs, public entry composition |
| deflate entry composition | deflate, deflateCopy, deflateEnd, deflateEnd_safety, deflateGetDictionary, deflatePending, deflateReset, deflateResetKeep, deflateReset_safety, deflateSetHeader, deflateTune, deflateUsed, deflate_refusal, deflate_sequence_safety, deflate lifecycle proofs, public entry composition |
| deflate lifecycle proofs | deflateCopy, deflateEnd, deflateEnd_safety, deflateGetDictionary, deflateInit_, deflatePending, deflatePrime_safety, deflateReset, deflateResetKeep, deflateReset_safety, deflateSetHeader, deflateTune, deflateUsed, deflate_refusal, deflate construction proofs, deflate entry composition, deflate window and match proofs, gzwrite.c proofs, inffast.c proofs, inflate storage and bit proofs, public entry composition, tree construction and emission proofs |
| deflate window and match proofs | deflate, deflate_sequence_safety, deflate construction proofs, deflate entry composition, deflate lifecycle proofs, gz.read-read proofs, gz.read-store proofs, gzfs.error-message-store proofs, gzfs.format-error-message proofs, gzlib.c proofs, gzwrite.c proofs, inflate storage and bit proofs, tree construction and emission proofs |
| deflate_base.c proofs | deflateBound_safety, deflateBound_z_safety, deflateCopy_safety, deflateEnd_safety, deflateGetDictionary_safety, deflateParams_safety, deflatePending_safety, deflatePrime_safety, deflateReset_safety, deflateSetDictionary_safety, deflateSetHeader_safety, deflateTune_safety, deflateUsed_safety, deflate_refusal, deflate_safety, gz_refusal, gzbuffer_safety, gzclearerr_safety, gzclose_r_safety, gzclose_safety, gzclose_w_safety, gzdirect_safety, gzdopen_safety, gzeof_safety, gzerror_safety, gzflush_safety, gzfread_safety, gzfwrite_safety, gzgetc__safety, gzgetc_safety, gzgets_safety, gzoffset64_safety, gzoffset_safety, gzopen64_safety, gzopen_safety, gzprintf_safety, gzputc_safety, gzputs_safety, gzread_safety, gzrewind_safety, gzseek64_safety, gzseek_safety, gzsetparams_safety, gztell64_safety, gztell_safety, gzungetc_safety, gzvprintf_safety, gzwrite_safety, inflateEnd_safety, inflateGetDictionary_safety, inflateGetHeader_safety, inflateMark_safety, inflatePrime_safety, inflateReset2_safety, inflateReset_safety, inflateSetDictionary_safety, inflateSync_safety, inflate_safety, deflate lifecycle proofs, gz.inv-clearerr proofs, gz.inv-close proofs, gz.inv-frame proofs, gz.inv-offset-rewind proofs, gz.inv-queries proofs, gz.inv-seek proofs, gz.read-close proofs, gz.read-decomp proofs, gz.read-direct-step proofs, gz.read-getc-step proofs, gz.read-gets-step proofs, gz.read-gzread proofs, gz.read-look proofs, gz.sequence-safety proofs, gzread.c proofs, gzwrite.c proofs, inflate storage and bit proofs, public entry composition, zlib.h.gzgetc-macro proofs |
| format proofs | short_decode_table_leaf_sound, short_rejected_leaf_stays_invalid, compress_roundtrip, format_deterministic, format_prefix_free, header_roundtrip, inflate_completes, rejected_has_no_symbols, api-model proofs, heap-free mathematics, infback.c proofs, inffast.c proofs, inffixed.h.input-meaning proofs, inflate storage and bit proofs, inftrees.c proofs, tree construction and emission proofs |
| format-model lemmas | inflate storage and bit proofs |
| gz.inv-clearerr proofs | gz.inv-seek proofs, gz.read-store proofs, gz.sequence-safety proofs, gzlib.c proofs, gzread.c proofs, gzwrite.c proofs |
| gz.inv-close proofs | gz.sequence-safety proofs |
| gz.inv-frame proofs | gz.inv-clearerr proofs, gz.read-decomp proofs, gz.read-gzread proofs, gz.read-load-error proofs, gz.read-look proofs, gz.read-read proofs, gz.read-store proofs, gz.sequence-safety proofs, gzlib.c proofs, gzread.c proofs, gzwrite.c proofs |
| gz.inv-model proofs | gz.inv-clearerr proofs, gz.inv-close proofs, gz.inv-frame proofs, gz.inv-offset-rewind proofs, gz.inv-open proofs, gz.inv-put-scalars proofs, gz.inv-queries proofs, gz.inv-reset proofs, gz.inv-seek proofs, gz.read-avail proofs, gz.read-close proofs, gz.read-decomp proofs, gz.read-direct-step proofs, gz.read-fetch proofs, gz.read-getc-step proofs, gz.read-gets-step proofs, gz.read-gzread proofs, gz.read-leaf-common proofs, gz.read-load-error proofs, gz.read-look proofs, gz.read-read proofs, gz.read-store proofs, gz.sequence-safety proofs, gzlib.c proofs, gzread.c proofs, gzwrite.c proofs, zlib.h.gzgetc-macro proofs |
| gz.inv-offset-rewind proofs | gz.sequence-safety proofs |
| gz.inv-open proofs | gz.inv-open-fresh proofs, gz.sequence-safety proofs, public entry composition |
| gz.inv-open-fd proofs | gz.inv-open-fresh proofs |
| gz.inv-open-fresh proofs | gz.sequence-safety proofs, public entry composition |
| gz.inv-open-path proofs | gz.inv-open-fresh proofs |
| gz.inv-put-scalars proofs | gz.inv-clearerr proofs, gz.inv-queries proofs, gz.inv-reset proofs, gz.inv-seek proofs, gz.read-avail proofs, gz.read-decomp proofs, gz.read-fetch proofs, gz.read-gets-step proofs, gz.read-leaf-common proofs, gz.read-load-error proofs, gz.read-look proofs, gz.read-read proofs, gz.read-store proofs, gzlib.c proofs, gzread.c proofs, gzwrite.c proofs |
| gz.inv-queries proofs | gz.inv-close proofs, gz.inv-seek proofs, gz.sequence-safety proofs |
| gz.inv-reset proofs | gz.inv-seek proofs |
| gz.inv-seek proofs | gz.inv-offset-rewind proofs, gz.inv-open proofs, gz.sequence-safety proofs |
| gz.read-assembly proofs | gz.read-getc-step proofs, gz.read-gets-step proofs, public entry composition |
| gz.read-avail proofs | gz.read-budget proofs, gz.read-decomp proofs, gz.read-fetch proofs, gz.read-look proofs |
| gz.read-budget proofs | gz.read-decomp proofs, gz.read-fetch proofs, gz.read-look proofs, gz.read-read proofs |
| gz.read-close proofs | gz.inv-close proofs, gz.sequence-safety proofs, gzwrite.c proofs |
| gz.read-decomp proofs | gz.read-assembly proofs, gz.read-fetch proofs, gz.read-gets-step proofs, gz.read-gzread proofs, gz.read-leaf-common proofs, gz.read-read proofs |
| gz.read-direct-step proofs | public entry composition |
| gz.read-fetch proofs | gz.read-assembly proofs, gz.read-gets-step proofs, gz.read-leaf-common proofs, gz.read-read proofs |
| gz.read-getc-step proofs | gz.read-direct-step proofs, public entry composition |
| gz.read-gets-step proofs | public entry composition |
| gz.read-gzread proofs | gz.read-assembly proofs, gzread.c proofs |
| gz.read-leaf-common proofs | gz.read-direct-step proofs, gz.read-getc-step proofs, gz.read-gets-step proofs |
| gz.read-load-error proofs | gz.read-avail proofs, gz.read-fetch proofs, gz.read-read proofs |
| gz.read-look proofs | gz.read-assembly proofs, gz.read-close proofs, gz.read-getc-step proofs, gz.read-gets-step proofs, gz.read-leaf-common proofs |
| gz.read-read proofs | gz.read-assembly proofs, gz.read-gzread proofs, gzread.c proofs |
| gz.read-store proofs | gz.read-avail proofs, gz.read-close proofs, gz.read-decomp proofs, gz.read-fetch proofs, gz.read-load-error proofs, gz.read-look proofs, gz.read-read proofs, gzread.c proofs, gzwrite.c proofs |
| gz.sequence-safety proofs | gz_sequence_safety |
| gzfs proofs | gz.inv-open-path proofs, gzfs.format-error-message proofs, gzlib.c proofs |
| gzfs.borrow-stable proofs | LibcBorrowLoops proofs, checksum.borrow-stable proofs, deflate lifecycle proofs, gzlib.c proofs, inflate storage and bit proofs, tree construction and emission proofs |
| gzfs.borrowed-error proofs | gz.read-gzread proofs, gz.read-load-error proofs, gzwrite.c proofs, libc-errno-cstring proofs |
| gzfs.error-message-store proofs | gzlib.c proofs |
| gzfs.format-error-message proofs | gzlib.c proofs, gzwrite.c proofs |
| gzfs.oracle proofs | gz.inv-open-fd proofs, gzlib.c proofs, gzread.c proofs, public entry composition |
| gzfs.read-contract proofs | gz.read-avail proofs, gz.read-decomp proofs, gz.read-fetch proofs, gz.read-look proofs, gz.read-read proofs, gz.read-store proofs, gzwrite.c proofs |
| gzlib.c proofs | gzclearerr, gzdopen, gz.inv-clearerr proofs, gz.inv-offset-rewind proofs, gz.inv-open proofs, gz.inv-open-fd proofs, gz.inv-open-fresh proofs, gz.inv-open-path proofs, gz.inv-queries proofs, gz.inv-seek proofs, gz.read-avail proofs, gz.read-close proofs, gz.read-decomp proofs, gz.read-direct-step proofs, gz.read-fetch proofs, gz.read-getc-step proofs, gz.read-gets-step proofs, gz.read-gzread proofs, gz.read-leaf-common proofs, gz.read-load-error proofs, gz.read-look proofs, gz.read-read proofs, gz.read-store proofs, gzfs.error-message-store proofs, gzfs.oracle proofs, gzfs.read-contract proofs, gzread.c proofs, gzwrite.c proofs, public entry composition, zlib.h.gzgetc-macro proofs |
| gzread.c proofs | gz.inv-offset-rewind proofs, gz.inv-seek proofs, gz.read-assembly proofs, gz.read-close proofs, gz.read-decomp proofs, gz.read-direct-step proofs, gz.read-fetch proofs, gz.read-getc-step proofs, gz.read-gets-step proofs, gz.read-gzread proofs, gz.read-leaf-common proofs, gz.read-read proofs, gzwrite.c proofs, zlib.h.gzgetc-macro proofs |
| gzwrite.c proofs | gz.inv-close proofs, gz.read-close proofs, gz.read-gzread proofs, gz.read-look proofs, gz.sequence-safety proofs, gzread.c proofs |
| heap-free mathematics | match_array_refines_lz77, output_copy_refines_lz77, window_copy_refines_lz77, copy_back_compose, retained_history_agrees, window_distance_check_agrees, api-model proofs, deflate construction proofs, deflate lifecycle proofs, deflate window and match proofs, gzlib.c proofs, infback.c proofs, inffixed.h.input-meaning proofs, inflate storage and bit proofs, inftrees.c proofs, libc-errno-cstring proofs, tree construction and emission proofs |
| infback.c proofs | inflateBackEnd, inflateBackInit_, inflateBack_safety, inflate_back_sequence_safety, gz.read-decomp proofs, gz.read-read proofs, gzlib.c proofs, gzread.c proofs, public entry composition |
| inffast.c proofs | actual_body_preserves_origin, actual_body_refines_token, actual_fast_preserves_origin, actual_distance_block_preserves_origin, actual_distance_refines_lz77, distance_lookup_matches_format, fast_safe, step_safe, length_lookup_matches_format, actual_body_retains_selected_length, actual_copy_match_refines_lz77, match_array_refines_lz77, actual_drop_preserves_origin, actual_pull_preserves_origin, actual_rollback_preserves_origin, drop_preserves_origin, initial_origin, pull_preserves_origin, rollback_preserves_origin, output_copy_refines_lz77, gzfs.error-message-store proofs, gzlib.c proofs, heap-free mathematics, infback.c proofs, inffixed.h.input-meaning proofs, inflate storage and bit proofs, inftrees.c proofs |
| inffixed.h.fast-flags proofs | fixed_tables_have_fast_leaf_flags |
| inffixed.h.input-meaning proofs | inflate storage and bit proofs |
| inffixed.h.meaning proofs | inffixed.h.input-meaning proofs |
| inflate entry composition | deflate_initialisation_domain, inflateCopy, inflateEnd, inflateGetDictionary, inflateGetHeader, inflateGetHeader_safety, inflateInit2_, inflateInit_, inflateMark, inflatePrime, inflateReset, inflateReset2, inflateSetDictionary, inflateSyncPoint, inflateUndermine, inflateValidate, inflate_initialisation_domain, inflate_refusal, gz.read-look proofs, inflate storage and bit proofs, public entry composition |
| inflate mode and exit proofs | gzlib.c proofs, infback.c proofs, inffast.c proofs, inflate storage and bit proofs |
| inflate storage and bit proofs | inflate, inflateBackEnd, inflateBackInit_, inflateCopy, inflateEnd, inflateGetDictionary, inflateGetHeader_safety, inflateInit2_, inflateInit_, inflateMark, inflateReset, inflateReset2, inflateResetKeep, inflateSetDictionary, inflateSyncPoint, inflateUndermine, inflateValidate, inflate_refusal, inflate_sequence_safety, api-model proofs, deflate lifecycle proofs, deflate window and match proofs, gz.inv-frame proofs, gz.read-assembly proofs, gz.read-avail proofs, gz.read-close proofs, gz.read-decomp proofs, gz.read-getc-step proofs, gz.read-gets-step proofs, gz.read-gzread proofs, gz.read-load-error proofs, gz.read-look proofs, gz.read-read proofs, gzlib.c proofs, gzread.c proofs, gzwrite.c proofs, infback.c proofs, inffast.c proofs, inflate entry composition, inflate mode and exit proofs, inftrees.c proofs, public entry composition |
| inflate.c proofs | inflate mode and exit proofs, inflate storage and bit proofs |
| inftrees.c proofs | decode_table_matches_format, short_decode_table_leaf_sound, decode_table_leaf_sound, decode_table_read_preserved, constructor_establishes_decode_table_invariant, decode_table_invariant_of_prefix, constructor_establishes_query_stability, short_rejected_leaf_stays_invalid, constructor_establishes_fast_leaf_flags, leaf_classification_agrees, inflate_table_content, inflate_table_decoder_safe, inflate_table_read_extent, constructor_root_bits, constructor_subtable_bits, heap-free mathematics, infback.c proofs, inffixed.h.input-meaning proofs, inflate storage and bit proofs, tree construction and emission proofs |
| libc-errno-cstring proofs | gz.read-gzread proofs, gz.read-load-error proofs, gzwrite.c proofs |
| public entry composition | adler32_combine, adler32_combine64, adler32_z, compress2_safety, compress2_z_safety, compressBound, compressBound_z, compress_safety, compress_z_safety, crc32_combine, crc32_combine64, crc32_combine_gen, crc32_combine_gen64, crc32_combine_op, deflateBound_safety, deflateBound_z_safety, deflateInit2__safety, get_crc_table, gz_sequence_nonvacuity, gz_sequence_safety, gzbuffer, gzbuffer_safety, gzclearerr_safety, gzclose_r_safety, gzclose_safety, gzclose_w_safety, gzdirect_safety, gzdopen, gzeof, gzeof_safety, gzerror, gzerror_safety, gzflush_safety, gzfread_safety, gzfwrite_safety, gzgetc__safety, gzgetc_safety, gzgets_safety, gzoffset, gzoffset64, gzoffset64_safety, gzoffset_safety, gzprintf_safety, gzputc_safety, gzputs_safety, gzread_safety, gzrewind, gzrewind_safety, gzseek64_safety, gzseek_safety, gzsetparams_safety, gztell64_safety, gztell_safety, gzungetc_safety, gzvprintf_safety, gzwrite_safety, inflateBackEnd, inflateBackInit_, inflateBackInit__safety, inflateInit2__safety, inflateSync_safety, inflate_back_initialisation_domain, inflate_refusal, uncompress2_safe, uncompress2_z_safe, uncompress_safe, uncompress_z_safe, zError, zlibVersion, adler32.c proofs, deflate lifecycle proofs, gz.inv-frame proofs, gz.inv-offset-rewind proofs, gz.inv-open proofs, gz.inv-open-path proofs, gz.inv-queries proofs, gz.read-look proofs, gz.read-store proofs, gzfs.error-message-store proofs, gzlib.c proofs, gzread.c proofs, inflate storage and bit proofs |
| runtime object and arithmetic lemmas | byte_modifies_preserve_bases, byte_stores_preserve_bases, every_layout_is_representable, LibcBorrow proofs, LibcBorrowLoops proofs, LibcBorrowPrimitives proofs, PlatformMemory proofs, crc32_all_byte_views, crc32_z_all_byte_views, actual_body_preserves_origin, actual_body_refines_token, actual_fast_preserves_origin, actual_distance_block_preserves_origin, actual_distance_refines_lz77, fast_safe, actual_body_retains_selected_length, actual_copy_match_refines_lz77, actual_pull_preserves_origin, actual_rollback_preserves_origin, decode_table_classifies_input, decode_table_matches_format, short_decode_table_leaf_sound, decode_table_leaf_sound, constructor_establishes_decode_table_invariant, constructor_establishes_query_stability, constructor_establishes_fast_leaf_flags, inflate_table_content, inflate_table_decoder_safe, inflate_table_read_extent, constructor_root_bits, constructor_subtable_bits, compress2_z_first_alloc_failure, adler32, adler32_safety, adler32_z, adler32_z_safety, crc32, crc32_combine64_safety, crc32_combine_gen64_safety, crc32_combine_gen_safety, crc32_combine_op_safety, crc32_combine_safety, crc32_safety, crc32_z, crc32_z_safety, deflateBound_safety, deflateBound_z_safety, deflateCopy, deflateCopy_safety, deflateEnd, deflateEnd_safety, deflateGetDictionary, deflateGetDictionary_safety, deflateInit2_, deflateInit2__safety, deflateInit_, deflateInit__safety, deflateParams_safety, deflatePending, deflatePending_safety, deflatePrime_safety, deflateReset, deflateResetKeep, deflateReset_safety, deflateSetDictionary_safety, deflateSetHeader, deflateSetHeader_safety, deflateTune, deflateTune_safety, deflateUsed, deflateUsed_safety, deflate_initialisation_domain, deflate_refusal, deflate_safety, get_crc_table, gz_refusal, gz_sequence_nonvacuity, gzbuffer_safety, gzclearerr, gzclearerr_safety, gzclose_r_safety, gzclose_safety, gzclose_w_safety, gzdirect_safety, gzdopen, gzdopen_safety, gzeof_safety, gzerror, gzerror_safety, gzflush_safety, gzfread_safety, gzfwrite_safety, gzgetc__safety, gzgetc_safety, gzgets_safety, gzoffset, gzoffset64, gzoffset64_safety, gzoffset_safety, gzopen64_safety, gzopen_safety, gzprintf_safety, gzputc_safety, gzputs_safety, gzread_safety, gzrewind, gzrewind_safety, gzseek64_safety, gzseek_safety, gzsetparams_safety, gztell64_safety, gztell_safety, gzungetc_safety, gzvprintf_safety, gzwrite_safety, inflate, inflateBackEnd, inflateBackEnd_safety, inflateBackInit_, inflateBackInit__safety, inflateBack_safety, inflateCodesUsed, inflateCopy, inflateCopy_safety, inflateEnd, inflateEnd_safety, inflateGetDictionary, inflateGetDictionary_safety, inflateGetHeader, inflateGetHeader_safety, inflateInit2_, inflateInit2__safety, inflateInit_, inflateInit__safety, inflateMark, inflateMark_safety, inflatePrime, inflatePrime_safety, inflateReset, inflateReset2, inflateReset2_safety, inflateResetKeep, inflateReset_safety, inflateSetDictionary, inflateSetDictionary_safety, inflateSyncPoint, inflateSync_safety, inflateUndermine, inflateValidate, inflate_back_initialisation_domain, inflate_back_sequence_safety, inflate_initialisation_domain, inflate_refusal, inflate_safety, uncompress2_safe, uncompress2_z_safe, uncompress_safe, uncompress_z_safe, zError, zlibVersion, zlibVersion_safety, adler32.c proofs, api-model proofs, borrowed-byte-frame proofs, checksum.borrow-stable proofs, crc32.c proofs, deflate construction proofs, deflate entry composition, deflate lifecycle proofs, deflate window and match proofs, gz.inv-clearerr proofs, gz.inv-close proofs, gz.inv-frame proofs, gz.inv-offset-rewind proofs, gz.inv-open proofs, gz.inv-open-fd proofs, gz.inv-open-fresh proofs, gz.inv-open-path proofs, gz.inv-put-scalars proofs, gz.inv-queries proofs, gz.inv-reset proofs, gz.inv-seek proofs, gz.read-assembly proofs, gz.read-avail proofs, gz.read-budget proofs, gz.read-close proofs, gz.read-decomp proofs, gz.read-direct-step proofs, gz.read-fetch proofs, gz.read-getc-step proofs, gz.read-gets-step proofs, gz.read-gzread proofs, gz.read-leaf-common proofs, gz.read-load-error proofs, gz.read-look proofs, gz.read-read proofs, gz.read-store proofs, gz.sequence-safety proofs, gzfs proofs, gzfs.borrow-stable proofs, gzfs.error-message-store proofs, gzfs.format-error-message proofs, gzlib.c proofs, gzread.c proofs, gzwrite.c proofs, heap-free mathematics, infback.c proofs, inffast.c proofs, inflate entry composition, inflate mode and exit proofs, inflate storage and bit proofs, inftrees.c proofs, libc-errno-cstring proofs, public entry composition, specification lemmas, tree construction and emission proofs, zlib.h.gzgetc-macro proofs, zutil.c proofs |
| specification lemmas | every_existing_heap_accepts_layout, actual_body_preserves_origin, actual_body_refines_token, actual_fast_preserves_origin, actual_distance_block_preserves_origin, actual_distance_refines_lz77, distance_lookup_matches_format, fast_safe, length_lookup_matches_format, actual_body_retains_selected_length, actual_copy_match_refines_lz77, actual_drop_preserves_origin, actual_pull_preserves_origin, actual_rollback_preserves_origin, drop_preserves_origin, initial_origin, pull_preserves_origin, rollback_preserves_origin, decode_table_matches_format, short_decode_table_leaf_sound, decode_table_leaf_sound, constructor_establishes_decode_table_invariant, decode_table_invariant_of_prefix, constructor_establishes_query_stability, short_rejected_leaf_stays_invalid, constructor_establishes_fast_leaf_flags, inflate_table_decoder_safe, inflate_table_read_extent, constructor_root_bits, constructor_subtable_bits, compress_bound_adequate, compress_roundtrip, deflate_bound_adequate, deflate_completes, deflate_full_flush_resync, deflate_valid, dict_roundtrip, header_roundtrip, inflate_completes, inflate_decodes, inflate_deferred_distance, roundtrip, roundtrip_completes, deflateCopy_safety, deflateEnd, deflateGetDictionary, deflateInit2_, deflateInit2__safety, deflateInit_, deflateReset, deflateResetKeep, deflateSetHeader, deflateTune, deflateUsed, deflate_initialisation_domain, gzdopen, inflateCopy, inflateCopy_safety, inflateEnd, inflateGetDictionary, inflateSetDictionary, inflateSyncPoint, inflateUndermine, inflateValidate, api-model proofs, deflate construction proofs, deflate entry composition, deflate lifecycle proofs, deflate window and match proofs, gz.inv-clearerr proofs, gz.inv-close proofs, gz.inv-frame proofs, gz.inv-model proofs, gz.inv-offset-rewind proofs, gz.inv-open proofs, gz.inv-put-scalars proofs, gz.inv-queries proofs, gz.inv-reset proofs, gz.inv-seek proofs, gz.read-avail proofs, gz.read-close proofs, gz.read-decomp proofs, gz.read-direct-step proofs, gz.read-fetch proofs, gz.read-getc-step proofs, gz.read-gets-step proofs, gz.read-gzread proofs, gz.read-leaf-common proofs, gz.read-load-error proofs, gz.read-look proofs, gz.read-read proofs, gz.read-store proofs, gzlib.c proofs, gzread.c proofs, gzwrite.c proofs, infback.c proofs, inffast.c proofs, inflate entry composition, inflate storage and bit proofs, inftrees.c proofs, public entry composition, tree construction and emission proofs, zlib.h.gzgetc-macro proofs |
| tree construction and emission proofs | deflate construction proofs, deflate entry composition, deflate lifecycle proofs, deflate window and match proofs, gzwrite.c proofs, heap-free mathematics, public entry composition |
| zlib.h.gzgetc-macro proofs | gz.sequence-safety proofs |
| zutil.c proofs | inflate_table_content, deflate construction proofs, deflate lifecycle proofs, gzfs.error-message-store proofs, gzlib.c proofs, gzwrite.c proofs, infback.c proofs, inflate entry composition, inflate mode and exit proofs, inflate storage and bit proofs, inftrees.c proofs |

## Other registered theorems

These declarations are registered supporting execution results, lemmas or witnesses.
They are not additional fixed targets and do not grant a caller coverage colour.

| Declaration | Used by a fixed-target proof |
| --- | --- |
| [Zlib.Adler32.Proofs.adler32_combine64_safe](../ZlibF/Proof/adler32.c.lean#L977) | No fixed-target composition recorded |
| [Zlib.Adler32.Proofs.adler32_combine_c_safe](../ZlibF/Proof/adler32.c.lean#L982) | [adler32_combine](#target-zlibf-spec-public-goal-adler32-combine), [adler32_combine64](#target-zlibf-spec-public-goal-adler32-combine64) |
| [Zlib.Adler32.Proofs.adler32_combine_correct](../ZlibF/Proof/adler32.c.lean#L953) | No fixed-target composition recorded |
| [Zlib.Adler32.Proofs.adler32_combine_safe](../ZlibF/Proof/adler32.c.lean#L941) | [adler32_combine](#target-zlibf-spec-public-goal-adler32-combine), [adler32_combine64](#target-zlibf-spec-public-goal-adler32-combine64) |
| [Zlib.Adler32.Proofs.adler32_safe](../ZlibF/Proof/adler32.c.lean#L987) | No fixed-target composition recorded |
| [Zlib.Adler32.Proofs.adler32_z_correct](../ZlibF/Proof/adler32.c.lean#L786) | No fixed-target composition recorded |
| [Zlib.Adler32.Proofs.adler32_z_correct_ne_one](../ZlibF/Proof/adler32.c.lean#L798) | No fixed-target composition recorded |
| [Zlib.Adler32.Proofs.adler32_z_safe](../ZlibF/Proof/adler32.c.lean#L809) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.addrOf_safe](../ZlibF/Proof/crc32.c.lean#L2467) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.blockLittle_safe](../ZlibF/Proof/crc32.c.lean#L2461) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.braidTab_safe](../ZlibF/Proof/crc32.c.lean#L2457) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crc32_combine64_correct](../ZlibF/Proof/crc32.c.lean#L2380) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crc32_combine64_safe](../ZlibF/Proof/crc32.c.lean#L2374) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crc32_combine_correct](../ZlibF/Proof/crc32.c.lean#L2395) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crc32_combine_gen64_correct](../ZlibF/Proof/crc32.c.lean#L2330) | [crc32_combine_gen](#target-zlibf-spec-public-goal-crc32-combine-gen), [crc32_combine_gen64](#target-zlibf-spec-public-goal-crc32-combine-gen64), [crc32_combine_op](#target-zlibf-spec-public-goal-crc32-combine-op) |
| [Zlib.Crc32.Proofs.crc32_combine_gen64_safe](../ZlibF/Proof/crc32.c.lean#L2320) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crc32_combine_gen_correct](../ZlibF/Proof/crc32.c.lean#L2349) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crc32_combine_gen_safe](../ZlibF/Proof/crc32.c.lean#L2343) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crc32_combine_op_correct](../ZlibF/Proof/crc32.c.lean#L2403) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crc32_combine_op_diverges](../ZlibF/Proof/crc32.c.lean#L2368) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crc32_combine_op_safe](../ZlibF/Proof/crc32.c.lean#L2359) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crc32_combine_safe](../ZlibF/Proof/crc32.c.lean#L2390) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crc32_correct](../ZlibF/Proof/crc32.c.lean#L2223) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Crc32.Proofs.crc32_null](../ZlibF/Proof/crc32.c.lean#L2219) | [crc32](#target-zlibf-spec-public-goal-crc32), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Crc32.Proofs.crc32_safe](../ZlibF/Proof/crc32.c.lean#L2232) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crc32_z_correct](../ZlibF/Proof/crc32.c.lean#L2199) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Crc32.Proofs.crc32_z_null](../ZlibF/Proof/crc32.c.lean#L2186) | [crc32](#target-zlibf-spec-public-goal-crc32), [crc32_z](#target-zlibf-spec-public-goal-crc32-z), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Crc32.Proofs.crc32_z_safe](../ZlibF/Proof/crc32.c.lean#L2213) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crcByte_safe](../ZlibF/Proof/crc32.c.lean#L2445) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crcTab_safe](../ZlibF/Proof/crc32.c.lean#L2436) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crc_word_big_safe](../ZlibF/Proof/crc32.c.lean#L2485) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crc_word_correct](../ZlibF/Proof/crc32.c.lean#L2419) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.crc_word_safe](../ZlibF/Proof/crc32.c.lean#L2414) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.get_crc_table_correct](../ZlibF/Proof/crc32.c.lean#L2245) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.get_crc_table_safe](../ZlibF/Proof/crc32.c.lean#L2240) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.loadWord_safe](../ZlibF/Proof/crc32.c.lean#L2431) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.multmodp_correct](../ZlibF/Proof/crc32.c.lean#L2279) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.multmodp_diverges](../ZlibF/Proof/crc32.c.lean#L982) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.multmodp_safe](../ZlibF/Proof/crc32.c.lean#L2272) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.shr64_safe](../ZlibF/Proof/crc32.c.lean#L2471) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.wordAt_safe](../ZlibF/Proof/crc32.c.lean#L2452) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.x2nTab_safe](../ZlibF/Proof/crc32.c.lean#L2440) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.x2nmodp_correct](../ZlibF/Proof/crc32.c.lean#L2303) | No fixed-target composition recorded |
| [Zlib.Crc32.Proofs.x2nmodp_safe](../ZlibF/Proof/crc32.c.lean#L2295) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.CommonInitializedDataTrace.cleanup](../ZlibF/Proof/deflate.c.engine.common-initialized-history-environment.lean) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.CommonInitializedDataTrace.completed](../ZlibF/Proof/deflate.c.engine.common-initialized-data-history.lean) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.CommonInitializedDataTrace.completes](../ZlibF/Proof/deflate.c.engine.common-initialized-history-completes.lean) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.CommonInitializedDataTrace.completes_post](../ZlibF/Proof/deflate.c.engine.common-initialized-history-completes.lean) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.CommonInitializedDataTrace.encoding](../ZlibF/Proof/deflate.c.engine.common-initialized-data-history.lean) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.CommonInitializedDataTrace.environment](../ZlibF/Proof/deflate.c.engine.common-initialized-history-environment.lean) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.CommonInitializedDataTrace.finish_continuation](../ZlibF/Proof/deflate.c.engine.common-initialized-history-completes.lean) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.CommonInitializedEncodingState.ordinary_encoding_request](../ZlibF/Proof/deflate.c.engine.common-initialized-request.lean) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.CommonNoFlushDataTrace.cleanup](../ZlibF/Proof/deflate.c.engine.common-no-flush-history-environment.lean) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.CommonNoFlushDataTrace.completed](../ZlibF/Proof/deflate.c.engine.common-no-flush-data-history.lean) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.CommonNoFlushDataTrace.completes](../ZlibF/Proof/deflate.c.engine.common-no-flush-history-completes.lean) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.CommonNoFlushDataTrace.encoding](../ZlibF/Proof/deflate.c.engine.common-no-flush-data-history.lean) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.CommonNoFlushDataTrace.environment](../ZlibF/Proof/deflate.c.engine.common-no-flush-history-environment.lean) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.CommonNoFlushDataTrace.finish_continuation](../ZlibF/Proof/deflate.c.engine.common-no-flush-history-completes.lean) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.CommonOrdinaryDataTrace.cleanup](../ZlibF/Proof/deflate.c.engine.common-ordinary-history-environment.lean) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.CommonOrdinaryDataTrace.completed](../ZlibF/Proof/deflate.c.engine.common-ordinary-data-history.lean) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.CommonOrdinaryDataTrace.completes](../ZlibF/Proof/deflate.c.engine.common-ordinary-history-completes.lean) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.CommonOrdinaryDataTrace.encoding](../ZlibF/Proof/deflate.c.engine.common-ordinary-data-history.lean) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.CommonOrdinaryDataTrace.environment](../ZlibF/Proof/deflate.c.engine.common-ordinary-history-environment.lean) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.CommonOrdinaryDataTrace.finish_continuation](../ZlibF/Proof/deflate.c.engine.common-ordinary-history-completes.lean) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.DefaultEncodingState.generic_basic_full_request](../ZlibF/Proof/deflate.c.engine.generic-basic-full-contract.lean) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.DefaultFinishBoundary.follow_finish_continuation_end_status](../ZlibF/Proof/deflate.c.engine.generic-continuation-end-status.lean) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.GenericDefaultRequestTrace.completes_with_original_birth_cleanup](../ZlibF/Proof/deflate.c.engine.generic-completion-lifetime.lean) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.GenericDefaultRequestTrace.full_next_request_contract](../ZlibF/Proof/deflate.c.engine.generic-basic-history-full-contract.lean) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.INSERT_STRING_ok](../ZlibF/Proof/deflate.c.engine.macros.lean#L177) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.UPDATE_HASH_ok](../ZlibF/Proof/deflate.c.engine.macros.lean#L147) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.chain_ok_of_chains](../ZlibF/Proof/deflate.c.engine.chains.lean#L194) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.chains_insert](../ZlibF/Proof/deflate.c.engine.chains.lean#L76) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.chains_slide](../ZlibF/Proof/deflate.c.engine.chains.lean#L138) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.common_initialized_level_four_complete_witness](../ZlibF/Proof/deflate.c.engine.common-initialized-data-history.lean#L93) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.common_no_flush_level_four_complete_witness](../ZlibF/Proof/deflate.c.engine.common-no-flush-history-witness.lean#L41) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.common_observed_initialization_encoding_state](../ZlibF/Proof/deflate.c.engine.common-initialized-state-init.lean#L15) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.common_observed_initialization_first_ordinary_encoding](../ZlibF/Proof/deflate.c.engine.common-initial-first-ordinary-encoding.lean#L15) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.common_observed_initialization_no_flush_encoding](../ZlibF/Proof/deflate.c.engine.common-initial-no-flush-encoding.lean#L14) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.common_ordinary_level_four_complete_witness](../ZlibF/Proof/deflate.c.engine.common-ordinary-history-witness.lean#L50) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.default_init_all_scalar_full_request_contract](../ZlibF/Proof/deflate.c.engine.all-scalar-full-contract.lean#L14) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.default_public_full_contract_witness](../ZlibF/Proof/deflate.c.engine.full-contract-witness.lean#L15) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.fill_fit](../ZlibF/Proof/deflate.c.engine.window.lean#L45) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.fill_post_room](../ZlibF/Proof/deflate.c.engine.window.lean#L40) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.form_init](../ZlibF/Proof/deflate.c.engine.hash.lean#L126) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.generic_default_public_contract](../ZlibF/Proof/deflate.c.default-public-contract.lean#L19) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.generic_default_request_trace_witness](../ZlibF/Proof/deflate.c.default-public-contract.lean#L62) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.header_ref_bound_128w](../ZlibF/Proof/deflate.c.engine.overlay-header-ref.lean#L290) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.header_ref_bound_256](../ZlibF/Proof/deflate.c.engine.overlay-header-ref.lean#L245) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.hkey_third](../ZlibF/Proof/deflate.c.engine.hash.lean#L139) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.lm_body_ok](../ZlibF/Proof/deflate.c.engine.lmbody.lean#L102) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.lm_inner_loop](../ZlibF/Proof/deflate.c.engine.lminner.lean#L114) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.lm_loop_ok](../ZlibF/Proof/deflate.c.engine.lmmain.lean#L77) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.longest_match_ok](../ZlibF/Proof/deflate.c.engine.lmmain.lean#L212) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.matchLen_agree](../ZlibF/Proof/deflate.c.engine.match.lean#L100) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.memory_fast_initialization_witness](../ZlibF/Proof/deflate.c.engine.memory-fast-initial.lean#L51) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.memory_fast_observed_initialization](../ZlibF/Proof/deflate.c.engine.memory-fast-observed-initial.lean#L49) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.memory_slow_initialized_state](../ZlibF/Proof/deflate.c.engine.memory-slow-initialized-state.lean#L62) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.memory_slow_observed_initialization](../ZlibF/Proof/deflate.c.engine.memory-slow-observed-initial.lean#L55) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.public_common_first_finish_encoding_input](../ZlibF/Proof/deflate.c.engine.common-first-finish-encoding.lean#L16) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.public_common_first_finish_encoding_state](../ZlibF/Proof/deflate.c.engine.common-first-finish-state.lean#L15) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.public_common_first_no_flush_encoding_input](../ZlibF/Proof/deflate.c.engine.common-first-input.lean#L16) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.public_common_first_no_flush_encoding_state](../ZlibF/Proof/deflate.c.engine.common-first-encoding-state.lean#L14) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.putShortMSB_ok](../ZlibF/Proof/deflate.c.engine.macros.lean#L119) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.put_byte_ok](../ZlibF/Proof/deflate.c.engine.macros.lean#L96) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.read_buf_ok](../ZlibF/Proof/deflate.c.engine.readbuf.lean#L99) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.read_buf_zero](../ZlibF/Proof/deflate.c.engine.readbuf.lean#L75) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.slide_copy](../ZlibF/Proof/deflate.c.engine.window.lean#L52) | No fixed-target composition recorded |
| [Zlib.Deflate.Engine.Proofs.slide_hash_ok](../ZlibF/Proof/deflate.c.engine.slide.lean#L166) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.tinyOverlay](../ZlibF/Proof/deflate.c.engine.overlay-header-ref.lean#L352) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.tinyOverlayAt_128](../ZlibF/Proof/deflate.c.engine.overlay-header-ref.lean#L347) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.tinyOverlayAt_256](../ZlibF/Proof/deflate.c.engine.overlay-header-ref.lean#L342) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Engine.Proofs.upd3_indep](../ZlibF/Proof/deflate.c.engine.hash.lean#L45) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Proofs.MemoryInit.public_valid_memory_init_lifecycle](../ZlibF/Proof/deflate.c.init.memory-lifecycle.lean#L13) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.MemoryInit.public_valid_memory_init_total](../ZlibF/Proof/deflate.c.init.memory-total.lean#L16) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflateBound_nostate](../ZlibF/Proof/deflate.c.life.bound.lean#L330) | [deflateBound_safety](#target-zlibf-spec-public-goal-deflatebound-safety) |
| [Zlib.Deflate.Proofs.deflateBound_safe](../ZlibF/Proof/deflate.c.life.bound.lean#L319) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Proofs.deflateBound_z_nostate](../ZlibF/Proof/deflate.c.life.bound.lean#L312) | [deflateBound_safety](#target-zlibf-spec-public-goal-deflatebound-safety), [deflateBound_z_safety](#target-zlibf-spec-public-goal-deflatebound-z-safety) |
| [Zlib.Deflate.Proofs.deflateBound_z_safe](../ZlibF/Proof/deflate.c.life.bound.lean#L302) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Proofs.deflateEnd_reject](../ZlibF/Proof/deflate.c.life.end.lean#L321) | [deflateEnd_safety](#target-zlibf-spec-public-goal-deflateend-safety) |
| [Zlib.Deflate.Proofs.deflateEnd_safe](../ZlibF/Proof/deflate.c.life.end.lean#L270) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflateEnd](#target-zlibf-spec-public-goal-deflateend), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Proofs.deflateGetDictionary_reject](../ZlibF/Proof/deflate.c.life.getdict.lean#L202) | [deflate_refusal](#target-zlibf-spec-public-goal-deflate-refusal) |
| [Zlib.Deflate.Proofs.deflatePending_reject](../ZlibF/Proof/deflate.c.life.check.lean#L173) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflatePending_safe](../ZlibF/Proof/deflate.c.life.check.lean#L146) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflatePrime_invalid_count](../ZlibF/Proof/deflate.c.prime.lean#L24) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Proofs.deflatePrime_refused](../ZlibF/Proof/deflate.c.prime.lean#L15) | [deflatePrime_safety](#target-zlibf-spec-public-goal-deflateprime-safety) |
| [Zlib.Deflate.Proofs.deflateResetKeep_reject](../ZlibF/Proof/deflate.c.life.reset.lean#L424) | [deflateReset_safety](#target-zlibf-spec-public-goal-deflatereset-safety) |
| [Zlib.Deflate.Proofs.deflateResetKeep_safe](../ZlibF/Proof/deflate.c.life.reset.lean#L367) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflateReset](#target-zlibf-spec-public-goal-deflatereset), [deflateResetKeep](#target-zlibf-spec-public-goal-deflateresetkeep), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Proofs.deflateReset_reject](../ZlibF/Proof/deflate.c.life.reset.lean#L430) | [deflateReset_safety](#target-zlibf-spec-public-goal-deflatereset-safety) |
| [Zlib.Deflate.Proofs.deflateReset_safe](../ZlibF/Proof/deflate.c.life.reset.lean#L401) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflateReset](#target-zlibf-spec-public-goal-deflatereset), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Proofs.deflateSetHeader_not_gzip](../ZlibF/Proof/deflate.c.life.check.lean#L92) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflateSetHeader_reject](../ZlibF/Proof/deflate.c.life.check.lean#L98) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflateSetHeader_safe](../ZlibF/Proof/deflate.c.life.check.lean#L83) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Proofs.deflateStateCheck_total](../ZlibF/Proof/deflate.c.base.lean#L631) | [deflateBound_safety](#target-zlibf-spec-public-goal-deflatebound-safety), [deflateBound_z_safety](#target-zlibf-spec-public-goal-deflatebound-z-safety), [deflateEnd_safety](#target-zlibf-spec-public-goal-deflateend-safety), [deflatePending](#target-zlibf-spec-public-goal-deflatepending), [deflatePrime_safety](#target-zlibf-spec-public-goal-deflateprime-safety), [deflateReset_safety](#target-zlibf-spec-public-goal-deflatereset-safety), [deflateSetHeader](#target-zlibf-spec-public-goal-deflatesetheader), [deflateTune](#target-zlibf-spec-public-goal-deflatetune), [deflateUsed](#target-zlibf-spec-public-goal-deflateused), [deflate_refusal](#target-zlibf-spec-public-goal-deflate-refusal), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Proofs.deflateTune_reject](../ZlibF/Proof/deflate.c.life.check.lean#L54) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflateTune_safe](../ZlibF/Proof/deflate.c.life.check.lean#L44) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Proofs.deflateUsed_reject](../ZlibF/Proof/deflate.c.life.check.lean#L119) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.deflateUsed_safe](../ZlibF/Proof/deflate.c.life.check.lean#L113) | No fixed-target composition recorded |
| [Zlib.Deflate.Proofs.lm_init_safe](../ZlibF/Proof/deflate.c.life.reset.lean#L151) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflateReset](#target-zlibf-spec-public-goal-deflatereset), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Universal.Call.flush_pending_cursor](../ZlibF/Proof/deflate.c.universal-flush-cursor.lean#L157) | No fixed-target composition recorded |
| [Zlib.Deflate.Universal.copy_callfacts](../ZlibF/Proof/deflate.c.universal-ops-copy.lean#L868) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Universal.copy_header](../ZlibF/Proof/deflate.c.universal-ops-copy.lean#L857) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Universal.copy_inv](../ZlibF/Proof/deflate.c.universal-ops-copy.lean#L848) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Universal.prime_callfacts](../ZlibF/Proof/deflate.c.universal-ops-callfacts.lean#L99) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Universal.resetKeep_refuse](../ZlibF/Proof/deflate.c.universal-ops-resetkeep.lean#L64) | No fixed-target composition recorded |
| [Zlib.Deflate.Universal.resetKeep_single](../ZlibF/Proof/deflate.c.universal-ops-resetkeep.lean#L31) | No fixed-target composition recorded |
| [Zlib.Deflate.Universal.reset_callfacts](../ZlibF/Proof/deflate.c.universal-ops-callfacts.lean#L43) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Universal.setDictionary_callfacts](../ZlibF/Proof/deflate.c.universal-ops-dictionary-slid.lean#L158) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Universal.setDictionary_header](../ZlibF/Proof/deflate.c.universal-ops-dictionary-slid.lean#L135) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Universal.setHeader_callfacts](../ZlibF/Proof/deflate.c.universal-ops-callfacts.lean#L77) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Universal.step_prime](../ZlibF/Proof/deflate.c.universal-ops-prime.lean#L565) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Universal.step_reset](../ZlibF/Proof/deflate.c.universal-ops-reset.lean#L85) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Universal.step_setDictionary](../ZlibF/Proof/deflate.c.universal-ops-dictionary-slid.lean#L121) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Deflate.Universal.tune_callfacts](../ZlibF/Proof/deflate.c.universal-ops-callfacts.lean#L64) | [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Gzclose.Proofs.gzclose_dispatch](../ZlibF/Proof/gzclose.c.lean#L22) | No fixed-target composition recorded |
| [Zlib.Gzclose.Proofs.gzclose_null](../ZlibF/Proof/gzclose.c.lean#L17) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.GT_OFF_run](../ZlibF/Proof/gzlib.c.simple.lean#L46) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Gzlib.Proofs.gz_error_null_run](../ZlibF/Proof/gzlib.c.error.lean#L134) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gz_intmax_run](../ZlibF/Proof/gzlib.c.simple.lean#L43) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gz_open_alloc_failure](../ZlibF/Proof/gzlib.c.open.lean#L36) | [gz_sequence_nonvacuity](#target-zlibf-spec-public-goal-gz-sequence-nonvacuity), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [gzdopen](#target-zlibf-spec-public-goal-gzdopen) |
| [Zlib.Gzlib.Proofs.gz_open_null](../ZlibF/Proof/gzlib.c.open.lean#L18) | [gz_sequence_nonvacuity](#target-zlibf-spec-public-goal-gz-sequence-nonvacuity), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [gzdopen](#target-zlibf-spec-public-goal-gzdopen) |
| [Zlib.Gzlib.Proofs.gz_reset_run](../ZlibF/Proof/gzlib.c.error.lean#L145) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gz_reset_safe](../ZlibF/Proof/gzlib.c.error.lean#L168) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzbuffer_null](../ZlibF/Proof/gzlib.c.simple.lean#L52) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzbuffer_run](../ZlibF/Proof/gzlib.c.simple.lean#L67) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzbuffer_safe](../ZlibF/Proof/gzlib.c.simple.lean#L84) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzclearerr_null](../ZlibF/Proof/gzlib.c.simple.lean#L191) | [gzclearerr](#target-zlibf-spec-public-goal-gzclearerr) |
| [Zlib.Gzlib.Proofs.gzclearerr_run](../ZlibF/Proof/gzlib.c.simple.lean#L199) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzclearerr_safe](../ZlibF/Proof/gzlib.c.simple.lean#L210) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzdopen_alloc_failure](../ZlibF/Proof/gzlib.c.open.lean#L62) | [gz_sequence_nonvacuity](#target-zlibf-spec-public-goal-gz-sequence-nonvacuity), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [gzdopen](#target-zlibf-spec-public-goal-gzdopen) |
| [Zlib.Gzlib.Proofs.gzdopen_joint_witness](../ZlibF/Proof/gzlib.c.dopen-joint-witness.lean#L92) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzdopen_negative](../ZlibF/Proof/gzlib.c.open.lean#L55) | [gz_sequence_nonvacuity](#target-zlibf-spec-public-goal-gz-sequence-nonvacuity), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [gzdopen](#target-zlibf-spec-public-goal-gzdopen) |
| [Zlib.Gzlib.Proofs.gzeof_null](../ZlibF/Proof/gzlib.c.simple.lean#L108) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzeof_run](../ZlibF/Proof/gzlib.c.simple.lean#L111) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzerror_null_file](../ZlibF/Proof/gzlib.c.simple.lean#L159) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzerror_run](../ZlibF/Proof/gzlib.c.simple.lean#L163) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzoffset64_null](../ZlibF/Proof/gzlib.c.rewind.lean#L103) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzoffset64_run](../ZlibF/Proof/gzlib.c.rewind.lean#L107) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzoffset_eq](../ZlibF/Proof/gzlib.c.rewind.lean#L129) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Gzlib.Proofs.gzopen64_alloc_failure](../ZlibF/Proof/gzlib.c.open.lean#L49) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzopen64_null](../ZlibF/Proof/gzlib.c.open.lean#L30) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzopen_alloc_failure](../ZlibF/Proof/gzlib.c.open.lean#L43) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzopen_null](../ZlibF/Proof/gzlib.c.open.lean#L25) | [gz_sequence_nonvacuity](#target-zlibf-spec-public-goal-gz-sequence-nonvacuity), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Gzlib.Proofs.gzrewind_null](../ZlibF/Proof/gzlib.c.rewind.lean#L73) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzrewind_spec](../ZlibF/Proof/gzlib.c.rewind.lean#L78) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzseek64_dangling_next_ok](../ZlibF/Proof/gzlib.c.seek.lean#L1053) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzseek64_head](../ZlibF/Proof/gzlib.c.seek.lean#L375) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Gzlib.Proofs.gzseek64_head_any](../ZlibF/Proof/gzlib.c.seek.lean#L232) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Gzlib.Proofs.gzseek64_null](../ZlibF/Proof/gzlib.c.seek.lean#L924) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzseek64_refuse](../ZlibF/Proof/gzlib.c.seek.lean#L956) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Gzlib.Proofs.gzseek64_safe](../ZlibF/Proof/gzlib.c.seek.lean#L931) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzseek64_set_negpos_refuse](../ZlibF/Proof/gzlib.c.seek.lean#L987) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gzseek64_write_run](../ZlibF/Proof/gzlib.c.seek.lean#L388) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Gzlib.Proofs.gzseek_eq](../ZlibF/Proof/gzlib.c.seek.lean#L969) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Gzlib.Proofs.gztell64_null](../ZlibF/Proof/gzlib.c.simple.lean#L122) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gztell64_spec](../ZlibF/Proof/gzlib.c.simple.lean#L143) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gztell_null](../ZlibF/Proof/gzlib.c.simple.lean#L154) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.gztell_run](../ZlibF/Proof/gzlib.c.simple.lean#L148) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.seekTail_back](../ZlibF/Proof/gzlib.c.seek.lean#L593) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Gzlib.Proofs.seekTail_copy](../ZlibF/Proof/gzlib.c.seek.lean#L429) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Gzlib.Proofs.seekTail_copy_ub](../ZlibF/Proof/gzlib.c.seek.lean#L1064) | No fixed-target composition recorded |
| [Zlib.Gzlib.Proofs.seekTail_fwd](../ZlibF/Proof/gzlib.c.seek.lean#L491) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Gzlib.Proofs.seekTail_fwd_empty](../ZlibF/Proof/gzlib.c.seek.lean#L1004) | No fixed-target composition recorded |
| [Zlib.Gzread.Proofs.gzclose_r_null](../ZlibF/Proof/gzread.c.close.lean#L44) | No fixed-target composition recorded |
| [Zlib.Gzread.Proofs.gzclose_r_unbuffered](../ZlibF/Proof/gzread.c.close.lean#L58) | No fixed-target composition recorded |
| [Zlib.Gzread.Proofs.gzclose_r_unbuffered_frame](../ZlibF/Proof/gzread.c.close.lean#L80) | No fixed-target composition recorded |
| [Zlib.Gzread.Proofs.gzclose_r_wrong_mode](../ZlibF/Proof/gzread.c.close.lean#L48) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Infback.Proofs.NEEDBITS_run](../ZlibF/Proof/infback.c.macros.lean#L240) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.PULLBYTE_run](../ZlibF/Proof/infback.c.macros.lean#L156) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.PULL_run](../ZlibF/Proof/infback.c.pull.lean#L16) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.ROOM_inv](../ZlibF/Proof/infback.c.stored.lean#L35) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.ROOM_run](../ZlibF/Proof/infback.c.room.lean#L27) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.TYPE_last](../ZlibF/Proof/infback.c.inv.lean#L87) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.TYPE_more](../ZlibF/Proof/infback.c.inv.lean#L145) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.backInit_witness](../ZlibF/Proof/infback.c.callbacks.lean#L143) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.badMode_run](../ZlibF/Proof/infback.c.inv.lean#L127) | [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety) |
| [Zlib.Infback.Proofs.inFinite_eof](../ZlibF/Proof/infback.c.macros.lean#L304) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.inflateBackEnd_nullstream](../ZlibF/Proof/infback.c.end.lean#L23) | [inflateBackEnd](#target-zlibf-spec-public-goal-inflatebackend) |
| [Zlib.Infback.Proofs.inflateBackEnd_ok](../ZlibF/Proof/infback.c.end.lean#L35) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.inflateBackEnd_refused](../ZlibF/Proof/infback.c.end.lean#L27) | [inflateBackEnd](#target-zlibf-spec-public-goal-inflatebackend) |
| [Zlib.Infback.Proofs.inflateBackInit__nullstream](../ZlibF/Proof/infback.c.init.lean#L239) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.inflateBackInit__ok](../ZlibF/Proof/infback.c.init.lean#L147) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.inflateBackInit__safe](../ZlibF/Proof/infback.c.init.lean#L203) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.inflateBack_eof](../ZlibF/Proof/infback.c.back.lean#L134) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.inflateBack_eof_witness](../ZlibF/Proof/infback.c.back.lean#L175) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.inflateBack_nostate](../ZlibF/Proof/infback.c.back.lean#L124) | [inflateBack_safety](#target-zlibf-spec-public-goal-inflateback-safety) |
| [Zlib.Infback.Proofs.inflateBack_nullstream](../ZlibF/Proof/infback.c.back.lean#L119) | [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety) |
| [Zlib.Infback.Proofs.order_inj](../ZlibF/Proof/infback.c.pure.lean#L17) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.order_lt](../ZlibF/Proof/infback.c.pure.lean#L14) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.order_surj](../ZlibF/Proof/infback.c.pure.lean#L21) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.storedTail_run](../ZlibF/Proof/infback.c.stored.lean#L125) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.stored_body_run](../ZlibF/Proof/infback.c.stored.lean#L285) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.stored_check](../ZlibF/Proof/infback.c.pure.lean#L35) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.stored_len_toNat](../ZlibF/Proof/infback.c.pure.lean#L58) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.stored_loop_run](../ZlibF/Proof/infback.c.stored.lean#L406) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.stored_run](../ZlibF/Proof/infback.c.stored.lean#L459) | No fixed-target composition recorded |
| [Zlib.Infback.Proofs.xwhileBrk_wf](../ZlibF/Proof/infback.c.wf.lean#L16) | [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety) |
| [Zlib.Inffast.Proofs.distfix_tableSafe](../ZlibF/Proof/inffast.c.tableok.lean#L43) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inffast.Proofs.lenfix_tableSafe](../ZlibF/Proof/inffast.c.tableok.lean#L29) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.BITS_run](../ZlibF/Proof/inflate.c.main.macros.lean#L224) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.BITS_toNat](../ZlibF/Proof/inflate.c.main.macros.lean#L234) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.BYTEBITS_inv](../ZlibF/Proof/inflate.c.main.macros.lean#L293) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.BYTEBITS_run](../ZlibF/Proof/inflate.c.main.macros.lean#L283) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.DROPBITS_inv](../ZlibF/Proof/inflate.c.main.macros.lean#L251) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.DROPBITS_run](../ZlibF/Proof/inflate.c.main.macros.lean#L241) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.INITBITS_inv](../ZlibF/Proof/inflate.c.main.macros.lean#L304) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.NEEDBITS_run](../ZlibF/Proof/inflate.c.main.macros.lean#L150) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.PULLBYTE_succ](../ZlibF/Proof/inflate.c.main.macros.lean#L89) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.PULLBYTE_zero](../ZlibF/Proof/inflate.c.main.macros.lean#L44) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.UPDATE_CHECK_run](../ZlibF/Proof/inflate.c.main.check.lean#L21) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.bytesBits_eq_bytesToBits](../ZlibF/Proof/inflate.c.main.bits.lean#L107) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateCodesUsed_spec](../ZlibF/Proof/inflate.c.misc.lean#L180) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflateEnd_safe](../ZlibF/Proof/inflate.c.end.lean#L119) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflateEnd](#target-zlibf-spec-public-goal-inflateend), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflateGetDictionary_spec](../ZlibF/Proof/inflate.c.dict.lean#L82) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateGetHeader_check](../ZlibF/Proof/inflate.c.hdr.lean#L54) | [inflateGetHeader_safety](#target-zlibf-spec-public-goal-inflategetheader-safety) |
| [Zlib.Inflate.Proofs.inflateGetHeader_nogzip](../ZlibF/Proof/inflate.c.hdr.lean#L64) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflateGetHeader_null_faults](../ZlibF/Proof/inflate.c.hdr.lean#L114) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateGetHeader_ok](../ZlibF/Proof/inflate.c.hdr.lean#L80) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflateInit2_ok](../ZlibF/Proof/inflate.c.start.lean#L237) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflateInit2_](#target-zlibf-spec-public-goal-inflateinit2), [inflateInit_](#target-zlibf-spec-public-goal-inflateinit), [inflate_initialisation_domain](#target-zlibf-spec-public-goal-inflate-initialisation-domain), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflateInit2_safe](../ZlibF/Proof/inflate.c.start.lean#L324) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateInit__ok](../ZlibF/Proof/inflate.c.hdr.lean#L160) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateInit__safe](../ZlibF/Proof/inflate.c.hdr.lean#L134) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateMark_spec](../ZlibF/Proof/inflate.c.misc.lean#L140) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflatePrime_spec](../ZlibF/Proof/inflate.c.misc2.lean#L28) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflateReset2_safe](../ZlibF/Proof/inflate.c.init.lean#L395) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflateResetKeep_safe](../ZlibF/Proof/inflate.c.base.lean#L460) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflateReset_safe](../ZlibF/Proof/inflate.c.reset.lean#L160) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflateSetDictionary_dataerr](../ZlibF/Proof/inflate.c.dict.lean#L222) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateSetDictionary_safe](../ZlibF/Proof/inflate.c.dict.lean#L146) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateSetDictionary_streamerr](../ZlibF/Proof/inflate.c.dict.lean#L209) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflateStateCheck_total](../ZlibF/Proof/inflate.c.base.lean#L384) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflateCodesUsed](#target-zlibf-spec-public-goal-inflatecodesused), [inflateEnd](#target-zlibf-spec-public-goal-inflateend), [inflateGetHeader_safety](#target-zlibf-spec-public-goal-inflategetheader-safety), [inflateMark](#target-zlibf-spec-public-goal-inflatemark), [inflatePrime](#target-zlibf-spec-public-goal-inflateprime), [inflateSyncPoint](#target-zlibf-spec-public-goal-inflatesyncpoint), [inflateSync_safety](#target-zlibf-spec-public-goal-inflatesync-safety), [inflateUndermine](#target-zlibf-spec-public-goal-inflateundermine), [inflateValidate](#target-zlibf-spec-public-goal-inflatevalidate), [inflate_refusal](#target-zlibf-spec-public-goal-inflate-refusal), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflateSyncPoint_spec](../ZlibF/Proof/inflate.c.misc.lean#L121) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflateSync_buf_error](../ZlibF/Proof/inflate.c.sync2.lean#L131) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflateSync_check](../ZlibF/Proof/inflate.c.sync2.lean#L113) | [inflateSync_safety](#target-zlibf-spec-public-goal-inflatesync-safety) |
| [Zlib.Inflate.Proofs.inflateUndermine_safe](../ZlibF/Proof/inflate.c.misc.lean#L109) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflateValidate_safe](../ZlibF/Proof/inflate.c.misc.lean#L95) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflate_CHECK_nowrap](../ZlibF/Proof/inflate.c.main.check.lean#L137) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflate_CHECK_run](../ZlibF/Proof/inflate.c.main.check.lean#L157) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflate_COPY__eq](../ZlibF/Proof/inflate.c.main.stored2.lean#L82) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflate_COPY_done](../ZlibF/Proof/inflate.c.main.stored.lean#L22) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflate_COPY_leave](../ZlibF/Proof/inflate.c.main.stored2.lean#L75) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflate_COPY_run](../ZlibF/Proof/inflate.c.main.stored2.lean#L57) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflate_DONE_run](../ZlibF/Proof/inflate.c.main.simple.lean#L25) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflate_LENGTH_run](../ZlibF/Proof/inflate.c.main.check.lean#L80) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflate_LENGTH_skip](../ZlibF/Proof/inflate.c.main.check.lean#L66) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflate_LENLENS_eq](../ZlibF/Proof/inflate.c.main.table3.lean#L82) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflate_LENLENS_run](../ZlibF/Proof/inflate.c.main.table6.lean#L41) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflate_LIT_full](../ZlibF/Proof/inflate.c.main.simple.lean#L29) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflate_LIT_run](../ZlibF/Proof/inflate.c.main.simple.lean#L37) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.inflate_STORED_bad](../ZlibF/Proof/inflate.c.main.stored2.lean#L97) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflate_STORED_ok](../ZlibF/Proof/inflate.c.main.stored2.lean#L116) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflate_STORED_wait](../ZlibF/Proof/inflate.c.main.stored2.lean#L88) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflate_TABLE_run](../ZlibF/Proof/inflate.c.main.table.lean#L52) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflate_TYPEDO_head](../ZlibF/Proof/inflate.c.main.type.lean#L61) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflate_TYPEDO_last](../ZlibF/Proof/inflate.c.main.type.lean#L26) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflate_TYPEDO_wait](../ZlibF/Proof/inflate.c.main.type.lean#L37) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflate_TYPE_go](../ZlibF/Proof/inflate.c.main.type.lean#L19) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.inflate_TYPE_leave](../ZlibF/Proof/inflate.c.main.type.lean#L11) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.ll1_run](../ZlibF/Proof/inflate.c.main.table4.lean#L69) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.llBody_run](../ZlibF/Proof/inflate.c.main.table3.lean#L95) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.llTail_run](../ZlibF/Proof/inflate.c.main.table5.lean#L46) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.lzBody_run](../ZlibF/Proof/inflate.c.main.table4.lean#L225) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.lz_run](../ZlibF/Proof/inflate.c.main.table4.lean#L244) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.noRet_NEEDBITS](../ZlibF/Proof/inflate.c.main.table2.lean#L321) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.ring_spec](../ZlibF/Proof/inflate.c.ring.lean#L112) | [inflateSetDictionary](#target-zlibf-spec-public-goal-inflatesetdictionary) |
| [Zlib.Inflate.Proofs.syncDone_good](../ZlibF/Proof/inflate.c.sync2.lean#L372) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.syncDone_owns](../ZlibF/Proof/inflate.c.sync2.lean#L423) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.syncDone_run](../ZlibF/Proof/inflate.c.sync2.lean#L248) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.syncScan_found_iff](../ZlibF/Proof/inflate.c.sync.lean#L342) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.syncScan_spec](../ZlibF/Proof/inflate.c.sync.lean#L300) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.syncStep_spec](../ZlibF/Proof/inflate.c.sync.lean#L202) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.syncTail_run](../ZlibF/Proof/inflate.c.sync2.lean#L543) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.syncsearch_null](../ZlibF/Proof/inflate.c.sync.lean#L450) | [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety) |
| [Zlib.Inflate.Proofs.syncsearch_run](../ZlibF/Proof/inflate.c.sync.lean#L381) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.syncsearch_spec](../ZlibF/Proof/inflate.c.sync.lean#L485) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.typedoTail_bad](../ZlibF/Proof/inflate.c.main.type.lean#L154) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.typedoTail_fixed](../ZlibF/Proof/inflate.c.main.type.lean#L116) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.typedoTail_fixed_trees](../ZlibF/Proof/inflate.c.main.type.lean#L132) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.typedoTail_stored](../ZlibF/Proof/inflate.c.main.type.lean#L92) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.typedoTail_table](../ZlibF/Proof/inflate.c.main.type.lean#L104) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Proofs.updatewindow_ring](../ZlibF/Proof/inflate.c.ring.lean#L193) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.updatewindow_safe](../ZlibF/Proof/inflate.c.uw.lean#L558) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.uwPost_counts](../ZlibF/Proof/inflate.c.ring.lean#L166) | [inflateSetDictionary](#target-zlibf-spec-public-goal-inflatesetdictionary) |
| [Zlib.Inflate.Proofs.uw_null_ok](../ZlibF/Proof/inflate.c.uw.lean#L492) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.uw_post](../ZlibF/Proof/inflate.c.uw.lean#L423) | No fixed-target composition recorded |
| [Zlib.Inflate.Proofs.xwhileBrk_run](../ZlibF/Proof/inflate.c.main.xloop.lean#L36) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inflate.Witness.init_witness](../ZlibF/Proof/inflate.c.witness.lean#L50) | No fixed-target composition recorded |
| [Zlib.Inftrees.Proofs.Cover.bits_add_drop](../ZlibF/Proof/inftrees.c.cover.leaf.lean#L80) | No fixed-target composition recorded |
| [Zlib.Inftrees.Proofs.Cover.cell_lt_fn](../ZlibF/Proof/inftrees.c.cover.fn.lean#L210) | No fixed-target composition recorded |
| [Zlib.Inftrees.Proofs.Cover.distLeaf_of](../ZlibF/Proof/inftrees.c.cover.leaf.lean#L56) | [decode_table_matches_format](#target-zlib-inftrees-spec-decodesemantics-goal-decode-table-matches-format), [decode_table_leaf_sound](#target-zlib-inftrees-spec-decodesoundness-goal-decode-table-leaf-sound), [constructor_establishes_query_stability](#target-zlib-inftrees-spec-decodetablestability-goal-constructor-establishes-query-stability), [constructor_establishes_fast_leaf_flags](#target-zlib-inftrees-spec-fasttableflags-goal-constructor-establishes-fast-leaf-flags), [inflate_table_decoder_safe](#target-zlib-inftrees-spec-goal-inflate-table-decoder-safe), [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent), [constructor_subtable_bits](#target-zlib-inftrees-spec-subtable-goal-constructor-subtable-bits), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inftrees.Proofs.Cover.group_cover](../ZlibF/Proof/inftrees.c.cover.group.lean#L64) | [inflate_table_decoder_safe](#target-zlib-inftrees-spec-goal-inflate-table-decoder-safe), [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent), [constructor_subtable_bits](#target-zlib-inftrees-spec-subtable-goal-constructor-subtable-bits), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inftrees.Proofs.Cover.group_cover_fn](../ZlibF/Proof/inftrees.c.cover.fn.lean#L163) | No fixed-target composition recorded |
| [Zlib.Inftrees.Proofs.Cover.group_cover_idx](../ZlibF/Proof/inftrees.c.cover.group.lean#L161) | [inflate_table_decoder_safe](#target-zlib-inftrees-spec-goal-inflate-table-decoder-safe), [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent), [constructor_subtable_bits](#target-zlib-inftrees-spec-subtable-goal-constructor-subtable-bits), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inftrees.Proofs.Cover.group_cover_idx_fn](../ZlibF/Proof/inftrees.c.cover.fn.lean#L185) | No fixed-target composition recorded |
| [Zlib.Inftrees.Proofs.Cover.invalid_leaf](../ZlibF/Proof/inftrees.c.cover.leaf.lean#L66) | [inflate_table_decoder_safe](#target-zlib-inftrees-spec-goal-inflate-table-decoder-safe), [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inftrees.Proofs.Cover.lenLeaf_of](../ZlibF/Proof/inftrees.c.cover.leaf.lean#L40) | [decode_table_matches_format](#target-zlib-inftrees-spec-decodesemantics-goal-decode-table-matches-format), [decode_table_leaf_sound](#target-zlib-inftrees-spec-decodesoundness-goal-decode-table-leaf-sound), [constructor_establishes_query_stability](#target-zlib-inftrees-spec-decodetablestability-goal-constructor-establishes-query-stability), [constructor_establishes_fast_leaf_flags](#target-zlib-inftrees-spec-fasttableflags-goal-constructor-establishes-fast-leaf-flags), [inflate_table_decoder_safe](#target-zlib-inftrees-spec-goal-inflate-table-decoder-safe), [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent), [constructor_subtable_bits](#target-zlib-inftrees-spec-subtable-goal-constructor-subtable-bits), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inftrees.Proofs.Cover.root_cover](../ZlibF/Proof/inftrees.c.cover.root.lean#L90) | [decode_table_matches_format](#target-zlib-inftrees-spec-decodesemantics-goal-decode-table-matches-format), [short_decode_table_leaf_sound](#target-zlib-inftrees-spec-decodeshort-goal-short-decode-table-leaf-sound), [decode_table_leaf_sound](#target-zlib-inftrees-spec-decodesoundness-goal-decode-table-leaf-sound), [constructor_establishes_decode_table_invariant](#target-zlib-inftrees-spec-decodetableinvariant-goal-constructor-establishes-decode-table-invariant), [constructor_establishes_query_stability](#target-zlib-inftrees-spec-decodetablestability-goal-constructor-establishes-query-stability), [constructor_establishes_fast_leaf_flags](#target-zlib-inftrees-spec-fasttableflags-goal-constructor-establishes-fast-leaf-flags), [inflate_table_content](#target-zlib-inftrees-spec-goal-inflate-table-content), [inflate_table_decoder_safe](#target-zlib-inftrees-spec-goal-inflate-table-decoder-safe), [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent), [constructor_subtable_bits](#target-zlib-inftrees-spec-subtable-goal-constructor-subtable-bits), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inftrees.Proofs.Cover.root_cover_complete_fn](../ZlibF/Proof/inftrees.c.cover.fn.lean#L140) | [inflate_table_decoder_safe](#target-zlib-inftrees-spec-goal-inflate-table-decoder-safe), [inflate_table_read_extent](#target-zlib-inftrees-spec-goal-inflate-table-read-extent), [constructor_subtable_bits](#target-zlib-inftrees-spec-subtable-goal-constructor-subtable-bits), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inftrees.Proofs.Cover.root_cover_fn](../ZlibF/Proof/inftrees.c.cover.fn.lean#L130) | No fixed-target composition recorded |
| [Zlib.Inftrees.Proofs.Cover.root_single_fn](../ZlibF/Proof/inftrees.c.cover.fn.lean#L226) | No fixed-target composition recorded |
| [Zlib.Inftrees.Proofs.inflate_fixed_ok](../ZlibF/Proof/inftrees.c.fixed.lean#L21) | [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety) |
| [Zlib.Inftrees.Proofs.inflate_table_correct_ret](../ZlibF/Proof/inftrees.c.lean#L65) | [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate](#target-zlibf-spec-public-goal-inflate), [inflateCopy](#target-zlibf-spec-public-goal-inflatecopy), [inflate_sequence_safety](#target-zlibf-spec-public-goal-inflate-sequence-safety), [uncompress2_safe](#target-zlibf-spec-public-goal-uncompress2-safe), [uncompress2_z_safe](#target-zlibf-spec-public-goal-uncompress2-z-safe), [uncompress_safe](#target-zlibf-spec-public-goal-uncompress-safe), [uncompress_z_safe](#target-zlibf-spec-public-goal-uncompress-z-safe) |
| [Zlib.Inftrees.Proofs.inflate_table_safe](../ZlibF/Proof/inftrees.c.lean#L34) | No fixed-target composition recorded |
| [Zlib.Trees.Proofs.GB.kraft_clamped](../ZlibF/Proof/trees.c.heap.gbtree.lean#L132) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Trees.Proofs.Out.bi_flush_spec](../ZlibF/Proof/trees.c.bits.lean#L548) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Trees.Proofs.Out.bi_reverse_correct](../ZlibF/Proof/trees.c.reverse.lean#L91) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Trees.Proofs.Out.bi_reverse_safe](../ZlibF/Proof/trees.c.reverse.lean#L51) | No fixed-target composition recorded |
| [Zlib.Trees.Proofs.Out.bi_windup_spec](../ZlibF/Proof/trees.c.bits.lean#L731) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Trees.Proofs.Out.init_block_spec](../ZlibF/Proof/trees.c.block.lean#L217) | No fixed-target composition recorded |
| [Zlib.Trees.Proofs.Out.init_block_spec0](../ZlibF/Proof/trees.c.block.lean#L102) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflateInit2_](#target-zlibf-spec-public-goal-deflateinit2), [deflateInit_](#target-zlibf-spec-public-goal-deflateinit), [deflateReset](#target-zlibf-spec-public-goal-deflatereset), [deflateResetKeep](#target-zlibf-spec-public-goal-deflateresetkeep), [deflate_initialisation_domain](#target-zlibf-spec-public-goal-deflate-initialisation-domain), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Trees.Proofs.Out.send_bits_spec](../ZlibF/Proof/trees.c.bits.lean#L411) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Trees.Proofs.Out.tr_align_emit](../ZlibF/Proof/trees.c.align.lean#L42) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Trees.Proofs.Out.tr_flush_bits_emit](../ZlibF/Proof/trees.c.align.lean#L30) | No fixed-target composition recorded |
| [Zlib.Trees.Proofs.Out.tr_init_spec](../ZlibF/Proof/trees.c.block.lean#L245) | [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflateInit_](#target-zlibf-spec-public-goal-deflateinit), [deflateReset](#target-zlibf-spec-public-goal-deflatereset), [deflateResetKeep](#target-zlibf-spec-public-goal-deflateresetkeep), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety) |
| [Zlib.Trees.Proofs.Out.tr_tally_spec](../ZlibF/Proof/trees.c.tally.lean#L327) | No fixed-target composition recorded |
| [Zlib.Trees.Proofs.gen_bitlen_correct](../ZlibF/Proof/trees.c.heap.gbtop.lean#L403) | No fixed-target composition recorded |
| [Zlib.Trees.Proofs.gen_bitlen_safe](../ZlibF/Proof/trees.c.heap.gbtop.lean#L421) | No fixed-target composition recorded |
| [Zlib.Trees.Proofs.pqdownheap_correct](../ZlibF/Proof/trees.c.heap.pqrun.lean#L313) | No fixed-target composition recorded |
| [Zlib.Trees.Proofs.pqdownheap_safe](../ZlibF/Proof/trees.c.heap.pqrun.lean#L330) | No fixed-target composition recorded |
| [Zlib.Trees.Proofs.pqremove_correct](../ZlibF/Proof/trees.c.heap.pqrun.lean#L342) | No fixed-target composition recorded |
| [Zlib.Trees.Proofs.pqremove_safe](../ZlibF/Proof/trees.c.heap.pqrun.lean#L359) | No fixed-target composition recorded |
| [Zlib.Zutil.Proofs.zError_correct](../ZlibF/Proof/zutil.c.lean#L125) | No fixed-target composition recorded |
| [Zlib.Zutil.Proofs.zError_safe](../ZlibF/Proof/zutil.c.lean#L117) | No fixed-target composition recorded |
| [Zlib.Zutil.Proofs.zcalloc_correct_none](../ZlibF/Proof/zutil.c.lean#L271) | No fixed-target composition recorded |
| [Zlib.Zutil.Proofs.zcalloc_correct_size](../ZlibF/Proof/zutil.c.lean#L262) | No fixed-target composition recorded |
| [Zlib.Zutil.Proofs.zcalloc_correct_some](../ZlibF/Proof/zutil.c.lean#L248) | No fixed-target composition recorded |
| [Zlib.Zutil.Proofs.zcalloc_safe](../ZlibF/Proof/zutil.c.lean#L234) | No fixed-target composition recorded |
| [Zlib.Zutil.Proofs.zcalloc_zcfree_no_leak](../ZlibF/Proof/zutil.c.lean#L316) | No fixed-target composition recorded |
| [Zlib.Zutil.Proofs.zcfree_correct](../ZlibF/Proof/zutil.c.lean#L290) | No fixed-target composition recorded |
| [Zlib.Zutil.Proofs.zcfree_correct_null](../ZlibF/Proof/zutil.c.lean#L308) | No fixed-target composition recorded |
| [Zlib.Zutil.Proofs.zcfree_safe](../ZlibF/Proof/zutil.c.lean#L280) | No fixed-target composition recorded |
| [Zlib.Zutil.Proofs.zlibCompileFlags_correct](../ZlibF/Proof/zutil.c.lean#L175) | No fixed-target composition recorded |
| [Zlib.Zutil.Proofs.zlibCompileFlags_safe](../ZlibF/Proof/zutil.c.lean#L169) | No fixed-target composition recorded |
| [Zlib.Zutil.Proofs.zlibVersion_correct](../ZlibF/Proof/zutil.c.lean#L159) | No fixed-target composition recorded |
| [Zlib.Zutil.Proofs.zlibVersion_safe](../ZlibF/Proof/zutil.c.lean#L134) | No fixed-target composition recorded |
| [ZlibF.Spec.Api.Proofs.Layer.ext](../ZlibF/Proof/Format/Api.lean) | [dict_roundtrip](#target-zlibf-spec-api-goal-dict-roundtrip), [format_deterministic](#target-zlibf-spec-api-goal-format-deterministic), [format_prefix_free](#target-zlibf-spec-api-goal-format-prefix-free), [inflate_completes](#target-zlibf-spec-api-goal-inflate-completes), [inflate_decodes](#target-zlibf-spec-api-goal-inflate-decodes), [inflate_deferred_distance](#target-zlibf-spec-api-goal-inflate-deferred-distance) |
| [ZlibF.Spec.Api.Proofs.inflate_deferred_distance_rejects_legacy_consistency](../ZlibF/Proof/Api/InflateCausality.lean#L229) | No fixed-target composition recorded |
| [ZlibF.Spec.Blocks.append](../ZlibF/Proof/Format/Deflate.lean) | [compress_roundtrip](#target-zlibf-spec-api-goal-compress-roundtrip), [dict_roundtrip](#target-zlibf-spec-api-goal-dict-roundtrip), [format_deterministic](#target-zlibf-spec-api-goal-format-deterministic), [format_prefix_free](#target-zlibf-spec-api-goal-format-prefix-free), [inflate_completes](#target-zlibf-spec-api-goal-inflate-completes), [inflate_decodes](#target-zlibf-spec-api-goal-inflate-decodes), [inflate_deferred_distance](#target-zlibf-spec-api-goal-inflate-deferred-distance) |
| [ZlibF.Spec.Blocks.det](../ZlibF/Proof/Format/Deflate.lean) | [compress_roundtrip](#target-zlibf-spec-api-goal-compress-roundtrip), [dict_roundtrip](#target-zlibf-spec-api-goal-dict-roundtrip), [format_deterministic](#target-zlibf-spec-api-goal-format-deterministic), [format_prefix_free](#target-zlibf-spec-api-goal-format-prefix-free), [inflate_completes](#target-zlibf-spec-api-goal-inflate-completes), [inflate_decodes](#target-zlibf-spec-api-goal-inflate-decodes), [inflate_deferred_distance](#target-zlibf-spec-api-goal-inflate-deferred-distance) |
| [ZlibF.Spec.Gzip.ext](../ZlibF/Proof/Format/Wrapper.lean) | [dict_roundtrip](#target-zlibf-spec-api-goal-dict-roundtrip), [format_deterministic](#target-zlibf-spec-api-goal-format-deterministic), [format_prefix_free](#target-zlibf-spec-api-goal-format-prefix-free), [inflate_completes](#target-zlibf-spec-api-goal-inflate-completes), [inflate_decodes](#target-zlibf-spec-api-goal-inflate-decodes), [inflate_deferred_distance](#target-zlibf-spec-api-goal-inflate-deferred-distance) |
| [ZlibF.Spec.Prefix.det](../ZlibF/Proof/Format/Deflate.lean) | No fixed-target composition recorded |
| [ZlibF.Spec.Prefix.ext](../ZlibF/Proof/Format/Deflate.lean) | [compress_roundtrip](#target-zlibf-spec-api-goal-compress-roundtrip), [dict_roundtrip](#target-zlibf-spec-api-goal-dict-roundtrip), [format_deterministic](#target-zlibf-spec-api-goal-format-deterministic), [format_prefix_free](#target-zlibf-spec-api-goal-format-prefix-free), [inflate_completes](#target-zlibf-spec-api-goal-inflate-completes), [inflate_decodes](#target-zlibf-spec-api-goal-inflate-decodes), [inflate_deferred_distance](#target-zlibf-spec-api-goal-inflate-deferred-distance) |
| [ZlibF.Spec.Proofs.prefixFree](../ZlibF/Proof/Format/Huffman.lean#L105) | [short_decode_table_leaf_sound](#target-zlib-inftrees-spec-decodeshort-goal-short-decode-table-leaf-sound), [decode_table_leaf_sound](#target-zlib-inftrees-spec-decodesoundness-goal-decode-table-leaf-sound), [constructor_establishes_query_stability](#target-zlib-inftrees-spec-decodetablestability-goal-constructor-establishes-query-stability), [short_rejected_leaf_stays_invalid](#target-zlib-inftrees-spec-decodetablestability-goal-short-rejected-leaf-stays-invalid), [constructor_establishes_fast_leaf_flags](#target-zlib-inftrees-spec-fasttableflags-goal-constructor-establishes-fast-leaf-flags), [compress_roundtrip](#target-zlibf-spec-api-goal-compress-roundtrip), [dict_roundtrip](#target-zlibf-spec-api-goal-dict-roundtrip), [format_deterministic](#target-zlibf-spec-api-goal-format-deterministic), [format_prefix_free](#target-zlibf-spec-api-goal-format-prefix-free), [inflate_completes](#target-zlibf-spec-api-goal-inflate-completes), [inflate_decodes](#target-zlibf-spec-api-goal-inflate-decodes), [inflate_deferred_distance](#target-zlibf-spec-api-goal-inflate-deferred-distance), [compress2_safety](#target-zlibf-spec-public-goal-compress2-safety), [compress2_z_safety](#target-zlibf-spec-public-goal-compress2-z-safety), [compress_safety](#target-zlibf-spec-public-goal-compress-safety), [compress_z_safety](#target-zlibf-spec-public-goal-compress-z-safety), [deflate](#target-zlibf-spec-public-goal-deflate), [deflateCopy](#target-zlibf-spec-public-goal-deflatecopy), [deflate_sequence_safety](#target-zlibf-spec-public-goal-deflate-sequence-safety), [gz_sequence_safety](#target-zlibf-spec-public-goal-gz-sequence-safety), [inflate_back_sequence_safety](#target-zlibf-spec-public-goal-inflate-back-sequence-safety) |
| [ZlibF.Spec.Public.Proofs.DeflateCore.completes](../ZlibF/Proof/deflate.c.default-core-completes.lean#L89) | No fixed-target composition recorded |
| [ZlibF.Spec.Public.Proofs.DeflateCore.correct](../ZlibF/Proof/deflate.c.default-core-completes.lean#L140) | No fixed-target composition recorded |
| [ZlibF.Spec.Public.Proofs.DeflateCore.safe_encoding_and_cleanup](../ZlibF/Proof/deflate.c.default-core.lean#L182) | No fixed-target composition recorded |
| [ZlibF.Spec.Public.Proofs.DeflateInit.default_init_witness](../ZlibF/Proof/public-deflate-init.lean#L283) | No fixed-target composition recorded |
| [ZlibF.Spec.Public.Proofs.free_writable_matches_dropWindow](../ZlibF/Proof/Api/HeapCleanup.lean#L57) | No fixed-target composition recorded |
| [ZlibF.Spec.Public.Proofs.legacy_codes_used_impossible](../ZlibF/Proof/Api/QueryLayout.lean#L125) | No fixed-target composition recorded |
| [ZlibF.Spec.Zlib.ext](../ZlibF/Proof/Format/Wrapper.lean) | [compress_roundtrip](#target-zlibf-spec-api-goal-compress-roundtrip), [dict_roundtrip](#target-zlibf-spec-api-goal-dict-roundtrip), [format_deterministic](#target-zlibf-spec-api-goal-format-deterministic), [format_prefix_free](#target-zlibf-spec-api-goal-format-prefix-free), [inflate_completes](#target-zlibf-spec-api-goal-inflate-completes), [inflate_decodes](#target-zlibf-spec-api-goal-inflate-decodes), [inflate_deferred_distance](#target-zlibf-spec-api-goal-inflate-deferred-distance) |

## Refresh

Regenerate after proof or registry changes. The generator builds and inspects
exact compiled theorem types. It never changes a proof, target or registry.
It writes this region of this page and of its Chinese twin `docs/progress.zh.md`.
Acceptance remains subject to [checking](checking/README.md).
The view is stale only when what it shows changes: a target, a registration, a proof status, a
link or a line anchor. Its links keep the revision they were generated at until then.
<!-- proof-progress:end -->

## Remaining work

All 98 required goals are registered; [Scope](#scope) gives the level of each result and the
acceptance runs. No goal has a documented blocker. The work that remains is listed in
[Ordered next work](#ordered-next-work).

The sections below hold facts and open items only. Finished work logs are kept unchanged under
`docs/history/`; their states, hours and counts describe the time they were written:

- Proof skeletons: [inflate](history/skeleton-inflate.md), [deflate](history/skeleton-deflate.md),
  [gz](history/skeleton-gz.md), [inflateBack](history/skeleton-inflate-back.md).
- [Earlier work order and readiness notes](history/next-work-and-readiness.md).
- [Specification review records](history/specification-review.md).
- [Coverage: review record](history/coverage-review-record.md) and
  [coverage: earlier open items](history/coverage-open-items.md).
- [Progress checkpoints](history/progress-checkpoints.md) and the
  [overview changelog](history/overview-changelog.md): older narrative notes.

### Core proof skeletons

A skeleton is the top-down plan of one core proof: the goal proved from named lemmas, with the
lemma proofs left open on a branch. Every skeleton is closed. The goals it was built for are
registered, so no lemma that a required goal needs is open. The lemma tables, the statement
corrections made on the way and the work logs are history.

| Skeleton | Goals it closed, all registered | Branch | Record |
| --- | --- | --- | --- |
| inflate | `Goal.inflate`, `Goal.inflate_sequence_safety`, `Goal.uncompress*_safe` | `skeleton/inflate` | [inflate skeleton](history/skeleton-inflate.md) |
| deflate | `Goal.deflateInit2_`, `Goal.deflate`, `Goal.deflate_sequence_safety`, `Goal.compress*_safety` | `skeleton/deflate` | [deflate skeleton](history/skeleton-deflate.md) |
| gz | `Goal.gz_sequence_safety`, `Goal.gz_sequence_nonvacuity`, `Goal.gz_refusal` | `skeleton/gz` | [gz skeleton](history/skeleton-gz.md) |
| inflateBack | `Goal.inflate_back_sequence_safety` | `skeleton/inflate-back` | [inflateBack skeleton](history/skeleton-inflate-back.md) |

Some rows of the archived tables still say "open". None of them is needed by a required goal:

- Functional rows: the format meaning of inflate, the deflate ledger, `completes` and
  `bound_before_output`. [Scope](#scope) says which functional work is planned.
- Cleanup rows, optional and not confirmed done: deleting inflate fast-path and
  fixed-configuration proofs that no registered theorem uses, and merging the restated
  `deflate.c.quiet-*` copies.
- gz helper rows: the loop rules `gwhile_partial` and `gdoWhile_partial`, and the alignment of
  the internal read helpers (`gz_load_safe` to `gz_skip_safe`) with the skeleton text. The
  goal is proved from the helper statements on `dev` and needs neither.
- The archived deflate table "Open work" shows hours for the strategy exports, `step_params` and
  the `HeaderInv` lemma of `deflate`. The archive does not record which of these rows were proved
  and which became unnecessary when `Goal.deflate_sequence_safety` was registered.

### No-fault coverage of zlib.h functions

The table with one row for each function that `zlib.h` documents is on its own page:
[coverage by function](coverage.md). Each row names the safety goal, the registered theorem whose
type is that goal, the proof file, the domain, and what the goal states for a `NULL` or
inconsistent stream. A separate column names the functional theorem.

Every documented function has a registered safety theorem on the domain its row states. Three
kinds of item are open or narrower than `zlib.h`:

1. **Refusal clauses.** Nothing is open here. The refusal of a `NULL` or inconsistent stream is
   a clause of the safety goal of every documented stream function except the four init functions, and of
   both copy goals (commit `71188823`). What the refusal domain leaves out is narrower than
   `zlib.h` only in the sense of [deviations, note 2](deviations.md#note-2-refused-streams): a
   record with set allocators whose `state` pointer is garbage, dangling or of the other stream
   kind. The level of these goals is in [Scope](#scope).
2. **Domains narrower than `zlib.h`**, each with a row in [deviations](deviations.md):
   `inflateBack` (`inputBound < 2^48`; the window and every input chunk in a heap byte block);
   `inflateCopy` and `deflateCopy`
   (`source ≠ dest`); `adler32` and `adler32_z` (a `NULL` `buf` only with `len = 0`: `len = 1`
   is a real C fault, and `NULL` with `len ≥ 2` is safe in C but unproved).
3. **Result cells passed as values.** The translations of eight public functions take a scalar
   out-parameter as a value and return the stored value as a further result: `destLen` of
   `compress`, `compress2` and their `_z` forms; `dictLength` of `inflateGetDictionary` and
   `deflateGetDictionary`; `pending` and `bits` of `deflatePending`; `bits` of `deflateUsed`. The
   safety goals of these functions therefore say nothing about the memory of the result cell
   ([deviations](deviations.md#stream-calls-inflate-and-deflate), rows "Result cells" and
   "Whole-buffer compression"). The working rules accept this representation for an
   out-parameter of an internal function only. Whether these translations change to take the
   cell as memory, as `uncompress*` and `gzerror` do, is an open decision of the owner.

The functional goals of `deflateParams`, `deflateSetDictionary`, `deflatePrime`, `deflateBound`,
`deflateBound_z` and `inflateSync` have no theorem and are not planned. Their safety goals are
registered.

### Ordered next work

Every required goal is registered: 98 safety and non-vacuity goals, none open
(`tests/audit/public-api.json`). [Scope](#scope) names the commit on which the acceptance suite
was green and what changed after it. What remains, in order:

1. **Acceptance** of the goals registered or changed after `bde170e9`: the 35 one-function safety
   goals of the gz functions and of the callback decoder, the widened init goals, the
   callback-decoder sequence goal in its present form, and the 25 stream and copy goals with a
   refusal clause (item 2). They are registered and wait only for a
   green acceptance suite on a named commit: axiom gate, exact goal match, self tests and
   differential tests. A mutant run is not needed for it. The commit goes into
   [Scope](#next-acceptance-run).
2. **Refusal clauses.** The statements and proofs are done: the 23 one-function stream safety
   goals and the two copy goals state the refusal
   ([coverage](#no-fault-coverage-of-zlibh-functions), item 1). Their theorems keep their
   registered names. What remains for them is the acceptance run of item 1. No mutant row was
   added for the new refusal clauses; the existing rows of these goals predate them. Mutants are
   additional evidence and do not gate acceptance.
3. **The round trip of the default zlib stream**, after the safety results ([Scope](#scope)).
4. **Upstream submission of the local patches** 0004 and 0005
   ([patches](../patches/README.md)). Patches 0001 to 0003 match submitted upstream pull
   requests.
5. **Open reviews and decisions**: [Translation review](#translation-review),
   [Historical reports to recheck](#historical-reports-to-recheck), and the owner's decision on
   the result cells of eight public functions
   ([coverage](#no-fault-coverage-of-zlibh-functions), item 3).
6. **Optional cleanup** of proofs that no registered theorem uses
   ([Core proof skeletons](#core-proof-skeletons)).
7. **Math modules that import proof modules.** The layout of `ZlibF/Spec/` is final
   ([layout of the specifications](design/safety-functional-split.md)): only `Safety/`,
   `Functional/` and `Common/`; safety and common modules import no functional module, common
   modules import no safety module, and no specification module imports a proof module, also
   through other modules. `scripts/check-spec-layers.py` checks this in the fast gate with no
   exception. What remains is its list `MATH_PROOF_IMPORTS`: 36 imports of proof modules by 28
   modules of `ZlibF/Math/`. The script records that they import lemmas, not definitions, and
   that moving those lemmas is later work. The list may only shrink.

The groups that [Scope](#scope) lists as not planned get no work. The earlier ordered table (13
rows, each registered or not planned) is in
[earlier work order](history/next-work-and-readiness.md).

### Public API proof readiness

The generated index links each unregistered public target to a row of the table below. The
generator reads the table, so its labels and anchors are kept. Every target in the table is a
functional goal: open, and not planned (see [Scope](#scope)). The safety of the same functions
is registered ([coverage by function](coverage.md)).

The notes say what a proof of the functional goal would need. Most were written when functional
correctness was a planned result, and each is **to confirm** against the exact target. They are
not a work plan. No row grants checked status or assumes a callee's specification.

Earlier content of this section is history: the stopped positional hash-chain work
([deflate skeleton](history/skeleton-deflate.md)), the inflateBack lemma table
([inflateBack skeleton](history/skeleton-inflate-back.md)), and the open, query and close
prerequisites with the rows of targets since registered
([readiness notes](history/next-work-and-readiness.md)).

#### Next work for every unfinished public target

"Start" means work can begin without a complete engine theorem. "Compose" names a
prerequisite for full closure.

<!-- proof-readiness:start -->
| Public targets | Proof work shown in graph | Next work and missing prerequisite |
| --- | --- | --- |
| `gzopen`, `gzopen64`, `gz_initialisation_domain`  | Start: open and cleanup | <a id="readiness-gzopen"></a> **Statement corrected:** see [gzip open path length](history/specification-review.md#gzip-open-path-length). **Start:** the path-open branch of `gz_open` (`fsOpen` outcomes, append and read seeks), reusing the registered `gzdopen` mode loop, allocation and `OpenState` composition. Entry/failure branches are locally checked above. |
| `gztell64`, `gztell`  | Needs: position history | <a id="readiness-gztell64"></a> **Compose:** derive `PosInv` from reads, writes, seeking and pushback; then reuse the existing arithmetic execution proof. |
| `gzclose_r`  | Needs: resource history | <a id="readiness-gzclose-r"></a> **Start:** initialized-buffer cleanup and its ownership producer over histories. Unbuffered execution and frame are locally checked; `inflateEnd` alone is insufficient. |
| `gzclose_w`, `gzclose`  | Needs: flush and cleanup | <a id="readiness-gzclose-w"></a> **Compose:** actual zero-fill/final compression and file writes, all cleanup/error paths, then dispatch using both complete close results. |
| `gzseek64`, `gzseek`  | Needs: seek and history | <a id="readiness-gzseek64"></a> **Start:** position/pointer history invariants, buffered and transparent paths, exact error frames. Negative-position reachability and historical overflow reports remain **to confirm**. |
| `gzdirect`, `gzread`, `gzfread`, `gzgetc`, `gzgetc_`, `gzgets`, `gzungetc`  | Needs: reader path proofs | <a id="readiness-gzdirect"></a> **Start:** common lazy setup, transparent reads and buffer/history invariants. **Compose:** actual decoder execution for compressed paths, then EOF/count/pushback/error clauses. `gzdirect` needs detection and init, not the full data-decoding loop. |
| `gzwrite`, `gzfwrite`, `gzputc`, `gzputs`, `gzvprintf`, `gzprintf`, `gzflush`, `gzsetparams`  | Needs: writer path proofs | <a id="readiness-gzwrite"></a> **Start:** buffering, formatting, transparent writes and failures. **Compose:** actual compressor execution for compressed output and parameter changes. |
| `deflatePrime`  | Start: compaction and bits | <a id="readiness-deflateprime"></a> **Start:** pending-byte compaction, checked shifts, bit insertion/flush and invariant/frame preservation. Refusal branches are locally checked; accepted counts remain open. |
| `deflateBound_z`, `deflateBound`  | Start: bound and header review | <a id="readiness-deflatebound-z"></a> **Start:** connect existing execution formulas to the saturated mathematical bound, including header strings and extra lengths. The extra-length report is reproduced on the pinned C: for an `extra_len` of `2^32 - 2` or `2^32 - 1` the C wraps `2 + extra_len` at 32 bits, and the value goals as stated do not ([finding](findings/deflatebound-extra-len/README.md)). The goals need a corrected statement before a proof starts. |
| `deflateSetDictionary`  | Start: window and hash | <a id="readiness-deflatesetdictionary"></a> **Start:** window fill, hash-chain insertion, saved-input restoration, then checksum and exact state/frame effects. Green checksum calls cover only that part. |
| `deflateParams` | Needs: block flush and parameter state | <a id="readiness-deflateparams"></a> **Compose:** actual old-block flushing, return-code handling and canonical tuning-row updates. Check exact state preservation on refusal before full closure. |
| `inflateSync`  | Needs: scan and history | <a id="readiness-inflatesync"></a> **Start:** compose existing first/resume scans, held bits, marker search, reset and accounting/frame results. Derive window/reset premises from histories. |
| `compress2_z`, `compress2`, `compress_z`, `compress`  | Needs: compressor execution | <a id="readiness-compress2-z"></a> **Start:** arguments, scalar lengths and cleanup. **Compose:** actual init/compress/end with exact output, then wrappers. Abstract roundtrip is insufficient. |
| `uncompress2_z`, `uncompress2`, `uncompress_z`, `uncompress`  | Needs: decoder execution | <a id="readiness-uncompress2-z"></a> **Start:** scalar results, insufficient space and cleanup. **Compose:** actual init/decompress/end, exact consumption/output, then wrappers. |
| `inflate_sequence`, `deflate_sequence`, `inflate_back_sequence`, `gz_sequence`  | Needs: execution and format | <a id="readiness-inflate-sequence"></a> **Compose:** actual per-call safety, history preservation, independent format refinement and completion across input/output splits. |
| `inflateBack` | Needs: tables, window and callbacks | <a id="readiness-inflateback"></a> **Compose:** compressed TABLE/LEN execution, output inside the window, public callback ownership, loop termination and exact input/output accounting. Existing stored and entry paths can progress independently. |
<!-- proof-readiness:end -->

### Specification review

The six records of this section are closed and kept in
[specification review records](history/specification-review.md): gzip seek mode, inflate
initialization cleanup, decompression utility cleanup, gzip open path length, gzip library
findings with local fixes, and gzip offset and rewind on the OS-call oracle. The two gz position
overflow findings are in the root `README.md`; the patches are in
[patches](../patches/README.md).

Open, and not planned, because these are model-only statements (see [Scope](#scope)):

- `Api.Goal.inflate_rejects_invalid` rests on `detectLag = 8`. A checked counterexample shows
  that the constant is wrong ([API model](design/api-model.md)).
- `Api.Goal.gz_seek_read` is corrected and
  [locally checked](../ZlibF/Proof/Api/GzSeekRead.lean). It is not registered.

Two items from the earlier text of this section are not confirmed done: an independent review of
the corrected shared `Uncompress2` relation, and the completion of the older abstract gz and
dictionary models. The concrete public targets do not assume the callee contracts of these
models.

### Translation review

The review of the translation against the C is not complete. The open items:

- **Null pointer arithmetic.** Which C language edition and implementation extensions the
  selected build relies on, and whether the reachable null-plus-zero and null-minus-null
  operations are defined, is not established. The model permits some of them: `Ptr.add`
  returns `NULL` for `NULL + 0`, and the helper `Zlib.Compress.ptrDiff` returns zero for
  `NULL - NULL`. `Ptr.diff` itself faults on `NULL - NULL`; its source comment says that C17 and
  C23 leave that subtraction undefined and that C++ defines it as 0. The
  [comparison table](spec/safety.md#null-pointers-and-pointer-differences) records the actual
  definitions and language references. No reachable upstream bug is claimed.
- **Statement-by-statement review.** The compressor's automatic storage was reviewed and
  corrected. The review of the rest is to be continued.
- **Compressor slide.** The slide checks signed subtraction in source order. Its
  [internal-state regression](../tests/regression/deflate-slide/README.md) compares three defined
  boundaries and rejects an artificial overflow in both C and Lean. Restoring unchecked
  subtraction changes only the overflow observation. That the artificial state is reachable is
  not claimed; the signed bound is not derived from legal call histories.
- **Depth reread in tree merging.** The translation rereads the selected depth as the source
  does, with a [six-case regression](../tests/regression/trees-depth-read/README.md) and a
  required structural check that rejects the cached expression. The temporal initialization
  history of internal depth reads is not proved.
- **Scalar-pointer aliasing and the null-minus-null special case** in compressor pointer
  subtraction are **to confirm**.

### Observations

**`gz_comp` spins on a `write` that returns 0.** In both write loops of `gz_comp`
(`gzwrite.c`: the transparent loop `while (strm->avail_in)` and the write-out loop
`while (strm->next_out > state->x.next)`), a `write` that returns 0 for a nonempty buffer
advances nothing and is not an error, so the loop repeats the same call. If the system keeps
returning 0, the C never returns. This is a reading of the code; a `write` that returns 0
forever was not run. Linux is not known to return 0 for a nonzero count on regular files, pipes
or sockets (**to confirm** for other file types), so the gz safety proof assumes it
([deviations](deviations.md#gzip-file-interface), row "Gz OS facts"). The fault-injection harness
of the gz safety study checked the other side: with a `write` that returns 0 on 10 % of nonempty
calls (40 histories, ASan and UBSan), every history ended with no report and no leak, because
each loop eventually gets a positive result. This is behaviour of the library, not a safety
finding; it is worth an upstream note only if a platform is known that returns 0. Scope:
`gzwrite`, `gzfwrite`, `gzputc`, `gzputs`, `gzprintf`, `gzflush`, `gzsetparams`, `gzclose_w`.

**A string returned by `gzerror` is freed by the next call that reaches `gz_error`.**
Unconfirmed finding, a documentation gap, not a code bug. `zlib.h` says only that later calls of
`gzerror` may invalidate the returned string. In fact `gzerror` returns `state->msg`, and every
call that reaches `gz_error` frees it. The writing entries (`gzwrite`, `gzfwrite`, `gzputc`,
`gzputs`, `gzprintf`, `gzvprintf`, `gzflush`, `gzsetparams`) reset the error with
`gz_error(state, Z_OK, NULL)` after their mode and error test and before they use their
arguments. The reading entries (`gzread`, `gzfread`, `gzgetc`, `gzungetc`, `gzgets`) do so only
when the previous read stalled ([deviations](deviations.md#why-the-handles-own-strings-are-excluded)
has the table). A caller that passes that string back to the same handle can get a use after free:
`gzprintf(f, "%s", gzerror(f, &e))` after a stalled write reads freed memory in `vsnprintf`
([reproduction](../tests/regression/gzprintf-error-string/README.md), ASan). No patch. The proved
domain keeps caller strings and buffers apart from the handle's blocks (`GzRange`, and the
separation clause of `GzArguments` for `gzprintf`/`gzvprintf`, [deviations](deviations.md)).

**`deflateBound` is too small in two cases.** Both are broken promises of `zlib.h` about a size,
not memory errors, and both are reproduced on the unpatched C. With `Z_FIXED` at levels 1 to 3,
`windowBits` 15 and `memLevel` 8, one `deflate(Z_FINISH)` call with `deflateBound` bytes of room
returns `Z_OK` ([finding](findings/deflatebound-fixed-far-matches/README.md)). With a gzip extra
field of length `2^32 - 2` or `2^32 - 1`, the sum `2 + extra_len` wraps at 32 bits
([finding](findings/deflatebound-extra-len/README.md)). No required safety goal depends on the
value of the bound. Two functional statements do, and the finding pages say they are false as
stated for these cases: `DeflateCompletes`, which quantifies over every strategy, and the value
goals `Goal.deflateBound` and `Goal.deflateBound_z`, which are open. The default strategy is not
affected, so the planned round trip of the default stream is not affected. The first case is
patched locally (patch 0006, owner's decision of 2026-11-15), so `DeflateCompletes` needs no
premise for it. How the value goals are corrected for the second case is not decided.

### Historical reports to recheck

Earlier work reported six items. Three were rechecked against the pinned source and are
findings with a reproduction:

- gzip extra-length arithmetic: [`deflateBound` with a long extra field](findings/deflatebound-extra-len/README.md);
- partial-read recovery: [`gzread` copies from a stale `x.next`](findings/gzread-transparent-stale-next/README.md), patch 0003;
- negative-position seeking: [`gzseek` after an initial `gzungetc`](findings/gzseek-pushback-overflow/README.md), patch 0002.

Three are not rechecked against the pinned source
([findings, earlier library observations](findings.md#earlier-library-observations)):

- lost parameter changes;
- failed-finish recovery;
- forward seek after EOF.

Conditional seek fault lemmas do not prove reachability: the signed-position and
borrowed-pointer conditions are not derived from actual call histories.
The `inflateBack` history report remains unconfirmed for that callback API;
ordinary-inflate sanitizer examples do not settle it.
The [earlier proof notes](history/proof-earlier-notes.md) keep the text of two of these reports:
the `inflateBack` missing-`whave` report (section "Callback decoder: the migrated domain table")
and the `gzsetparams` "lost parameter changes" experiment
([section](history/proof-earlier-notes.md#gzsetparams-experiment)).
The external string allocator and the fixed loop fuel are not reviewed to the point where full
gzip ownership or arbitrary finite callback termination could be claimed.
A suspected defect is not permission to exclude a public case.
[Findings](findings.md) records evidence and confidence; the patches are in
[patches/README.md](../patches/README.md). No blanket UB patch is applied.

The [architecture guide](design/architecture.md#design-decisions) records design decisions
D1–D6. The [safety specification](spec/safety.md#uninitialised-memory) defines
the fresh-memory obligations.
