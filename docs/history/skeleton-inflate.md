# Inflate proof skeleton (historical)

This page keeps the inflate part of the section "Core proof skeletons" of [progress](../progress.md), as it stood
after the required goals were accepted on `bde170e9`. The text is unchanged apart from relative links. It is a historical
record: states such as "open" and "checked", hours, counts and dates describe the time each
entry was written. They are not current status. Current status and remaining work are only in
[progress](../progress.md).

#### inflate

Safety of the inflate family (owner's decision of 2026-11-11): no undefined behaviour, no
memory error, no leak, and termination, for every reachable history. Termination is part of
every row: each theorem concludes that the call returns `.ok`, which excludes
`Fault.outOfFuel` (`docs/spec/safety.md`). "Checked" means the theorem is on `dev` with the
fast gate green; "accepted" also needs the acceptance suite. Estimates are focused hours,
with an uncertainty of about half the figure, including build time on the shared build host.
The `meaning_*` rows of the format meaning are not planned and are no longer listed; what is
proved of them stays on `dev`.

Decoder invariant `InflateInv` (`inflate.c.invariant`): it generalizes `DefaultOriginState` to
raw, zlib, gzip and automatic detection, windowBits 0, and an attached gzip header record.
`DecoderHeldBits` (outside `BAD`, `MEM` and `SYNC`, at most 32 held bits) is carried beside it
on every reachable history.

| Lemma | Meaning | State | Hours |
| --- | --- | --- | ---: |
| `inflate_public` (`public-inflate`) | The theorem of type `Goal.inflate`: one call from every reachable stream, every configuration, gzip header record included. First sorry-free on `dev` at `8b12ff6a`; fast gate green on `2dab2f5e`. | checked | 0 |
| `inflate_reachable_invariant` (`inflate.c.reachable`) | `InflateInv` and `DecoderHeldBits` on every reachable history: init, rebuffer, every stream operation, `inflateCopy`. | checked | 0 |
| `inflate_call_held` (`inflate.c.held-history`) | One `inflate` call keeps `DecoderHeldBits`. A functional fact that safety needs: the bit buffer `hold` is 32 bits wide, so the decoder must never hold more. | checked | 0 |
| Progress clause of `Goal.inflate` | `rc = Z_OK → used ≠ 0 ∨ out ≠ []`. A functional fact that the termination of the `uncompress*` loop needs; part of `inflate_public`. | checked | 0 |
| `inflate_call_safe`, `operation_safe` (`inflate.c.sequence-safety`) | Every stream operation from a reachable history writes only the stream record, its own blocks, the header record and the caller regions of `StreamWriteRegions`, and changes the live blocks exactly by its own ledger. `inflate` through `InflateCall.safe`; `inflateSync` through `inflateSync_call_safe` (a window freed by the resynchronization included); the 12 others through `inflate.c.call-safety`. | checked | 0 |
| `inflateEnd_invariant` (`inflate.c.call-safety`) | `inflateEnd` on a reachable stream returns `Z_OK`, clears the state and frees every block the stream owns. | checked | 0 |
| `inflate_sequence_safety_public` (`public-inflate-sequence-safety`) | The theorem of type `Goal.inflate_sequence_safety` (= `StreamSequenceSafety .inflate`, the safety half of `Goal.inflate_sequence`). | checked | 0 |
| `inflateInit_`, `inflateInit2_` (`public-inflate-init`, `public-inflate-init2`) | Every windowBits and allocation outcome, in the source error order; an invalid width frees its state. `inflate_init2_public` is proved; it still needs registration. | checked | 0 |
| Resets, `inflateEnd`, `inflateGetDictionary`, `inflateSetDictionary`, `inflateGetHeader`, `inflatePrime`, `inflateSyncPoint`, `inflateMark`, `inflateCodesUsed`, `inflateUndermine`, `inflateValidate` | The lifecycle and query goals, including null and invalid streams. | registered | 0 |
| `inflateSync` | Safety on every reachable history: `inflateSync_call_safe`, part of the sequence theorem. The rest of `Goal.inflateSync` is the exact marker search (`Api.syncSearch`), a functional clause that no safety proof needs. | checked (safety) | 0 |
| `inflate_copy_public` (`public-inflate-copy`, `inflate.c.copy-public`) | The theorem of type `Goal.inflateCopy`: null arguments are refused; from every reachable source both allocation failures free what they allocated and clear `dest->state`, and success gives the relocated state, the window prefix and exactly the new blocks in the ledger. Composed from the six execution lemmas of `inflate.c.copy-*`. | checked | 0 |
| Acceptance batch | `inflate_public`, `inflate_init2_public`, `inflate_sequence_safety_public` and `inflate_copy_public` registered in `tests/audit/theorems.txt`, `Goal.inflate_sequence_safety` in `tests/audit/goals.txt`; nine function-body proof mutants for `inflate`, `inflateCopy` and `inflateInit2_` in `tests/proof-mutants/public-streams.tsv`, each killed in its listed module by a local run. The acceptance suite has not yet run on a named commit. | prepared | 0 |
| Cleanup | Delete fast-path and fixed-configuration proofs that no registered theorem uses. | open | 4 |
| `uncompress*` (`public-uncompress*`) | The functional goals: all four composed on `dev` from `DecoderFacts` (`uncompress2_z_of_facts`, `uncompress2_of_facts`, `uncompress_z_of_facts`, `uncompress_of_facts`). Not planned: the format facts of `DecoderFacts` are out of scope (safety only). | not planned | 0 |
| `uncompress*_safe` (batch 3) | `Goal.uncompress2_z_safe`, `uncompress2_safe`, `uncompress_z_safe`, `uncompress_safe` (`Spec/Public/Utilities`): no undefined behaviour, termination, writes only into the output buffer (at most its capacity) and the length cells, every allocation freed on every return path, the documented return codes, `Z_MEM_ERROR` only after an allocation failure. Proved with no premise in `public-uncompress-safe` (`uncompress2_z_safe`, `uncompress2_safe`, `uncompress_z_safe`, `uncompress_safe`): every `inflate` call is `inflate_public`, every reachable stream has a decoder (`reachable_invariant_kind`); no format fact and no functional fact. The functional proof shares the run (`SafeState`, `SafeFinal`) and adds its format fact (`NoOver`). Termination: the loop's measure (unread source plus unfilled room) is below the loop fuel and falls at every `Z_OK` call, by the progress clause of `Goal.inflate` (`rc = Z_OK → used ≠ 0 ∨ out ≠ []`), a safety fact. Statement test `tests/goals/uncompress-safety` (ASan, UBSan, leak count, allocation failures; no clause violated in 9000 runs). Accepted batch: the four theorems and goals are registered (`tests/audit/theorems.txt`, `goals.txt`); four translation mutants of `uncompress2_z` (`tests/proof-mutants/api-boundary.tsv`: dropped `inflateEnd`, wrong `destLen` count, refill off by one, leak on the init error path) are each killed in `public-uncompress-safe`, where the run meets the safety facts. The proof no longer restates the program (`program`, `program_eq` removed): it runs the translation, and the loop body is described by `BodyOK` with the refill stated as a minimum. | checked | 0 |
| **Total remaining** | | | **4** |

Batch 3 statement corrections and public domains. Each changes only an internal fact of
`DecoderFacts`; no public goal (`Goal.inflate_completes`/`InflateCompletes`, the four
`uncompress*` goals, the format goals) loses any part of its domain, so no `docs/deviations.md`
row is needed.
- `d23ce2d5` `NeedDictionaryCall` gains `log.singleDictionary = true` and `ByteObjectsFit h`;
  `InflateCompletes` and the uncompress loop already assume both.
- `61995719` `TraceEvidence` excludes a zlib dictionary with a configured window larger than
  the header's. Its only use, the uncompress loop, has no dictionary. The excluded case is C
  decoding a stream that RFC 1950 (`Zlib.Decodes`) does not allow, but it is not new: it is
  zlib's default with `INFLATE_STRICT` undefined, already modelled by
  `Api.Layer.InflateAccepted` and recorded in `tests/regression/inflate-configured-window`.
- `0c56ca53` `ConsumesWithinStream` clause 2 asks for a trailer, or room and a flush other than
  `Z_BLOCK`/`Z_TREES`. `InflateCompletes` gives room and such a flush; uncompress decodes zlib.
  The excluded case (raw data, no room) is correct C behaviour, not a finding.
- `ConsumesWithinStream` clause 2 concludes `rc ≠ Z_OK ∧ rc ≠ Z_BUF_ERROR` instead of
  `Z_STREAM_END ∨ Z_MEM_ERROR`: a call refused after the end (NULL `next_out`) returns
  `Z_STREAM_ERROR` with the whole stream consumed. Every use only rules out `Z_OK` and
  `Z_BUF_ERROR`. Correct C behaviour, not a finding.
- `a974ea43` `ConsumesWithinStream` and `StopsWhenBlocked` gain `ByteObjectsFit h`; the
  protocol history records it before every call.
- `ParseMeaning`'s request clause is an implication from the token to a `needDict` stage with
  `havedict = 0`, no longer an equivalence: after `Z_NEED_DICT`, a call refused with a NULL
  `next_out` returns `Z_STREAM_ERROR`, the token becomes false and the decoder still waits
  (`tests/verification/regressions/inflate-refused-dictionary-request.lean`). Every use took
  the implication. Internal; correct C behaviour, not a finding.

Object-size limit: `StreamReachable` assumes the LP64 `PTRDIFF_MAX` limit before every inflate
call and after every caller edit, and `StreamSequenceSafety` before every call (`408c1f04`).

##### inflate, batch 1: decoding side of the format meaning

The body of a deflate stream inside one call: block headers, fixed and dynamic table installation,
the code-length table, slow symbol decoding, stored copies, the whole `inflate_fast` call, match
copies from the output and the window, and the window update at `inf_leave`. Files
`inflate.c.meaning-<topic>`. Every lemma covers every window width 8 to 15 and every wrapper;
none fixes a configuration. Statement test: `tests/goals/inflate-meaning-body` (body-mode state
fields of the real decoder against the parse position: no clause violated in about 56,000 states
of 3,200 sessions, after the corrections below).

Interface corrections agreed with the inflate owner (2026-11-10). Each made `meaning_step` false
or unprovable; the evidence is the real decoder or a counterexample state.

- P1 (`0696a247`): zlib rejects some dynamic headers only after a whole part of the header is
  read, so `dynamicBits` has no completability premise
  (`tests/goals/inflate-meaning/late-rejection.c`: three one-call sessions stop in `LENLENS` or
  `CODELENS` with `Z_OK`).
- P2 (`0696a247`): `BodyMatches` of a dynamic header gets `DynamicMatches` (counts, code-length
  code and table, lengths read so far).
- P3 (`0696a247`): `WindowMeaning` with no window requires an empty history.
- P4 (`0696a247`): `storedPad`, because `STORED` drops the pad before it waits for `LEN`; real
  decoder: raw -15, a call stopped in `STORED` with 32808 bits consumed after a header ending at
  bit 32805 (regression `tests/verification/regressions/inflate-stored-pad.lean`).
- P5 (`0696a247`): `TableMeaning` includes `StableQuery`, needed to reject an invalid code on
  fewer than 15 held bits.
- P6 (`d9fa89d1`): a stored block holds no bits, so `COPY` follows the input.
- P7 (`69b25ebe`): held-bit bounds at every waiting position, so that fewer than 8 bits at a
  block boundary is inductive; real decoder: no violation of the numeric bounds in about 32,000
  body states of 1,800 sessions.
- P8 (`03c98f14`): in a body stage `out - left` is the call's output, as `MATCH` uses it.
- P9 (`03c98f14`): `partialCopy` carries the token's distance (`0 < dist ≤ |dict ++ out|`,
  `dist ≤ 32768`).
- P11: `BodyMatches` at `.storedHeader` holds fewer than 32 bits. The `STORED` complement check
  reads bits above 32, so without the bound `stored_step` is false: raw -15, input
  `01 01 00 FE FF 01` (a valid final stored block of one byte) read whole, 45 bits held in `STORED`;
  the check goes to `BAD`. zlib holds fewer than 8 bits after `TYPEDO` and fewer than 32 after
  waiting in `STORED`.
- P12 (`123722bb`): `PendingParsed` at `.copy` admits a complete match with nothing written and no
  history bound. `MATCH` leaves for want of output room before it checks the distance, so a
  too-far distance can wait there while the call returns `Z_OK`; real decoder: raw -15, input
  `03 02` with no output room stops in `MATCH` with `Z_OK`, offset 1 and an empty window, and the
  next call reports "invalid distance too far back" (`tests/goals/inflate-meaning-body/far-match.c`,
  regression `tests/verification/regressions/inflate-unchecked-match.lean`).
- P13 (`f88873e0`): the held-bit bounds at `.none` and `.distance` exclude only valid symbols
  (at most 285, at most 29) in the held bits without their last byte. `TableMeaning` says nothing
  of the bits a reserved symbol's entry consumes (30 and 31 in `fixedDistLens`, 286 and 287 in
  `fixedLitLens`), so the bound with any symbol was not provable at a lookup that leaves for
  input; a reserved symbol leads to `BAD` instead.
- P14: the `CODELENS` clause of `DynamicMatches` also holds the converse of `Trace`: every parse
  of the header bits from no length passes through the stored lengths. `Trace` alone does not fix
  where the items of the header end, so `codelens_step` was false at a repeat error. Counterexample
  state: `HLIT = 0`, `HDIST = 3` (261 lengths); the code-length code gives symbols 2, 16, 17, 18
  length 2 (`00`, `01`, `10`, `11`); `A = [2,2,2] ++ 0^253 ++ [2]` read by items `R`; header bits
  `R ++ 01` (the code of 16, its extra bits not read); stored lengths `A ++ [2,2]`. `Trace` holds
  (the only completion is two literals 2, and `R ++ 01 00 00` also gives `A ++ 2^4`). The source
  `R ++ 01 10 ...` is valid (16 with extra 1 gives `A ++ 2^4`, a complete literal/length code with
  end-of-block and a complete distance code), but the decoder reads `10` as 17 and goes to `BAD`.
- P15: `TableMeaning` also holds `PrefixQuery` (a fitted query selects the same entry from its
  zero-padded consumed bits) and `QueryCompatible` (the fast leaf flags). At `BAD`,
  `inflate_fast` drops only the rejected token's bits and then returns the unused whole bytes, so
  the input read can end inside the bits the lookup looked at; `Inv` and `StableQuery` do not fix
  how many bits a rejected entry needs. Counterexample: a fixed block whose literal/length table
  reads `{op 64, bits 6}` for the codes of 286 and 287 keeps `Inv`, `StableQuery` and
  `QueryCompatible`, the fast call reads up to `110001`, and the code of 284 (`11000100`) continues
  it validly. Kept as a smaller kernel-checked table with `Inv` and `StableQuery` but not
  `PrefixQuery` (`tests/verification/regressions/inflate-prefix-query.lean`). The constructor
  establishes it (`constructor_establishes_prefix_query`, kept by a later builder:
  `prefix_query_of_prefix`), and so do the fixed tables (`lenfix_prefix`, `distfix_prefix`).
- Shared block (goal change). The fast decoder's `Env` required input and output in distinct
  blocks (`hsep : ib ≠ ob`). That was too narrow: input and output may be disjoint ranges of one
  block, which is defined C ([reproduction](../../tests/regression/inflate-shared-block/README.md)).
  `Env.hsep` is now `ib ≠ ob ∨ (ib = ob ∧ the input range [i0, i0 + avail_in) and the output range
  [o0, o0 + avail_out) are disjoint)`. The window block stays distinct from the output block. A
  piece of the loop whose output array `A` is arbitrary now also assumes `Env.InputFrame A i`: when
  the blocks are shared, `A` keeps the original input from the cursor `i` to the end of the input.
  Registered goals whose type changed: every goal over `Env` admits the shared block
  (`step_safe`, `fast_safe`, `actual_body_preserves_origin`, `actual_body_refines_token`,
  `actual_fast_preserves_origin`, `actual_distance_block_preserves_origin`,
  `actual_distance_refines_lz77`, `distance_lookup_matches_format`,
  `length_lookup_matches_format`, `actual_body_retains_selected_length`,
  `actual_copy_match_refines_lz77`, and the `Origin` goals). `StepPre` (so `step_safe`, the
  `actual_body_*` goals and `actual_body_retains_selected_length`) gains the field
  `inputFrame`; `actual_pull_preserves_origin`, `actual_rollback_preserves_origin`,
  `actual_distance_block_preserves_origin` and `actual_distance_refines_lz77` gain the premise
  `InputFrame`. With distinct blocks the new premise is vacuous, so each new type implies the old
  one. The whole-call goals `fast_safe` and `actual_fast_preserves_origin` carry no new premise: the
  loop discharges `InputFrame` from the separation, since the decoder writes only in the output
  range (`Env.inputFrame_of_frame`, `Env.InputFrame.write`).

The body-mode clauses are checked on the real decoder by `tests/goals/inflate-meaning-body`
(about 56,000 states of 3,200 sessions, no violation).

| Lemma | Meaning | State | Hours |
| --- | --- | --- | ---: |
| `meaning_interface_body` | P1 to P4, `DynamicMatches` and suffix stability in `TableMeaning` (`inflate.c.meaning`, `0696a247`). | checked | 0 |
| `LoopMatches` (`meaning-loop`, `meaning-write`, `meaning-frame`) | The relation between mode steps inside one call: registers, input consumed in the call, held bits, stage, output since the call base, window and check of the output before the call. Shared with batch 2. Agreed with batch 2; output-write and frame lemmas. | checked | 0 |
| `lenfix_inv`, `distfix_inv`, `lenfix_stable`, `distfix_stable` (`meaning-fixed-tables`) | The static fixed tables have `DecodeTableInvariant.Inv` with the fixed code lengths, short lookups included, suffix-stable and prefix-read queries (`lenfix_prefix`, `distfix_prefix`) and compatible leaf flags. | checked | 0 |
| `lookup_meaning` (`meaning-lookup`, `meaning-length`, `meaning-distance`) | Slow `lookup1`/`lookup2` on an `Inv` table with refill: the selected leaf is the symbol of the held bits, with fewer than 15 bits available, or the input has no valid symbol. Folded into the step lemmas (`fitted_leaf_meaning`, `lookupLoop_fail`, `lookup1_len_fail`, `lookup2_len_fail`). | checked | 0 |
| `codes_lookup_meaning` (`meaning-codelens-items`) | The same for the code-length table (`CodeLengthMeaning`), the empty code-length code included (`cl_iter`). | checked | 0 |
| `table_step` (`meaning-dynamic-steps`) | `TABLE`: wait, the count rejection (`BAD`, no valid continuation), or fall-through to `LENLENS` with `LoopMatches`. No hypothesis beyond the stream record. | checked | 0 |
| `lenlens_step` (`meaning-dynamic-steps`) | `LENLENS`: code-length code lengths across calls; rejected with no completion, or fall-through to `CODELENS` with `CodeLengthMeaning`, the empty-code cells and fewer than 8 held bits. Hypothesis beyond the stream record: `WellFormed` (array sizes). | checked | 0 |
| `codelens_step` (`meaning-dynamic-steps`, `meaning-codelens-items`, `meaning-dynamic-tables`) | `CODELENS`: lengths across calls, repeats (`BAD` through the converse of the parse), end-of-block and code checks (`BAD`: no `DynamicHeader` completion), installation of both tables with `Inv`, `StableQuery`, `PrefixQuery` and `QueryCompatible`, leave for `Z_TREES` or fall-through to `LEN_`. Hypotheses beyond the stream record: `WellFormed`, `CodeLengthInvariant`, the installed table's content classification. | checked | 0 |
| `typedo_step`, `type_step` (`meaning-block`) | `TYPE`, `TYPEDO` before the final block: stored, fixed (with `lenfix_inv`), dynamic, type 3 (`BAD`, no type-3 body). The static tables come from `LibraryGlobals`. | checked | 0 |
| `stored_step` (`meaning-block`, `meaning-copy`) | `STORED`, `COPY_`, `COPY`: padding, length check and byte copies across calls. No hypothesis beyond `LoopMatches`, the stream record and the window bounds; the held-bit bound comes from `BodyMatches` (P11). | checked | 0 |
| `len_slow_step` (`meaning-length`) | `LEN_`, slow `LEN`: literal, end of block (fewer than 8 held bits), length, invalid code (`len_slow_step`, `len__step`, into `lenext_step`). Hypotheses beyond those of `match_step`: the negated fast-branch condition and `DataTablesSafe`. | checked | 0 |
| `distance_steps` (`meaning-distance`) | `LENEXT`, `DIST`, `DISTEXT`: extra bits, distance symbol, invalid distance (`lenext_step`, `dist_step`, `distext_step`, into `match_step`). Hypotheses beyond those of `match_step`: `DataTablesSafe` and the back-counter bound (`DataPendingInvariant`). | checked | 0 |
| `lit_step` (`meaning-lit`) | `LIT`: the pending literal is written. | checked | 0 |
| `match_step` (`meaning-match`) | `MATCH`: copies from the output and from the window, overlap, too far back. | checked | 0 |
| `fast_call_meaning` (`meaning-fast-token`, `meaning-fast-loop`, `meaning-fast`, `inffast.c.body-token-reject`) | One whole `inflate_fast` call from `LEN`, in the standard step shape: more tokens of the block or the end of the block give `LoopMatches`; a rejected token gives `BAD` with `LoopDoomed` (P15: the token is rejected on its own bits, `actual_body_rejects_prefix`; a distance too far for the saved window is too far for the whole history under a full window, `Token.Rejected.rebase`). Input and output are any caller byte views `DispatchBuffers` admits, also disjoint ranges of one block (`inflate_fast_entry`, shared-block goal change above). The window block differs from the output block by the caller's output range (`callerRange_slow_output`), not by a premise. Hypotheses beyond `match_step`: `Good`, `DataTablesSafe`, `DataPendingInvariant`, `DispatchBuffers`, `ByteObjectsFit`. | checked | 0 |
| `leave_window_meaning` (`meaning-leave-window`) | `updatewindow` at `inf_leave` gives `WindowMeaning` of the output after the call, the first allocation included; an allocation failure keeps the state and the old `WindowMeaning`. Hypotheses: `Good`, the default allocator, the output bytes, the output buffer not the window block. | checked | 0 |
| Cleanup | Deleted the 33 `inflate.c.fast*` modules that no registered theorem, public goal, meaning module or other module imports (the earlier semantic slices and the view frames built on them). The other `inflate.c.fast*` modules are imported by the fast path of the meaning proof. | checked | 0 |
| **Remaining for batch 1** | | | **0** |

For batch 3: ConsumesWithinStream bounds.

| Name | Meaning | State | Hours |
| --- | --- | --- | --- |
| `HeldWithin` (`heldWithin`, `meaning-held-within`) | A decoder state at a grammar stage holds no bits past the end of a valid stream its bits are comparable with; no stage lies beyond a complete stream. Batch 3's statement plus one premise, `(consumed ++ held).length % 8 = 0`, which holds at the use. No other premise. | checked | 0 |
| `LeaveShort`, `LoopRefuted` in batch 1 step lemmas (`meaning-leave-short`) | Every leave of a body step for want of input (`have = 0`) holds bits that do not complete the field its mode waits for (`LeaveShort`: fewer than the `NEEDBITS` count, `COPY` with bytes left, no complete valid symbol or code-length item of any meaning of the installed table). Every rejection (`BAD`) reads input comparable with no valid full-window stream (`LoopRefuted`, stronger than `LoopDoomed`: the stream also does not end inside the bits read). Steps: `TYPE`/`TYPEDO`, `STORED`, `COPY_`/`COPY`, `TABLE`, `LENLENS`, `CODELENS`, `LEN_`/`LEN`, `LENEXT`, `DIST`, `DISTEXT`, `MATCH`, `inflate_fast`. Both checked first on the real decoder (`tests/goals/inflate-meaning-body`: about 75,000 starved leaves, about 490 data errors on corrupted sources, no violation). `LoopBad` (batch 2) still carries `LoopDoomed` (`LoopRefuted.doomed`). | checked | 0 |
| `StopShort` | A call that consumes exactly the whole valid stream does not return `Z_OK` or `Z_BUF_ERROR` (raw: unless the output room is short or flush is `Z_BLOCK`/`Z_TREES`). Per-call part checked: a trip of the mode loop short of its field (`LeaveShort`) has not read a whole valid stream (`LoopMatches.starved_not_end`, `meaning-stop-short`). Left: the whole-call composition (`loop_meaning`, batch 3), and the stops for room or `Z_BLOCK`/`Z_TREES` (`BlockedLeave`, `wrapParsed_due`). | not planned | — |
| `FailWithin` | A call that leaves `BAD` or `MEM` did not read past the end of a valid stream the input before it began. Per-call parts checked: a rejection excludes every comparable valid stream (`LoopRefuted.not_comparable`, `meaning-stop-short`), and at every trip the input read is a beginning of every comparable valid stream (`LoopMatches.within`, `meaning-held-within`, for the `MEM` leave). Left: the whole-call composition (`loop_meaning`, batch 3). | not planned | — |

##### inflate, batch 2: stream side of the format meaning

The wrapper header, the dictionary request and installation, the trailer, the end, the assembly
of mode steps into a call and of calls into a history, and `meaning_init`, `meaning_rebuffer`,
`meaning_dictionary`, `meaning_accepted`, `meaning_prefix`. Files `inflate.c.meaning-<topic>` and
`ZlibF/Math/inflate-meaning-*`. Every lemma covers raw, zlib, gzip and automatic detection and
every accepted windowBits, 0 included. In a protocol trace no header record is attached
(`inflateGetHeader` is not a trace step), so header capture never happens; the header modes are
proved with `head = NULL`. Statement test: `tests/goals/inflate-meaning` (state fields of the
real decoder against the parse position; no fact violated in 6000 sessions).

Interface corrections, agreed with the inflate owner and on `dev` (`bd0831d3`): the header stage
admits raw data before its first call; `ConfigMatches` ties the decoder configuration to the
trace; `needDict` admits any `DICTID`; fewer than 8 bits are held at a block boundary (batch 1
proves it); a `MEM` state keeps the conclusions of `meaning_accepted` and `meaning_prefix`;
`WrapMatches` holds the stream-side stage fields (`inflate.c.meaning-stream`).

| Lemma | Meaning | State | Hours |
| --- | --- | --- | ---: |
| `ConfigMatches`, `WrapMatches` | Configuration fields and per-stage fields of the header, `needDict`, trailer and end stages (`bd0831d3`). | defined | 0 |
| `LoopMatches` | Batch 1's row; batch 2 sent the draft and composes against it. | batch 1 | 0 |
| `wrap_header_grammar` (`Math/inflate-meaning-wrap`, `meaning-wrap-steps`) | Byte steps of the zlib and gzip headers keep a completable header prefix; the decoder's waiting points are not complete headers; completion to body or `needDict`; each rejection of `HEAD`, `FLAGS`, `HCRC` has no completion. | checked | 0 |
| `wrap_trailer_grammar` (`meaning-wrap-steps`, `meaning-accept`) | End of body to trailer to done; a trailer mismatch has no completion. | checked | 0 |
| `meaning_init` (`inflate.c.meaning-init`) | `inflateInit2_` for every accepted windowBits gives the header stage with no input. | checked | 0 |
| `meaning_rebuffer` (`meaning-rebuffer`) | A caller rebuffer keeps the state, window and tables; frame lemmas for every stage. | checked | 0 |
| `head_step` | `HEAD`: raw to `TYPEDO`, zlib header (width 0 sets the width), gzip magic, every rejection. | not planned | — |
| `dictid_step`, `dict_step` (`meaning-dictid`) | `DICTID` stores the identifier and asks for the dictionary (`dictid_step`, checked; `NeedDictExit`); `DICT` asks again or enters the body (open; needs P16, `last = total = 0` in the `needDict` clause, asked of batch 1). | not planned | — |
| `gzip_fixed_steps` | `FLAGS`, `TIME`, `OS`, `EXLEN`, with the header CRC accumulator. | not planned | — |
| `gzip_field_steps` | `EXTRA`, `NAME`, `COMMENT`: byte runs across calls, CRC over the input bytes. | not planned | — |
| `hcrc_step` | `HCRC`: the header CRC check and entry to the body. | not planned | — |
| Shared loop lemmas (`meaning-bits`, `meaning-stuck`, `meaning-outcome`, `meaning-fields`) | `LoopMatches.needbits`; `LoopDoomed.of_stuck`; `LoopBad`, `TripOutcome`, `bad_trip`; held bits as little-endian bytes. | checked | 0 |
| `trailer_steps` (`meaning-trailer`, `meaning-check`) | `DONE` and gzip `LENGTH` (checked); zlib and gzip `CHECK` with the Adler-32 or CRC-32 update of the call's output, then the length field or the end (`check_step`, checked); raw `CHECK` needs P10 (end stage in `CHECK` for raw data, proposed to batch 1). | not planned | — |
| `leave_meaning` (batch 3, `meaning-leave`) | `inf_leave`: totals and check update with the call's output; window update from batch 1's lemma; `Z_MEM_ERROR`. `leave_meaning` for a loop exit with `LoopMatches` (`LeaveMeaning`), `leave_meaning_bad` for the `BAD` exit (`LeaveBad`), from `inflate_leave_values` and `checkMeaning_leave`. | checked | 0 |
| `loop_meaning` (batch 3, `meaning-run`) | The mode loop of one call, entered with `LoopMatches`, ends in a `LoopExit`: a leave with `LoopMatches`, `Z_STREAM_END`, or `Z_DATA_ERROR` with `LoopBad`, or the dictionary request. Premises: `TripMeaning` (the per-mode steps of batches 1 and 2, mode by mode) and `SideKept` (the safety facts the steps need, kept by every trip). | checked | 0 |
| `meaning_step` assembly (batch 3) | Entry, refusals, run and leave give `ParseMeaning` after the call, with the request token. | not planned | — |
| `meaning_dictionary` (`meaning-dictionary`) | `inflateSetDictionary`: refusals, identifier mismatch, `Z_MEM_ERROR`, raw installation, zlib installation in `DICT`. | checked | 0 |
| `deflate_prefix_order` (`meaning-prefix-order`, `meaning-accept`) | A parse position on a prefix of a valid stream lies on its parse (output prefix, exact end), a finished parse is a specification parse, the configured zlib window decodes like the announced one, and stage headers are the stream's header. | checked | 0 |
| `meaning_accepted` (`meaning-format`) | A finished single-dictionary epoch consumed an accepted stream. | checked | 0 |
| `meaning_prefix` (`meaning-format`) | Prefix, no data error, exact end, also after `Z_MEM_ERROR`. | checked | 0 |
| Cleanup | Generalize or delete the default-configuration header, dictionary and wrapper modules. | not planned | — |
| **Remaining for batch 2** | | | **0** |

Batch 2, gzip header modes for `inflate_call_gzip`. Checked on `dev`:
`inflate_dispatch_gzip_header_rank` (`inflate.c.gzip-header-dispatch`), the inflate owner's
interface statement, exactly. One dispatch from `FLAGS` .. `HCRC` runs without a fault for any
wrapper with gzip allowed, with or without an attached header record, and keeps the
representation, the caller packet, the header record and the footprint. Two premises are
narrower than zlib.h (`docs/deviations.md`): the record's `extra` buffer is separate from the
unread input, and in `EXTRA` the record's `extra_len` is not below the remaining length. Both
come from real C undefined behaviour in EXTRA's `zmemcpy`
(`tests/regression/inflate-gzip-extra`). Whether `Goal.inflate` keeps them as caller-domain
clauses is the owner's decision. The name and comment buffers may overlap the input.

The skeleton clause "the flags word is kept or a 16-bit word" (skeleton/inflate 5d6f00e8) is
false as stated: `inflatePrime` can leave 32 bits in the bit buffer while the decoder waits in
`FLAGS`, and the real C then writes `flags = 65544`
(`tests/regression/inflate-gzip-flags-prime`). The proved form adds the condition on the entry
bit buffer. `InflatePhase.flags` makes the same 16-bit claim over every history; the owner decides
how to correct it.

| Lemma | Meaning | State | Hours |
| --- | --- | --- | ---: |
| `HeaderFoot` (`inflate.c.gzip-header-frame`) | Pointwise footprint against the entry heap; gives `BufferFrame` and `LiveChange`. | checked | 0 |
| `GzInv` (`inflate.c.gzip-header-state`) | Step invariant: state, stream and record writes, `hbuf` and region stores, `NEEDBITS`, input consumption. | checked | 0 |
| `gz_FLAGS` .. `gz_HCRC` (`inflate.c.gzip-header-modes`) | Each mode runs to a leave in a header mode, `TYPE` or `BAD`; the `NAME`/`COMMENT` byte loop; `CRC2`, `CRC4`; `EXTRA`'s copy. | checked | 0 |
| `inflate_dispatch_gzip_header_rank` (`inflate.c.gzip-header-dispatch`) | The interface theorem. | checked | 0 |
| `inflate_dispatch_gzip_header_flags_leave_word` (`inflate.c.gzip-header-dispatch`) | A leave has no input left; the flags word is kept, or is a 16-bit word when the entry bit buffer held 0, 8 or 16 bits. | checked | 0 |
| **gzip header modes** | | | **0** |
