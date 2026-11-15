# Callback decoder proof skeleton (historical)

This page keeps the inflateBack part of the section "Public API proof readiness" of [progress](../progress.md), as it stood
after the required goals were accepted on `bde170e9`. The text is unchanged apart from relative links. It is a historical
record: states such as "open" and "checked", hours, counts and dates describe the time each
entry was written. They are not current status. Current status and remaining work are only in
[progress](../progress.md).

#### inflateBack

Safety of the callback decoder (owner's request of 2026-11-12): `Goal.inflate_back_sequence_safety`
(`ZlibF/Spec/Public/Sequences.lean`), stated beside the unchanged `Goal.inflate_back_sequence`. The
call-backs are the goal's `CallbackProtocol`: arbitrary caller code that returns, changes only its
own blocks and the window slice it must keep, hands out readable input outside the window, and
offers a finite total input (`inputBound`). The goal adds `inputBound < 2^48` (loop fuel;
`docs/deviations.md`). Statement test: `tests/goals/infback-callbacks` (ASan/UBSan, 30000 cases,
no report). Skeleton: branch `skeleton/inflate-back`, `ZlibF/Proof/infback.c.safety-skeleton.lean`
(type-checks; lemma proofs open). The earlier internal contract `CbContract` is narrower than the
protocol, so the call-back lemmas are restated over `PInv`; their bit algebra is reused.
Issue (not planned, functional goal): `Goal.inflateBack` has no bound on `inputBound`, so a
protocol whose input exceeds the loop fuel makes it false in the model.
Needed invariant: `inflate_fast` assumes `state->bits < 8` on entry. `inflate.c` checks it before the
fast path (upstream e7bb978); `infback.c` does not, so the proof shows that fewer than 8 bits are
held when a round starts in `TYPE`, `TABLE` or `LEN` (row `BitsShort`). With 8 or more bits held,
`inflate_fast` could move `next` back before the chunk `in` gave. Evidence:
`tests/goals/infback-callbacks/bits8.sh` (60000 cases, no trap).
Goal corrections (46ce3a0a, 200f80e1): the histories are `BackSafeReachable`. The window is a
slice of a heap byte block; every byte object has fewer than `2^63` bytes on the heap of a call
and after each call-back step (`BackPlatform`); every input chunk lies in a heap byte block
(`BackFirstChunk`, `BackPlatform`); a caller edit between calls keeps the read-only flag of a live
block. Deviation rows: "Callback decoder window", "Callback decoder input chunks", the platform
row and "Callbacks". Candidate generalisation, not planned now: an input chunk at any byte reference
(a caller's structure field, static data) for both decoders together, `inflate` and `inflateBack`;
both rest on `inflate_fast`, whose entry takes a raw byte block.
Composition: `inflate_back_sequence_safety` (c7169b54) composes the lemmas below with `lenFast_of_blk`,
the fast path at a window in a heap byte block, and no open premise; every history has its window there
(`back_reach_window`). The earlier composition `inflate_back_sequence_safety_of`, from the premise
`FastOk` (the fast path at every window), is deleted; `docs/proof/callbacks.md` says why the premise was
not proved. Registered with proof mutants (`tests/proof-mutants/infback-sequence.tsv`).

| Lemma | Meaning | State | Hours |
| --- | --- | --- | ---: |
| `PInv` frames | The loop invariant over the caller protocol: `CallbackFrame` and the live set compose across call-back calls and library writes; `PInv` survives a state or register write | checked (dd5f9e1e) | 0 |
| `PULL_p` | `PULL()`: `in` only on an empty chunk; the protocol's `inStep` gives the chunk and the log entry; `Z_BUF_ERROR` on 0 | checked (dd5f9e1e) | 0 |
| `PULLBYTE_p`, `NEEDBITS_p` | One byte into `hold`, and `NEEDBITS(k)` for `k ≤ 32` (bit algebra of `inflate.c.main.macros`) | checked (52ae3999) | 0 |
| `ROOM_p` | `ROOM()`: `out` on the full window (`outStep`), `whave = wsize`, restart at the window; `Z_BUF_ERROR` on refusal | checked (7971d171) | 0 |
| `TYPE_p` | `case TYPE`: last flag and block type, `DONE` after the last block | checked (472c8a15) | 0 |
| `STORED_p` | `case STORED`: length check and the copy through `PULL` and `ROOM`; the chunk may share the window's block | checked (eec477cd) | 0 |
| `TABLE_p` | `case TABLE`: header, code-length code, decoded lengths, three `inflate_table` calls, tables installed (`TablesOk`, with the decode invariant and query stability), and the fall-through into `LEN` | checked (650c8931) | 0 |
| `BitsShort` | Fewer than 8 bits held at the start of a round in `TYPE`, `TABLE`, `LEN` (`Short` in `Round`): lookups with pull witnesses, `consumed_gt` from `StableQuery` and `PrefixQuery`, the code-length decoding of `TABLE` by `CodeLengthContents` | checked (57c7fabd, 9e93b576) | 0 |
| `fast_env` | From `PInv` at `LEN` after `RESTORE`: an `EnvG true` with `start = wsize`; the window aliasing itself is covered by c51943af (`EnvG true`, `inflate_fast_safe_progress`). Owner: batch C | checked (c7169b54) | 0 |
| `fast_consumes` | `inflate_fast` on an `EnvG α` whose length table has `LenLeavesPositive` strictly consumes bits: `bits' + 8·avail_in' < bits + 8·avail_in` unless it ends in `TYPE` or `BAD` (the measure of route (a)). Owner: batch C | checked (02e8c222) | 0 |
| `LEN_slow_p` | `case LEN` without the fast path: literal, end of block, length/distance with the distance check and the copy through `ROOM`, invalid codes | checked (06e4a17d) | 0 |
| `LEN_fast_p` | `case LEN` with the fast path: `RESTORE`, `inflate_fast` on `fast_env`, `LOAD`; `PInv`, the measure (from `fast_consumes`) and `Short` afterwards. Owner: batch C | checked (c7169b54) | 0 |
| `dispatch_p` | One round of the dispatch: every mode reachable from `PInv`; the measure falls or the call leaves with one of three results; the fast path is the premise `LenFast` until `LEN_fast_p` | checked (650c8931) | 0 |
| `loop_p` | The dispatch loop ends within the fuel (`backMeasure < 2^64` from `inputBound < 2^48`) | checked (650c8931) | 0 |
| `back_call` | One call: prologue, `loop_p`, epilogue (the last partial window to `out`, `next_in`, `avail_in`): `back_call_partial` (a call that returns, any input) and `back_call_total` (input below `2^48`) | checked (3a2a8753, f91f401d) | 0 |
| `back_null`, `back_end_blk` | Null stream; `inflateBackEnd` on a reachable history (`back_end_public`) | checked (6f9575e7, c7169b54) | 0 |
| `back_reach_valid_blk` | Every reachable history leaves a valid state over the caller's window (init, rebuffer, `back_call_partial` with the loop rule without a measure) | checked (6f9575e7, c7169b54) | 0 |
| **Total** | | | **0** |
