# 2333419: `inflateBack` reads `state->sane` without setting it

- **Fix:** upstream commit `2333419cd76cb9ae5f15c9b240b16a2052b27691`, "Fix inflateBack to detect invalid
  input with distances too far", in zlib 1.2.13.
- **Revert** (`revert.patch`, `lean.patch`): `inflateBackInit_` no longer sets `state->sane = 1`. The
  state is allocated without zeroing, so the field holds whatever the allocation held.
- **Calls** (`trigger.c`, `model.lean`): `inflateBackInit` with `windowBits` 9 and a 512-byte window;
  `inflateBack` on a raw fixed-code block whose first symbol is a match of length 3 at distance
  1000, followed by ten zero bytes, so that `inflateBack` takes `inflate_fast`; `inflateBackEnd`.
  The allocation reads as zeros: in C ASan fills every allocation with zeros (`run.sh`); in the
  model the heap's oracle for uninitialised values gives 0, one of the values every goal must hold
  for.
- **C:** with the revert, `sane` is 0 and `inflate_fast` skips the "invalid distance too far back"
  check; it copies from `window + (wsize - op)` with the unsigned `512 - 1000` wrapped, and ASan
  reports a read fault (SEGV on x86_64 Linux, a bus error on arm64 macOS) in `inflate_fast`.
  Without it, no report; `inflateBack` returns `Z_DATA_ERROR` "invalid distance too far back".
- **Model:** with the revert, `Fault.ub` "pointer arithmetic outside its object". Without it, the line
  `trigger.c` prints.
- **Domain:** inside `Goal.inflate_back_sequence_safety`: the history is `inflateBackInit` with the
  default allocator and a window of `1 << windowBits` bytes, then `inflateBack` with call-backs that
  give the input once and count the output; the goal holds for every value of the uninitialised
  memory, 0 included. The state that `Goal.inflateBackInit__safety` promises has `sane` set to 1, so
  with the revert that goal fails too. Checked by reading the premises.
