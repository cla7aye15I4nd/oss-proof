# Working rules (`projects/brotli`)

Inherits all rules of [`../../AGENTS.md`](../../AGENTS.md), including the **Strict ISO C17 Undefined Behaviour Policy**
(no `NULL + 0`, no wild/dangling pointer `+ 0`, no `NULL - NULL`, no cross-object pointer subtraction or comparison,
and no `memcpy`/`memset` with `n == 0` on `NULL` or dangling pointers).

Goal: kernel-checked Lean 4 proofs about a faithful translation of upstream Google Brotli (`master`),
covering `libbrotlidec` (`c/include/brotli/decode.h`, `c/dec/`, and the `c/common/` units it links).
The goal is full safety (no undefined behaviour, no memory error, no dangling borrow, no leak,
termination) of every public decoder function and every call sequence, for the default scalar
x86_64 Linux LP64 build (`BROTLI_BUILD_PORTABLE` / scalar fallback without target-specific SIMD
intrinsics):

1. `BrotliDecoderDecompressStream` is safe on every input and every buffer split across calls,
   including error states, partial block switches, custom attached dictionaries and zero-copy
   output borrows;
2. `BrotliDecoderDecompress` (one-shot decompression) is safe on every input;
3. Every other public function in `c/include/brotli/decode.h` is safe across every call sequence:
   `BrotliDecoderCreateInstance`, `BrotliDecoderDestroyInstance`, `BrotliDecoderSetParameter`,
   `BrotliDecoderAttachDictionary`, `BrotliDecoderHasMoreOutput`, `BrotliDecoderTakeOutput`,
   `BrotliDecoderIsUsed`, `BrotliDecoderIsFinished`, `BrotliDecoderGetErrorCode`,
   `BrotliDecoderErrorString`, and `BrotliDecoderVersion`.

The encoder (`c/enc/`) and functional decoding equivalence to RFC 7932 beyond what safety requires
are not planned: a functional fact that a safety proof depends on (such as Huffman table bounds in
`c/dec/huffman.c` or ringbuffer cursor bounds in `c/dec/decode.c`) is in scope. Read
`docs/overview.md` first, then `docs/spec/safety.md`. Keep proof explanations in `docs/proof/`.
State the status only in `docs/progress.md`, as done or not done.

Work as fast as honest work allows: process exists to keep the result honest, not to slow it down.

## Source

- `brotli/` is the upstream submodule (`https://github.com/google/brotli`). Never modify it. The
  verified source is `brotli/` plus `patches/*.patch` applied in name order.
- A patch is allowed only for a confirmed Brotli bug that blocks a proof. It must be minimal, match
  a fix submitted upstream, and be listed in `patches/README.md`. A patch may land before its
  upstream submission when the owner approves it; `patches/README.md` then marks it as local and
  pending, and it is replaced by the upstream fix when one exists. Delete a patch once upstream
  merges the fix and the pin moves past it.
- Translations mirror the C layout:
  - `brotli/c/common/X.c` is `BrotliF/Brotli/common/X.c.lean` (`.h` -> `.h.lean`);
  - `brotli/c/dec/X.c` is `BrotliF/Brotli/dec/X.c.lean` (`.h` -> `.h.lean`);
  - `brotli/c/include/brotli/decode.h` is `BrotliF/Brotli/include/decode.h.lean`.
  Each function keeps its C name, and its docstring starts with the C signature.
- Specifications live in `BrotliF/Spec/{Common,Safety,Functional}/`. No `Safety` or `Common` module
  may import a `Functional` module, and no `Spec` module may import `BrotliF/Proof/`.
- Proofs about `X.c` live in `BrotliF/Proof/X.c.<topic>.lean`. Proofs of public goals live in
  `BrotliF/Proof/public-<name>.lean`.
- Heap-free mathematics (Kraft inequality, two-level Huffman geometry, prefix coding, ringbuffer
  modular arithmetic) goes to `BrotliF/Math/`. The runtime (heap, pointers, loops, faults) is
  `BrotliF/Runtime/*.lean`.

## Translation

- Translate statement by statement. Do not reorder, merge or simplify.
  Four normalisations are accepted and are not translation bugs:
  an out-parameter of an internal function is passed by value and returned as a second result;
  two reads of one location with no store between them are one read;
  consecutive assignments to fields of one record are one record update;
  a signed operation that a preceding test of the same function keeps in range uses the plain
  operator. Anything else is a translation bug, documented with examples in
  `docs/design/translation.md`.
- Every undefined behaviour the C can reach raises `Fault.ub`. Unsigned arithmetic wraps. Signed
  arithmetic, shifts and narrowing conversions are checked. Pointer arithmetic (`p + k`) is checked
  against object bounds at the point the pointer is formed, even if it is not dereferenced.
- Reading an uninitialised integer returns an arbitrary value from `Heap.garbage`, and a theorem
  must hold for every garbage function. A pointer in fresh memory is `NULL` in the model, which is
  weaker than C: the proof and review show that every pointer field of `BrotliDecoderState` (and of
  embedded sub-structs such as `BrotliMetablockHeaderArena` / `BrotliMetablockBodyArena`) is
  written before it is read (`docs/trusted-base.md`).
- **Static tables stay symbolic in proofs.** The built-in 120 KB static dictionary
  (`brotli/c/common/dictionary.c`) and the 121 word transforms (`brotli/c/common/transform.c`) are
  represented in `LibraryGlobals` with exact byte-size and structural predicates. Never run
  `decide +kernel` over large tables or monadic `C.run` computations.
- Never change a translation to make a proof easier. A mismatch with the C is a translation bug.
  Fix it, and add a differential test that catches it.
- Every proof depends on the runtime. Change `BrotliF/Runtime/` only for a confirmed mismatch with C,
  in its own commit.

## Key Brotli hazards to model and verify without shortcuts

1. **Streaming suspension and resumption (`decode.c`).** `BrotliDecoderDecompressStream` suspends
   and resumes across dozens of `BrotliRunningState` and sub-state enumerators. The state invariant
   must hold on **every** return (`SUCCESS`, `NEEDS_MORE_INPUT`, `NEEDS_MORE_OUTPUT`, and `ERROR`),
   and subsequent calls on an already-finished or already-errored state must be proved safe without
   assuming the caller stops calling.
2. **Zero-copy output borrows (`BrotliDecoderTakeOutput`).** `TakeOutput` returns a `const uint8_t*`
   into the decoder's internal ringbuffer. The specification must prove that the returned slice is
   readable and valid until the next mutating call (`DecompressStream`, `TakeOutput`, or
   `DestroyInstance`), and the history model must allow the caller to read it in that window.
3. **Attached dictionaries (`BrotliDecoderAttachDictionary`).** Ordering (`BROTLI_STATE_UNINITED`)
   and caller-buffer liveness through `DestroyInstance` must be explicit in the sequence invariant.
4. **Two-level Huffman tables (`huffman.c`) and static dictionary transforms (`transform.c`).**
   Prove exact table-allocation bounds (`BROTLI_HUFFMAN_MAX_SIZE_*`) and word-transform slice
   bounds from first principles; never assume table entries are in bounds without proving
   `BrotliBuildCodeLengthsHuffmanTable` / `BrotliBuildHuffmanTable` establishes them.

## What counts as proved

There are two levels. Say which one you mean.

- **Checked.** The theorem is on `dev`, and the fast gate is green on that commit: everything
  builds, there is no `sorry`, and no forbidden construct (`PartialCheck.lean` rejects `unsafe`,
  `partial`, `opaque`, `extern`, `implemented_by`, and any axiom outside the three below). Lean's
  kernel has checked the proof. Day-to-day work is merged at this level.
- **Accepted.** The theorem is also listed in `tests/audit/theorems.txt`, and the acceptance suite
  is green on a commit you name: axiom gate, fresh-environment kernel replay, exact goal match,
  self tests, and differential tests (with AddressSanitizer and UndefinedBehaviorSanitizer). Only
  an accepted result may be reported as final.

Rules that hold at both levels:

- Only `propext`, `Classical.choice` and `Quot.sound` are allowed. Never use `sorry`,
  `native_decide`, `bv_decide`, `axiom`, `implemented_by`, `extern`, `unsafe`, `partial` or
  `opaque`. Do not look for ways around the checks; report the obstacle.
- A goal is proved only by a theorem whose type is exactly the goal, plus a concrete non-vacuity
  witness theorem showing all premises hold simultaneously on a non-trivial execution.
- A theorem states its precondition explicitly. A precondition narrower than `decode.h` allows is
  written in the theorem's docstring and listed in `docs/deviations.md`. Never shrink the domain
  silently.
- **Disjoint caller regions.** Caller-supplied memory regions with no semantic reason to overlap
  may be assumed pairwise disjoint when that makes the proof simpler: input buffer, output buffer,
  attached dictionary buffers, and scalar in/out parameter cells (`available_in`, `next_in`,
  `available_out`, `next_out`, `total_out`, `decoded_size`, `size`). Each such premise stays
  explicit in the statement and gets a row in `docs/deviations.md`. This does not allow narrowing
  by parameter value, or dropping a reachable case in which regions do not alias (including
  `available_out == 0` with `next_out == NULL` for zero-copy streaming).
- **No callee contracts as assumptions.** A callee's specification is a theorem about the
  translated callee. A representation invariant is established by `BrotliDecoderCreateInstance`,
  which also shows that the invariant can hold.
- When a proof is stuck, decide which of four causes it is, without assuming the answer: the proof
  technique, a wrong specification, a translation bug, or a real Brotli bug. For a possible Brotli
  bug, build a concrete input, run the real C under AddressSanitizer and UndefinedBehaviorSanitizer,
  and report it with the reproduction. Never narrow a precondition to hide it.
- Differential tests are evidence of fidelity, not proof. Say so when reporting.

## Proof workflow

1. **Bootstrap runtime and audit gates first.** Port the runtime (`Heap`, `Ptr`, `Monad`, `Libc`),
   `PartialCheck.lean`, `Audit.lean`, `check-spec-layers.py` and `check-sorry.sh` before writing
   proofs, so every commit from the start passes the fast gate.
2. **Translate and differential-test before proving.** Translate the `c/common/` and `c/dec/` units
   and run C-vs-Lean differential tests (single-shot, 1-byte streaming splits, error streams,
   dictionary transforms, zero-copy `TakeOutput`) to shake out translation mismatches early.
3. **Test the goal statements first.** Check each public safety goal and sequence invariant on
   concrete C executions (including allocation failure at every `BROTLI_DECODER_ALLOC` site).
4. **Build the skeleton top down.** On branch `skeleton/<result>`, write the proof of the goal from
   named lemma statements, with lemma proofs left open (`sorry` is allowed on `skeleton/*` branches
   and nowhere else). Keep the open-lemma table in a comment at the head of the skeleton file.
5. **Hide large state invariants behind an interface.** `BrotliDecoderState` is large; expose small
   interface lemmas per sub-phase and never unfold the full invariant across unrelated modules.
6. **Close lemmas on `dev`.** Prove one lemma at a time, build only the affected module target
   during iteration, and run at most four parallel build jobs (`-j 4`) under a 16 GB memory limit.
   Delete dead modules that no goal or skeleton uses.

## Findings

A finding is listed in `docs/findings.md` (with a reproduction under `docs/findings/<name>/`) only
if it is a confirmed defect of upstream Brotli itself, reachable through documented `decode.h`
calls, and demonstrated under ASan/UBSan or by the letter of C. Every sanitizer reproduction also
goes under `tests/regression/<name>/` with `run.sh` and `report.txt`.

## Documents and collaboration

- File names are lowercase, with hyphens (`overview.md`); `README.md` and `AGENTS.md` keep their
  conventional names.
- Write short sentences. Say what is proved, what is assumed, and what is not done.
- Do not put machine names, addresses, user names, local paths or tool names in the repository or
  in commit messages.
- Land day-to-day work on `dev` once the fast gate is green; merge `dev` to `main` at milestones
  after the acceptance suite is green. Parallel workers own disjoint files and never edit the same
  file concurrently.
