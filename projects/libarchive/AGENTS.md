# Working rules (`projects/libarchive`)

Inherits all rules of [`../../AGENTS.md`](../../AGENTS.md), including the **Strict ISO C17 Undefined Behaviour Policy**
(no `NULL + 0`, no wild/dangling pointer `+ 0`, no `NULL - NULL`, no cross-object pointer subtraction or comparison,
and no `memcpy`/`memset` with `n == 0` on `NULL` or dangling pointers).

Goal: kernel-checked Lean 4 proofs about a faithful translation of upstream `libarchive` (`master`),
covering its two highest-complexity archive format decoders:

1. **RAR5 format decoder (`libarchive/archive_read_support_format_rar5.c` + `archive_blake2sp_ref.c`)**
2. **7-Zip format decoder (`libarchive/archive_read_support_format_7zip.c` + `archive_ppmd7.c` / `archive_ppmd8.c`)**

The goal is full safety (no undefined behaviour, no out-of-bounds read/write, no use-after-free or
double-free across solid/multivolume resets, no memory leak, and termination) across every callback
sequence invoked by `archive_read_next_header`, `archive_read_data`, `archive_read_data_block`,
`archive_read_data_skip`, and `archive_read_free`, for the default scalar x86_64 Linux LP64 build.

## Source

- `libarchive/` is the upstream submodule (`https://github.com/libarchive/libarchive`). Never modify
  it. The verified source is `libarchive/` plus `patches/*.patch` applied in name order.
- A patch is allowed only for a confirmed upstream `libarchive` defect reachable through documented
  `archive_read_*` calls. Every patch must be minimal, listed in `patches/README.md`, and paired
  with a patch-revert case under `tests/patch-reverts/<name>/`.
- Top-down state and invariant models live in `LibarchiveF/Model/`.
- Statement-by-statement C translations live in `LibarchiveF/Libarchive/`.
- Specifications live in `LibarchiveF/Spec/{Common,Safety,Functional}/`, proofs in
  `LibarchiveF/Proof/`, heap-free math in `LibarchiveF/Math/`, and the C runtime model in
  `LibarchiveF/Runtime/`.
- `LibarchiveF/Results.lean` is the Lean-checked registry of proved and open goals.

## Key hazards to model and verify without shortcuts

1. **RAR5 solid & multivolume state reinitialisation (`rar5.c`).** Window buffers, Huffman tables,
   and queued post-decompression filters (`struct filter_info`) persist across solid entries and
   multivolume boundaries; prove zero UAF, zero double-free, and valid window masks across corrupted,
   encrypted, zero-length, or resized entries.
2. **RAR5 circular LZSS window & E8/E8E9/Delta/ARM bytecode filters (`rar5.c`).** Prove strict
   bounds for `window_mask` wrap-around copies and `block_start` / `block_length` / `channels`
   filter execution buffers.
3. **7-Zip `EncodedHeader` bootstrap & `Folder` / `BindPairs` DAG (`7zip.c`).** Prove acyclicity,
   stream-index bounds, BCJ2 4-stream arity, and exact allocation/unpack-size consistency across
   two-stage compressed headers and solid `SubStreamsInfo` ledgers.
4. **PPMd custom sub-allocator (`archive_ppmd7.c` / `archive_ppmd8.c`).** Prove memory safety of
   `SplitBlock`, `GlueFreeBlocks`, `AllocUnits`, and `SON`/`REF` offset pointers under arbitrary
   adversarial bitstreams.

## Rules

- Only `propext`, `Classical.choice` and `Quot.sound` are allowed. Never use `sorry`,
  `native_decide`, `bv_decide`, `axiom`, `implemented_by`, `extern`, `unsafe`, `partial` or
  `opaque` on `main` or `dev` (`sorry` is allowed only on `skeleton/*` branches).
- Every undefined behaviour reachable in C11 (including signed overflow, shift UB, `NULL + 0`, and
  cross-object pointer subtraction/comparison) raises `Fault.ub` in the model.
- Documentation lives under `docs/en/` and `docs/zh/` with mirrored paths and no language suffixes.
- Do not put machine names, addresses, user names, local paths or tool names in the repository or
  commit messages.
