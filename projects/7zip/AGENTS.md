# Working rules (`projects/7zip`)

Inherits all rules of [`../../AGENTS.md`](../../AGENTS.md), including the **Strict ISO C17 Undefined Behaviour Policy**
(no `NULL + 0`, no wild/dangling pointer `+ 0`, no `NULL - NULL`, no cross-object pointer subtraction or comparison,
and no `memcpy`/`memset` with `n == 0` on `NULL` or dangling pointers).

Goal: kernel-checked Lean 4 proofs about a faithful translation of the official `7-Zip` pure-C SDK
(`C/` directory of upstream `ip7z/7zip`), covering the `.7z` archive parser, folder decoder pipeline,
executable filters, LZMA/LZMA2 decoders, and PPMd7 decoder with its custom memory sub-allocator:

- `C/7zArcIn.c`, `C/7zDec.c`, `C/7zBuf.c`, `C/7zCrc.c`, `C/7zStream.c` (`C/7z.h`)
- `C/Bcj2.c`, `C/Bra.c`, `C/Bra86.c`, `C/Delta.c`
- `C/Ppmd7.c`, `C/Ppmd7Dec.c` (`C/Ppmd7.h`, `C/Ppmd.h`)
- `C/LzmaDec.c`, `C/Lzma2Dec.c` (`C/LzmaDec.h`, `C/Lzma2Dec.h`)

The goal is full safety (no undefined behaviour, no out-of-bounds read/write, no custom-allocator
corruption, no use-after-free or leak across cached solid-folder extractions, and termination)
across every documented C SDK entry point (`SzArEx_Open`, `SzArEx_Extract`, `SzArEx_Free`,
`Bcj2Dec_Decode`, `Ppmd7_Construct` / `Ppmd7_Alloc` / `Ppmd7_Init` / `Ppmd7_DecodeSymbol`,
`LzmaDec_DecodeToBuf`, `Lzma2Dec_DecodeToBuf`) for the portable scalar x86_64 Linux LP64 build.

## Source

- `7zip/` is the upstream submodule (`https://github.com/ip7z/7zip`). Never modify it. The verified
  source is `7zip/` plus `patches/*.patch` applied in name order.
- A patch is allowed only for a confirmed upstream defect or C11 undefined behaviour reachable
  through documented C SDK calls, paired with an ablation test under `tests/patch-reverts/<name>/`.
- Top-down state and invariant models live in `SevenZipF/Model/`.
- Statement-by-statement C translations live in `SevenZipF/SevenZip/`.
- Specifications live in `SevenZipF/Spec/{Common,Safety,Functional}/`, proofs in `SevenZipF/Proof/`,
  heap-free math in `SevenZipF/Math/`, and the C runtime model in `SevenZipF/Runtime/`.
- `SevenZipF/Results.lean` is the Lean-checked registry of proved and open goals.

## Key hazards to model and verify without shortcuts

1. **Two-stage `EncodedHeader` & `CSzFolder` / `BindPairs` DAG (`7zArcIn.c`, `7zDec.c`).** Prove
   acyclicity, port-index bounds, `PackStreams` / `UnpackSizes` array bounds, and cached solid-block
   reuse (`blockIndex` / `outBuffer` across repeated `SzArEx_Extract` calls, including after errors).
2. **BCJ2 4-stream decoder (`Bcj2.c`).** Prove strict cursor bounds across all four simultaneous
   input streams (`bufs[0..3]`..`lims[0..3]`) and destination assembly (`dest`..`destLim`).
3. **PPMd7 custom heap sub-allocator (`Ppmd7.c`, `Ppmd7Dec.c`).** Prove arena partition invariants
   (`Base <= Text <= UnitsStart <= LoUnit <= HiUnit`), free-list integrity across `SplitBlock` and
   `GlueFreeBlocks`, and 32-bit `CPpmd_Void_Ref` offset dereferences across `RestartModel` and
   `RestoreModelRare`.
4. **LZMA / LZMA2 chunk state resets (`LzmaDec.c`, `Lzma2Dec.c`).** Prove dictionary wrap-around,
   `lc/lp/pb` property-table bounds, and lookahead fast-loop margins (`LZMA_REQUIRED_INPUT_MAX`).

## Rules

- Only `propext`, `Classical.choice` and `Quot.sound` are allowed. Never use `sorry`,
  `native_decide`, `bv_decide`, `axiom`, `implemented_by`, `extern`, `unsafe`, `partial` or
  `opaque` on `main` or `dev` (`sorry` is allowed only on `skeleton/*` branches).
- Every undefined behaviour reachable in C11 raises `Fault.ub` in the model.
- Documentation lives under `docs/en/` and `docs/zh/` with mirrored paths and no language suffixes.
- Do not put machine names, addresses, user names, local paths or tool names in the repository or
  commit messages.
