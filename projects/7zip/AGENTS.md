# Working rules (`projects/7zip`)

Inherits all rules of [`../../AGENTS.md`](../../AGENTS.md), including the **Strict ISO C17 Undefined Behaviour Policy**
(no `NULL + 0`, no wild/dangling pointer `+ 0`, no `NULL - NULL`, no cross-object pointer subtraction or comparison,
and no `memcpy`/`memset` with `n == 0` on `NULL` or dangling pointers).

- **Status:** Registered in `framework/projects.json`; top-down state/arena models (`SevenZipF.Model`)
  and strict ISO C17 runtime (`SevenZipF.Runtime`) checked, statement-by-statement C translation and
  end-to-end public safety proofs **Not done**.

## Scope (`SevenZipF`)

Goal: kernel-checked Lean 4 proofs about a faithful, statement-by-statement translation of the
official `7-Zip` pure-C SDK (`C/` directory of upstream `ip7z/7zip`, pinned submodule `7zip/` +
`patches/*.patch`), covering **both decompression/extraction AND standalone LZMA/LZMA2/BCJ2/PPMd7
compression paths** for the portable scalar, single-threaded x86_64 Linux LP64 build
(`-DZ7_ST -D_7ZIP_ST -DZ7_PPMD_SUPPORT`, no x86/ARM assembly or SIMD intrinsics).

The goal is full safety (no ISO C17 undefined behaviour, no out-of-bounds read/write, no custom
sub-allocator corruption, no use-after-free or leak across cached solid-folder extractions or
encoder resets, stated write frame, and termination) across every documented C SDK entry point in
scope.

## Real-World Usage Paths & Function Priority

The `7-Zip` pure-C SDK (`C/`) is widely embedded verbatim (often statically vendored with delayed
patching) into high-exposure software:
- **Firmware, Bootloaders & OS Images (UEFI/EDK2, U-Boot, Linux kernel `lib/lzma`, SquashFS, Android OTA):**
  `LzmaDec_DecodeToBuf`, `LzmaDec_DecodeToDic`, `Lzma2Dec_DecodeToBuf`, `LzmaUncompress`,
  `SzArEx_Open` / `SzArEx_Extract`, plus firmware-image creation via `LzmaEnc_Encode` / `Lzma2Enc_Encode2`.
- **Antivirus, Malware Sandboxes, Email Gateways & Security Scanners:** Continuously unpack
  adversarial `.7z` archives (including solid multi-coder folders, BCJ2 x86 executable streams, and
  PPMd7 text streams) using `SzArEx_Open`, `SzArEx_Extract`, `SzArEx_Free`, `Bcj2Dec_Decode`, and
  `Ppmd7_DecodeSymbol`.
- **Installers, Package Tools & Language Bindings (NSIS, Inno Setup, Windows/macOS extractors,
  `py7zr` / embedded SDK wrappers):** Both `.7z` extraction (`7zArcIn.c`, `7zDec.c`) and LZMA/LZMA2
  compression (`LzmaEnc.c`, `Lzma2Enc.c`, `LzFind.c`).

### Tier 1 (P0) — Decompression & Archive Extraction (Prove First)

1. **`.7z` archive parser & solid-folder extractor (`C/7zArcIn.c`, `C/7zDec.c`, `C/7zBuf.c`,
   `C/7zCrc.c`, `C/7zStream.c`):** `SzArEx_Init`, `SzArEx_Open`, `SzArEx_Extract`, `SzArEx_Free`,
   `SzArEx_GetFileNameUtf16`, `SzArEx_GetFolderFullPackSize`, `SzAr_DecodeFolder`.
2. **LZMA & LZMA2 decoders (`C/LzmaDec.c`, `C/Lzma2Dec.c`, `C/LzmaLib.c`):** `LzmaDec_Construct`,
   `LzmaDec_Allocate`, `LzmaDec_Init`, `LzmaDec_DecodeToBuf`, `LzmaDec_DecodeToDic`, `LzmaDec_Free`,
   `Lzma2Dec_Allocate`, `Lzma2Dec_Init`, `Lzma2Dec_DecodeToBuf`, `Lzma2Dec_DecodeToDic`,
   `LzmaUncompress`.
3. **BCJ2 & branch/delta executable filters (`C/Bcj2.c`, `C/Bra.c`, `C/Bra86.c`, `C/Delta.c`):**
   `Bcj2Dec_Init`, `Bcj2Dec_Decode`, `z7_BranchConv_*`, `Delta_Decode`.
4. **PPMd7 decoder & custom arena sub-allocator (`C/Ppmd7.c`, `C/Ppmd7Dec.c`):** `Ppmd7_Construct`,
   `Ppmd7_Alloc`, `Ppmd7_Free`, `Ppmd7_Init`, `Ppmd7z_RangeDec_Init`, `Ppmd7z_DecodeSymbol`.

### Tier 2 (P1) — Compression Path (Single-Threaded Pure-C Encoders)

Server-side archiving, firmware packaging, and installer builders compress untrusted or user-supplied
payloads with the SDK's match finders and range encoders:

1. **LZMA & LZMA2 encoders (`C/LzmaEnc.c`, `C/Lzma2Enc.c`, `C/LzFind.c`, `C/LzmaLib.c`):**
   `LzmaEnc_Create`, `LzmaEnc_Destroy`, `LzmaEnc_SetProps`, `LzmaEnc_WriteProperties`,
   `LzmaEnc_Encode`, `LzmaEnc_MemEncode`, `LzmaCompress`, `Lzma2Enc_Create`, `Lzma2Enc_Destroy`,
   `Lzma2Enc_SetProps`, `Lzma2Enc_Encode2`.
2. **BCJ2 & PPMd7 encoders (`C/Bcj2Enc.c`, `C/Ppmd7Enc.c`, `C/Delta.c`):** `Bcj2Enc_Init`,
   `Bcj2Enc_Encode`, `Ppmd7z_Init_RangeEnc`, `Ppmd7z_EncodeSymbol`, `Delta_Encode`.

### Explicitly Not Planned

- The full C++ 7-Zip application (`CPP/` directory, GUI, multi-format C++ handlers like RAR/NTFS/UDF/Zstd).
- Multi-threaded match finder (`C/LzFindMt.c`, `C/MtCoder.c`, `C/MtDec.c`, `C/Threads.c`),
  x86/ARM assembly (`Asm/`), hardware AES/SHA/CRC intrinsics (`C/AesOpt.c`, `C/Sha256Opt.c`,
  `C/7zCrcOpt.c`), and full compression-ratio or decompression-equivalence proofs beyond safety.

## Source & Layout

- `7zip/` — pinned upstream submodule (`https://github.com/ip7z/7zip`). Never modify it. Verified
  source is `7zip/` plus `patches/*.patch` applied in name order (with ablation tests under
  `tests/patch-reverts/<name>/`).
- `SevenZipF/Model/` — top-down state and invariant models.
- `SevenZipF/SevenZip/` — statement-by-statement C translations mirroring `C/`.
- `SevenZipF/Spec/{Common,Safety,Functional}/`, `SevenZipF/Proof/`, `SevenZipF/Math/`,
  `SevenZipF/Runtime/`, `SevenZipF/Results.lean`.

## Key Hazards to Model and Verify Without Shortcuts

1. **Two-stage `EncodedHeader` & `CSzFolder` / `BindPairs` DAG (`7zArcIn.c`, `7zDec.c`).**
   Prove acyclicity, port-index bounds, `PackStreams` / `UnpackSizes` 64-bit integer overflow safety,
   and cached solid-block reuse (`blockIndex` / `outBuffer` across repeated `SzArEx_Extract` calls,
   including after errors and zero-size entries).
2. **BCJ2 4-stream decoder & encoder (`Bcj2.c`, `Bcj2Enc.c`).**
   Prove strict cursor bounds across all four simultaneous input/output streams (`bufs[0..3]`..
   `lims[0..3]`) and destination assembly (`dest`..`destLim`), plus range-coder renormalization.
3. **PPMd7 custom heap sub-allocator (`Ppmd7.c`, `Ppmd7Dec.c`, `Ppmd7Enc.c`).**
   Prove arena partition invariants (`Base <= Text <= UnitsStart <= LoUnit <= HiUnit`), free-list
   integrity across `SplitBlock` and `GlueFreeBlocks`, and 32-bit `CPpmd_Void_Ref` offset
   dereferences across `RestartModel` and `RestoreModelRare` under arbitrary bitstreams.
4. **LZMA / LZMA2 dictionary wrap-around & lookahead margins (`LzmaDec.c`, `Lzma2Dec.c`, `LzmaEnc.c`,
   `LzFind.c`).**
   Prove circular dictionary indexing, `lc/lp/pb` probability-table allocation bounds, fast-loop
   lookahead margins (`LZMA_REQUIRED_INPUT_MAX`), and `MatchFinder` hash/son-tree bounds +
   `MatchFinder_Normalize3` cyclic-buffer wrap-around in `LzFind.c`.

## Proof Workflow & Local Commands

- Only `propext`, `Classical.choice`, and `Quot.sound` are allowed (`sorry` permitted on
  `skeleton/*` branches only). Every safety goal pairs with a non-vacuity witness theorem.
- Any narrower precondition (e.g. default `ISzAlloc`, disjoint caller buffers) is stated explicitly
  and listed in `docs/{en,zh}/deviations.md`. Build with at most `-j 4`.

From repository root:

```bash
lake --dir projects/7zip build --wfail SevenZipF SevenZipF.Results
python3 framework/check_project.py 7zip --skip-build
```
