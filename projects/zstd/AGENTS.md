# Working rules (`projects/zstd`)

Inherits all rules of [`../../AGENTS.md`](../../AGENTS.md), including the **Strict ISO C17 Undefined Behaviour Policy**
(no `NULL + 0`, no wild/dangling pointer `+ 0`, no `NULL - NULL`, no cross-object `virtualStart` pointer subtraction
or relational comparison, and no `memcpy`/`memset` with `n == 0` on `NULL` or dangling pointers).

- **Status:** Registered in `framework/projects.json`; strict ISO C17 runtime (`ZstdF.Runtime`)
  checked, statement-by-statement C translation and public safety proofs **Not done**.

## Scope (`ZstdF`)

Goal: kernel-checked Lean 4 proofs about a faithful, statement-by-statement translation of upstream
Meta Zstandard (`facebook/zstd`, pinned submodule `zstd/` + `patches/*.patch`), covering **both the
standalone C decoder AND the single-threaded C compressor**, dictionary loader/compiler, frame
inspector, and shared entropy/checksum units (`lib/zstd.h`, `lib/zstd_errors.h`, `lib/common/*.c`,
`lib/decompress/*.c`, and `lib/compress/*.c`).

Target configuration — portable scalar, single-threaded x86_64 Linux LP64 build:

```text
-DZSTD_DISABLE_ASM -DDYNAMIC_BMI2=0 -DZSTD_LEGACY_SUPPORT=0 -DZSTD_MULTITHREAD=0
-DXXH_NAMESPACE=ZSTD_ -DXXH_NO_XXH3 -DXXH_VECTOR=0
```

The goal is full safety (no ISO C17 undefined behaviour, no out-of-bounds read/write, no dangling
dictionary/prefix borrow, no memory leak, stated write frame, and termination) across every
documented public decompression **and** compression call sequence.

## Real-World Usage Paths & Function Priority

Audit of production callers shows that **both** decompression and compression paths of `libzstd`
handle attacker-influenced data at massive scale:
- **Node.js (`node:zlib` `src/node_zlib.cc`):** `ZSTD_createCCtx`/`ZSTD_createDCtx`,
  `ZSTD_CCtx_setParameter`/`ZSTD_DCtx_setParameter`, `ZSTD_compressStream2`,
  `ZSTD_decompressStream`, `ZSTD_CCtx_reset`/`ZSTD_DCtx_reset`, dictionary loading (`ZSTD_createCDict`,
  `ZSTD_createDDict`, `ZSTD_CCtx_refCDict`, `ZSTD_DCtx_refDDict`).
- **Python (`compression.zstd` in Python 3.14+, `python-zstandard`, `pyarrow`/Parquet):**
  `ZSTD_compressStream2`, `ZSTD_decompressStream`, `ZSTD_compress2`, `ZSTD_decompressDCtx`,
  `ZSTD_createCDict`/`ZSTD_createDDict`, `ZSTD_getFrameContentSize`, `ZSTD_compressBound`.
- **HTTP/CDN & Reverse Proxies (`Content-Encoding: zstd` in Chrome, Firefox, Nginx, Cloudflare, Envoy):**
  Streaming decode of untrusted server/client payloads (`ZSTD_decompressStream`) and streaming
  re-compression of dynamic HTTP bodies (`ZSTD_compressStream2` at levels 1–9, fast/dfast/greedy/lazy
  strategies, including flush directives `ZSTD_e_continue`, `ZSTD_e_flush`, `ZSTD_e_end`).
- **OS Packages, Databases & Containers (`pacman`, RPM, Debian, `libarchive`, RocksDB, Kafka, Docker/OCI, Linux kernel):**
  Both streaming (`ZSTD_compressStream2` / `ZSTD_decompressStream`) and block/one-shot paths
  (`ZSTD_compress`, `ZSTD_compress2`, `ZSTD_decompress`, `ZSTD_decompressDCtx`, `ZSTD_decompress_usingDDict`).

### Tier 1 (P0) — Decompression Path (Prove First)

1. **Streaming decompression:** `ZSTD_decompressStream`, `ZSTD_createDStream`, `ZSTD_freeDStream`,
   `ZSTD_initDStream`, `ZSTD_sizeof_DStream`, `ZSTD_DStreamInSize`, `ZSTD_DStreamOutSize`,
   `ZSTD_createDCtx`, `ZSTD_freeDCtx`, `ZSTD_sizeof_DCtx`, `ZSTD_DCtx_setParameter`,
   `ZSTD_dParam_getBounds`, `ZSTD_DCtx_reset` — across arbitrary input/output buffer splits,
   multi-frame & skippable frames, contiguous/ring-buffer/`extDict` modes, allocation failure, and
   calls after completion or error.
2. **One-shot & context decompression:** `ZSTD_decompress`, `ZSTD_decompressDCtx`,
   `ZSTD_decompress_usingDict`, `ZSTD_decompress_usingDDict`.
3. **Decompression dictionaries & prefixes (untrusted `0xEC30A437` formatted + raw):**
   `ZSTD_createDDict`, `ZSTD_freeDDict`, `ZSTD_sizeof_DDict`, `ZSTD_DCtx_loadDictionary`,
   `ZSTD_DCtx_refDDict`, `ZSTD_DCtx_refPrefix`, `ZSTD_getDictID_fromDict`,
   `ZSTD_getDictID_fromDDict`, `ZSTD_getDictID_fromFrame`.
4. **Frame inspection & query utilities:** `ZSTD_getFrameContentSize`, `ZSTD_getDecompressedSize`,
   `ZSTD_findFrameCompressedSize`, `ZSTD_decompressBound`, `ZSTD_isError`, `ZSTD_getErrorCode`,
   `ZSTD_getErrorName`, `ZSTD_versionNumber`, `ZSTD_versionString`, `ZSTD_isDeterministicBuild`.

### Tier 1 (P0) — Compression Path (Prove Immediately After / Alongside Decoder)

Compression paths process untrusted user uploads, dynamic web responses, and caller-provided tight
destination buffers (note historical `CVE-2019-11922` OOB write on tight output buffers, plus stale
dictionary/window pointer hazards on context reuse and reset):

1. **Streaming compression (primary Node.js/Python/HTTP path):** `ZSTD_createCCtx`, `ZSTD_freeCCtx`,
   `ZSTD_sizeof_CCtx`, `ZSTD_createCStream`, `ZSTD_freeCStream`, `ZSTD_initCStream`,
   `ZSTD_sizeof_CStream`, `ZSTD_CStreamInSize`, `ZSTD_CStreamOutSize`, `ZSTD_cParam_getBounds`,
   `ZSTD_CCtx_setParameter`, `ZSTD_CCtx_setPledgedSrcSize`, `ZSTD_CCtx_reset`,
   `ZSTD_compressStream`, `ZSTD_compressStream2` (all `ZSTD_EndDirective` modes: `ZSTD_e_continue`,
   `ZSTD_e_flush`, `ZSTD_e_end`), `ZSTD_flushStream`, `ZSTD_endStream`.
2. **One-shot & context compression:** `ZSTD_compress`, `ZSTD_compress2`, `ZSTD_compressCCtx`,
   `ZSTD_compress_usingDict`, `ZSTD_compress_usingCDict`, `ZSTD_compressBound`,
   `ZSTD_minCLevel`, `ZSTD_maxCLevel`, `ZSTD_defaultCLevel`.
3. **Compression dictionaries & prefixes:** `ZSTD_createCDict`, `ZSTD_freeCDict`,
   `ZSTD_sizeof_CDict`, `ZSTD_CCtx_loadDictionary`, `ZSTD_CCtx_refCDict`, `ZSTD_CCtx_refPrefix`.
   Covers all single-threaded scalar match-finding strategies (`fast`, `dfast`, `greedy`, `lazy`,
   `lazy2`, `btlazy2`, `btopt`, `btultra`, `btultra2`) and entropy encoders (`huf_compress.c`,
   `fse_compress.c`, `hist.c`).

### Tier 2 (P1) & Explicitly Not Planned

- **Tier 2 (optional follow-up):** Long-distance matching (`zstd_ldm.c`), `ZSTD_CCtx_setParametersUsingCCtxParams`
  / `ZSTD_createCCtxParams` / `ZSTD_freeCCtxParams`, and `ZSTD_CCtxParams_*`.
- **Not planned:** Multi-threaded job pool (`lib/compress/zstdmt_compress.c`, `lib/common/pool.c`,
  `lib/common/threading.c`), dictionary trainer (`lib/dictBuilder/`), legacy v0.1–v0.7 decoders
  (`lib/legacy/`), handwritten amd64 assembly (`huf_decompress_amd64.S`), CLI (`programs/`),
  experimental `ZSTD_STATIC_LINKING_ONLY` APIs outside those required by public `zstd.h`, and full
  RFC 8878 functional round-trip equivalence beyond invariants needed for safety.

## Verified Translation Units

- **Shared (`lib/common/`):** `debug.c`, `entropy_common.c`, `error_private.c`, `fse_decompress.c`,
  `xxhash.c` (`XXH64` scalar path), `zstd_common.c` (plus `lib/zstd.h`, `lib/zstd_errors.h`).
- **Decoder (`lib/decompress/`):** `huf_decompress.c`, `zstd_ddict.c`, `zstd_decompress.c`,
  `zstd_decompress_block.c`.
- **Compressor (`lib/compress/`):** `hist.c`, `fse_compress.c`, `huf_compress.c`, `zstd_compress.c`,
  `zstd_compress_literals.c`, `zstd_compress_sequences.c`, `zstd_compress_superblock.c`,
  `zstd_fast.c`, `zstd_double_fast.c`, `zstd_lazy.c`, `zstd_opt.c`, `zstd_preSplit.c`
  (and `zstd_ldm.c` in Tier 2).

Translations mirror the C layout (`zstd/lib/<dir>/X.c` -> `ZstdF/Zstd/<dir>/X.c.lean`, `.h` -> `.h.lean`).
Each function keeps its C name and starts its docstring with the C signature.

## Key Zstandard Hazards to Model and Verify Without Shortcuts

1. **Fast sequence execution and `WILDCOPY_OVERLENGTH` (`zstd_decompress_block.c`).**
   `ZSTD_wildcopy` intentionally copies in 8- or 16-byte chunks up to `WILDCOPY_OVERLENGTH` (32
   bytes) past the logical end of a literal or match copy, relying on fast-loop guards
   (`oend_w = oend - WILDCOPY_OVERLENGTH`) before falling back to `ZSTD_execSequenceEnd` /
   `ZSTD_safecopy`. In `SplitLitBuffer` mode, decoded literals temporarily reside at the tail of the
   destination buffer while sequences overwrite the front. Prove from first principles that every
   wildcopy stays strictly within the writable destination block and never clobbers unread split
   literals.
2. **Cross-object `virtualStart` and `extDict` pointer arithmetic (`zstd_decompress.c`,
   `zstd_decompress_block.c`, `zstd_compress.c`, `zstd_fast.c`, `zstd_lazy.c`, `zstd_opt.c`).**
   Both decoder and compressor compute `virtualStart = prefixStart - extDictSize` and
   `ip - virtualStart` across distinct heap objects in `extDict` / streaming window modes. Do **not**
   weaken `ZstdF/Runtime/Ptr.lean`: confirm every ISO C17 UB site on real C (UBSan + ASan
   `detect_invalid_pointer_pair=2`), document in `docs/{en,zh}/findings.md`, and isolate minimal
   `uintptr_t`/offset-arithmetic fixes in `patches/` with `tests/patch-reverts/` ablations.
3. **Reverse bitstreams (`BIT_DStream_t` / `BIT_CStream_t`), 4-stream Huffman, and FSE workspace
   aliasing (`huf_decompress.c`, `huf_compress.c`, `fse_decompress.c`, `fse_compress.c`,
   `entropy_common.c`).**
   Model exact buffer/workspace layouts (including `LLTable`/`OFTable`/`MLTable` flat `U32` aliasing
   in `ZSTD_loadDEntropy`, 6-byte 4-stream jump tables, and `BIT_flushBitsFast` tight-destination
   bounds in `huf_compress.c` / `fse_compress.c`).
4. **Compressor window-index wraparound (`ZSTD_window_t`) and tight-buffer fallback (`zstd_compress.c`,
   `zstd_fast.c`, `zstd_double_fast.c`, `zstd_lazy.c`, `zstd_opt.c`).**
   Prove hash/chain/binary-tree table indices stay in bounds across window overflow corrections
   (`ZSTD_window_correctOverflow`), `CDict` prefix/extDict switches, `ZSTD_CCtx_reset` calls after
   errors, and destination buffers strictly smaller than `ZSTD_compressBound(srcSize)` (the exact
   failure class of `CVE-2019-11922`).
5. **Untrusted formatted dictionaries (`0xEC30A437`) and borrowed references (`ZSTD_DCtx_refDDict`,
   `ZSTD_DCtx_refPrefix`, `ZSTD_CCtx_refCDict`, `ZSTD_CCtx_refPrefix`).**
   Prove full parser safety for untrusted formatted dictionaries (including `rep[0..2]` validation)
   and track caller-buffer liveness explicitly in the sequence invariant across streaming calls.

## Proof Workflow & Local Commands

- Only `propext`, `Classical.choice`, and `Quot.sound` are allowed (`sorry` permitted on
  `skeleton/*` branches only). Every safety goal pairs with a concrete non-vacuity witness theorem.
- Any narrower precondition (e.g. pairwise disjoint caller buffers, default allocator) is explicit
  in the goal and listed in `docs/{en,zh}/deviations.md`.
- Build with at most `-j 4` under a 16 GB RAM limit.

From repository root:

```bash
lake --dir projects/zstd build --wfail ZstdF ZstdF.Results
python3 framework/check_project.py zstd --skip-build
```
