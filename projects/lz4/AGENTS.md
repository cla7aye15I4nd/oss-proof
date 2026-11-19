# Working rules (`projects/lz4`)

Inherits all rules of the repository root [`../../AGENTS.md`](../../AGENTS.md), including the
**Strict ISO C17 Undefined Behaviour Policy** (`framework/check_runtime_ub.py` enforces this
mechanically):

- **No wild, uninitialised, freed/dangling, or `NULL` pointer `+ 0` (`p + 0`, `p - 0`, `&p[0]`)** —
  `Ptr.add` MUST check non-null, live allocation, `off <= a.size`, and `0 <= off + k <= a.size`
  even when `k = 0` (start from `framework/lean/StrictPtr.lean`; NEVER copy legacy shortcuts).
- **No `NULL - NULL` and no cross-object pointer subtraction or relational comparison** (`p - q`,
  `<`, `<=`, `>`, `>=` require the same live array object).
- **No out-of-bounds pointer formation**, even without dereference (`lowPrefix - dictSize` across
  distinct heap objects is `Fault.ub`).
- **No `memcpy` / `memmove` / `memset` / `memcmp` with `n == 0` on `NULL` or dangling pointers**.
- **Every struct pointer field must be written before it is read** (never rely on fresh model
  pointers defaulting to `.null` to excuse an uninitialised C pointer read).
- **Never argue "benign UB"**. When upstream C reaches ISO C17 UB through documented API calls,
  confirm it, record it in `docs/{en,zh}/findings.md`, and propose a minimal upstream C patch in
  `patches/`.

- **Status:** Upstream submodule `lz4/` pinned (not yet registered in `framework/projects.json`; Lean
  runtime bootstrap, C translation, and safety proofs **Not done**).

## Scope (`Lz4F`)

- **Upstream source:** `lz4/` pinned submodule (`https://github.com/lz4/lz4`) + `patches/*.patch`
  in name order.
- **Target configuration:** portable scalar x86_64 Linux LP64 static build
  (`-DLZ4_FORCE_MEMORY_ACCESS=0 -DXXH_NO_XXH3 -DXXH_VECTOR=0`, default `malloc`/`free` allocator,
  ~5k LOC pure C — one of the highest security-ROI targets in `oss-proof`).
- **Verification goal:** full safety (no ISO C17 undefined behaviour, no integer wraparound into
  negative `memmove`/`memcpy` lengths, no wildcopy overrun, no cross-object dictionary pointer UB,
  no memory leak, stated write frame, and termination) across **both decompression AND compression**
  block, streaming-ring, high-compression (HC), and frame (`LZ4F_*`) APIs.

## Real-World Usage Paths & Function Priority

LZ4 is embedded directly into latency-critical and untrusted-input systems across infrastructure,
databases, and language bindings:
- **Databases, Analytics & Messaging (Apache Kafka, Apache Parquet / Arrow, ClickHouse, Redis,
  RocksDB, ZFS, Linux kernel `lib/lz4`):** High-frequency raw block and frame decompression &
  compression (`LZ4_decompress_safe`, `LZ4_decompress_safe_partial`, `LZ4_compress_default`,
  `LZ4_compress_fast`, `LZ4_compress_HC`, `LZ4F_decompress`, `LZ4F_compressFrame`).
- **Python (`python-lz4` `lz4.block` / `lz4.frame`, `pyarrow`) & Node.js (`lz4`):** User-supplied
  untrusted network/storage payloads hit `LZ4_decompress_safe`, `LZ4_decompress_safe_usingDict`,
  `LZ4F_decompress`, and `LZ4_compress_default` / `LZ4_compress_HC` / `LZ4F_compressUpdate`.
- **Archive & Container Tools (`libarchive`, SquashFS, initramfs, Chromium/Android):** Streaming
  frame decode (`LZ4F_createDecompressionContext`, `LZ4F_getFrameInfo`, `LZ4F_decompress`) and
  frame encode (`LZ4F_createCompressionContext`, `LZ4F_compressBegin`, `LZ4F_compressUpdate`,
  `LZ4F_compressEnd`).
- **Critical CVE Anchor — CVE-2021-3520 (CVSS 9.8 / Critical):** Integer overflow in `LZ4_decompress_*`
  / block size arithmetic caused a negative length to be passed to `memmove`, triggering heap memory
  corruption on crafted inputs. Earlier `CVE-2019-17543` hit a heap buffer overflow in
  `LZ4_write32` during compression/decompression edge cases.

### Tier 1 (P0) — Block & Frame Decompression + Standard Compression (Prove First)

1. **Block decompression (`lib/lz4.h`, `lib/lz4.c`):** `LZ4_decompress_safe`,
   `LZ4_decompress_safe_partial`, `LZ4_decompress_safe_usingDict`,
   `LZ4_decompress_safe_continue`, `LZ4_createStreamDecode`, `LZ4_freeStreamDecode`,
   `LZ4_setStreamDecode`.
2. **Block compression (`lib/lz4.h`, `lib/lz4.c`):** `LZ4_compressBound`, `LZ4_compress_default`,
   `LZ4_compress_fast`, `LZ4_compress_fast_extState`, `LZ4_compress_destSize`,
   `LZ4_createStream`, `LZ4_freeStream`, `LZ4_resetStream_fast`, `LZ4_loadDict`,
   `LZ4_compress_fast_continue`, `LZ4_saveDict`.
3. **LZ4 Frame API (`lib/lz4frame.h`, `lib/lz4frame.c`, `lib/xxhash.c`):**
   - Decompression: `LZ4F_createDecompressionContext`, `LZ4F_freeDecompressionContext`,
     `LZ4F_getFrameInfo`, `LZ4F_decompress`, `LZ4F_resetDecompressionContext`;
   - Compression: `LZ4F_compressFrameBound`, `LZ4F_compressFrame`, `LZ4F_createCompressionContext`,
     `LZ4F_freeCompressionContext`, `LZ4F_compressBound`, `LZ4F_compressBegin`,
     `LZ4F_compressUpdate`, `LZ4F_flush`, `LZ4F_compressEnd`;
   - Error/version helpers: `LZ4F_isError`, `LZ4F_getErrorName`, `LZ4_versionNumber`,
     `LZ4_versionString`.

### Tier 2 (P1) — High-Compression (HC) Path

- **HC compressor (`lib/lz4hc.h`, `lib/lz4hc.c`):** `LZ4_compress_HC`, `LZ4_compress_HC_extStateHC`,
  `LZ4_compress_HC_destSize`, `LZ4_createStreamHC`, `LZ4_freeStreamHC`, `LZ4_resetStreamHC_fast`,
  `LZ4_loadDictHC`, `LZ4_compress_HC_continue`, `LZ4_saveDictHC`, `LZ4_attach_HC_dictionary`.

### Explicitly Not Planned

- Deprecated unsafe functions explicitly marked insecure upstream (`LZ4_decompress_fast`,
  `LZ4_decompress_fast_continue`, `LZ4_decompress_fast_usingDict` — lack input-buffer end checks
  by design).
- `LZ4FILE` (`lib/lz4file.c`) stdio wrapper, CLI tool (`programs/`), and functional compression
  round-trip proofs beyond invariants needed for safety.

## Verified Translation Units

- `lib/lz4.h`, `lib/lz4.c`
- `lib/lz4hc.h`, `lib/lz4hc.c`
- `lib/lz4frame.h`, `lib/lz4frame.c`
- `lib/xxhash.h`, `lib/xxhash.c` (`XXH32` path used by LZ4 frame checksums)

## Library-Specific Verification Hazards (No Shortcuts)

1. **Signed `int` size overflow & negative-size `memmove` (`lz4.c` — `CVE-2021-3520`).**
   `LZ4_decompress_generic` takes `int compressedSize` and `int dstCapacity` and performs `op + length`
   and `ip + length` arithmetic over variable-length `read_variable_length` extensions. Prove that
   signed overflow, wraparound to negative values, and negative `memmove` sizes are impossible for
   every possible `int` input including `<= 0` and `INT_MAX`.
2. **Wildcopy overruns & overlapping match copies (`LZ4_wildCopy8`, `LZ4_memcpy_using_offset`).**
   Fast loops intentionally overwrite up to `WILDCOPYLENGTH` (8/16 bytes) past logical match/literal
   ends, guarded by `MFLIMIT` (12) and `LASTLITERALS` (5) margins. Prove every fast-path and
   tail-path write stays strictly inside `[dst, dst + dstCapacity]`, including overlapping RLE
   matches (`offset < 8`).
3. **External-dictionary (`extDict`) pointer arithmetic (`lz4.c`, `lz4hc.c`).**
   Streaming/dictionary decompression and compression reference both `dst` and `dictStart..dictEnd`
   (separate heap allocations). Under strict ISO C17, forming `dictEnd - (op - lowPrefix)` or
   comparing pointers across distinct objects is `Fault.ub`; audit every site on real C with ASan
   `detect_invalid_pointer_pair=2` and patch via offset arithmetic if needed.
4. **LZ4 Frame state machine & block/content checksums (`lz4frame.c`).**
   Prove safe resumption across arbitrary 1-byte input/output splits, skippable frames, linked vs.
   independent blocks, block/content `XXH32` validation, and re-entry after error or
   `LZ4F_resetDecompressionContext`.
5. **HC hash-chain & optimal parser bounds (`lz4hc.c`).**
   Prove 16-bit cyclic `chainTable` offsets, `base`/`dictBase` index adjustments, and
   `LZ4HC_compress_optimal` price-table indices never access out of bounds under adversarial inputs
   or repeated `LZ4_loadDictHC` / `LZ4_compress_HC_continue` calls.

## Bootstrap & Local Commands

When onboarding into `framework/projects.json`: copy `lean-toolchain`, start
`Lz4F/Runtime/Ptr.lean` from `framework/lean/StrictPtr.lean`, wire `Lz4F/Results.lean` and
`project.json`, then run:

```bash
lake --dir projects/lz4 build --wfail Lz4F Lz4F.Results
python3 framework/check_project.py lz4 --skip-build
```
