# Working rules (`projects/xz`)

Inherits all rules of the repository root [`../../AGENTS.md`](../../AGENTS.md), including the
**Strict ISO C17 Undefined Behaviour Policy** (`framework/check_runtime_ub.py` enforces this
mechanically):

- **No wild, uninitialised, freed/dangling, or `NULL` pointer `+ 0` (`p + 0`, `p - 0`, `&p[0]`)** —
  `Ptr.add` MUST check non-null, live allocation, `off <= a.size`, and `0 <= off + k <= a.size`
  even when `k = 0` (start from `framework/lean/StrictPtr.lean`; NEVER copy legacy shortcuts).
- **No `NULL - NULL` and no cross-object pointer subtraction or relational comparison** (`p - q`,
  `<`, `<=`, `>`, `>=` require the same live array object).
- **No out-of-bounds pointer formation**, even without dereference.
- **No `memcpy` / `memmove` / `memset` / `memcmp` with `n == 0` on `NULL` or dangling pointers**.
- **Every struct pointer field must be written before it is read**.
- **Never argue "benign UB"**. Report confirmed ISO C17 UB in `docs/{en,zh}/findings.md` with
  minimal upstream patches in `patches/`.

- **Status:** Upstream submodule `xz/` pinned (not yet registered in `framework/projects.json`; Lean
  runtime bootstrap, C translation, and safety proofs **Not done**).

## Scope (`XzF`)

- **Upstream source:** `xz/` pinned git submodule directly from upstream git
  (`https://github.com/tukaani-project/xz` — **strictly git source, never release tarballs**,
  reflecting supply-chain lessons of `CVE-2024-3094`) + `patches/*.patch` in name order.
- **Target configuration:** portable scalar, single-threaded x86_64 Linux LP64 build of `liblzma`
  (`--disable-threads --disable-assembler --disable-clmul-crc --disable-arm64-crc32 --disable-symbol-versions`,
  default allocator, no IFUNC hooks).
- **Verification goal:** full safety (no ISO C17 undefined behaviour, no out-of-bounds read/write,
  no use-after-free on error unwinding, no memory leak, stated write frame, and termination) across
  **both single-threaded decompression AND compression** public `liblzma` entry points in
  `src/liblzma/api/lzma/*.h`.

## Real-World Usage Paths & Function Priority

`liblzma` is critical foundational infrastructure embedded across Python, Linux distributions, and
archive tools:
- **Python standard library (`Modules/_lzmamodule.c` -> `lzma.LZMACompressor`, `lzma.LZMADecompressor`,
  `lzma.compress`, `lzma.decompress`, `lzma.open`):** Directly invokes `lzma_stream_decoder`,
  `lzma_auto_decoder`, `lzma_alone_decoder`, `lzma_raw_decoder`, `lzma_easy_encoder`,
  `lzma_stream_encoder`, `lzma_alone_encoder`, `lzma_raw_encoder`, `lzma_code`, `lzma_end`,
  `lzma_lzma_preset`, and `lzma_memlimit_set`.
- **Package Managers & OS Core (`dpkg`/`.deb`, `rpm`, `pacman`, `tar -J`, `libarchive`, `systemd`,
  Linux kernel module decompression, `initramfs`):** Unpacks untrusted/signed `.tar.xz` and `.xz`
  streams (`lzma_stream_decoder`, `lzma_auto_decoder`, `lzma_stream_buffer_decode`,
  `lzma_index_decoder`) and builds packages (`lzma_easy_encoder`, `lzma_stream_encoder`).
- **Security Anchors:** `CVE-2025-31115` (premature free / use-after-free in threaded `.xz` decoder
  on invalid input), `CVE-2026-34743` (memory-tracking edge case in `liblzma`), and the historic
  `CVE-2024-3094` supply-chain backdoor (reinforcing why verifiable, clean-source, IFUNC-free
  builds of `liblzma` matter).

### Tier 1 (P0) — Single-Threaded Decompression & Stream Infrastructure (Prove First)

1. **Core streaming lifecycle & codec driver (`common/common.c`, `common/stream_decoder.c`,
   `common/auto_decoder.c`, `common/alone_decoder.c`, `common/block_decoder.c`):**
   `lzma_code` (all `lzma_action`: `LZMA_RUN`, `LZMA_SYNC_FLUSH`, `LZMA_FULL_FLUSH`,
   `LZMA_FULL_BARRIER`, `LZMA_FINISH`), `lzma_end`, `lzma_stream_decoder`, `lzma_auto_decoder`,
   `lzma_alone_decoder`, `lzma_raw_decoder`, `lzma_block_decoder`, `lzma_stream_buffer_decode`.
2. **Container headers, VLI, Index & filter chain (`common/stream_header_decoder.c`,
   `common/stream_footer_decoder.c`, `common/block_header_decoder.c`, `common/vli_decoder.c`,
   `common/index.c`, `common/index_decoder.c`, `common/index_hash.c`, `common/filter_decoder.c`,
   `common/filter_flags_decoder.c`):** `lzma_stream_header_decode`, `lzma_stream_footer_decode`,
   `lzma_block_header_decode`, `lzma_index_decoder`, `lzma_index_buffer_decode`, `lzma_index_end`,
   `lzma_vli_decode`, `lzma_memusage`, `lzma_memlimit_get`, `lzma_memlimit_set`.
3. **LZMA1 / LZMA2 / LZ ring-buffer decoder & BCJ / Delta filters (`lzma/lzma_decoder.c`,
   `lzma/lzma2_decoder.c`, `lz/lz_decoder.c`, `delta/delta_decoder.c`, `simple/simple_coder.c`,
   `simple/simple_decoder.c`, `simple/x86.c`, `simple/arm64.c`, `simple/arm.c`, `simple/riscv.c`):**
   Full filter chain execution under arbitrary chunk boundaries.
4. **Integrity checks (`check/check.c`, `check/crc32_fast.c`, `check/crc64_fast.c`,
   `check/sha256.c`):** `lzma_crc32`, `lzma_crc64`, `lzma_check_is_supported`, `lzma_check_size`.

### Tier 1 (P0) — Single-Threaded Compression Path

Directly invoked by Python `lzma.compress` / `LZMACompressor`, `tar -cJ`, `libarchive`, and package
builders over untrusted or arbitrary user data:

1. **Streaming & one-shot encoders (`common/stream_encoder.c`, `common/easy_encoder.c`,
   `common/easy_preset.c`, `common/alone_encoder.c`, `common/block_encoder.c`,
   `common/stream_buffer_encoder.c`, `common/easy_buffer_encoder.c`, `common/filter_encoder.c`,
   `common/filter_flags_encoder.c`, `common/block_header_encoder.c`, `common/stream_header_encoder.c`,
   `common/stream_footer_encoder.c`, `common/index_encoder.c`, `common/vli_encoder.c`):**
   `lzma_easy_encoder`, `lzma_stream_encoder`, `lzma_alone_encoder`, `lzma_raw_encoder`,
   `lzma_block_encoder`, `lzma_easy_buffer_encode`, `lzma_stream_buffer_encode`,
   `lzma_stream_buffer_bound`, `lzma_lzma_preset`.
2. **LZMA1 / LZMA2 encoder & match finders (`lzma/lzma_encoder.c`, `lzma/lzma2_encoder.c`,
   `lzma/lzma_encoder_optimum_fast.c`, `lzma/lzma_encoder_optimum_normal.c`,
   `lz/lz_encoder.c`, `lz/lz_encoder_mf.c`, `delta/delta_encoder.c`, `simple/simple_encoder.c`).**

### Tier 2 (P1) & Explicitly Not Planned

- **Tier 2 (optional follow-up):** `common/lzip_decoder.c`, `common/microlzma_decoder.c`,
  `common/microlzma_encoder.c`, remaining legacy BCJ filters (`powerpc.c`, `ia64.c`, `sparc.c`,
  `armthumb.c`), and `common/string_conversion.c`.
- **Not planned:** Multi-threaded codecs (`stream_decoder_mt.c`, `stream_encoder_mt.c`, `outqueue.c`
  — note `CVE-2025-31115` lives in `stream_decoder_mt.c`, which requires a concurrent memory model
  outside sequential ISO C17), hardware CLMUL/ARM64 CRC assembly (`crc_clmul.c`, `crc_x86_clmul.h`),
  CLI binaries (`src/xz/`, `src/xzdec/`), and full compression round-trip equivalence beyond safety.

## Library-Specific Verification Hazards (No Shortcuts)

1. **Dynamic filter-chain DAG & `lzma_next_coder` re-initialisation (`common/filter_common.c`,
   `common/common.c`).**
   `liblzma` chains up to 4 arbitrary filters (`LZMA_FILTERS_MAX`) via function pointers in
   `lzma_next_coder` and re-initialises chains across concatenated `.xz` streams and blocks. Prove
   zero use-after-free, zero double-free, and zero leak on mid-chain allocation failure, invalid
   filter-chain rejection, and `lzma_end` from any error state.
2. **Memory-limit (`memlimit`) & `Index` overflow accounting (`common/index.c`, `common/vli_decoder.c`).**
   Untrusted `.xz` streams can encode huge `vli` values (up to `2^63 - 1`), multi-block padding,
   and malicious `Index` records. Prove overflow-free `uint64_t` / `size_t` arithmetic across
   `lzma_index_append`, `lzma_index_hash_append`, and dictionary allocation checks.
3. **LZ dictionary circular wraparound & `lz_encoder_mf.c` match-finder tables.**
   Prove that `lzma_dict` (`pos`, `full`, `limit`, `size`, `need_reset`) in `lz_decoder.c` and
   cyclic hash/binary-tree tables (`hc3`, `hc4`, `bt2`, `bt3`, `bt4`) + `lz_mf_move_window`
   normalisation in `lz_encoder.c` / `lz_encoder_mf.c` never read/write out of bounds or perform
   invalid pointer subtraction across resizes.
4. **Range coder bit-read/write bounds (`rangecoder/range_decoder.h`, `rangecoder/range_encoder.h`)
   & LZMA2 chunk resets (`lzma2_decoder.c`, `lzma2_encoder.c`).**
   Prove that LZMA2 uncompressed/LZMA chunk switches, property resets, dictionary resets, and
   `LZMA_REQUIRED_IN_MAX` / `in_buf` staging preserve strict buffer bounds across arbitrary 1-byte
   `lzma_code` calls.
5. **BCJ `simple_coder.c` lookahead buffering.**
   BCJ filters (`x86.c`, `arm64.c`, etc.) hold trailing unconvertible bytes in a small internal
   buffer between calls; prove buffer offset/count arithmetic never overflows or over-reads.

## Bootstrap & Local Commands

When onboarding into `framework/projects.json`: copy `lean-toolchain`,
start `XzF/Runtime/Ptr.lean` from `framework/lean/StrictPtr.lean`, wire `XzF/Results.lean` and
`project.json`, then run:

```bash
lake --dir projects/xz build --wfail XzF XzF.Results
python3 framework/check_project.py xz --skip-build
```
