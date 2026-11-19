# Working rules (`projects/brotli`)

Inherits all rules of [`../../AGENTS.md`](../../AGENTS.md), including the **Strict ISO C17 Undefined Behaviour Policy**
(no `NULL + 0`, no wild/dangling pointer `+ 0`, no `NULL - NULL`, no cross-object pointer subtraction or comparison,
and no `memcpy`/`memset` with `n == 0` on `NULL` or dangling pointers).

- **Status:** Registered in `framework/projects.json`; strict ISO C17 runtime (`BrotliF.Runtime`)
  checked, statement-by-statement C translation and public safety proofs **Not done**.

## Scope (`BrotliF`)

Goal: kernel-checked Lean 4 proofs about a faithful, statement-by-statement translation of upstream
Google Brotli (`google/brotli`, pinned submodule `brotli/` + `patches/*.patch`), covering **both
`libbrotlidec` (decoder) AND `libbrotlienc` (encoder)** together with their shared `c/common/` units
(`c/include/brotli/decode.h`, `c/include/brotli/encode.h`, `c/include/brotli/shared_dictionary.h`,
`c/dec/*.c`, `c/enc/*.c`, `c/common/*.c`).

Target configuration — portable scalar x86_64 Linux LP64 build (`-DBROTLI_BUILD_PORTABLE`, scalar
fallback without target-specific SIMD intrinsics, default `malloc`/`free` allocator).

The goal is full safety (no ISO C17 undefined behaviour, no memory error, no dangling zero-copy
borrow or dictionary borrow, no memory leak, stated write frame, and termination) of every public
decoder **and** encoder function across every valid call sequence.

## Real-World Usage Paths & Function Priority

Brotli sits directly on the internet-facing HTTP edge (`Content-Encoding: br`) and inside major
language runtimes:
- **Node.js (`node:zlib` `src/node_zlib.cc`):** `BrotliDecoderCreateInstance`,
  `BrotliDecoderSetParameter`, `BrotliDecoderDecompressStream`, `BrotliDecoderDestroyInstance`,
  `BrotliEncoderCreateInstance`, `BrotliEncoderSetParameter`, `BrotliEncoderCompressStream`,
  `BrotliEncoderDestroyInstance` — directly exposed by `zlib.createBrotliDecompress()`,
  `zlib.brotliDecompress()`, `zlib.createBrotliCompress()`, and `zlib.brotliCompress()`.
  *(Critical real-world anchor: **CVE-2026-111497** ("Node2Shell" / "HTTP2Shell", CVSS 9.2–9.8) in
  `c/dec/decode.c` caused an out-of-bounds write on an unhandled invalid block-switch error in
  Brotli 1.0.3–1.2.0, impacting Node.js `node:zlib`, Nginx `ngx_brotli`, Envoy, Istio, Python, and .NET.)*
- **Web Servers & CDNs (Nginx `ngx_brotli`, Envoy, Cloudflare, Apache `mod_brotli`):** High-volume
  **encoding** of dynamic HTTP responses (`BrotliEncoderCompressStream` at qualities 0–6 with
  `BROTLI_OPERATION_PROCESS`/`FLUSH`/`FINISH` and zero-copy `BrotliEncoderTakeOutput`) as well as
  request-body **decoding** (`BrotliDecoderDecompressStream`).
- **Browsers & Fonts (Chrome, Firefox, Safari, WOFF2):** Streaming decoding of HTTP responses and
  embedded WOFF2 web-font payloads (`BrotliDecoderDecompressStream`, `BrotliDecoderDecompress`,
  `BrotliDecoderTakeOutput`, shared dictionary compression RFC 9842).
- **Python (`brotli`, `brotlicffi`, `urllib3`/`aiohttp`/`httpx`):** Both `BrotliDecoderDecompressStream`
  / `BrotliDecoderDecompress` and `BrotliEncoderCompressStream` / `BrotliEncoderCompress`.

### Tier 1 (P0) — Decoder Path (`libbrotlidec`, Prove First)

1. **Streaming decompression:** `BrotliDecoderDecompressStream` across arbitrary input/output
   splits, every `BrotliRunningState` suspension/resumption point (`SUCCESS`, `NEEDS_MORE_INPUT`,
   `NEEDS_MORE_OUTPUT`, `ERROR`), malformed block switches (`CVE-2026-111497` class!), zero-copy
   output (`available_out == 0`, `next_out == NULL`), and repeated calls after finish or error.
2. **One-shot decompression:** `BrotliDecoderDecompress`.
3. **Lifecycle, parameters, borrows, and dictionaries:** `BrotliDecoderCreateInstance`,
   `BrotliDecoderDestroyInstance`, `BrotliDecoderSetParameter`, `BrotliDecoderAttachDictionary`,
   `BrotliDecoderHasMoreOutput`, `BrotliDecoderTakeOutput`, `BrotliDecoderIsUsed`,
   `BrotliDecoderIsFinished`, `BrotliDecoderGetErrorCode`, `BrotliDecoderErrorString`,
   `BrotliDecoderVersion`.

### Tier 1 (P0) — Encoder Path (`libbrotlienc`, Prove Immediately After Decoder)

Servers, CDNs, and Node.js/Python apps run the Brotli encoder continuously on attacker-influenced
HTTP responses, API JSON, and uploaded text/assets (often with caller-chosen quality/lgwin/flush
splits and tight output buffers):

1. **Streaming compression:** `BrotliEncoderCreateInstance`, `BrotliEncoderDestroyInstance`,
   `BrotliEncoderSetParameter`, `BrotliEncoderCompressStream` (`BROTLI_OPERATION_PROCESS`,
   `BROTLI_OPERATION_FLUSH`, `BROTLI_OPERATION_FINISH`, `BROTLI_OPERATION_EMIT_METADATA`),
   `BrotliEncoderHasMoreOutput`, `BrotliEncoderTakeOutput`, `BrotliEncoderIsFinished`,
   `BrotliEncoderVersion`.
2. **One-shot compression & sizing:** `BrotliEncoderCompress`, `BrotliEncoderMaxCompressedSize`.
3. **Prepared/shared dictionaries:** `BrotliEncoderPrepareDictionary`,
   `BrotliEncoderDestroyPreparedDictionary`, `BrotliEncoderAttachPreparedDictionary`,
   `BrotliSharedDictionaryCreateInstance`, `BrotliSharedDictionaryDestroyInstance`,
   `BrotliSharedDictionaryAttach`.

### Explicitly Not Planned

- Functional decoding/encoding equivalence to RFC 7932 beyond invariants required for safety (e.g.,
  Huffman table bounds, ringbuffer cursor bounds, metablock bit-emission bounds are in scope).
- Platform-specific SIMD/assembly intrinsics, Java/JS/Python bindings, and CLI tool (`c/tools/brotli.c`).

## Verified Translation Units

- **Common (`c/common/`):** `constants.c`, `context.c`, `dictionary.c`, `platform.c`,
  `shared_dictionary.c`, `transform.c` (plus `c/include/brotli/*.h`).
- **Decoder (`c/dec/`):** `bit_reader.c`, `decode.c`, `huffman.c`, `prefix.c`, `state.c`, `static_init.c`.
- **Encoder (`c/enc/`):** `backward_references.c`, `backward_references_hq.c`, `bit_cost.c`,
  `block_splitter.c`, `brotli_bit_stream.c`, `cluster.c`, `command.c`, `compound_dictionary.c`,
  `compress_fragment.c`, `compress_fragment_two_pass.c`, `dictionary_hash.c`, `encode.c`,
  `encoder_dict.c`, `entropy_encode.c`, `fast_log.c`, `histogram.c`, `literal_cost.c`, `memory.c`,
  `metablock.c`, `static_dict.c`, `static_dict_lut.c`, `static_init.c`.

Translations mirror the C layout (`brotli/c/<dir>/X.c` -> `BrotliF/Brotli/<dir>/X.c.lean`).
Static dictionary (`c/common/dictionary.c`, 120 KB) and transforms (`c/common/transform.c`, 121
entries) stay symbolic in `LibraryGlobals` with exact byte-size and structural predicates — never
run `decide +kernel` over large tables.

## Key Brotli Hazards to Model and Verify Without Shortcuts

1. **Streaming state-machine corruption & block-switch errors (`c/dec/decode.c` — `CVE-2026-111497`).**
   `BrotliDecoderDecompressStream` suspends and resumes across dozens of `BrotliRunningState` and
   sub-state enumerators. Prove the state invariant holds on **every** exit (`SUCCESS`,
   `NEEDS_MORE_INPUT`, `NEEDS_MORE_OUTPUT`, `ERROR`), specifically verifying `DecodeCommandBlockSwitch`
   / `DecodeLiteralBlockSwitch` / `DecodeDistanceBlockSwitch` and subsequent calls after error.
2. **Zero-copy output borrows (`BrotliDecoderTakeOutput` & `BrotliEncoderTakeOutput`).**
   Both functions return a `const uint8_t*` slice into internal ringbuffer/storage memory. Prove
   that the returned slice is readable and live until the next mutating call (`*Stream`, `TakeOutput`,
   or `DestroyInstance`).
3. **Two-level Huffman tables (`c/dec/huffman.c`) & static dictionary transforms (`c/common/transform.c`).**
   Prove exact table-allocation bounds (`BROTLI_HUFFMAN_MAX_SIZE_*`) and transformed-word slice
   bounds from first principles; never assume table entries are in bounds without proving
   `BrotliBuildCodeLengthsHuffmanTable` / `BrotliBuildHuffmanTable` establishes them.
4. **Encoder ringbuffer, hashers & arena allocator (`c/enc/encode.c`, `memory.c`, `ringbuffer.h`,
   `hash_*_inc.h`, `compress_fragment*.c`, `brotli_bit_stream.c`).**
   Prove that the fast-path `BrotliCompressFragmentFast` (quality 0–1, heavily used in live HTTP),
   two-pass fragment encoder, generic hash-chain/binary-tree match finders (qualities 2–11),
   `MemoryManager` pool/OOM unwinding (`BROTLI_IS_OOM`), and `BrotliStoreMetaBlock` bit-writer never
   write past `storage` / `cmd_buf` / caller output buffers, even on `BROTLI_OPERATION_FLUSH` /
   `EMIT_METADATA` / OOM mid-stream.
5. **Attached / compound dictionaries (`BrotliDecoderAttachDictionary`, `BrotliEncoderAttachPreparedDictionary`).**
   Enforce call-ordering invariants (`BROTLI_STATE_UNINITED`) and explicit caller-buffer liveness
   through `DestroyInstance` in the call-sequence invariant.

## Proof Workflow & Local Commands

- Only `propext`, `Classical.choice`, and `Quot.sound` are allowed (`sorry` permitted on
  `skeleton/*` branches only). `BrotliF/Results.lean` is the Lean-checked registry of all goals;
  every safety goal pairs with a non-vacuity witness theorem.
- Any narrower precondition (pairwise disjoint caller regions, default allocator) is explicit in
  the goal and documented in `docs/{en,zh}/deviations.md`.
- Build with at most `-j 4` under a 16 GB RAM limit.

From repository root:

```bash
lake --dir projects/brotli build --wfail BrotliF BrotliF.Results
python3 framework/check_project.py brotli --skip-build
```
