# Working rules (`projects/bzip2`)

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

- **Status:** Upstream submodule `bzip2/` pinned (not yet registered in `framework/projects.json`;
  Lean runtime bootstrap, C translation, and safety proofs **Not done**).

## Scope (`Bzip2F`)

- **Upstream source:** `bzip2/` pinned submodule (`https://sourceware.org/git/bzip2.git`) +
  `patches/*.patch` in name order.
- **Target configuration:** portable scalar x86_64 Linux LP64 build of `libbz2` (`-DBZ_NO_STDIO` for
  Tier 1 memory/stream APIs; full `bzlib.h` with `BZ2_bzRead`/`BZ2_bzWrite` stdio wrappers in Tier 2;
  ~4k LOC pure C — one of the smallest, cleanest, and highest-ROI complete compression+decompression
  libraries in `oss-proof`).
- **Verification goal:** full safety (no ISO C17 undefined behaviour, no out-of-bounds read/write,
  no memory leak, stated write frame, and termination) of **every** documented decompression AND
  compression function in `bzlib.h`.

## Real-World Usage Paths & Function Priority

`libbz2` is shipped in nearly every Python and Linux installation and routinely touches untrusted
archives and compressed payloads:
- **Python standard library (`Modules/_bz2module.c` -> `bz2.BZ2Decompressor`, `bz2.BZ2Compressor`,
  `bz2.decompress`, `bz2.compress`, `bz2.open`):** Directly calls `BZ2_bzDecompressInit`,
  `BZ2_bzDecompress`, `BZ2_bzDecompressEnd`, `BZ2_bzCompressInit`, `BZ2_bzCompress`,
  `BZ2_bzCompressEnd`.
- **Archive & Package Ecosystems (`libarchive` `archive_read_support_filter_bzip2.c`, `tar -j`,
  `dpkg`, `rpm`, `git`/source tarballs, FreeType BZIP2-compressed PCF/font streams):** Calls the
  streaming `BZ2_bzDecompress*` and `BZ2_bzCompress*` APIs and one-shot buffer helpers.
- **Critical CVE Anchor — CVE-2019-12900:** Out-of-bounds write in `BZ2_decompress` (`decompress.c`)
  when a crafted `.bz2` stream specified `nSelectors > BZ_MAX_SELECTORS` (18002), writing past
  `s->selectorMtf` / `s->selector` on the heap.

### Tier 1 (P0) — Streaming & One-Shot Decompression + Compression (Prove All)

1. **Streaming decompression (`bzlib.c`, `decompress.c`, `huffman.c`, `crctable.c`, `randtable.c`):**
   `BZ2_bzDecompressInit` (both `small == 0` fast mode and `small == 1` low-memory mode),
   `BZ2_bzDecompress`, `BZ2_bzDecompressEnd`.
2. **Streaming compression (`bzlib.c`, `compress.c`, `blocksort.c`, `huffman.c`, `crctable.c`):**
   `BZ2_bzCompressInit` (all `blockSize100k` 1..9 and `workFactor` 0..250), `BZ2_bzCompress`
   (`BZ_RUN`, `BZ_FLUSH`, `BZ_FINISH`), `BZ2_bzCompressEnd`.
3. **One-shot buffer & version APIs (`bzlib.c`):** `BZ2_bzBuffToBuffDecompress`,
   `BZ2_bzBuffToBuffCompress`, `BZ2_bzlibVersion`.

### Tier 2 (P1) — High-Level `BZFILE` Wrappers & Explicitly Not Planned

- **Tier 2 (`bzlib.c` stdio layer):** `BZ2_bzReadOpen`, `BZ2_bzRead`, `BZ2_bzReadGetUnused`,
  `BZ2_bzReadClose`, `BZ2_bzWriteOpen`, `BZ2_bzWrite`, `BZ2_bzWriteClose`, `BZ2_bzWriteClose64`,
  `BZ2_bzopen`, `BZ2_bzdopen`, `BZ2_bzread`, `BZ2_bzwrite`, `BZ2_bzflush`, `BZ2_bzclose`,
  `BZ2_bzerror` (modeled against the same abstract file-handle runtime used by `projects/zlib` `gz*`).
- **Not planned:** CLI utilities (`bzip2.c`, `bzip2recover.c`) and full BWT/MTF/Huffman round-trip
  functional equivalence beyond invariants needed for safety.

## Verified Translation Units

Entire `libbz2` library (7 small C files + 2 headers):
- `bzlib.h`, `bzlib_private.h`
- `bzlib.c`, `decompress.c`, `compress.c`, `blocksort.c`, `huffman.c`, `crctable.c`, `randtable.c`

## Library-Specific Verification Hazards (No Shortcuts)

1. **Selector, group, and Huffman code-length table bounds (`decompress.c`, `huffman.c` — `CVE-2019-12900`).**
   Prove that `nGroups` (`2..6`), `nSelectors` (`<= BZ_MAX_SELECTORS`), MTF selector decoding,
   delta-coded bit-lengths (`curr` in `1..20`), and `BZ2_hbCreateDecodeTables` (`limit`/`base`/`perm`)
   stay strictly in bounds for arbitrary adversarial bitstreams.
2. **Inverse BWT (`tt` / `ll16` / `ll4`) & RLE1/RLE2 expansion (`decompress.c`, `bzlib.c`).**
   Prove that `origPtr < nblock`, `cftab` cumulative counts, `tt[tPos]` permutation traversal (and
   the 20-bit split `ll16`/`ll4` representation in `small == 1` mode), `tPos` masking, and
   `unRLE_obuf_to_output_FAST` / `_SMALL` never index out of `blockSize100k * 100000` or overrun
   `strm->next_out`.
3. **BWT sorting (`blocksort.c` — `mainSort` & `fallbackSort`).**
   `mainSort` uses a 3-way radix quicksort with overshoot bytes (`BZ_N_OVERSHOOT = 34`) appended to
   the end of `block`, plus `fallbackSort` when `budget < 0`. Prove overshoot writes, `ftab`/`quadrant`
   indexing, stack bounds (`MAIN_QSORT_STACK_SIZE`, `FALLBACK_QSORT_STACK_SIZE`), and signed integer
   arithmetic are completely free of UB and terminate on pathological repetitive inputs.
4. **Canonical Huffman encoder & bitstream emitter (`compress.c`, `huffman.c`).**
   Prove `BZ2_hbMakeCodeLengths` heap/weight array bounds, `sendMTFValues` selector/MTF buffer
   bounds, and `bsW` / `zbits` output buffer capacity invariants across `BZ_RUN`, `BZ_FLUSH`, and
   `BZ_FINISH`.
5. **Stream suspension/resumption & `avail_in`/`avail_out == 0` with `NULL` pointers.**
   Under strict ISO C17, verify whether `bzlib.c` ever executes `next_in += 0` or `next_out += 0` on
   `NULL` or stale pointers; report and patch any confirmed ISO C17 UB rather than weakening the
   runtime.

## Bootstrap & Local Commands

When onboarding into `framework/projects.json`: copy `lean-toolchain`, start
`Bzip2F/Runtime/Ptr.lean` from `framework/lean/StrictPtr.lean`, wire `Bzip2F/Results.lean` and
`project.json`, then run:

```bash
lake --dir projects/bzip2 build --wfail Bzip2F Bzip2F.Results
python3 framework/check_project.py bzip2 --skip-build
```
