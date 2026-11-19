# Working rules (`projects/zlib`)

Inherits all rules of the repository root [`../../AGENTS.md`](../../AGENTS.md), including the
**Strict ISO C17 Undefined Behaviour Policy** (no wild/dangling/`NULL` pointer `+ 0`, no `NULL - NULL`,
no cross-object pointer arithmetic/comparison, no zero-length `memcpy`/`memset` on invalid pointers,
and no arguing "benign UB").

- **Status:** Registered in `framework/projects.json`; **Done** (86 / 86 documented public functions
  proved safe + default zlib stream round trip; legacy pointer-UB debt removal tracked below).

## Scope (`ZlibF`)

Kernel-checked Lean 4 proofs about a statement-by-statement translation of upstream `zlib` 1.4
(commit `99623ef7097352da7993ba614161fd6a311e046e` plus `patches/*.patch`), for the default x86_64
Linux LP64 static build (`86` documented public functions covering **both decompression and
compression**):

1. **Safety (proved / done):** `inflate`, `deflate`, `compress*`, `uncompress*`, checksums, utility
   and stream functions, the `gz*` file interface, and `inflateBack` are free of undefined
   behaviour, memory errors, and memory leaks, write only their stated frame, and terminate across
   every valid call sequence.
2. **Round trip (proved / done):** Conditional and unconditional round trip of the default zlib
   stream (`deflateInit` at default level + arbitrary chunking/flushes finished by
   `deflate(Z_FINISH)`, decoded by `inflateInit` + `inflate`), completeness with `deflateBound` /
   `compressBound`, and `uncompress(compress(x)) = x`.
3. **Not planned:** Functional correctness for non-default levels/strategies/wrappers/dictionaries,
   `gz*` or `inflateBack` round trips, non-LP64 build configurations, custom allocators, and the 10
   functions `zlib.h` lists after `/* undocumented functions (not part of the zlib API) */`. Any
   theorem that no goal in `ZlibF/Results.lean` depends on is deleted.

Read `docs/en/overview.md` first, then `docs/en/spec/safety.md`. Proof explanations live in
`docs/en/proof/` and `docs/zh/proof/`. Status is stated only in `docs/en/progress.md` and
`docs/zh/progress.md`.

## Real-World Usage Paths & Function Criticality

Because `zlib` is the foundational deflate engine linked directly or transitively by **Python**
(`zlib`, `gzip`, `zipfile`, **Pillow** PNG/ZIP/TIFF via `ZipDecode.c`/`ZipEncode.c`), **Node.js**
(`node:zlib`, **Sharp** via `libspng`/`libpng`/`libtiff`), **libarchive**, **libpng**, **libspng**,
**libtiff**, **OpenSSL/TLS**, **Git**, **HTTP/2 & HTTP/1.1 servers/clients**, and Linux package
managers, both its **decompression** and **compression** surfaces process untrusted data directly:

| Priority | Real-world call path | Critical C entry points (`zlib.h`) | Downstream callers |
| --- | --- | --- | --- |
| **Tier 1 (P0) — Decompression** | Streaming & one-shot inflate of untrusted deflate/zlib/gzip payloads | `inflateInit_`, `inflateInit2_`, `inflate`, `inflateEnd`, `inflateReset`, `inflateReset2`, `inflateSetDictionary`, `inflateSync`, `uncompress`, `uncompress2` | Pillow (`ZipDecode.c`), `libspng`, `libpng`, `libtiff` (`tif_zip.c`), `libarchive`, Node.js `node:zlib`, Python `zlib`/`gzip`/`zipfile`, HTTP clients/servers |
| **Tier 1 (P0) — Compression** | Streaming & one-shot deflate of user uploads, HTTP bodies, and re-encoded images | `deflateInit_`, `deflateInit2_`, `deflate`, `deflateEnd`, `deflateReset`, `deflateBound`, `deflateParams`, `deflateSetDictionary`, `compress`, `compress2`, `compressBound` | Pillow (`ZipEncode.c` PNG/PDF/TIFF save), `libspng`/`libpng` encode, `libtiff` (`tif_zip.c`), Node.js `node:zlib`, Python `zlib`/`gzip`, HTTP servers (note patches `0006` and `0007` caught real `deflateBound` under-sizing bugs) |
| **Tier 1 (P0) — Checksums** | Frame & chunk integrity checks over untrusted buffers | `crc32`, `crc32_z`, `crc32_combine*`, `adler32`, `adler32_z`, `adler32_combine*` | PNG chunk CRCs (`libspng`, `libpng`, Pillow), ZIP/gzip trailers, `libarchive` |
| **Tier 2 (P1) — File & callback streams** | `.gz` file streaming and callback-driven inflate | `gzopen`, `gzdopen`, `gzread`, `gzwrite`, `gzgets`, `gzseek*`, `gzoffset*`, `gzclose*`, `inflateBackInit_`, `inflateBack`, `inflateBackEnd`, `inflateCopy`, `deflateCopy`, `inflateGetHeader`, `deflateSetHeader` | CLI tools, log pipelines, `gz*` wrappers (note patches `0001`–`0005` caught real bugs in `inflateCopy`, `gzread`, `gzwrite`, `gzseek`, and `gzoffset`) |

## Layout within `projects/zlib/`

- `zlib/` — pinned upstream submodule (`https://github.com/madler/zlib`). Never modify it.
- `patches/` — minimal upstream-submitted fixes, listed in `patches/README.md` with ablation tests
  in `tests/regression/*/run.sh`.
- `ZlibF/Zlib/` — statement-by-statement translations (`zlib/X.c` -> `ZlibF/Zlib/X.c.lean`,
  `zlib/X.h` -> `ZlibF/Zlib/X.h.lean`).
- `ZlibF/Runtime/` — heap, pointers, loops, faults, and libc primitives.
- `ZlibF/Math/` — heap-free mathematics (`ZlibF/Spec/` -> `ZlibF/Proof/`, enforced by
  `framework/check_spec_layers.py`).
- `ZlibF/Spec/{Common,Safety,Functional}/` — specifications and `Goal.*` definitions.
- `ZlibF/Proof/` — internal proofs (`X.c.<topic>.lean`) and public goal proofs (`public-<name>.lean`).
- `ZlibF/Results.lean` — Lean-checked goal registry (`proved`, `notDone`, `required`).

## Legacy Runtime UB Debt Notice (Do Not Copy or Extend)

`ZlibF/Runtime/Ptr.lean` currently contains two historical relaxations documented in
`docs/en/model-limits.md`:
1. `Ptr.add p 0` returns `.ok (p, h)` without checking that `p` is non-null and points into a live
   allocation (`gzseek64` and `gz_skip_have` execute `x.next += 0` when `x.next` is unwritten or
   points into a caller buffer that may have been freed);
2. `Ptr.diff .null .null` returns `.ok (0, h)` (`compress2_z` evaluates `stream.next_out - dest`
   when both are `NULL` and `*destLen == 0`).

**Strict rules regarding this legacy debt:**
- These two relaxations are **legacy debt**, NOT accepted `oss-proof` policy (`zlib` is the sole
  shrink-only entry in `LEGACY_PERMISSIVE_PTR_PROJECTS` of `framework/check_runtime_ub.py`).
- **Never** argue that `NULL + 0`, wild/dangling pointer `+ 0`, or `NULL - NULL` is valid C, **never**
  add any new permissive shortcut to `ZlibF/Runtime/`, and **never** copy `ZlibF/Runtime/Ptr.lean`
  into another project (new projects MUST start from `framework/lean/StrictPtr.lean`).
- Removing these two shortcuts from `ZlibF/Runtime/Ptr.lean` (together with minimal upstream C
  patches for `gzlib.c` / `gzread.c` / `compress.c` and updating `gzlib.c.seek.lean` &
  `gzread.c.skip-have.lean`) must be done in its own dedicated PR, after which `"zlib"` is removed
  from `LEGACY_PERMISSIVE_PTR_PROJECTS`.

## Local commands

From repository root:

```bash
# Build ZlibF (largest modules crc32.c.lean and inftrees.c.lean need 8-9 GB RAM each; max -j 4)
lake --dir projects/zlib build --wfail ZlibF

# Run full project verification gate
python3 framework/check_project.py zlib --skip-build

# Run ASan + UBSan differential tests and patch-revert reproductions
(cd projects/zlib && SAN=1 ZLIB_SRC="$PWD/zlib" bash tests/run.sh)
```
