# oss-proof

Machine-checked Lean 4 proofs about statement-by-statement translations of open-source C libraries:
every covered public function is free of undefined behaviour, memory errors and leaks, writes only
its stated frame, and returns, under the premises each theorem states.

## Libraries

| Library | Source | Build target | Scope & current state | Findings / patches | Status |
| --- | --- | --- | --- | --- | --- |
| [`zlib`](projects/zlib/README.md) | zlib 1.4.0.1-motley (`617e19a8`) + [6 patches](projects/zlib/patches/README.md) | default x86_64 Linux LP64 | 86 / 86 documented functions safe + default zlib stream round trip | [8 issues](https://www.dataisland.org/oss-proof/zlib/en/findings.html), [6 patches](projects/zlib/patches/README.md) | Done |
| [`7zip`](projects/7zip/README.md) | 7-Zip C SDK 26.00 (`d3296e39`) | portable scalar x86_64 Linux LP64 | Top-down container/BCJ2/PPMd7/LZMA2 invariants & strict ISO C17 runtime checked; C translation not done | — | Not done |
| [`libarchive`](projects/libarchive/README.md) | libarchive 3.8 (`432ab464`) | default scalar x86_64 Linux LP64 | Top-down RAR5 & 7-Zip invariants & strict ISO C17 runtime checked; C translation not done | — | Not done |
| [`zstd`](projects/zstd/README.md) | Zstandard 1.5.7 (`756e62a9`) | portable scalar x86_64 Linux LP64 (`libzstd` decoder) | Strict ISO C17 runtime checked; C translation & public decoder proofs not done | — | Not done |
| [`brotli`](projects/brotli/README.md) | Brotli 1.2 (`libbrotlidec` decoder) | portable scalar x86_64 Linux LP64 | Strict ISO C17 runtime checked; C translation & public decoder proofs not done | — | Not done |
| [`zlib-ng`](projects/zlib-ng/README.md) | zlib-ng `develop` (`e591472c`) + [22 patches](projects/zlib-ng/patches/README.md) | `ZLIB_COMPAT` x86_64 Linux LP64, generic C kernels | Checksums, version/error strings & `compressBound` safe (most also functionally correct); streaming `deflate`/`inflate`, one-shot and `gz*` not done | [22 patches](projects/zlib-ng/patches/README.md) | Not done |
| [`mozjpeg`](projects/mozjpeg/README.md) | mozjpeg 5.0.0 (`08265790`) | portable static 8-bit `WITH_JPEG8=1` x86_64 Linux LP64 | Strict ISO C17 runtime, `jutils.c`, `jpeg_std_error`, `jpeg_save_markers`, teardown/query helpers & `jpeg_calc_output_dimensions` (incl. `1/2`–`1/8` shrink-on-load) proved; header/entropy/IDCT scanline decode not done | — | Not done |

## Candidate targets (Tier 0)

The C code that Sharp (Node.js) and Pillow (Python) run on untrusted images by default, chosen from
what the published packages actually ship and the functions their callers actually invoke. **Tier
0** is the code that turns untrusted bytes into pixels or metadata; each project's `AGENTS.md`
lists exactly that code and nothing else. Every candidate tracks its upstream's latest default
branch; none is registered for CI yet, and no translation or proof exists.

| Library | Reached from | Tier 0 |
| --- | --- | --- |
| [`libvips`](projects/libvips/AGENTS.md) | every [Sharp](projects/sharp/AGENTS.md) call | format sniffing, loader glue, vendored GIF decoder, EXIF and ICC bridges |
| [`libpng`](projects/libpng/AGENTS.md) | Sharp PNG | `png_read_info`, chunk handlers, `png_read_row` / `png_read_image` |
| [`libwebp`](projects/libwebp/AGENTS.md) | Sharp and Pillow WebP | `WebPDecode`, demuxer, `WebPAnimDecoder*` |
| [`libtiff`](projects/libtiff/AGENTS.md) | Sharp and Pillow TIFF | directory parsing, strip/tile reads, built-in codecs |
| [`libexif`](projects/libexif/AGENTS.md) | Sharp, any input with EXIF | `exif_data_load_data`, `exif_entry_get_value` |
| [`lcms2`](projects/lcms2/AGENTS.md) | Sharp, any input with an ICC profile | `cmsOpenProfileFromMem`, `cmsCreateTransform`, `cmsDoTransform` |
| [`libxml2`](projects/libxml2/AGENTS.md) | Sharp SVG (through librsvg) | SAX parsing via `xmlCreateIOParserCtxt` / `xmlParseDocument` |
| [`pillow`](projects/pillow/AGENTS.md) | every Pillow `load()` | `src/libImaging/` decoders and their glue |
| [`libjpeg-turbo`](projects/libjpeg-turbo/AGENTS.md) | Pillow JPEG | `jpeg_read_header` … `jpeg_read_scanlines`, draft scaling |
| [`libavif`](projects/libavif/AGENTS.md) | Pillow AVIF | `avifDecoderParse`, `avifDecoderNthImage`, `avifImageYUVToRGB` |
| [`openjpeg`](projects/openjpeg/AGENTS.md) | Pillow JPEG 2000 | `opj_read_header`, `opj_read_tile_header`, `opj_decode_tile_data` |
| [`xz`](projects/xz/AGENTS.md) | Pillow LZMA-compressed TIFF, Python `lzma` | `lzma_stream_decoder`, `lzma_code` |
| [`bzip2`](projects/bzip2/AGENTS.md), [`lz4`](projects/lz4/AGENTS.md) | Python `bz2`, python-lz4, libarchive | decompression entry points |

Sharp and Pillow also rely on [`zlib-ng`](projects/zlib-ng/README.md) for PNG and Deflate TIFF.

## What it rests on

Each C library is translated to Lean statement by statement. Every undefined behaviour reachable in
ISO C17 raises an explicit fault in the translation, and the theorems prove that no fault occurs.
Lean's kernel checks every proof against the exact goal statement using only the three standard
axioms (`propext`, `Classical.choice`, `Quot.sound`).

Six items are trusted and not proved: the Lean kernel and the programs that check axioms and goal
types, the runtime model of memory and pointers, the hand translation from C, the pinned upstream
source and patches, the target build and external-call model, and the goal statements themselves.
Differential tests under AddressSanitizer and UndefinedBehaviorSanitizer compare each translation
byte-for-byte against the real C as evidence of fidelity, not proof.

## Not claimed

Compiler, operating-system and hardware correctness; build configurations, custom allocators or
undocumented entry points outside each theorem's stated domain; and functional correctness beyond
the functional goals explicitly proved for a library.

## Check it yourself

```bash
# Build and kernel-check zlib (largest modules need 8 to 9 GB RAM each; cap parallelism via LEAN_NUM_THREADS=4)
LEAN_NUM_THREADS=4 lake --dir projects/zlib build --wfail ZlibF
(cd projects/zlib && lake env leanchecker --fresh ZlibF.Results)

# Run the shared verification gate (options, forbidden constructs, runtime UB policy, layers, kernel env, coverage, patches)
python3 framework/check_project.py zlib --skip-build
```

## Read more

- [oss-proof portal (English)](https://www.dataisland.org/oss-proof/en/) · [中文门户](https://www.dataisland.org/oss-proof/zh/)
- [zlib × Lean (English)](https://www.dataisland.org/oss-proof/zlib/en/) · [zlib × Lean（中文）](https://www.dataisland.org/oss-proof/zlib/zh/)
- [zlib status](https://www.dataisland.org/oss-proof/zlib/en/progress.html) · [deviations](https://www.dataisland.org/oss-proof/zlib/en/deviations.html) · [trusted base](https://www.dataisland.org/oss-proof/zlib/en/trusted-base.html) · [findings](https://www.dataisland.org/oss-proof/zlib/en/findings.html)
