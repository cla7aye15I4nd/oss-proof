# Working rules (`projects/libavif`)

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

- **Status:** Upstream submodule `libavif/` pinned (not yet registered in `framework/projects.json`;
  Lean runtime bootstrap, C translation, and safety proofs **Not done**).

## Scope (`LibavifF`)

- **Upstream source:** `libavif/` pinned submodule (`https://github.com/AOMediaCodec/libavif`) +
  `patches/*.patch` in name order.
- **Target configuration:** portable scalar x86_64 Linux LP64 pure-C build (`-DAVIF_LIBYUV=OFF
  -DAVIF_LIBSHARPYUV=OFF`, modeling external AV1 elementary-stream codec callbacks `dav1d`/`libaom`
  at the `avifCodec` interface boundary so the entire **ISOBMFF/MIAF container parser, tile grid
  assembler, YUV<->RGB reformatter, alpha/EXIF/ICC/XMP metadata handler, and AVIF muxer** are
  verified in pure C!).
- **Verification goal:** full safety (no ISO C17 undefined behaviour, no integer/stream buffer
  overflow in ISOBMFF box parsing or YUV<->RGB reformatting, no tile-grid heap overflow, no UAF or
  memory leak, stated write frame, and termination) across **both AVIF decoding/demuxing AND AVIF
  encoding/muxing** APIs in `include/avif/avif.h`.

## Real-World Usage Paths & Function Priority

AVIF has become a standard modern web image format — and **Pillow 11.3+ added native AVIF support**
via `libavif` (`src/_avif.c`), alongside **Chrome / Firefox / Android / ImageMagick / GIMP**:
- **PIL / Pillow (`src/_avif.c`):**
  - Decode: `avifDecoderCreate`, `avifDecoderSetIOMemory`, `avifDecoderParse`,
    `avifDecoderNextImage`, `avifDecoderNthImage`, `avifImageYUVToRGB`, `avifRGBImageSetDefaults`,
    `avifRGBImageAllocatePixels`, `avifRGBImageFreePixels`, `avifDecoderDestroy`.
  - Encode: `avifImageCreate`, `avifRGBImageSetDefaults`, `avifImageRGBToYUV`,
    `avifImageSetMetadataExif`, `avifImageSetMetadataXMP`, `avifImageSetProfileICC`,
    `avifEncoderCreate`, `avifEncoderAddImage`, `avifEncoderFinish`, `avifEncoderWrite`,
    `avifEncoderDestroy`, `avifRWDataFree`.
- **Critical Recent CVE Anchor — CVE-2025-48174 (fixed in libavif 1.3.0):** Integer overflow in
  `src/stream.c` / `makeRoom` and box/buffer size calculations leading to heap buffer overflow on
  crafted AVIF inputs.

### Tier 1 (P0) — ISOBMFF Container Parser, Tile Grid Assembly & YUV->RGB Decode Path (Prove First)

1. **Stream reader & ISOBMFF/MIAF container parser (`src/stream.c`, `src/read.c`, `src/rawdata.c`,
   `src/mem.c`, `src/avif.c`, `src/obu.c`, `src/colr.c`, `src/diag.c`):**
   `avifDecoderCreate`, `avifDecoderSetIOMemory`, `avifDecoderSetIO`, `avifDecoderParse`,
   `avifDecoderNextImage`, `avifDecoderNthImage`, `avifDecoderRead`, `avifDecoderReadMemory`,
   `avifDecoderReset`, `avifDecoderDestroy`, `avifPeekCompatibleFileType` — including nested box
   parsing (`ftyp`, `meta`, `iinf`, `iloc`, `iprp`/`ipco`/`ipma`, `iref`, `grid`, `ispe`, `pixi`,
   `colr`, `irot`, `imir`, `clap`, `moov`/`trak` animations), AV1 OBU sequence-header parsing
   (`src/obu.c`), and EXIF/ICC/XMP extraction.
2. **YUV -> RGB conversion & pixel buffer management (`src/reformat.c`, `src/alpha.c`,
   `src/scale.c`):**
   `avifRGBImageSetDefaults`, `avifRGBImageAllocatePixels`, `avifRGBImageFreePixels`,
   `avifImageYUVToRGB`, `avifImageAllocatePlanes`, `avifImageFreePlanes`, `avifImageCopy`,
   `avifImageSetViewRect`, `avifImageScale`.

### Tier 1 (P0) — AVIF Muxing & RGB->YUV Encode Path

- **Container writer & RGB -> YUV conversion (`src/write.c`, `src/reformat.c`, `src/stream.c`):**
  `avifEncoderCreate`, `avifEncoderAddImage`, `avifEncoderAddImageGrid`, `avifEncoderFinish`,
  `avifEncoderWrite`, `avifEncoderDestroy`, `avifImageCreate`, `avifImageDestroy`,
  `avifImageRGBToYUV`, `avifImageSetProfileICC`, `avifImageSetMetadataExif`,
  `avifImageSetMetadataXMP`, `avifRWDataRealloc`, `avifRWDataFree`.

### Explicitly Not Planned

- External AV1 video codec internals (`dav1d` ~80k LOC, `libaom` ~400k LOC, `rav1e`, `svt-av1` —
  modeled at the `avifCodec` decode/encode boundary), optional `libyuv` C++ SIMD (`reformat_libyuv.c`),
  experimental gain-map / HDR tone-mapping extensions, and CLI tools (`apps/avifdec.c`, `avifenc.c`).

## Library-Specific Verification Hazards (No Shortcuts)

1. **Stream buffer growth & box-length integer overflows (`src/stream.c`, `src/read.c` —
   `CVE-2025-48174`).**
   Prove `avifRWStreamWrite` / `makeRoom`, 32-bit/64-bit ISOBMFF box header sizes (`size == 0`,
   `size == 1` extended `largesize`), and `avifROStreamRead*` offset arithmetic cannot wrap
   `size_t` / `uint64_t` or read/write out of bounds.
2. **Tile-grid (`grid` item) geometry, depth & subsampling mismatches (`src/read.c`).**
   Untrusted AVIF `grid` items specify `rows`, `columns`, `outputWidth`, `outputHeight`, plus
   per-tile decoded `avifImage` dimensions/bit-depths/YUV formats (and separate alpha grids). Prove
   every tile blit stays strictly inside destination Y/U/V/A planes without mismatching bit depth
   (`8/10/12`) or chroma subsampling (`420`/`422`/`444`/`400`).
3. **`iloc` item extents, `iref` reference graphs & `clap` clean-aperture crop boxes (`src/read.c`).**
   Prove bounds on extent offset+length sums, cyclic `iref` item references, and `clap` signed
   rational cropping math (`int32_t` overflow / `INT_MIN` negation UB).
4. **YUV <-> RGB reformatting & premultiplied alpha (`src/reformat.c`, `src/alpha.c`).**
   Prove row-stride arithmetic (`rowBytes`), odd-dimension 4:2:0 chroma subsampling (`(w+1)/2`),
   8/10/12/16-bit shift counts, and `rgb.pixels` allocation bounds.
5. **AV1 OBU bit-parser (`src/obu.c`).**
   `avifSequenceHeaderParse` parses raw untrusted AV1 OBU bitstreams before calling the AV1 codec;
   prove `uleb128` decoding and bit-reader bounds never over-read.

## Bootstrap & Local Commands

When onboarding into `framework/projects.json`: copy `lean-toolchain`,
start `LibavifF/Runtime/Ptr.lean` from `framework/lean/StrictPtr.lean`, wire `LibavifF/Results.lean`
and `project.json`, then run:

```bash
lake --dir projects/libavif build --wfail LibavifF LibavifF.Results
python3 framework/check_project.py libavif --skip-build
```
