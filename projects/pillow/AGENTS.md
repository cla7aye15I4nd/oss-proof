# Working rules (`projects/pillow`)

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

- **Status:** Upstream submodule `pillow/` pinned (not yet registered in `framework/projects.json`;
  Lean runtime bootstrap, C translation, and safety proofs **Not done**).

## Scope (`PillowF`)

- **Upstream source:** `pillow/` pinned submodule (`https://github.com/python-pillow/Pillow`) +
  `patches/*.patch` in name order.
- **Target configuration:** portable scalar x86_64 Linux LP64 C core build of **`src/libImaging/`**
  (~30k LOC pure C!) plus the C-layer decoding/encoding glue in `src/decode.c`, `src/encode.c`,
  `src/_imaging.c`, `src/_webp.c`, `src/_imagingcms.c`, and `src/_imagingft.c` (excluding Python
  interpreter internals via explicit boundary specs).
- **Why Pillow (`libImaging`) is a premier standalone C verification target:** Unlike Sharp (which
  delegates almost everything to `libvips` + external codecs), **Pillow contains its own ~30k LOC
  pure-C imaging engine (`src/libImaging/`)** implementing memory allocation, raw/bit/RLE/GIF/ZIP
  decoders & encoders, pixel packing/unpacking, Lanczos/bicubic resampling, color conversion,
  quantization, drawing, AND codec bridges for JPEG, TIFF, and JPEG 2000. Even PNG in Pillow does
  **not** use `libpng` — Pillow parses PNG chunks in Python (`PngImagePlugin.py`) and calls
  `src/libImaging/ZipDecode.c` / `ZipEncode.c` -> `zlib` (already proved in `projects/zlib`!).
- **2026 CVE Proof of Importance (fixed in Pillow 13.0.0):**
  - **CVE-2026-112403 (`src/libImaging/JpegDecode.c` `ImagingJpegDecode`):** Heap buffer overflow
    when downscaling (`Image.thumbnail()` / draft scaling) 8-bit lossless SOF3 JPEGs — scanline
    buffer allocated for requested draft width rather than `libjpeg`'s actual output width/components!
  - **CVE-2026-112393 (`src/libImaging/TiffDecode.c` `_tiffWriteProc`):** Heap buffer overflow &
    stale heap disclosure when **saving** compressed TIFF to in-memory `BytesIO` streams!
  - **CVE-2026-128067 (`src/libImaging/TiffDecode.c` `ImagingLibTiffEncode`):** Out-of-bounds heap
    read & write (especially with Predictor 2) when attacker-controlled tags (`exif=` / `tiffinfo=`)
    override `libtiff`'s encoder geometry tags during **saving**!

## Real-World Python Usage Paths & Exact Call Graph

Over 95% of real-world Pillow deployments (Django/FastAPI/Flask user uploads, PyTorch/torchvision
& HuggingFace vision data loaders, PDF/OCR preprocessing, report/thumbnail generators) hit these
exact Python -> C paths:

| Real-World Python Call | C Bridge (`src/`) | Pure-C Core (`src/libImaging/`) | External C Codec (`oss-proof` Project) |
| --- | --- | --- | --- |
| `Image.open(buf).load()` — **JPEG** (+ `thumbnail()` / `draft()`) | `decode.c` (`PyImaging_JpegDecoderNew`) | `Alloc.c`, `JpegDecode.c` (`CVE-2026-112403`), `Unpack.c` | [`../libjpeg-turbo/AGENTS.md`](../libjpeg-turbo/AGENTS.md) |
| `Image.open(buf).load()` — **PNG** | `decode.c` (`PyImaging_ZipDecoderNew`) | `Alloc.c`, `ZipDecode.c`, `Unpack.c` | [`../zlib/AGENTS.md`](../zlib/AGENTS.md) **(Done)** |
| `Image.open(buf).load()` — **WebP** | `_webp.c` (`WebPDecode*`, `WebPDemux*`) | `Alloc.c`, `Unpack.c` | [`../libwebp/AGENTS.md`](../libwebp/AGENTS.md) |
| `Image.open(buf).load()` — **TIFF** | `decode.c` (`PyImaging_LibTiffDecoderNew`) | `Alloc.c`, `TiffDecode.c`, `Unpack.c` | [`../libtiff/AGENTS.md`](../libtiff/AGENTS.md) |
| `Image.open(buf).load()` — **GIF** | `decode.c` (`PyImaging_GifDecoderNew`) | `Alloc.c`, `GifDecode.c` (self-contained LZW!) | *(None — pure `libImaging` C!)* |
| `Image.open(buf).load()` — **BMP / ICO / PPM / PCX / TGA / FLI / SGI** | `decode.c` | `RawDecode.c`, `BitDecode.c`, `PackBits` (`TiffDecode.c`), `PcxDecode.c`, `TgaRleDecode.c`, `FliDecode.c`, `SgiRleDecode.c`, `Unpack.c` | *(None — pure `libImaging` C!)* |
| `Image.open(buf).load()` — **AVIF** (Pillow 11.3+) | `_avif.c` | `Alloc.c`, `Unpack.c` | [`../libavif/AGENTS.md`](../libavif/AGENTS.md) |
| `Image.open(buf).load()` — **JPEG 2000** | `decode.c` | `Jpeg2KDecode.c` | [`../openjpeg/AGENTS.md`](../openjpeg/AGENTS.md) |
| `.resize()`, `.thumbnail()`, `.reduce()` | `_imaging.c` | `Resample.c` (`ImagingResample`, `ImagingReduce`), `Alloc.c` | *(Pure `libImaging` C)* |
| `.convert()`, `.transpose()`, `.crop()`, `.paste()`, `.alpha_composite()`, `ImageOps.exif_transpose()` | `_imaging.c` | `Convert.c`, `ConvertYCbCr.c`, `Geometry.c`, `Crop.c`, `Paste.c`, `AlphaComposite.c`, `Quant.c` | *(Pure `libImaging` C)* |
| `.save(out, format=...)` — **JPEG / PNG / WebP / TIFF / GIF / JP2 / BMP** | `encode.c`, `_webp.c` | `JpegEncode.c`, `ZipEncode.c`, `TiffDecode.c` (`ImagingLibTiffEncode`, `_tiffWriteProc` — `CVE-2026-112393`, `CVE-2026-128067`), `GifEncode.c`, `Jpeg2KEncode.c`, `RawEncode.c`, `Pack.c` | `libjpeg-turbo`, `zlib`, `libwebp`, `libtiff`, `openjpeg` |
| `ImageCms.profileToProfile()` | `_imagingcms.c` | `Imaging` buffer bridge | [`../lcms2/AGENTS.md`](../lcms2/AGENTS.md) |
| `ImageDraw.Draw(im).text()` / `ImageFont.truetype()` | `_imagingft.c`, `_imaging.c` | `Draw.c`, `Alloc.c` | [`../freetype/AGENTS.md`](../freetype/AGENTS.md) |

### Tier 1 (P0) — `libImaging` Core Allocator, Untrusted Decoders, Resampling & High-CVE Encoders (Prove First)

1. **Image allocation & pixel-storage core (`Alloc.c`, `Storage.c`, `Access.c`, `Imaging.h`):**
   `ImagingNewPrologue`, `ImagingNewPrologueSubtype`, `ImagingNewDirty`, `ImagingNew`,
   `ImagingNewBlock`, `ImagingDelete`, `ImagingMemorySetBlocksMax` — proving overflow-free
   `ysize * linesize` and `block` allocation invariants (`im->image[y]` / `im->image32[y]` row-pointer
   arrays).
2. **Primary decoders (`JpegDecode.c`, `TiffDecode.c`, `ZipDecode.c`, `GifDecode.c`, `RawDecode.c`,
   `BitDecode.c`, `Unpack.c`, `UnpackYCC.c`):**
   `ImagingJpegDecode` (`CVE-2026-112403`!), `ImagingLibTiffDecode`, `ImagingZipDecode`,
   `ImagingGifDecode`, `ImagingRawDecode`, `ImagingBitDecode`, and all `ImagingUnpack*` scanline
   unpackers.
3. **Auto-sniffed legacy/RLE decoders reachable via `Image.open()` (`FliDecode.c`, `PcxDecode.c`,
   `SgiRleDecode.c`, `TgaRleDecode.c`, `SunRleDecode.c`, `PcdDecode.c`, `XbmDecode.c`, `HexDecode.c`,
   `MspDecode.c`):**
   **Critical insight:** `Image.open(untrusted_bytes)` probes **every registered plugin's magic
   header** automatically (not just JPEG/PNG/WebP!). Historically, a huge share of Pillow RCE/OOB
   CVEs occurred in `FliDecode.c`, `PcxDecode.c`, `SgiRleDecode.c`, and `TgaRleDecode.c` triggered
   by uploading a file with a `.jpg` extension!
4. **High-CVE encoder paths (`TiffDecode.c` `ImagingLibTiffEncode` / `_tiffWriteProc`, `JpegEncode.c`,
   `ZipEncode.c`, `GifEncode.c`, `RawEncode.c`, `Pack.c`):**
   Directly eliminates the `CVE-2026-112393` and `CVE-2026-128067` heap overflow / stale-heap
   disclosure classes on `im.save(BytesIO(), ...)`.
5. **Resampling & core pixel transforms (`Resample.c`, `Convert.c`, `ConvertYCbCr.c`, `Crop.c`,
   `Paste.c`, `Geometry.c`, `AlphaComposite.c`, `Bands.c`, `Copy.c`):**
   `ImagingResample`, `ImagingResampleHorizontal`, `ImagingResampleVertical`, `ImagingReduce`,
   `ImagingConvert`, `ImagingCrop`, `ImagingPaste`, `ImagingTranspose`, `ImagingRotate`,
   `ImagingAlphaComposite`.

### Tier 2 (P1) — Drawing, Quantization, Filtering & Secondary Bridges

- `Draw.c`, `Quant.c`, `QuantOctree.c`, `QuantHash.c`, `QuantHeap.c`, `QuantPngQuant.c`,
  `Jpeg2KDecode.c`, `Jpeg2KEncode.c`, `Filter.c`, `BoxBlur.c`, `Point.c`, `Chops.c`, `Blend.c`,
  `Composite.c`, `Fill.c`, `GetBBox.c`, `Histo.c`, `Matrix.c`, `Offset.c`, `RankFilter.c`,
  and the thin C-extension glue layers `src/decode.c`, `src/encode.c`, `src/_webp.c`,
  `src/_imagingcms.c`, `src/_imagingft.c`.

### Explicitly Not Planned

- Pure-Python plugin logic and OS subprocess wrappers (`EpsImagePlugin.py` Ghostscript argument
  injection `CVE-2026-112900` is a Python/subprocess security issue, not ISO C17 memory safety).
- External C codec internals verified in their own projects (`zlib`, `libjpeg-turbo`, `libwebp`,
  `libtiff`, `lcms2`, `libavif`, `openjpeg`, `freetype`).
- X11/Windows/macOS display/clipboard drivers (`src/_imagingtk.c`, `src/display.c`), `raqm`/HarfBuzz
  shaping internals, and visual-quality/functional equivalence beyond safety invariants.

## Library-Specific Verification Hazards (No Shortcuts)

1. **Decoder/Encoder geometry mismatch between `im` and external codecs (`JpegDecode.c` —
   `CVE-2026-112403`; `TiffDecode.c` — `CVE-2026-128067`).**
   Prove that `ImagingJpegDecode` checks `cinfo.output_width`, `cinfo.output_height`, and
   `cinfo.output_components` against the allocated `im` and scanline buffer after
   `jpeg_start_decompress` (even under `draft()` / `scale_num/scale_denom` or lossless SOF3), and
   that `ImagingLibTiffEncode` enforces `TIFFTAG_IMAGEWIDTH`/`IMAGELENGTH`/`SAMPLESPERPIXEL`/
   `BITSPERSAMPLE` agreement with `im` before writing scanlines or running Predictor 2.
2. **In-memory stream seek/grow & stale-memory disclosure (`TiffDecode.c` `_tiffWriteProc` —
   `CVE-2026-112393`).**
   When libtiff seeks forward past the current end-of-buffer on `BytesIO`-backed writes, prove that
   grown regions are zero-initialized and bounds-checked before copying tag/ICC/pixel bytes.
3. **RLE & LZW decoder loops (`GifDecode.c`, `FliDecode.c`, `PcxDecode.c`, `SgiRleDecode.c`,
   `TgaRleDecode.c`, `BitDecode.c`, `RawDecode.c`).**
   Prove that `state->x`, `state->y`, `state->xoff`, `state->yoff`, `state->xsize`, `state->ysize`,
   `state->buffer` capacity, LZW stack/prefix/suffix tables (`4096` entries in `GifDecode.c`), and
   RLE run lengths never index outside `im->image[y]` or read past `buf + bytes`.
4. **Resampling filter-kernel window & coefficient overflow (`Resample.c`).**
   Prove that `precompute_coeffs` (`ksize`, `bounds[2*i]`, `bounds[2*i+1]`, `kk`) computes strictly
   in-bounds source row/column windows `[xmin, xmin + ksize) ⊆ [0, inSize]` without signed `int`
   overflow even for extreme resize aspect ratios or `box` crops.
5. **Row-pointer table (`im->image[y]`) & `Unpack.c` / `Pack.c` stride alignment.**
   Pillow supports both single-block and per-line block allocations (`ImagingNewBlock`) plus
   arbitrary raw modes (`RGB`, `RGBA`, `CMYK`, `YCbCr`, `LA`, `P;1..4`, `I;16*`, `F`). Prove every
   `ImagingShuffler` unpack/pack function stays within `[0, linesize]` for both source and dest.

## Bootstrap & Local Commands

When onboarding into `framework/projects.json`: copy `lean-toolchain`,
start `PillowF/Runtime/Ptr.lean` from `framework/lean/StrictPtr.lean`, model external codec &
CPython buffer contracts explicitly, wire `PillowF/Results.lean` and `project.json`, then run:

```bash
lake --dir projects/pillow build --wfail PillowF PillowF.Results
python3 framework/check_project.py pillow --skip-build
```
