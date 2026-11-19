# Working rules (`projects/sharp`)

Inherits all rules of the repository root [`../../AGENTS.md`](../../AGENTS.md), including the
**Strict ISO C17 Undefined Behaviour Policy** (`framework/check_runtime_ub.py` enforces this
mechanically on all C translation units):

- **No wild, uninitialised, freed/dangling, or `NULL` pointer `+ 0`**, **no `NULL - NULL`**, **no
  cross-object pointer subtraction or relational comparison**, **no out-of-bounds pointer
  formation**, **no zero-length `memcpy`/`memmove`/`memset`/`memcmp` on invalid pointers**, and
  **no arguing "benign UB"**.

- **Status:** Scoped umbrella & boundary audit (not yet registered in `framework/projects.json`).
  Because `lovell/sharp` itself is a ~8k LOC C++ Node-API (N-API) binding layer over `libvips` and
  its prebuilt `@img/sharp-libvips-*` C dependency stack, formal Lean 4 C17 proofs are decomposed
  across **`projects/libvips`** and the underlying pure-C codecs listed below, while this document
  pins the **exact Node.js -> C++ -> `libvips` -> C codec call graph** and Sharp's own C++ N-API
  boundary invariants.

## Architectural Decomposition (`lovell/sharp` + `lovell/sharp-libvips`)

- **Upstream source:** `https://github.com/lovell/sharp` (`src/*.cc`, `src/*.h`, `lib/*.js`) and
  `https://github.com/lovell/sharp-libvips` (`versions.properties` / `build/lin.sh`).
- **Why Sharp is a top-priority security target:** Sharp is the dominant Node.js image-processing
  library (Next.js `next/image`, Astro, Gatsby, Strapi, Directus, Payload CMS, serverless thumbnail
  pipelines, AI vision ingestion). In nearly all deployments, **untrusted user-uploaded bytes** flow
  directly into `sharp(buffer)` inside a multi-tenant Node.js process — any heap corruption in a
  bundled C library becomes server-side RCE or cross-tenant memory disclosure (demonstrated by
  `libwebp` `CVE-2023-4863`, `libvips` `CVE-2026-33327`, `CVE-2026-35591`, `CVE-2026-35590`).

### Complete `sharp-libvips` Native Dependency Audit (What to Prove vs. What Not to Prove)

Every prebuilt `@img/sharp-libvips-*` binary bundles the following native stack. Only pure-C
memory-unsafe components on reachable untrusted-input paths warrant Lean 4 C17 safety verification:

| Bundled Component | Role in Sharp | Language | Reachable on Untrusted Uploads? | `oss-proof` Target |
| --- | --- | --- | --- | --- |
| **`libvips`** (`foreign/`, `colour/`, `resample/`, `iofuncs/` + vendored **`libnsgif`**) | Pipeline orchestrator, format sniffer, loaders/savers, GIF decode, resize/thumbnail, EXIF/ICC plumbing | C (core & foreign) + C++ (wrappers/resample) | **Yes — 100% of calls** (`CVE-2026-33327`, `CVE-2026-35591`, `CVE-2026-35590`) | [`../libvips/AGENTS.md`](../libvips/AGENTS.md) |
| **`mozjpeg` / `libjpeg-turbo`** | JPEG decode (incl. shrink-on-load) & JPEG encode (`mozjpeg: true/false`) | Pure C (scalar) | **Yes — #1 input/output format** | [`../libjpeg-turbo/AGENTS.md`](../libjpeg-turbo/AGENTS.md) |
| **`libwebp`** | WebP lossy/lossless/animated decode & encode | Pure C (scalar) | **Yes — #1 modern web format** (`CVE-2023-4863`) | [`../libwebp/AGENTS.md`](../libwebp/AGENTS.md) |
| **`libspng`** | PNG decode & encode (Sharp uses `libspng`, NOT `libpng`, for PNG I/O) | Pure C (~4k LOC) | **Yes — #2 input/output format** | [`../libspng/AGENTS.md`](../libspng/AGENTS.md) |
| **`zlib` / `zlib-ng`** | Deflate/inflate inside `libspng`, `libtiff`, `libarchive` | Pure C | **Yes — every PNG & ZIP-TIFF** | [`../zlib/AGENTS.md`](../zlib/AGENTS.md) **(Done)** |
| **`libexif`** | EXIF parsing (`metadata()`, `rotate()`, `autoOrient()`, `keepExif()`) | Pure C (~10k LOC) | **Yes — nearly every JPEG/WebP/TIFF** | [`../libexif/AGENTS.md`](../libexif/AGENTS.md) |
| **`lcms2`** | Embedded ICC profile parsing & sRGB/CMYK color conversion | Pure C | **Yes — every image with ICC profile** | [`../lcms2/AGENTS.md`](../lcms2/AGENTS.md) |
| **`libtiff`** | TIFF multi-page/tiled/stripped decode & encode | Pure C | **Yes — auto-sniffed unless blocked!** | [`../libtiff/AGENTS.md`](../libtiff/AGENTS.md) |
| **`cgif`** | Animated & static GIF encode (`.gif()`) | Pure C (~2k LOC) | **Yes — GIF output re-encoding** | [`../cgif/AGENTS.md`](../cgif/AGENTS.md) |
| **`expat`** | XMP XML metadata parsing (embedded in JPEG/PNG/WebP/TIFF) & fontconfig/SVG XML | Pure C (~20k LOC) | **Yes — every image with XMP metadata** | [`../expat/AGENTS.md`](../expat/AGENTS.md) |
| **`libarchive`** | Deep Zoom `.zip` tile-pyramid output (`.tile()`) | Pure C | Secondary (output path only in Sharp) | [`../libarchive/AGENTS.md`](../libarchive/AGENTS.md) |
| **`freetype`** (+ `harfbuzz`/`fribidi`/`pango`/`cairo`/`pixman`/`fontconfig`/`libxml2`) | Text rendering (`create: { text }`) & SVG rasterization backend | Pure C / C++ | Secondary (SVG & text-overlay paths) | [`../freetype/AGENTS.md`](../freetype/AGENTS.md) |
| **`libheif` + `libaom` / `libde265`** | AVIF / HEIC decode & encode (`.avif()`, `.heif()`) | C++ (`libheif`/`libde265`) + huge C (`libaom` ~400k LOC) | Yes (AVIF/HEIC uploads) | Not planned for direct C17 translation (C++ / codebase size); see [`../libavif/AGENTS.md`](../libavif/AGENTS.md) for pure-C AVIF container verification |
| **`librsvg`**, **`libimagequant`** | SVG parsing/rendering; PNG palette quantization (`palette: true`) | **Rust** (memory-safe) | Yes, but already Rust | **Out of scope** (already memory-safe except C FFI boundary to `cairo`/`libxml2`) |
| **`glib` / `gobject` / `libffi` / `highway`** | GObject runtime, SIMD dispatch | C / C++ | Infrastructure | **Out of scope** (runtime infrastructure; disable SIMD/Highway in scalar verification targets) |

## Real-World Node.js Usage Paths & Exact Call Graph

Over 95% of real-world Sharp traffic falls into **six concrete JavaScript pipelines**. Tracing each
through `lovell/sharp/src/*.cc` identifies the exact native functions that truly matter:

### Path 1: Untrusted Upload -> Resize / Thumbnail -> WebP / JPEG / PNG (The #1 Web Pipeline)
```js
await sharp(userBuffer)
  .rotate()               // auto-orient from EXIF
  .resize(800, 600, { fit: 'cover' })
  .webp({ quality: 80 })  // or .jpeg({ mozjpeg: true }) / .png()
  .toBuffer();
```
- **Sharp C++ (`src/pipeline.cc` `PipelineWorker::Execute`, `src/common.cc` `OpenInput`):**
  1. Sniffs buffer format via `vips_foreign_find_load_buffer` (CRITICAL: an attacker uploading a
     `.jpg` filename containing TIFF, GIF, SVG, or `.vips` bytes triggers **any enabled loader**
     unless `sharp.block()` disables unused `VipsForeignLoad*` operations!).
  2. Opens input with shrink-on-load (`vips_jpegload_buffer` with `shrink=2/4/8`, `vips_webpload_buffer`
     with `scale`, `vips_spngload_buffer`, `vips_nsgifload_buffer`, `vips_tiffload_buffer`,
     `vips_heifload_buffer`) guarded by `limitInputPixels` (default `268402689` = `16384^2`).
  3. Reads EXIF orientation via `libvips/foreign/exif.c` -> `libexif` (`exif_data_new_from_data`),
     rotates via `vips_autorot` / `vips_rot`.
  4. Normalizes color space / embedded ICC profile via `vips_icc_transform` -> `lcms2`
     (`cmsOpenProfileFromMem`, `cmsCreateTransform`, `cmsDoTransform`).
  5. Resizes via `vips_shrink` + `vips_reduce` (Lanczos3 default) + optional `vips_extract_area` /
     `vips_embed`.
  6. Encodes output via `vips_webpsave_buffer` (`libwebp`), `vips_jpegsave_buffer` (`mozjpeg` /
     `libjpeg-turbo`), `vips_spngsave_buffer` (`libspng` + `zlib`), or `vips_cgifsave_buffer` (`cgif`).

### Path 2: Fast Upload Validation & Inspection (`.metadata()` / `.stats()`)
```js
const meta = await sharp(userBuffer).metadata();
```
- **Sharp C++ (`src/metadata.cc` `MetadataWorker::Execute`, `src/stats.cc`):**
  Calls `OpenInput` -> format sniffer -> header-only decode (`jpeg_read_header`, `WebPGetFeatures`,
  `spng_get_ihdr`, `TIFFClientOpen` + `TIFFGetField`, `nsgif_process_data`), extracts `VIPS_META_EXIF_NAME`
  (`libexif`), `VIPS_META_ICC_NAME` (`lcms2` profile header), `VIPS_META_XMP_NAME` (`expat`), and
  dimensions/bands/alpha. **Notice:** `.metadata()` runs before any user validation code and is
  therefore the first untrusted-byte parser exposed on upload endpoints!

### Path 3: Re-encoding / Format Transcoding & Metadata Stripping / Preservation
```js
await sharp(userBuffer).keepIccProfile().jpeg({ mozjpeg: true }).toBuffer();
await sharp(userBuffer).png({ compressionLevel: 9, palette: true }).toBuffer();
await sharp(userBuffer).gif().toBuffer();
```
- Exercises **encoder paths** (`libjpeg-turbo`/`mozjpeg` `jc*.c`, `libspng` `spng_encode_image`,
  `libwebp` `WebPEncode`/`WebPAnimEncoder*`, `cgif` `cgif_newgif`/`cgif_addframe`, `libtiff`
  `TIFFWriteScanline`/`TIFFWriteTile`) plus metadata re-serialization (`exif_data_save_data` in
  `libexif`, ICC/XMP chunk injection).

### Path 4: Compositing, Cropping, Watermarking & Raw Pixel Buffers (AI / Vision Pipelines)
```js
await sharp(userBuffer).extract(rect).composite([{ input: overlay }]).raw().toBuffer();
await sharp(rawUint8Array, { raw: { width, height, channels } }).png().toBuffer();
```
- **Sharp C++ (`src/pipeline.cc`, `src/operations.cc`):** `vips_extract_area`, `vips_composite2`,
  `vips_flatten`, `vips_bandjoin`, `vips_colourspace`, `vips_image_new_from_memory` (raw buffer
  length validation: `raw.width * raw.height * raw.channels * bytesPerSample <= buffer.byteLength`!).

### Path 5: Animated GIF / WebP Multi-Page Processing
```js
await sharp(userBuffer, { animated: true }).resize(400).webp().toBuffer();
```
- Exercises `libvips` `nsgifload.c` + vendored `libnsgif`, `libwebp` `WebPDemux*`/`WebPAnimEncoder*`,
  `cgif` `cgif_addframe`, and `libvips` toilet-roll multi-page height limits (`pages`, `pageHeight`).

### Path 6: Explicit Attack-Surface Hardening (`sharp.block()`)
- **Critical finding from 2026 CVEs (`CVE-2026-33327`, `CVE-2026-35591`):** Because `libvips`
  auto-sniffs formats from magic bytes, disabling unused loaders via `sharp.block({ operation: [...] })`
  (notably `VipsForeignLoadVips`, `VipsForeignLoadTiff`, `VipsForeignLoadNsgif`, `VipsForeignLoadSvg`,
  `VipsForeignLoadHeif`) dramatically shrinks the reachable native parser surface. Every enabled
  loader must be treated as internet-facing untrusted input.

## Sharp C++ Boundary Invariants (What Matters Inside `lovell/sharp/src/` Itself)

Even once the underlying C codecs are verified, Sharp's own C++ N-API bridge (`src/pipeline.cc`,
`src/metadata.cc`, `src/operations.cc`, `src/common.cc`, `src/stats.cc`) owns five critical safety
boundaries that must be audited and kept invariant:

1. **N-API Buffer Ownership & Async Worker Lifetimes (`src/common.cc` `InputDescriptor`, `FreeCallback`):**
   Async `Napi::AsyncWorker` jobs execute `libvips` pipelines on libuv worker threads while V8 runs
   concurrently; `Napi::Reference` pinning on input `Buffer`/`TypedArray` objects must outlive
   `VipsSource` / `vips_image_new_from_memory` zero-copy reads (no UAF on GC).
2. **`raw` Input Geometry Overflow Checks (`src/common.cc` `CreateInputDescriptor`):**
   When constructing images from caller-supplied `{ raw: { width, height, channels } }`, multiplying
   `width * height * channels * sizeof(sample)` must use overflow-checked `size_t` arithmetic before
   comparing against `bufferLength`.
3. **`limitInputPixels` & Multi-Page `pages` Enforcement (`src/pipeline.cc`, `src/common.cc`):**
   Must reject overflows in `width * height * pages` before full pixel decoding allocates giant
   buffers.
4. **Error-Buffer Hygiene & Partial-Failure Cleanup:**
   Every libvips failure path must drain `vips_error_buffer()` / `vips_error_clear()` and release
   allocated output buffers (`g_free`) cleanly without double-free or leak.
5. **No Implicit Format Escalation:**
   File-extension / user-declared format never restricts `libvips` sniffing; security boundaries
   must assume any input buffer can trigger any unblocked `VipsForeignLoad*` subclass.

## Verification Execution Order for Sharp Coverage

To eliminate memory-safety risk in production Sharp deployments in highest ROI order:
1. **Wave 1 (Fastest Wins + Highest Traffic):** [`zlib`](../zlib/AGENTS.md) *(Done)* ->
   [`libspng`](../libspng/AGENTS.md) (~4k LOC, all Sharp PNG) -> [`cgif`](../cgif/AGENTS.md) (~2k LOC,
   all Sharp GIF encode) -> [`libexif`](../libexif/AGENTS.md) (~10k LOC, all Sharp EXIF/autoOrient).
2. **Wave 2 (Critical Web Codecs):** [`libwebp`](../libwebp/AGENTS.md) (WebP decode+encode,
   `CVE-2023-4863`) -> [`libjpeg-turbo`](../libjpeg-turbo/AGENTS.md) (JPEG/mozjpeg decode+encode) ->
   [`lcms2`](../lcms2/AGENTS.md) (embedded ICC profiles) -> [`expat`](../expat/AGENTS.md) (XMP XML).
3. **Wave 3 (Core Engine & Highest-CVE Format):** [`libvips`](../libvips/AGENTS.md) (foreign
   loaders/savers, vendored `libnsgif`, `exif.c`, `icc_transform.c`, `vipsload.c`, `resample/`) ->
   [`libtiff`](../libtiff/AGENTS.md) (TIFF decode+encode, `CVE-2026-35591`).
4. **Wave 4 (Secondary Sharp Paths):** [`libarchive`](../libarchive/AGENTS.md) (Deep Zoom ZIP) and
   [`freetype`](../freetype/AGENTS.md) (SVG/text rendering).
