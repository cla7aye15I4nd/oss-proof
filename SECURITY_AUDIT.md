# Security Verification Target Audit & Portfolio Roadmap (`oss-proof`)

This document records the systematic selection and deep real-world call-path audit of the open-source
C repositories most worth formal ISO C17 safety verification in `oss-proof`, covering:

1. **Compression and archive libraries — explicitly covering BOTH decompression/read AND
   compression/write paths**;
2. **Sharp (Node.js) and PIL / Pillow (Python)** — full end-to-end tracing from JavaScript/Python
   production APIs down to every native C file and underlying C codec dependency;
3. **Shared high-exposure C parsers and image/metadata/color/font engines** whose verification
   eliminates memory-corruption risk simultaneously across Node.js, Python, browsers, and cloud
   infrastructure.

Every selected repository has its own dedicated `projects/<id>/AGENTS.md` specifying exact upstream
translation units, real-world usage paths, Tier 1 (P0) vs. Tier 2 (P1) vs. Out-of-Scope functions,
library-specific ISO C17 UB hazards, and real CVE anchors.

---

## 1. Selection Criteria

Each repository was scored across four criteria:

1. **Untrusted-input exposure (both decode AND encode):** Processes attacker-controlled bytes in
   internet-facing servers, browsers, Node.js (`sharp`, `node:zlib`), Python (`Pillow`, `zlib`,
   `bz2`, `lzma`, `zstd`, `expat`), or OS package managers.
2. **Real-world memory-safety vulnerability density:** Confirmed heap overflows, integer overflows,
   out-of-bounds reads/writes, use-after-free, or ISO C17 pointer/arithmetic UB — notably the
   **2023–2026 CVE wave** across compression, archive, and image pipelines.
3. **Ecosystem multiplier:** Proving one pure-C library protects multiple major stacks at once
   (e.g., `libjpeg-turbo`, `libwebp`, `libtiff`, and `lcms2` protect **both Sharp and Pillow** plus
   browsers/OSes).
4. **Verification tractability under `oss-proof`'s ISO C17 LP64 model:** Self-contained pure-C core
   with a portable scalar build configuration (disabling SIMD/ASM and threads), or a cleanly
   isolated C/C++ boundary decomposition.

### Why Compression / Encode / Write Paths Matter Alongside Decompression

Decompression is not the only memory-safety hazard. Production services routinely **re-compress,
re-encode, or repackage untrusted user uploads and attacker-influenced data** (HTTP responses,
avatar/thumbnail re-encoding, TIFF/JPEG/PNG/WebP/GIF output, ZIP/TAR archive generation). Real
vulnerabilities confirm severe memory corruption on compression/write paths:

- **Pillow (`CVE-2026-112393` & `CVE-2026-128067`):** Heap buffer overflows and stale-heap memory
  disclosure when **saving/encoding** compressed TIFFs (`TiffDecode.c` `_tiffWriteProc` and
  `ImagingLibTiffEncode` + Predictor 2)!
- **libarchive (`CVE-2026-16517`):** Signed integer overflow in the **ZIP writer**
  (`archive_write_set_format_zip.c`) when encryption metadata pushes entry size past `INT64_MAX`.
- **Zstandard (`CVE-2019-11922`):** Out-of-bounds write in compression when given a tight
  destination buffer smaller than recommended bounds.
- **zlib (`projects/zlib/patches/0006` & `0007`):** Real `deflateBound` under-sizing defects found
  directly during `oss-proof` formal verification!

Accordingly, `projects/zstd`, `projects/brotli`, `projects/7zip`, `projects/libarchive`, and all
newly selected compression and image codec projects explicitly include **both** decode/decompress
and encode/compress paths in their `AGENTS.md`.

---

## 2. Deep Audit: Sharp (Node.js) vs. PIL / Pillow (Python)

Both Sharp and Pillow sit at the exact same dangerous boundary in modern backends (web upload
endpoints, CDN/Next.js image optimizers, AI/LLM vision ingestion): **untrusted bytes from the
internet enter a high-level memory-safe runtime (JS/Python) and immediately execute unsafe C**.
However, their internal native architectures differ sharply:

### Sharp (Node.js): Thin C++ N-API Bridge -> `libvips` -> Bundled `sharp-libvips` C Codecs

- **`lovell/sharp` itself** (`src/pipeline.cc`, `src/metadata.cc`, `src/operations.cc`,
  `src/common.cc`, `src/stats.cc`) is ~8k LOC of C++ N-API glue. Its main risks are N-API async
  buffer pinning, `{ raw }` geometry overflow, `limitInputPixels`, and **format auto-sniffing**
  (`vips_foreign_find_load_buffer` lets an attacker upload TIFF/GIF/VIPS/SVG bytes disguised as
  `.jpg` unless blocked via `sharp.block()`).
- **Important nuance discovered in audit:**
  - Sharp uses **`libspng`** (~4k LOC pure C, built on proved `zlib`) — **NOT `libpng`** — for PNG
    decode and encode!
  - Sharp uses **`libvips`'s vendored `libnsgif`** (pure C) for GIF decode, and **`cgif`** (~2k LOC
    pure C) for GIF encode.
  - Sharp's bundled **`librsvg`** (SVG) and **`libimagequant`** (PNG palette quantization) are now
    **Rust** (already memory-safe outside C FFI boundaries), so formal C17 effort should focus on
    the **pure-C memory-unsafe libraries** instead: `libspng`, `cgif`, `libexif`, `libwebp`,
    `libjpeg-turbo` (`mozjpeg`), `lcms2`, `expat`, `libvips` C core (`vipsload.c`, `tiffload.c`,
    `exif.c`, `libnsgif`, `icc_transform.c`, `resample/`), `libtiff`, `libarchive`, `freetype`.
- See [`projects/sharp/AGENTS.md`](projects/sharp/AGENTS.md) and
  [`projects/libvips/AGENTS.md`](projects/libvips/AGENTS.md).

### PIL / Pillow (Python): ~30k LOC Pure-C `src/libImaging/` Core + External C Codecs

- **Unlike Sharp, Pillow owns a massive pure-C imaging core (`src/libImaging/`)** compiled directly
  into `_imaging.so`, where Pillow's own 2026 CVEs live (`CVE-2026-112403` in `JpegDecode.c`,
  `CVE-2026-112393` and `CVE-2026-128067` in `TiffDecode.c`) alongside historical CVEs in
  `FliDecode.c`, `PcxDecode.c`, `SgiRleDecode.c`, `TgaRleDecode.c`, `GifDecode.c`, `RawDecode.c`,
  `Resample.c`, and `Alloc.c`.
- **Important nuances discovered in audit:**
  - Pillow does **NOT** link `libpng` — PNG is parsed in Python (`PngImagePlugin.py`) and
    compressed/decompressed through `src/libImaging/ZipDecode.c` / `ZipEncode.c` -> **`zlib`**
    (already proved in `projects/zlib`!).
  - Pillow handles GIF completely inside `src/libImaging/GifDecode.c` & `GifEncode.c` (pure C), and
    auto-sniffs legacy RLE/raster formats (`FLI`, `PCX`, `SGI`, `TGA`, `BMP`, `ICO`) on every
    `Image.open(untrusted_bytes)` call!
  - Pillow delegates JPEG, WebP, TIFF, AVIF (11.3+), JPEG 2000, ICC color management, and font
    rendering to **`libjpeg-turbo`**, **`libwebp`**, **`libtiff`**, **`libavif`**, **`openjpeg`**,
    **`lcms2`**, and **`freetype`**.
  - Pure-Python subprocess flaws (e.g., `CVE-2026-112900` Ghostscript argument injection in
    `EpsImagePlugin.py`) are outside C memory safety and explicitly marked out of scope.
- See [`projects/pillow/AGENTS.md`](projects/pillow/AGENTS.md).

---

## 3. Complete Selected Portfolio (23 Projects)

### Pillar 1 — Core Compression Libraries (Both Decompress & Compress)

| Project | Upstream | Repo Status | Real-World Reach | Key Recent / Historic CVEs | `AGENTS.md` |
| --- | --- | --- | --- | --- | --- |
| **`zlib`** | `madler/zlib` | Registered (**Done**, 86/86) | Universal: Pillow PNG/ZIP, `libspng`, `libpng`, `libtiff`, Node.js, Python, `libarchive` | 8 findings & 7 patches in `oss-proof` | [`projects/zlib/AGENTS.md`](projects/zlib/AGENTS.md) |
| **`zstd`** | `facebook/zstd` | Registered (Runtime checked) | Node.js `node:zlib`, Python 3.14 `compression.zstd`, HTTP zstd, Parquet, RocksDB, Linux | `CVE-2019-11922` (compress OOB), `extDict` pointer UB | [`projects/zstd/AGENTS.md`](projects/zstd/AGENTS.md) |
| **`brotli`** | `google/brotli` | Registered (Runtime checked) | Node.js `node:zlib`, Nginx `ngx_brotli`, Envoy, Cloudflare, Chrome/Firefox, WOFF2 | **`CVE-2026-111497`** ("Node2Shell" CVSS 9.2–9.8 OOB write in `decode.c`) | [`projects/brotli/AGENTS.md`](projects/brotli/AGENTS.md) |
| **`lz4`** | `lz4/lz4` | Scoped candidate (~5k LOC) | Linux kernel, Kafka, Parquet/Arrow, ClickHouse, RocksDB, ZFS, Python/Node.js `lz4` | **`CVE-2021-3520`** (CVSS 9.8 int overflow -> negative `memmove`), `CVE-2019-17543` | [`projects/lz4/AGENTS.md`](projects/lz4/AGENTS.md) |
| **`xz`** | `tukaani-project/xz` | Scoped candidate (`liblzma`) | Python stdlib `lzma`, `tar -J`, `.deb`/RPM, `libarchive`, systemd, kernel | `CVE-2025-31115`, `CVE-2026-34743`, `CVE-2024-3094` (supply chain) | [`projects/xz/AGENTS.md`](projects/xz/AGENTS.md) |
| **`bzip2`** | `sourceware.org/bzip2` | Scoped candidate (~4k LOC) | Python stdlib `bz2`, `tar -j`, `libarchive`, dpkg/RPM | **`CVE-2019-12900`** (`BZ2_decompress` selector OOB write) | [`projects/bzip2/AGENTS.md`](projects/bzip2/AGENTS.md) |

### Pillar 2 — Multi-Format Archive Libraries (Both Read & Write)

| Project | Upstream | Repo Status | Real-World Reach | Key Recent / Historic CVEs | `AGENTS.md` |
| --- | --- | --- | --- | --- | --- |
| **`7zip`** | `ip7z/7zip` (`C/` SDK) | Registered (Models + runtime) | AV/malware scanners, firmware/UEFI/SquashFS, installers, `py7zr` | `.7z` DAG/PPMd7/BCJ2/LZMA integer & OOB classes | [`projects/7zip/AGENTS.md`](projects/7zip/AGENTS.md) |
| **`libarchive`** | `libarchive/libarchive` | Registered (Models + runtime) | macOS/Windows/FreeBSD `tar`, `pacman`, `pkg`, CMake, `sharp-libvips`, Python | **`CVE-2026-15028`** (PAX), **`CVE-2026-16517`** (ZIP write), **`CVE-2026-17591`** (UAF), `CVE-2025-5918` | [`projects/libarchive/AGENTS.md`](projects/libarchive/AGENTS.md) |

### Pillar 3 — Sharp (Node.js) & PIL / Pillow (Python) Native Engines

| Project | Upstream | Repo Status | Real-World Reach | Key Recent / Historic CVEs | `AGENTS.md` |
| --- | --- | --- | --- | --- | --- |
| **`sharp`** | `lovell/sharp` + `sharp-libvips` | Scoped umbrella & C++ audit | #1 Node.js image processor (Next.js, CMSs, serverless, AI pipelines) | Inherits `libvips`, `libwebp`, `libtiff`, `libexif` CVEs | [`projects/sharp/AGENTS.md`](projects/sharp/AGENTS.md) |
| **`libvips`** | `libvips/libvips` | Scoped candidate (C core) | Powers Sharp, `pyvips`, `ruby-vips`, `govips` (incl. vendored `libnsgif`) | **`CVE-2026-33327`** (`vipsload`), **`CVE-2026-35591`** (`tiffload`), **`CVE-2026-35590`** (`exif.c`) | [`projects/libvips/AGENTS.md`](projects/libvips/AGENTS.md) |
| **`pillow`** | `python-pillow/Pillow` (`src/libImaging/`) | Scoped candidate (~30k LOC C) | #1 Python image library (Django/FastAPI, PyTorch, HuggingFace, OCR) | **`CVE-2026-112403`** (`JpegDecode`), **`CVE-2026-112393`** & **`CVE-2026-128067`** (`TiffDecode` save!) | [`projects/pillow/AGENTS.md`](projects/pillow/AGENTS.md) |

### Pillar 4 — Shared Image Codecs, Metadata, Color, Font & XML C Libraries

| Project | Upstream | Used By | Approx. C Scope | Key Recent / Historic CVEs | `AGENTS.md` |
| --- | --- | --- | --- | --- | --- |
| **`libspng`** | `randy408/libspng` | **Sharp** (ALL PNG decode & encode) | ~4k LOC (on proved `zlib`) | Highest-ROI Sharp PNG target | [`projects/libspng/AGENTS.md`](projects/libspng/AGENTS.md) |
| **`cgif`** | `dloebl/cgif` | **Sharp** (ALL GIF encode) | ~2k LOC | Smallest Sharp encoder target | [`projects/cgif/AGENTS.md`](projects/cgif/AGENTS.md) |
| **`libexif`** | `libexif/libexif` | **Sharp** (EXIF/`autoOrient` on every JPEG/WebP/TIFF) | ~10k LOC | `CVE-2020-13112`/`13113`/`13114`/`0452`/`0198` | [`projects/libexif/AGENTS.md`](projects/libexif/AGENTS.md) |
| **`libwebp`** | `webmproject/libwebp` | **Sharp + Pillow** + all browsers/OSes | ~40k LOC scalar | **`CVE-2023-4863`** (VP8L `BuildHuffmanTable` 0-day RCE) | [`projects/libwebp/AGENTS.md`](projects/libwebp/AGENTS.md) |
| **`libjpeg-turbo`** | `libjpeg-turbo/libjpeg-turbo` | **Sharp (`mozjpeg`) + Pillow** + browsers | ~40k LOC scalar | `CVE-2021-29390`, `CVE-2023-2804` | [`projects/libjpeg-turbo/AGENTS.md`](projects/libjpeg-turbo/AGENTS.md) |
| **`libpng`** | `pnggroup/libpng` | Browsers, Cairo (Sharp SVG), OpenCV, matplotlib | ~35k LOC (on proved `zlib`) | **`CVE-2025-65018`/`64720`/`64505`**, **`CVE-2026-22695`/`25646`/`33416`/`34757`** | [`projects/libpng/AGENTS.md`](projects/libpng/AGENTS.md) |
| **`libtiff`** | `libtiff/libtiff` | **Sharp + Pillow** + PDF/OCR/GDAL | ~50k LOC | Highest CVE density; `CVE-2026-35591` & `CVE-2026-128067` surface | [`projects/libtiff/AGENTS.md`](projects/libtiff/AGENTS.md) |
| **`lcms2`** | `mm2/Little-CMS` | **Sharp + Pillow** + Chrome/Firefox/OpenJDK | ~35k LOC | `CVE-2018-16435`, LUT/tag/CLUT overflows | [`projects/lcms2/AGENTS.md`](projects/lcms2/AGENTS.md) |
| **`expat`** | `libexpat/libexpat` | **Sharp** (XMP/SVG) + **Python stdlib** XML | ~20k LOC (4 `.c` files) | **`CVE-2024-45490`/`45491`/`45492`**, **`CVE-2026-77214`/`118370`** | [`projects/expat/AGENTS.md`](projects/expat/AGENTS.md) |
| **`libavif`** | `AOMediaCodec/libavif` | **Pillow 11.3+** (native AVIF) + browsers | ~15k LOC container/reformat | **`CVE-2025-48174`** (`stream.c` int/buffer overflow) | [`projects/libavif/AGENTS.md`](projects/libavif/AGENTS.md) |
| **`openjpeg`** | `uclouvain/openjpeg` | **Pillow** (JPEG 2000) + PDFium/Poppler/MuPDF | ~50k LOC scalar | High historical J2K/TCD/T1/T2/DWT OOB density | [`projects/openjpeg/AGENTS.md`](projects/openjpeg/AGENTS.md) |
| **`freetype`** | `freetype/freetype` | **Pillow** (`ImageFont`) + **Sharp** (SVG/text) + OSes | Scoped SFNT/TT/CFF/smooth core | `CVE-2020-15999`, TrueType/CFF VM hazards | [`projects/freetype/AGENTS.md`](projects/freetype/AGENTS.md) |

---

## 4. Recommended Execution Waves (ROI-Ordered)

1. **Wave 1 — Fastest High-Impact Wins (Small Pure-C Libraries, 2k–10k LOC):**
   `lz4`, `bzip2`, `libspng` (secures all Sharp PNG on top of proved `zlib`), `cgif` (all Sharp GIF
   encode), `libexif` (all Sharp EXIF/`autoOrient`), plus closing `zlib`'s legacy `Ptr.add 0` /
   `NULL - NULL` debt.
2. **Wave 2 — Critical Compression & Web-Image Codecs (15k–40k LOC):**
   `brotli` (decode + encode; blocks `CVE-2026-111497` class), `zstd` (decode + encode), `expat`
   (Python XML + Sharp XMP), `libwebp` (Sharp + Pillow; blocks `CVE-2023-4863` class),
   `libjpeg-turbo` (Sharp + Pillow), `libavif` (Pillow AVIF), `libpng` (2025–2026 CVE wave).
3. **Wave 3 — Sharp & Pillow Native Cores + Highest-CVE Parsers:**
   `pillow` (`src/libImaging/` — blocks `CVE-2026-112403`/`112393`/`128067` + all RLE/GIF/Resample
   paths), `libvips` (foreign loaders/savers + vendored `libnsgif` + `exif.c` + `vipsload.c` +
   `tiffload.c`), `lcms2` (Sharp + Pillow ICC), `libtiff` (Sharp + Pillow TIFF).
4. **Wave 4 — Large Multi-Format Archives, XZ & Font Engines:**
   `xz` (`liblzma` decode + encode), `libarchive` (TAR/PAX + ZIP read/write + RAR5 + 7-Zip),
   `7zip` (C SDK decode + encode), `openjpeg`, `freetype` (scoped SFNT/TrueType/CFF/smooth).

*(Note: Only the five projects listed in `framework/projects.json` — `zlib`, `7zip`, `libarchive`,
`zstd`, and `brotli` — currently have Lean packages registered in CI. All 18 additional candidate
directories under `projects/<id>/` currently contain their scoped `AGENTS.md` audit specifications
and pinned upstream submodules (`projects/<id>/<id>`), and will be registered in
`framework/projects.json` as each project bootstraps its strict ISO C17 Lean runtime from
`framework/lean/StrictPtr.lean`.)*
