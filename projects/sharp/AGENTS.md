# Working rules (`projects/sharp`)

Inherits every rule of the repository root [`../../AGENTS.md`](../../AGENTS.md), including the strict
ISO C17 undefined-behaviour policy.

- **Status:** umbrella. Upstream submodule `sharp/` tracks the latest upstream default branch. Sharp
  itself is C++ Node-API glue and gets no Lean package; its untrusted-input paths are proved in the
  C libraries listed below.

## What ships (measured, not assumed)

Measured by installing `sharp@0.35.5` from npm on Linux x86_64 and reading `sharp.versions` and
`sharp.format`, cross-checked against the build script of the prebuilt `@img/sharp-libvips-*`
packages:

- **Bundled C/C++ stack:** libvips 8.18.7, mozjpeg `0826579` (libjpeg-turbo fork), libpng 1.6.58,
  libwebp 1.6.0, libtiff 4.7.2, libexif 0.6.26, lcms 2.19.1, cgif 0.5.4, libimagequant 2.4.1 (the C
  fork), zlib-ng 2.3.3, libheif 1.23.5 + aom 3.15.1, librsvg 2.63.2 (Rust) + libxml2 2.15.4 + cairo
  / pixman / pango / harfbuzz / freetype / fontconfig, libarchive 3.8.9, expat 2.8.5, libultrahdr
  2.0.2. libvips is built with `-Dspng=disabled`: **PNG goes through libpng, not libspng.**
- **Input formats:** jpeg, png, webp, tiff, gif, svg, heif/avif (file, buffer, stream); vips
  (file only); raw pixels. **Output:** jpeg, png, webp, tiff, gif, heif/avif, dz (tile pyramid),
  raw. Not available in the prebuilt binary: jp2, jxl, pdf, magick, openslide, fits, ppm, rad.

## How untrusted bytes reach C

1. `sharp(input)` and `.metadata()` both go through `src/common.cc` `OpenInput`, which calls
   `vips_foreign_find_load_buffer` (magic-byte sniffing — the file name or MIME type is never
   consulted) and then `VImage::new_from_buffer` with the chosen loader. A buffer whose loader is
   not in sharp's `loaderToType` table is rejected.
2. Resizing re-opens JPEG with `jpegload_buffer` + `shrink` (2/4/8) and WebP with
   `webpload_buffer` + `scale` (shrink-on-load, `src/pipeline.cc`).
3. libvips flags `svgload`, `heifload` and `vipsload` as untrusted, but they are blocked only when
   `VIPS_BLOCK_UNTRUSTED` is set or the application calls `sharp.block()`. **By default SVG and
   HEIF/AVIF buffers are accepted.**
4. Any loader that attaches an EXIF blob triggers `vips__exif_parse` from `vips_image_set`
   (`libvips/iofuncs/header.c`), so libexif runs during the header read — including
   `.metadata()`.
5. An embedded ICC profile is converted with `icc_transform` / `icc_import` (lcms2) in
   `src/pipeline.cc` unless the caller keeps the profile; CMYK input is always converted.

| Sharp call | libvips file | C library reached | Proof target |
| --- | --- | --- | --- |
| JPEG in / `.jpeg()` | `foreign/jpeg2vips.c`, `foreign/vips2jpeg.c` | mozjpeg | [`mozjpeg`](../mozjpeg/AGENTS.md) |
| PNG in / `.png()` | `foreign/vipspng.c` | libpng → zlib-ng | [`libpng`](../libpng/AGENTS.md), `zlib-ng` |
| WebP in / `.webp()` | `foreign/webp2vips.c`, `foreign/webpsave.c` | libwebp | [`libwebp`](../libwebp/AGENTS.md) |
| TIFF in / `.tiff()` | `foreign/tiff2vips.c`, `foreign/vips2tiff.c` | libtiff (+ mozjpeg, zlib-ng) | [`libtiff`](../libtiff/AGENTS.md) |
| GIF in | `foreign/nsgifload.c` | vendored libnsgif | [`libvips`](../libvips/AGENTS.md) |
| `.gif()` | `foreign/cgifsave.c`, `foreign/quantise.c` | cgif, libimagequant | [`cgif`](../cgif/AGENTS.md) |
| Any input with EXIF | `foreign/exif.c` | libexif | [`libexif`](../libexif/AGENTS.md) |
| Any input with ICC, CMYK | `colour/icc_transform.c` | lcms2 | [`lcms2`](../lcms2/AGENTS.md) |
| SVG in | `foreign/svgload.c` | librsvg (Rust) → libxml2 (SAX parser), cairo | [`libxml2`](../libxml2/AGENTS.md) |
| HEIF/AVIF in / `.avif()` | `foreign/heifload.c`, `foreign/heifsave.c` | libheif (C++) → aom | not planned (C++, large codec) |
| `.tile()` zip output | `foreign/dzsave.c` | libarchive (write only) | `libarchive` (existing project) |

## Sharp's own C++ boundary (review items, not Lean goals)

- Raw pixel input: `width * height * channels * bytes-per-sample` must match the buffer before
  `VImage::new_from_memory`.
- `limitInputPixels`, `failOn` and multi-page `pages` / `pageHeight` must be enforced before full
  decode.
- Input `Buffer` objects must stay referenced while libvips reads them on worker threads.
