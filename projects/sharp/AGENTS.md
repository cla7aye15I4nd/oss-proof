# Working rules (`projects/sharp`)

Inherits every rule of the repository root [`../../AGENTS.md`](../../AGENTS.md).

**Status:** umbrella. Upstream submodule `sharp/` tracks the latest default branch. Sharp is C++
Node-API glue and gets no Lean package; its Tier 0 code is proved in the libraries below.

## Tier 0

Tier 0 is the code that turns untrusted bytes into pixels or metadata on a default path.

**How bytes reach C.** `sharp(input)`, `.metadata()` and every pipeline go through
`src/common.cc` `OpenInput`, which calls `vips_foreign_find_load_buffer` (magic bytes only; the
file name and MIME type are never consulted) and `VImage::new_from_buffer`. Resizing reopens JPEG
with `jpegload_buffer` + `shrink` and WebP with `webpload_buffer` + `scale`. Any loader that
attaches EXIF triggers `vips__exif_parse` from `vips_image_set`; an embedded ICC profile is
converted by `icc_transform` unless the caller keeps it. SVG and HEIF/AVIF are flagged untrusted in
libvips but accepted unless the application sets `VIPS_BLOCK_UNTRUSTED` or calls `sharp.block()`.

**What ships** (measured from `sharp@0.35.5`): libvips 8.18.7 built with `-Dspng=disabled`,
mozjpeg (the only JPEG implementation), libpng, libwebp, libtiff, libexif, lcms2, zlib-ng,
librsvg + libxml2, libheif + aom, all statically linked into `libvips-cpp`.

| Input | libvips code | Tier 0 library |
| --- | --- | --- |
| JPEG | `foreign/jpeg2vips.c` `read_jpeg_header`, `read_jpeg_image` | [`mozjpeg`](../mozjpeg/AGENTS.md) |
| PNG | `foreign/vipspng.c` `read_new`, `png2vips_header` | [`libpng`](../libpng/AGENTS.md) → `zlib-ng` |
| WebP | `foreign/webp2vips.c` `read_header`, `read_frame` | [`libwebp`](../libwebp/AGENTS.md) |
| TIFF | `foreign/tiff.c` `vips__tiff_openin_source`, `foreign/tiff2vips.c` `rtiff_header_read` | [`libtiff`](../libtiff/AGENTS.md) (+ mozjpeg, zlib-ng) |
| GIF | `foreign/nsgifload.c` + vendored libnsgif | [`libvips`](../libvips/AGENTS.md) |
| SVG | `foreign/svgload.c` → librsvg (Rust) | [`libxml2`](../libxml2/AGENTS.md) |
| any input with EXIF | `iofuncs/header.c` → `foreign/exif.c` | [`libexif`](../libexif/AGENTS.md) |
| any input with ICC, CMYK | `colour/icc_transform.c` | [`lcms2`](../lcms2/AGENTS.md) |

HEIF/AVIF (libheif is C++, aom is a large codec) and all encoders are outside Tier 0.
