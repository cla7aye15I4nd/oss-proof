# Which C code Sharp and Pillow actually run on untrusted images

## How to read this page {#evidence}

**Tier 0** is the code that turns untrusted bytes into pixels or metadata on a default path. It is the only scope of every target below. Encoding, resizing and colour processing of already-decoded pixels are left out.

Nothing here comes from package descriptions. `sharp@0.35.5` and Pillow 13.0.0 were installed from npm and PyPI on Linux x86_64 to see which libraries actually ship, and every function name in the chains was looked up in the latest upstream source; each file name links to it.

Two facts decide reachability. Sharp picks a loader with `vips_foreign_find_load_buffer`, and Pillow's `Image.open` tries every registered plugin. Both look only at the file's magic bytes, never at its name, so **every decoder they enable is reachable from an upload**.

## Call chains {#explorer}

Pick a chain above the diagram. Each chain starts from ordinary application code and follows the call down to the C library that parses the bytes. Blue boxes are Tier 0 targets, green boxes already have recorded progress, dashed grey boxes are on the path but not planned.

[[audit-explorer]]

## Tier 0 targets {#targets}

| Library | Reached from | Status |
| --- | --- | --- |
| libvips: format sniffing, loader glue, the vendored GIF decoder, EXIF and ICC glue | every Sharp call | not done |
| mozjpeg | Sharp JPEG, JPEG inside TIFF | not done |
| libpng | Sharp PNG | not done |
| libwebp | Sharp and Pillow WebP | not done |
| libtiff | Sharp and Pillow TIFF | not done |
| libexif | Sharp, every input that carries EXIF | not done |
| lcms2 | Sharp, every input that carries an ICC profile | not done |
| libxml2 | Sharp SVG | not done |
| Pillow `libImaging` decoders | every Pillow `load()` | not done |
| libjpeg-turbo | Pillow JPEG, JPEG inside TIFF | not done |
| libavif | Pillow AVIF | not done |
| openjpeg | Pillow JPEG 2000 | not done |
| liblzma (xz) | Pillow LZMA-compressed TIFF, Python `lzma` | not done |
| zlib-ng | Sharp and Pillow PNG and Deflate TIFF | [recorded progress](../zlib-ng/en/progress.html) |

zlib, zstd, brotli, the 7-Zip SDK and libarchive keep their existing scopes and are not repeated here.

## Checked and left out {#excluded}

| Library | Why it is not a target |
| --- | --- |
| libspng | Sharp's libvips is built with `-Dspng=disabled`; Pillow does not use it |
| expat | in Sharp it only reads `.vips` files from a path and fontconfig configuration; Pillow does not ship it |
| FreeType | renders fonts chosen by the application, not uploaded fonts |
| cgif, libimagequant | Sharp's GIF encoding path; inputs are already-decoded pixels, so not Tier 0 |
| librsvg | Rust; the C library it uses to parse XML, libxml2, is a target |
| libheif, aom, dav1d | C++ or very large AV1 codecs; deferred |
