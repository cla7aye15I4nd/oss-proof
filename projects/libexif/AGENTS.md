# Working rules (`projects/libexif`)

Inherits every rule of the repository root [`../../AGENTS.md`](../../AGENTS.md), which is
authoritative on proof soundness, allowed axioms and the strict ISO C17 undefined-behaviour policy.
The runtime starts from `framework/lean/StrictPtr.lean`.

**Status:** candidate. Upstream submodule `libexif/` tracks the latest default branch; not
registered in `framework/projects.json`; translation and proofs are not done.

## Tier 0

Tier 0 is the code that turns untrusted bytes into pixels or metadata on a default path. It is the
whole scope of this project.

**How it is reached.** In Sharp, any loader that finds an EXIF block (JPEG `APP1`, PNG `eXIf`, WebP
`EXIF`) attaches it to the image, and `vips_image_set` (libvips `iofuncs/header.c`) immediately
calls `vips__exif_parse` (`foreign/exif.c`). This happens while the header is read, so
`sharp(upload).metadata()` already reaches libexif. Pillow does not use libexif.

**Functions:** `exif_data_new_mem`, `exif_data_set_option`, `exif_data_unset_option`,
`exif_data_load_data` (including the MakerNote parsers it runs), `exif_data_get_byte_order`,
`exif_data_foreach_content`, `exif_content_foreach_entry`, `exif_content_get_entry`,
`exif_entry_get_value`, `exif_get_short`, `exif_get_sshort`, `exif_get_long`, `exif_get_slong`,
`exif_get_rational`, `exif_get_srational`, `exif_data_free`.

**What the proofs must cover.**

1. Entry offsets and sizes (`offset + size`, `components × format size`) never overflow or read
   past the blob.
2. Sub-IFD pointers and MakerNote offsets cannot loop or escape the blob.
3. `exif_entry_get_value` writes only inside the caller's buffer, for non-terminated strings and
   zero denominators too.

## Local commands

```bash
lake --dir projects/libexif build --wfail LibexifF LibexifF.Results
python3 framework/check_project.py libexif --skip-build
```
