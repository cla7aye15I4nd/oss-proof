# Working rules (`projects/libexif`)

Inherits every rule of the repository root [`../../AGENTS.md`](../../AGENTS.md), including the strict
ISO C17 undefined-behaviour policy: no `NULL`, wild or dangling pointer `+ 0`, no `NULL - NULL`, no
cross-object pointer subtraction or comparison, no out-of-bounds pointer formation, no zero-length
`memcpy`/`memset` on invalid pointers, every struct pointer field written before it is read, and no
"benign UB" arguments. The runtime starts from `framework/lean/StrictPtr.lean`.

- **Status:** candidate. Upstream submodule `libexif/` tracks the latest default branch. Not
  registered in `framework/projects.json`; translation and proofs are not done.

## Why it matters

In Sharp, any loader that finds an EXIF block (JPEG `APP1`, PNG `eXIf`, WebP `EXIF`, HEIF metadata)
attaches it to the image, and `vips_image_set` (`libvips/iofuncs/header.c`) immediately calls
`vips__exif_parse` in `libvips/foreign/exif.c`, which hands the raw bytes to libexif. This happens
during the header read, so `sharp(buf).metadata()` and every pipeline reach libexif (0.6.26 in
Sharp 0.35.5) before the application sees anything. Saving with `.keepExif()` / `.withExif()`
re-serialises through libexif. Pillow does not use libexif.

## Interfaces to prove (P0)

Exactly what `libvips/foreign/exif.c` calls:

- **Parse:** `exif_data_new_from_data`, `exif_data_new_mem`, `exif_mem_new`,
  `exif_data_set_option`, `exif_data_unset_option`,
  `exif_data_load_data` (including the MakerNote parsers it runs), `exif_data_get_byte_order`,
  `exif_data_foreach_content`, `exif_content_foreach_entry`, `exif_content_get_entry`,
  `exif_entry_get_ifd`, `exif_entry_get_value`, `exif_get_short`, `exif_get_sshort`,
  `exif_get_long`, `exif_get_slong`, `exif_get_rational`, `exif_get_srational`,
  `exif_tag_get_name_in_ifd`, `exif_tag_get_title`, `exif_tag_from_name`, `exif_ifd_get_name`,
  `exif_format_get_name`, `exif_byte_order_get_name`, `exif_data_free`.
- **Update and save:** `exif_data_fix`, `exif_data_set_byte_order`, `exif_data_set_data_type`,
  `exif_entry_new_mem`, `exif_entry_initialize`, `exif_content_add_entry`,
  `exif_content_remove_entry`, `exif_entry_unref`, `exif_set_short`, `exif_set_sshort`,
  `exif_set_long`, `exif_set_slong`, `exif_set_rational`, `exif_set_srational`, `exif_mem_alloc`,
  `exif_mem_unref`, `exif_data_save_data`.

## Verification hazards

1. IFD entry offsets and sizes: 32-bit `offset + size` and `components × format size` overflow.
2. Sub-IFD pointers (EXIF, GPS, Interoperability, IFD1) that loop or nest deeply.
3. MakerNote parsers (Canon, Olympus, Pentax, Fuji, Apple) with their own offset bases.
4. `exif_entry_get_value` formatting untrusted data into the caller's fixed-size buffer:
   non-terminated strings, zero denominators, signed edge values.
5. `exif_data_save_data` buffer growth and thumbnail placement.

## Not in scope

`gettext` localisation (build with `--disable-nls`), debug dump helpers, and the command-line
tool.

## Local commands

```bash
lake --dir projects/libexif build --wfail LibexifF LibexifF.Results
python3 framework/check_project.py libexif --skip-build
```
