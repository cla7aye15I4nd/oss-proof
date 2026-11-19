# Working rules (`projects/libexif`)

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

- **Status:** Upstream submodule `libexif/` pinned (not yet registered in `framework/projects.json`;
  Lean runtime bootstrap, C translation, and safety proofs **Not done**).

## Scope (`LibexifF`)

- **Upstream source:** `libexif/` pinned submodule (`https://github.com/libexif/libexif`) +
  `patches/*.patch` in name order.
- **Target configuration:** portable scalar x86_64 Linux LP64 build (`--disable-nls`, ~10k LOC
  pure C — compact, high CVE density, and directly on the hot path of every Sharp upload!).
- **Verification goal:** full safety (no ISO C17 undefined behaviour, no heap OOB read/write on
  untrusted TIFF/EXIF IFD & MakerNote blobs, no signed integer overflow in tag offset/component
  multiplication, no stack/recursion exhaustion on cyclic IFDs, no memory leak or UAF, stated write
  frame, and termination) across **both EXIF parsing AND EXIF re-serialization**.

## Real-World Usage Paths & Function Priority

- **Sharp / `libvips` (`libvips/foreign/exif.c` — triggered on nearly EVERY uploaded JPEG, WebP,
  TIFF, and HEIF!):**
  Whenever a Node.js app calls `sharp(buf).metadata()`, `sharp(buf).rotate()` / `.autoOrient()`,
  `.keepExif()`, or `.withExif()`, `libvips` feeds the raw untrusted EXIF byte blob directly into
  `libexif`:
  - **Parse / inspect:** `exif_data_new_from_data`, `exif_data_new`, `exif_data_set_option`,
    `exif_data_load_data`, `exif_data_get_byte_order`, `exif_content_foreach_item`,
    `exif_content_get_entry`, `exif_entry_get_value`, `exif_get_short`, `exif_get_long`,
    `exif_get_slong`, `exif_get_rational`, `exif_get_srational`, `exif_data_get_mnote_data`,
    `exif_mnote_data_count`, `exif_mnote_data_get_value`, `exif_data_unref`.
  - **Mutate / re-serialize (encode path):** `exif_data_fix`, `exif_entry_initialize`,
    `exif_content_add_entry`, `exif_content_remove_entry`, `exif_set_short`, `exif_set_long`,
    `exif_data_save_data`.
- **Desktop, Mobile, DAM & Cloud Photo Pipelines (GNOME, GIMP, ImageMagick, digiKam, PHP `exif`):**
  Same untrusted `exif_data_new_from_data` -> `exif_entry_get_value` -> `exif_data_save_data` flow.
- **Historical CVE Density:** `libexif` has dozens of historical CVEs (e.g., `CVE-2020-13112`,
  `CVE-2020-13113`, `CVE-2020-13114`, `CVE-2020-0452`, `CVE-2020-0182`, `CVE-2020-0198`) —
  overwhelmingly heap OOB reads/writes, signed integer overflows in `offset + size`, uninitialized
  memory reads, and MakerNote parser overflows.

### Tier 1 (P0) — Core EXIF Parsing, Value Formatting & Re-Serialization (Prove First)

1. **Data container, IFD parser & serializer (`libexif/exif-data.c`, `exif-content.c`,
   `exif-entry.c`, `exif-loader.c`, `exif-utils.c`, `exif-format.c`, `exif-tag.c`,
   `exif-byte-order.c`, `exif-mem.c`, `exif-log.c`):**
   `exif_data_new_from_data`, `exif_data_load_data`, `exif_data_save_data`, `exif_data_fix`,
   `exif_data_unref`, `exif_content_foreach_item`, `exif_content_get_entry`, `exif_entry_get_value`,
   `exif_entry_fix`, `exif_loader_write`, `exif_loader_get_data`, `exif_loader_unref`.
2. **MakerNote sub-parsers reachable automatically from `exif_data_load_data` (`libexif/canon/`,
   `libexif/fuji/`, `libexif/olympus/`, `libexif/pentax/`, `libexif/apple/`):**
   **Critical insight:** By default `exif_data_new_from_data` enables `EXIF_DATA_OPTION_FOLLOW_SPECIFICATION`
   and **automatically invokes MakerNote parsers** whenever tag `0x927C` (`EXIF_TAG_MAKER_NOTE`)
   appears in an untrusted JPEG — historically the #1 source of `libexif` heap OOB bugs!

### Explicitly Not Planned

- GNU `gettext` localization (`--disable-nls`; string lookups stay fixed C literals),
  `exif_data_dump` stdout debug printers, and CLI utilities.

## Verified Translation Units

- `libexif/exif-byte-order.c`, `exif-content.c`, `exif-data.c`, `exif-entry.c`, `exif-format.c`,
  `exif-ifd.c`, `exif-loader.c`, `exif-log.c`, `exif-mem.c`, `exif-mnote-data.c`, `exif-tag.c`,
  `exif-utils.c`
- `libexif/apple/*.c`, `libexif/canon/*.c`, `libexif/fuji/*.c`, `libexif/olympus/*.c`,
  `libexif/pentax/*.c`

## Library-Specific Verification Hazards (No Shortcuts)

1. **Unsigned/signed 32-bit `offset + s` wraparound & `components * format_size` overflow
   (`exif-data.c`, `exif-entry.c` — `CVE-2020-0452`, `CVE-2020-0198`).**
   EXIF IFDs store attacker-controlled 32-bit `components` and `offset` fields. Prove every
   `exif_data_load_data_content` and `exif_data_load_data_entry` bounds check cannot wrap 32-bit
   integers or read past `ds` (data size).
2. **Recursive / cyclic Sub-IFD pointers (`ExifIFD`, `GPSIFD`, `InteroperabilityIFD`, `IFD1`).**
   Prove bounded recursion depth (`recursion_cost` / visited-offset guards) guarantees termination
   and prevents stack exhaustion / exponential CPU blowup (`CVE-2020-13114`).
3. **MakerNote raw-offset indexing & `exif_mnote_data_load` (`canon/`, `olympus/`, `pentax/`,
   `fuji/`, `apple/` — `CVE-2020-13112`, `CVE-2020-13113`).**
   MakerNotes mix TIFF-base-relative and MakerNote-relative offsets across arbitrary endianness;
   prove every sub-parser validates `ofs + len <= buf_size` without integer overflow or uninitialized
   `entry->data` pointers.
4. **String formatting & rational division by zero (`exif_entry_get_value` in `exif-entry.c`).**
   `exif_entry_get_value` formats arbitrary untrusted binary tags into caller-supplied `val[maxlen]`
   using `snprintf`, rational divisions (`r.denominator == 0`), and UCS-2/ASCII decoding without
   guaranteed NUL terminators. Prove zero OOB reads on non-NUL-terminated `e->data` and zero
   div-by-zero / `INT_MIN / -1` UB.
5. **EXIF serialization (`exif_data_save_data` in `exif-data.c`).**
   Prove output buffer reallocation (`*d`, `*ds`), thumbnail embedding, and IFD offset table
   emission cannot overflow or leak on `exif_mem_realloc` failure.

## Bootstrap & Local Commands

When onboarding into `framework/projects.json`: copy `lean-toolchain`,
start `LibexifF/Runtime/Ptr.lean` from `framework/lean/StrictPtr.lean`, wire `LibexifF/Results.lean`
and `project.json`, then run:

```bash
lake --dir projects/libexif build --wfail LibexifF LibexifF.Results
python3 framework/check_project.py libexif --skip-build
```
