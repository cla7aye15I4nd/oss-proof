# Working rules (`projects/libarchive`)

Inherits all rules of [`../../AGENTS.md`](../../AGENTS.md), including the **Strict ISO C17 Undefined Behaviour Policy**
(no `NULL + 0`, no wild/dangling pointer `+ 0`, no `NULL - NULL`, no cross-object pointer subtraction or comparison,
and no `memcpy`/`memset` with `n == 0` on `NULL` or dangling pointers).

- **Status:** Registered in `framework/projects.json`; top-down RAR5 & 7-Zip invariant models
  (`LibarchiveF.Model`) and strict ISO C17 runtime (`LibarchiveF.Runtime`) checked,
  statement-by-statement C translation and public safety proofs **Not done**.

## Scope (`LibarchiveF`)

Goal: kernel-checked Lean 4 proofs about a faithful, statement-by-statement translation of upstream
`libarchive` (`libarchive/libarchive`, pinned submodule `libarchive/` + `patches/*.patch`), covering
its **highest-exposure real-world read formats, core streaming filter dispatcher, AND archive write
formats** for the default scalar x86_64 Linux LP64 build.

The goal is full safety (no ISO C17 undefined behaviour, no out-of-bounds read/write, no signed
integer overflow in header/size calculations, no use-after-free or double-free across solid,
multivolume, or metadata resets, no memory leak, stated write frame, and termination) across every
documented `archive_read_*`, `archive_write_*`, and `archive_entry_*` call sequence in scope.

## Real-World Usage Paths & Function Priority

`libarchive` is the system archive engine for **macOS `tar`**, **Windows 10/11 `tar.exe`**,
**FreeBSD `bsdtar`/`bsdcpio`**, **Arch Linux `pacman`** (root-privileged `.pkg.tar.zst` / `.tar.xz`
extraction), **FreeBSD `pkg`**, **CMake** (`cmake -E tar`), **systemd**, **GNOME `autoar`**,
**`python-libarchive-c`**, and **`sharp-libvips`** (bundled for Deep Zoom `.zip` archive output).
Recent real-world vulnerabilities prove that **both read AND write paths** carry severe memory-safety
risk:
- **CVE-2026-15028:** Heap buffer overflow in PAX extended-header / sparse-file parsing in the TAR
  reader (`archive_read_support_format_tar.c`).
- **CVE-2026-16517:** Signed integer overflow in the **ZIP writer** (`archive_write_set_format_zip.c`)
  when encryption metadata overhead pushes entry size past `INT64_MAX`.
- **CVE-2026-17591:** Use-after-free in `archive_entry` metadata cleanup
  (`archive_entry_copy_mac_metadata`).
- **CVE-2025-5918:** Out-of-bounds read in streaming archive readers when piped into `bsdtar`.

### Tier 1 (P0) — Highest-Exposure Read & Core Infrastructure (Prove First)

1. **Core streaming reader & `archive_entry` lifecycle (`archive_read.c`, `archive_read_open_memory.c`,
   `archive_read_data_into_fd.c`, `archive_entry.c`, `archive_string.c`):** `archive_read_new`,
   `archive_read_open_memory`, `archive_read_open`, `archive_read_next_header`,
   `archive_read_next_header2`, `archive_read_data`, `archive_read_data_block`,
   `archive_read_data_skip`, `archive_read_close`, `archive_read_free`, plus `archive_entry_*`
   metadata setters/getters (`CVE-2026-17591` class).
2. **TAR / PAX / USTAR / GNU reader (`archive_read_support_format_tar.c`):** The #1 most-used
   format (`bsdtar`, `pacman`, `pkg`, containers, CI artifacts) and site of `CVE-2026-15028` (PAX
   extended headers, GNU longnames, sparse-file maps, base-256/octal integer parsers).
3. **ZIP reader (`archive_read_support_format_zip.c`):** #2 most-used format (streaming local-header
   & seekable central-directory parsing, Zip64 extra fields, Deflate/LZMA/Zstd/BZip2/Store entries).
4. **RAR5 & 7-Zip readers (`archive_read_support_format_rar5.c`, `archive_blake2sp_ref.c`,
   `archive_read_support_format_7zip.c`, `archive_ppmd7.c`, `archive_ppmd8.c`):** Highest parser and
   sub-allocator complexity on untrusted desktop/web archives (already modeled top-down in
   `LibarchiveF/Model/`).

### Tier 2 (P1) — Archive Write Paths & Read Compression Filters

1. **PAX / USTAR / GNU TAR writer (`archive_write.c`, `archive_write_open_memory.c`,
   `archive_write_set_format_pax.c`, `archive_write_set_format_ustar.c`):** `archive_write_new`,
   `archive_write_set_format_pax_restricted`, `archive_write_open_memory`, `archive_write_header`,
   `archive_write_data`, `archive_write_finish_entry`, `archive_write_close`, `archive_write_free`.
2. **ZIP writer (`archive_write_set_format_zip.c`):** Directly exercised by `bsdtar`, `cmake`, and
   `sharp-libvips` Deep Zoom ZIP output; directly targets the `CVE-2026-16517` signed-overflow class.
3. **CPIO reader (`archive_read_support_format_cpio.c`) & core filter bid/stream wrappers
   (`archive_read_support_filter_gzip.c`, `_xz.c`, `_zstd.c`, `_bzip2.c`, `_lz4.c`,
   `archive_write_add_filter_gzip.c`, `_zstd.c`, `_xz.c`):** Framing glue around the underlying
   compression codecs (which are verified independently in `projects/{zlib,zstd,xz,bzip2,lz4}/`).

### Explicitly Not Planned

- Disk/filesystem extraction & OS ACL/xattr/symlink enforcement (`archive_write_disk_*.c`,
  `archive_read_disk_*.c` — OS-syscall dependent; path-traversal policy belongs to callers/disk layer).
- Low-traffic legacy formats: `ar`, `cab`, `lha`, `mtree`, `raw`, `warc`, `xar`, `iso9660`, legacy
  `rar` (v1–v4), `uu`/`compress`/`grzip`/`lrzip`/`lzop`/`rpm` filters, and CLI utilities (`tar/`, `cpio/`, `cat/`).
- Cryptographic correctness of ZIP/RAR/7z encryption beyond memory safety of key-derivation/header
  parsers.

## Source & Layout

- `libarchive/` — pinned upstream submodule (`https://github.com/libarchive/libarchive`). Never
  modify it. Verified source is `libarchive/` plus `patches/*.patch` applied in name order (each
  paired with `tests/patch-reverts/<name>/`).
- `LibarchiveF/Model/`, `LibarchiveF/Libarchive/`, `LibarchiveF/Spec/{Common,Safety,Functional}/`,
  `LibarchiveF/Proof/`, `LibarchiveF/Math/`, `LibarchiveF/Runtime/`, `LibarchiveF/Results.lean`.

## Key Hazards to Model and Verify Without Shortcuts

1. **PAX extended headers & sparse-file tables (`archive_read_support_format_tar.c` — `CVE-2026-15028`).**
   Prove strict bounds on PAX key/value length parsing, GNU/PAX sparse-entry linked lists and offset
   arithmetic (`int64_t` overflow checks), and base-256/octal field decoders.
2. **ZIP streaming vs. seekable central directory & ZIP writer size arithmetic
   (`archive_read_support_format_zip.c`, `archive_write_set_format_zip.c` — `CVE-2026-16517`).**
   Prove Zip64 extra-field parsing bounds, local-vs-central-directory mismatch safety, and overflow-free
   `int64_t`/`uint64_t` entry-size + encryption-overhead accounting in the writer.
3. **RAR5 solid & multivolume state reinitialisation & circular LZSS/filters (`rar5.c`).**
   Window buffers, Huffman tables, and queued post-decompression filters (`struct filter_info`)
   persist across solid entries and multivolume boundaries; prove zero UAF, zero double-free, valid
   `window_mask` wrap-around copies, and strict `block_start`/`block_length`/`channels` filter bounds.
4. **7-Zip `EncodedHeader` bootstrap, `Folder`/`BindPairs` DAG & PPMd sub-allocator (`7zip.c`,
   `archive_ppmd7.c`, `archive_ppmd8.c`).**
   Prove DAG acyclicity, BCJ2 4-stream arity, `SubStreamsInfo` bounds, and `SplitBlock`/`GlueFreeBlocks`
   /`SON`/`REF` memory safety under arbitrary bitstreams.
5. **`archive_entry` & `archive_string` ownership (`archive_entry.c`, `archive_string.c` — `CVE-2026-17591`).**
   Prove zero UAF / double-free when metadata blobs (`mac_metadata`, symlinks, xattrs, PAX attributes)
   are copied, overwritten, or cleared across entries.

## Proof Workflow & Local Commands

- Only `propext`, `Classical.choice`, and `Quot.sound` are allowed (`sorry` permitted on
  `skeleton/*` branches only). Every safety goal pairs with a non-vacuity witness theorem.
- Any narrower precondition (e.g. memory I/O callbacks, disjoint caller buffers) is stated
  explicitly and listed in `docs/{en,zh}/deviations.md`. Build with at most `-j 4`.

From repository root:

```bash
lake --dir projects/libarchive build --wfail LibarchiveF LibarchiveF.Results
python3 framework/check_project.py libarchive --skip-build
```
