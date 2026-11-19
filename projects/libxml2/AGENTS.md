# Working rules (`projects/libxml2`)

Inherits every rule of the repository root [`../../AGENTS.md`](../../AGENTS.md), including the strict
ISO C17 undefined-behaviour policy: no `NULL`, wild or dangling pointer `+ 0`, no `NULL - NULL`, no
cross-object pointer subtraction or comparison, no out-of-bounds pointer formation, no zero-length
`memcpy`/`memset` on invalid pointers, every struct pointer field written before it is read, and no
"benign UB" arguments. The runtime starts from `framework/lean/StrictPtr.lean`.

- **Status:** candidate. Upstream submodule `libxml2/` tracks the latest default branch. Not
  registered in `framework/projects.json`; translation and proofs are not done.

## Why it matters

Sharp accepts SVG input by default (libvips' `svgload` is flagged untrusted, but nothing blocks it
unless the application sets `VIPS_BLOCK_UNTRUSTED` or calls `sharp.block()`). libvips passes the
bytes to librsvg (`rsvg_handle_new_from_data`). librsvg is written in Rust, but it parses the XML
with libxml2's SAX parser through FFI (`rsvg/src/xml/xml2_load.rs`), so every SVG upload is parsed
by libxml2 C code (2.15.4 in Sharp 0.35.5). Pillow does not use libxml2.

## Interfaces to prove (P0)

Exactly what librsvg calls: `xmlInitParser`, `xmlCreateIOParserCtxt` (with librsvg's SAX handler
and I/O callbacks), `xmlCtxtUseOptions`, `xmlParseDocument`, `xmlStopParser`,
`xmlCtxtGetLastError`, `xmlNewEntity`, `xmlFreeEntity`, `xmlFreeNode`, `xmlFreeDoc`,
`xmlFreeParserCtxt` — and the parser core they drive: input buffers and encoding conversion,
tokenizer, entity handling, and the SAX callback dispatch.

## Verification hazards

1. Push/pull input buffer growth and the pointer adjustments made after each `realloc`.
2. Encoding detection and conversion (UTF-8, UTF-16, Latin-1) with sequences split across input
   chunks.
3. Entity declaration and expansion, including amplification limits.
4. SAX callbacks that stop the parser (`xmlStopParser`) from inside a callback.
5. Error paths freeing partially built nodes and entities.

## Not in scope

XPath, XInclude, XSLT, schema and RelaxNG validation, HTML parser, catalogs, network I/O, the
tree-building DOM API beyond what the SAX path touches, threads, and `xmllint`.

## Local commands

```bash
lake --dir projects/libxml2 build --wfail Libxml2F Libxml2F.Results
python3 framework/check_project.py libxml2 --skip-build
```
