# Working rules (`projects/libxml2`)

Inherits every rule of the repository root [`../../AGENTS.md`](../../AGENTS.md), which is
authoritative on proof soundness, allowed axioms and the strict ISO C17 undefined-behaviour policy.
The runtime starts from `framework/lean/StrictPtr.lean`.

**Status:** candidate. Upstream submodule `libxml2/` tracks the latest default branch; not
registered in `framework/projects.json`; translation and proofs are not done.

## Tier 0

Tier 0 is the code that turns untrusted bytes into pixels or metadata on a default path. It is the
whole scope of this project.

**How it is reached.** Sharp accepts SVG by default: `sharp(Buffer.from(svg)).png().toBuffer()` →
libvips `foreign/svgload.c` `vips_foreign_load_svg_source_header` →
`rsvg_handle_new_from_stream_sync`. librsvg is Rust, but it parses the XML with libxml2's SAX parser
through FFI (`rsvg/src/xml/xml2_load.rs`). Pillow does not use libxml2.

**Functions:** `xmlInitParser`, `xmlCreateIOParserCtxt` (with librsvg's SAX handler and read
callbacks), `xmlCtxtUseOptions`, `xmlParseDocument`, `xmlStopParser`, `xmlCtxtGetLastError`,
`xmlFreeParserCtxt` — and the parser core they drive: input buffers, encoding detection and
conversion, the tokenizer, entities and SAX dispatch.

**What the proofs must cover.**

1. Input buffer growth and the pointer adjustments after each reallocation.
2. Multi-byte sequences split across input chunks, in every supported encoding.
3. Entity expansion within its amplification limits, and stopping the parser from a callback.

## Local commands

```bash
lake --dir projects/libxml2 build --wfail Libxml2F Libxml2F.Results
python3 framework/check_project.py libxml2 --skip-build
```
