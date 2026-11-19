# Working rules (`projects/bzip2`)

Inherits every rule of the repository root [`../../AGENTS.md`](../../AGENTS.md), which is
authoritative on proof soundness, allowed axioms and the strict ISO C17 undefined-behaviour policy.
The runtime starts from `framework/lean/StrictPtr.lean`.

**Status:** candidate. Upstream submodule `bzip2/` tracks the latest default branch; not
registered in `framework/projects.json`; translation and proofs are not done.

## Tier 0

Tier 0 is the code that turns untrusted bytes into data on a default path. It is the whole scope
of this project. bzip2 is not on a Sharp or Pillow image path.

**How it is reached.** Python's `bz2.decompress()` / `BZ2Decompressor` (`Modules/_bz2module.c`)
and libarchive's bzip2 read filter.

**Functions:** `BZ2_bzDecompressInit`, `BZ2_bzDecompress`, `BZ2_bzDecompressEnd` — covering
`bzlib.c`, `decompress.c`, `huffman.c`, `crctable.c`, `randtable.c`.

**What the proofs must cover.**

1. Selector counts, group counts and code lengths read from the stream, and the Huffman tables
   built from them, stay in bounds.
2. The inverse BWT (`origPtr`, `tt` / `ll16` / `ll4`) and run-length expansion stay inside the
   block and the caller's output buffer, in normal and `small` modes.
3. Suspension and resumption with zero-length input or output.

## Local commands

```bash
lake --dir projects/bzip2 build --wfail Bzip2F Bzip2F.Results
python3 framework/check_project.py bzip2 --skip-build
```
