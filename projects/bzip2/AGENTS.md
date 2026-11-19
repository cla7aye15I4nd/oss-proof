# Working rules (`projects/bzip2`)

Inherits every rule of the repository root [`../../AGENTS.md`](../../AGENTS.md), including the strict
ISO C17 undefined-behaviour policy: no `NULL`, wild or dangling pointer `+ 0`, no `NULL - NULL`, no
cross-object pointer subtraction or comparison, no out-of-bounds pointer formation, no zero-length
`memcpy`/`memset` on invalid pointers, every struct pointer field written before it is read, and no
"benign UB" arguments. The runtime starts from `framework/lean/StrictPtr.lean`.

- **Status:** candidate. Upstream submodule `bzip2/` tracks the latest default branch. Not
  registered in `framework/projects.json`; translation and proofs are not done.

## Why it matters

Not on a Sharp or Pillow image path. It is on the Python standard-library path (`bz2` module,
`Modules/_bz2module.c`) and libarchive's bzip2 read filter, and the whole library is small enough
to prove completely.

## Interfaces to prove (P0)

Exactly what those callers use: `BZ2_bzDecompressInit`, `BZ2_bzDecompress`,
`BZ2_bzDecompressEnd`, `BZ2_bzCompressInit`, `BZ2_bzCompress` (`BZ_RUN`, `BZ_FLUSH`,
`BZ_FINISH`), `BZ2_bzCompressEnd`, `BZ2_bzlibVersion` — covering `bzlib.c`, `decompress.c`,
`compress.c`, `blocksort.c`, `huffman.c`, `crctable.c`, `randtable.c`.

## Verification hazards

1. Selector count, group count and code lengths read from the stream, and the Huffman decode
   tables built from them.
2. Inverse BWT (`origPtr`, `tt` / `ll16` / `ll4`) and run-length expansion into the caller's
   buffer, in both normal and `small` modes.
3. Block sorting with overshoot bytes, fallback sort, and bounded sort stacks.
4. Suspension and resumption with zero-length input or output.

## Not in scope

The `BZFILE` stdio API (`BZ2_bzRead`, `BZ2_bzWrite`, `BZ2_bzopen` and friends — neither caller
uses it), and the `bzip2` / `bzip2recover` tools.

## Local commands

```bash
lake --dir projects/bzip2 build --wfail Bzip2F Bzip2F.Results
python3 framework/check_project.py bzip2 --skip-build
```
