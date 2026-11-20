# Working rules (`projects/lz4`)

Inherits every rule of the repository root [`../../AGENTS.md`](../../AGENTS.md), which is
authoritative on proof soundness, allowed axioms and the strict ISO C17 undefined-behaviour policy.
The runtime starts from `framework/lean/StrictPtr.lean`.

**Status:** candidate. Upstream submodule `lz4/` tracks the latest default branch; not registered
in `framework/projects.json`; translation and proofs are not done.

## Tier 0

Tier 0 is the code that turns untrusted bytes into data on a default path. It is the whole scope
of this project. lz4 is not on a Sharp or Pillow image path.

**How it is reached.** python-lz4 (`lz4.block.decompress`, `lz4.frame.decompress`) and
libarchive's lz4 read filter.

**Functions:** `LZ4_decompress_safe`, `LZ4_decompress_safe_usingDict`,
`LZ4_decompress_safe_withPrefix64k`, `LZ4F_createDecompressionContext`, `LZ4F_getFrameInfo`,
`LZ4F_decompress`, `LZ4F_resetDecompressionContext`, `LZ4F_freeDecompressionContext`.

**What the proofs must cover.**

1. `int` sizes and capacities, including negative values and `INT_MAX`, never produce a negative
   or overlong copy.
2. Wild copies past the logical end stay inside the guaranteed margins; overlapping matches with
   small offsets are correct.
3. Dictionaries and prefixes in a separate allocation are reached without cross-object pointer
   arithmetic; the frame decoder is safe across arbitrary input and output splits.

## Local commands

```bash
LEAN_NUM_THREADS=4 lake --dir projects/lz4 build --wfail Lz4F Lz4F.Results
python3 framework/check_project.py lz4 --skip-build
```
