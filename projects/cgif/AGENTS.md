# Working rules (`projects/cgif`)

Inherits every rule of the repository root [`../../AGENTS.md`](../../AGENTS.md), including the strict
ISO C17 undefined-behaviour policy: no `NULL`, wild or dangling pointer `+ 0`, no `NULL - NULL`, no
cross-object pointer subtraction or comparison, no out-of-bounds pointer formation, no zero-length
`memcpy`/`memset` on invalid pointers, every struct pointer field written before it is read, and no
"benign UB" arguments. The runtime starts from `framework/lean/StrictPtr.lean`.

- **Status:** candidate. Upstream submodule `cgif/` tracks the latest default branch. Not
  registered in `framework/projects.json`; translation and proofs are not done.

## Why it matters

Every `.gif()` output in Sharp (cgif 0.5.4 in Sharp 0.35.5) is written by cgif through
`libvips/foreign/cgifsave.c`, typically re-encoding an uploaded animation. The frames it receives
are attacker-shaped (size, frame count, palette indices after quantisation with libimagequant in
`foreign/quantise.c`). cgif is small, so the whole public API is in scope.

## Interfaces to prove (P0)

`cgif_newgif`, `cgif_addframe`, `cgif_close` (the latter is called through libvips' `VIPS_FREEF`),
together with the raw encoder they use (`src/cgif.c`, `src/cgif_raw.c`): LZW code generation,
255-byte sub-block output, palette and transparency handling, and the frame-difference window.

## Verification hazards

1. Pixel indices larger than the active palette, and the transparency index.
2. LZW dictionary size and code width (at most 12 bits) across clear codes.
3. Frame-difference rectangle against the previous frame, and `width × height` products for
   16-bit dimensions.
4. Write-callback failure and allocation failure in the middle of an animation, followed by
   `cgif_close`.

## Not in scope

The RGB convenience API (`src/cgif_rgb.c`, not called by libvips), the file-path output mode, and
compression ratio.

## Local commands

```bash
lake --dir projects/cgif build --wfail CgifF CgifF.Results
python3 framework/check_project.py cgif --skip-build
```
