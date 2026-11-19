# Working rules (`projects/cgif`)

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

- **Status:** Upstream submodule `cgif/` pinned (not yet registered in `framework/projects.json`;
  Lean runtime bootstrap, C translation, and safety proofs **Not done**).

## Scope (`CgifF`)

- **Upstream source:** `cgif/` pinned submodule (`https://github.com/dloebl/cgif`) +
  `patches/*.patch` in name order.
- **Target configuration:** portable scalar x86_64 Linux LP64 build (~2k LOC pure C — the smallest
  and fastest-to-prove encoder library in the Sharp stack!).
- **Verification goal:** full safety (no ISO C17 undefined behaviour, no out-of-bounds read/write
  in LZW dictionary/sub-block emission or frame-delta clipping, no memory leak or double-free across
  `cgif_addframe` errors and `cgif_close`, stated write frame, and termination) of **100% of the
  public `cgif.h` API**.

## Real-World Usage Paths & Function Priority

- **Sharp / `libvips` (`libvips/foreign/cgifsave.c` — ALL `.gif()` output in Sharp!):**
  Every time a Node.js service converts an uploaded video/WebP/APNG/GIF into an optimized static or
  animated GIF via `sharp(input, { animated: true }).gif().toBuffer()`, `libvips` invokes `cgif`:
  - `cgif_newgif` (configuring `width`, `height`, `pGlobalPalette`, `numGlobalPaletteEntries`,
    `attrFlags` including `CGIF_ATTR_IS_ANIMATED`, `CGIF_ATTR_NO_GLOBAL_TABLE`,
    `CGIF_ATTR_HAS_TRANSPARENCY`, `genFlags` including `CGIF_GEN_KEEP_IDENT_FRAMES`, `pWriteFn`
    callback into `VipsTarget`, `numLoops`);
  - `cgif_addframe` (per-frame indexed pixel buffer `pImageData`, optional `pLocalPalette`,
    `transIndex`, `delay`, `attrFlags`, `genFlags` including `CGIF_FRAME_GEN_USE_TRANSPARENCY` and
    `CGIF_FRAME_GEN_USE_DIFF_WINDOW`);
  - `cgif_close` (flushes GIF trailer `0x3B` and frees all internal LZW / previous-frame buffers).
- **Direct True-Color RGB API (`cgif_rgb.c`):** `cgif_rgb_newgif`, `cgif_rgb_addframe`,
  `cgif_rgb_close` (optional RGB->palette quantization path).

### Tier 1 (P0) — Core Palette/Indexed GIF Encoder (100% of Sharp `cgifsave.c`, Prove First)

- **`inc/cgif.h`, `src/cgif.c`, `src/cgif_raw.c`:**
  `cgif_newgif`, `cgif_addframe`, `cgif_close`, plus internal LZW encoder (`cgif_raw_newgif`,
  `cgif_raw_addframe`, `cgif_raw_close`, `lzw_generate`), frame-difference bounding-box optimizer,
  and palette/transparency index remapping.

### Tier 2 (P1) — True-Color RGB Wrapper & Explicitly Not Planned

- **Tier 2 (`src/cgif_rgb.c`):** `cgif_rgb_newgif`, `cgif_rgb_addframe`, `cgif_rgb_close`.
- **Not planned:** File-path `path` stdio branch beyond abstract `pWriteFn` callback model, and
  GIF compression-ratio optimality proofs beyond invariants needed for safety.

## Verified Translation Units

- `inc/cgif.h`, `inc/cgif_raw.h`
- `src/cgif.c`, `src/cgif_raw.c` (Tier 1)
- `src/cgif_rgb.c` (Tier 2)

## Library-Specific Verification Hazards (No Shortcuts)

1. **Pixel index validation against palette size & `transIndex` (`cgif.c`, `cgif_raw.c`).**
   Caller pixel indices (`uint8_t` in `0..255`) can exceed `numGlobalPaletteEntries` /
   `numLocalPaletteEntries` or collide with `transIndex`. Prove strict validation (`index < numColors`
   or rejected with `CGIF_EINDEX`) before indexing LZW tree nodes (`MAX_DICT_LEN = 4096`) or
   transparency maps.
2. **LZW trie / hash dictionary bounds & variable bit-width packing (`cgif_raw.c`).**
   Prove `initDictLen`, `curBitWidth` (`<= 12`), `CLEAR_CODE`, `EOI_CODE`, sub-block 255-byte
   chunking (`aSubBlock[256]`), and LZW table resets never overflow or shift by `>= 32`/`< 0`.
3. **Frame-difference bounding box & `CGIF_FRAME_GEN_USE_DIFF_WINDOW` (`cgif.c`).**
   When comparing current frame against `pPrevImageData` (`width * height` bytes, with `uint16_t`
   dimensions up to `65535 * 65535` — watch 32-bit `width * height` signed/unsigned overflow!),
   prove sub-rectangle `(left, top, subWidth, subHeight)` and identical-frame skipping stay in
   bounds for all non-zero and zero-diff frames.
4. **Write callback failure & error cleanup (`cgif_addframe` -> `cgif_close`).**
   Prove that if `pWriteFn` returns non-zero or `malloc` fails mid-animation, internal state
   transitions cleanly to error, no partial memory leaks occur, and calling `cgif_addframe` or
   `cgif_close` afterwards is safe and leak-free.

## Bootstrap & Local Commands

When onboarding into `framework/projects.json`: copy `lean-toolchain`,
start `CgifF/Runtime/Ptr.lean` from `framework/lean/StrictPtr.lean`, wire `CgifF/Results.lean` and
`project.json`, then run:

```bash
lake --dir projects/cgif build --wfail CgifF CgifF.Results
python3 framework/check_project.py cgif --skip-build
```
