# Working rules (`projects/freetype`)

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

- **Status:** Upstream submodule `freetype/` pinned (not yet registered in `framework/projects.json`;
  Lean runtime bootstrap, C translation, and safety proofs **Not done**).

## Scope (`FreetypeF`)

- **Upstream source:** `freetype/` pinned submodule (`https://gitlab.freedesktop.org/freetype/freetype`)
  + `patches/*.patch` in name order.
- **Target configuration:** tightly scoped, portable scalar x86_64 Linux LP64 build enabling **only
  the modern web/desktop font modules that actually matter in Pillow, Sharp, and browsers**
  (`base`, `sfnt`, `truetype`, `cff`, `psaux`, `pshinter`, `psnames`, `smooth`, `raster`,
  `autofit`, `stroke`, linking our proved `zlib` for WOFF/compressed tables; disabling legacy
  Type1/CID/PCF/BDF/WinFNT/PFR/Type42 drivers and optional OT-SVG/Brotli hooks in Tier 1).
- **Verification goal:** full safety (no ISO C17 undefined behaviour, no heap buffer overflow in
  SFNT table / TrueType bytecode VM / CFF CharString interpreter / smooth rasterizer, no signed
  fixed-point `FT_Fixed` overflow UB, no UAF/double-free on `FT_Done_Face` / `FT_Stroker_Done`,
  stated write frame, and termination) across every FreeType entry point called by **Pillow
  (`src/_imagingft.c`)** and **Sharp / `libvips` (`pango`/`cairo`)**.

## Real-World Usage Paths & Function Priority

FreeType parses extraordinarily complex binary font formats (including two embedded bytecode VMs:
the TrueType Hinting VM and the CFF/Type2 CharString VM!) and is a classic zero-day RCE target
across browsers, OSes, PDF renderers, **Pillow** (custom user fonts, CAPTCHA/thumbnail/OG-image
generators), and **Sharp** (SVG `<text>` and `create: { text }` rendering):
- **PIL / Pillow (`src/_imagingft.c` -> `PIL.ImageFont.truetype`, `ImageDraw.text`):**
  Directly invokes `FT_Init_FreeType`, `FT_New_Memory_Face`, `FT_New_Face`, `FT_Select_Charmap`,
  `FT_Set_Pixel_Sizes`, `FT_Set_Char_Size`, `FT_Get_Char_Index`, `FT_Load_Glyph`, `FT_Render_Glyph`,
  `FT_Get_Glyph`, `FT_Glyph_Stroke`, `FT_Glyph_To_Bitmap`, `FT_Stroker_New`, `FT_Stroker_Set`,
  `FT_Stroker_Done`, `FT_Done_Glyph`, `FT_Done_Face`, `FT_Done_FreeType`, plus variable-font
  axes (`FT_Get_MM_Var`, `FT_Set_Var_Design_Coordinates`).
  *(Note: Pillow itself had invalid-free / uninitialized-pointer bugs in `_imagingft.c` around
  `FT_Load_Glyph` + stroker error unwinding.)*
- **Sharp / `libvips` (`pango` -> `cairo` -> `freetype`) & Browsers / PDFs:**
  Same core `FT_New_Memory_Face` -> `FT_Load_Glyph` -> `FT_Render_Glyph` pipeline over TrueType
  (`.ttf`) and OpenType/CFF (`.otf`).

### Tier 1 (P0) — Modern TrueType/OpenType Core (`sfnt` + `truetype` + `smooth` + `stroke`, Prove First)

1. **Base library, memory, stream, outline & stroker (`src/base/ftinit.c`, `ftobjs.c`, `ftstream.c`,
   `ftsystem.c`, `ftutil.c`, `ftcalc.c`, `ftoutln.c`, `ftglyph.c`, `ftbitmap.c`, `ftstroke.c`,
   `ftmm.c`, `fttrigon.c`, `ftbbox.c`):**
   `FT_Init_FreeType`, `FT_Done_FreeType`, `FT_New_Memory_Face`, `FT_Done_Face`, `FT_Set_Pixel_Sizes`,
   `FT_Set_Char_Size`, `FT_Get_Char_Index`, `FT_Load_Glyph`, `FT_Render_Glyph`, `FT_Get_Glyph`,
   `FT_Glyph_Stroke`, `FT_Glyph_To_Bitmap`, `FT_Stroker_New`, `FT_Stroker_Set`, `FT_Stroker_Done`,
   `FT_Done_Glyph`.
2. **SFNT container & tables (`src/sfnt/`: `sfobjs.c`, `ttload.c`, `ttcmap.c`, `ttmtx.c`, `ttkern.c`,
   `ttpost.c`, `ttsbit.c`, `ttcolr.c`, `ttcpal.c`, `pngshim.c`):**
   OpenType table directory, `cmap`, `head`/`hhea`/`hmtx`/`maxp`/`loca`/`glyf`, embedded bitmaps
   (`CBDT`/`CBLC`/`sbix` — note historical `CVE-2020-15999` heap overflow in `Load_SBit_Png`!),
   and `COLR`/`CPAL` color glyphs.
3. **TrueType glyph loader & bytecode VM (`src/truetype/`: `ttobjs.c`, `ttdriver.c`, `ttgload.c`,
   `ttpload.c`, `ttinterp.c`, `ttgxvar.c`):**
   Composite glyph recursion, `glyf` contour parsing, `gvar` variable-font deltas, and the
   stack-based TrueType hinting VM (`ttinterp.c` — historically a huge source of OOB stack/storage/
   twilight-zone memory corruption).
4. **Anti-aliased scan-converter & monochrome rasterizer (`src/smooth/ftgrays.c`, `ftsmooth.c`,
   `src/raster/ftraster.c`, `ftrend1.c`):**
   Cell-pool rasterization (`ftgrays.c`) into caller/slot bitmaps.

### Tier 2 (P1) — OpenType CFF / CFF2 Driver & Auto-Hinter

- **CFF / CFF2 & PS auxiliary (`src/cff/`, `src/psaux/`, `src/pshinter/`, `src/psnames/`):**
  OpenType `.otf` CFF/CFF2 Index parsing and Type2 CharString bytecode interpreter (`cffgload.c`,
  `psintrp.c` — critical web font format alongside TrueType).
- **Auto-hinter (`src/autofit/`):** Invoked when `FT_LOAD_FORCE_AUTOHINT` or unhinted glyphs run.

### Explicitly Not Planned

- Legacy/obsolete font drivers not needed for modern web/Pillow/Sharp pipelines: `type1`, `cid`,
  `type42`, `pcf`, `bdf`, `winfonts`, `pfr`, `lzw`, `gzip`, `bzip2` wrappers, `otvalid`/`gxvalid`,
  and external `librsvg` OT-SVG hook (`FT_CONFIG_OPTION_SVG`).
- Visual hinting fidelity / typographic rendering equivalence beyond safety invariants.

## Library-Specific Verification Hazards (No Shortcuts)

1. **TrueType & CFF2 bytecode VMs (`src/truetype/ttinterp.c`, `src/psaux/psintrp.c`).**
   Both are Turing-complete-like stack VMs executing untrusted bytecode embedded inside font files!
   Prove strict bounds on execution stack (`stack[stackSize]`), storage area (`storage[storeSize]`),
   CVT (`cvt[cvtSize]`), twilight/glyph point zones (`zp0`/`zp1`/`zp2`), call-stack depth, and loop
   counters (guaranteed termination via instruction-count fuel limits enforced by FreeType!).
2. **Signed 16.16 / 26.6 fixed-point arithmetic UB (`ftcalc.c`, `ttgload.c`, `ttinterp.c`,
   `ftgrays.c`, `ftstroke.c`).**
   FreeType performs pervasive signed arithmetic on `FT_Pos` (`long`) and `FT_Fixed`; under strict
   ISO C17, signed overflow and negative left shifts are `Fault.ub` (upstream uses `ADD_LONG`/
   `SUB_LONG` unsigned-wrapping macros in many places — audit every raw signed op!).
3. **Composite glyph recursion & `gvar` variable-font tuple deltas (`ttgload.c`, `ttgxvar.c`).**
   Prove cyclic composite glyphs terminate via recursion depth caps and point-count / delta-array
   allocations match across `glyf` + `gvar` + phantom points.
4. **Embedded bitmap / `CBDT`/`sbix` dimension overflow (`ttsbit.c`, `pngshim.c` — `CVE-2020-15999`).**
   Prove `uint16_t`/`uint32_t` bitmap width/height/pitch calculations cannot truncate or under-allocate
   before decoding into `slot->bitmap.buffer`.
5. **Smooth rasterizer cell-pool overflow & `FT_Outline` bounds (`src/smooth/ftgrays.c`,
   `src/base/ftstroke.c`).**
   Prove Bezier subdivision stack depth (`32 * 3 + 1`), clip-box coordinates (`min_ex..max_ex`,
   `min_ey..max_ey`), cell-pool band splitting, and stroker point-array growth never write out of
   bounds.

## Bootstrap & Local Commands

When onboarding into `framework/projects.json`: copy `lean-toolchain`,
start `FreetypeF/Runtime/Ptr.lean` from `framework/lean/StrictPtr.lean`, wire
`FreetypeF/Results.lean` and `project.json`, then run:

```bash
lake --dir projects/freetype build --wfail FreetypeF FreetypeF.Results
python3 framework/check_project.py freetype --skip-build
```
