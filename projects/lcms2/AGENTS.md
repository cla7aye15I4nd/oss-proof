# Working rules (`projects/lcms2`)

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

- **Status:** Scoped candidate project (not yet registered in `framework/projects.json`; Lean
  runtime bootstrap, upstream submodule pin, C translation, and safety proofs **Not done**).

## Scope (`Lcms2F`)

- **Upstream source:** `lcms2/` pinned submodule (`https://github.com/mm2/Little-CMS`) +
  `patches/*.patch` in name order.
- **Target configuration:** portable scalar, single-threaded x86_64 Linux LP64 build
  (`-DCMS_NO_PTHREADS`, default `malloc`/`free` allocator, pure C ~35k LOC).
- **Verification goal:** full safety (no ISO C17 undefined behaviour, no integer overflow or heap
  buffer overflow in ICC tag/LUT/CLUT/curve parsers, no null dereference or div-by-zero in
  pipeline optimization/evaluation, no memory leak or UAF across `cmsCloseProfile` /
  `cmsDeleteTransform`, stated write frame, and termination) across the real-world ICC profile
  loading, transform compilation, pixel-transform execution, and profile-saving APIs in `lcms2.h`.

## Real-World Usage Paths & Function Priority

Almost every image format on the web (JPEG `APP2`, PNG `iCCP`, WebP `ICCP`, TIFF tag `34675`,
AVIF `colr`) can carry an **attacker-controlled embedded binary ICC color profile** — and both
**Sharp** and **Pillow** feed those untrusted bytes straight into `lcms2`:
- **Sharp / `libvips` (`libvips/colour/icc_transform.c` — `vips_icc_transform`, `vips_icc_import`,
  `vips_icc_export`):** Invoked whenever `.toColorspace('srgb')`, `.pipelineColourspace()`, or
  CMYK-to-sRGB conversion encounters an embedded ICC profile. Calls `cmsOpenProfileFromMem`,
  `cmsCreate_sRGBProfile`, `cmsCreateTransform`, `cmsCreateMultiprofileTransform`,
  `cmsDoTransform`, `cmsGetColorSpace`, `cmsGetPCS`, `cmsGetHeaderRenderingIntent`,
  `cmsIsIntentSupported`, `cmsCloseProfile`, `cmsDeleteTransform`.
- **PIL / Pillow (`src/_imagingcms.c` — `PIL.ImageCms`):** Calls `cmsOpenProfileFromMem`,
  `cmsOpenProfileFromFile`, `cmsCreateTransform`, `cmsCreateProofingTransform`,
  `cmsCreate_sRGBProfile`, `cmsDoTransform`, `cmsGetProfileInfoASCII`, `cmsGetHeaderFlags`,
  `cmsGetHeaderProfileID`, `cmsSaveProfileToMem`, `cmsCloseProfile`, `cmsDeleteTransform`.
- **Browsers, PDF & Print Engines (Chromium/PDFium, Firefox, Ghostscript, OpenJDK, ImageMagick):**
  Same untrusted embedded ICC profile -> `cmsOpenProfileFromMem` -> `cmsCreateTransform` ->
  `cmsDoTransform` pipeline.
- **Historical CVE Patterns:** Heap OOB writes/reads in `SetData` / `Type_LUT*` / `Type_MLU_Read`
  / `Type_MPE_Read` (`CVE-2018-16435`), integer overflows in CLUT grid-point allocation (`nGridPoints`),
  null derefs and signed shift/float-to-int UB on crafted v2/v4 ICC tags.

### Tier 1 (P0) — Untrusted ICC Profile Parsing, Transform Compilation & Execution (Prove First)

1. **Profile I/O, header & tag-table parsing (`cmsio0.c`, `cmsio1.c`, `cmstypes.c`, `cmsnamed.c`,
   `cmserr.c`, `cmsmd5.c`):**
   `cmsOpenProfileFromMem`, `cmsOpenProfileFromMemTHR`, `cmsCloseProfile`, `cmsReadTag`,
   `cmsIsTag`, `cmsGetTagCount`, `cmsGetTagSignature`, `cmsGetColorSpace`, `cmsGetPCS`,
   `cmsGetDeviceClass`, `cmsGetEncodedICCversion`, `cmsGetHeaderRenderingIntent`,
   `cmsGetHeaderFlags`, `cmsGetProfileInfo`, `cmsGetProfileInfoASCII`, `cmsIsIntentSupported`,
   `cmsCreate_sRGBProfile`, `cmsCreateXYZProfile`, `cmsCreateLab4Profile`.
2. **Transform compilation, pipeline optimizer & pixel evaluation (`cmsxform.c`, `cmscnvrt.c`,
   `cmslut.c`, `cmsopt.c`, `cmspack.c`, `cmsgamma.c`, `cmsintrp.c`, `cmspcs.c`, `cmsmtrx.c`,
   `cmswtpnt.c`, `cmsvirt.c`):**
   `cmsCreateTransform`, `cmsCreateTransformTHR`, `cmsCreateProofingTransform`,
   `cmsCreateMultiprofileTransform`, `cmsDoTransform`, `cmsDoTransformLineStride`,
   `cmsDeleteTransform`, `cmsChangeBuffersFormat`.

### Tier 2 (P1) — Profile Serialization & Secondary Color APIs

- **Profile writing (`cmsio0.c`, `cmstypes.c`):** `cmsSaveProfileToMem`, `cmsWriteTag`,
  `cmsWriteRawTag` (used by Pillow `ImageCms.ImageCmsProfile.tobytes()` and profile builders).
- **Secondary inspection/helpers (`cmsplugin.c`, `cmsalpha.c`, `cmssamp.c`, `cmsgmt.c`):**
  Black-point compensation (`cmsDetectBlackPoint`), alpha-copy transforms, context creation
  (`cmsCreateContext`, `cmsDeleteContext`).

### Explicitly Not Planned

- PostScript CSA/CRD generators (`cmsps2.c`), CIECAM02 (`cmscam02.c`), CGATS/IT8 text parser
  (`cmscgats.c`), third-party plugin registration (`cmsPlugin`), file-path I/O wrappers beyond
  in-memory `cmsIOHANDLER`, and colorimetric perceptual accuracy proofs beyond safety invariants.

## Verified Translation Units

- `include/lcms2.h`, `include/lcms2_plugin.h`, `src/lcms2_internal.h`
- `src/cmsio0.c`, `src/cmsio1.c`, `src/cmstypes.c`, `src/cmsxform.c`, `src/cmscnvrt.c`,
  `src/cmslut.c`, `src/cmsopt.c`, `src/cmspack.c`, `src/cmsgamma.c`, `src/cmsintrp.c`,
  `src/cmspcs.c`, `src/cmsmtrx.c`, `src/cmsnamed.c`, `src/cmswtpnt.c`, `src/cmsvirt.c`,
  `src/cmserr.c`, `src/cmsmd5.c`, `src/cmsalpha.c`, `src/cmssamp.c`, `src/cmsgmt.c`,
  `src/cmsplugin.c`

## Library-Specific Verification Hazards (No Shortcuts)

1. **ICC tag-directory offset/size overflows & lazy tag deserialization (`cmsio0.c`, `cmstypes.c`).**
   ICC profiles store a tag table with arbitrary 32-bit `(offset, size)` pairs (including overlapping
   tags and `offset + size` wraparound) that are lazily parsed on `cmsReadTag`. Prove every
   `Type_*_Read` handler (`Type_LUT8_Read`, `Type_LUT16_Read`, `Type_LUTAToB_Read`,
   `Type_Curve_Read`, `Type_ParametricCurve_Read`, `Type_MLU_Read`, `Type_MPE_Read`, `Type_Text_*`)
   enforces strict byte-budget bounds and frees partial structures on error without UAF/leak.
2. **CLUT grid-dimension multiplication overflow (`cmslut.c`, `cmsintrp.c` — `CVE-2018-16435` class).**
   N-dimensional color lookup tables multiply `nGridPoints[0] * ... * nGridPoints[nIn-1] * nOut`.
   Prove overflow-checked allocation sizing and strict in-bounds tetrahedral/trilinear interpolation
   indices for `nIn` up to `cmsMAXCHANNELS` (16).
3. **Pixel format unpacker / packer strides (`cmspack.c`, `cmsxform.c`).**
   `cmsDoTransform` dispatches to format-specific `Unroll*` / `Pack*` callbacks across planar,
   chunky, premultiplied, swapped, 8-bit, 16-bit, and float formats. Prove caller input/output
   buffers of `Size * bytesPerPixel` (or `LineStride`) are never overrun.
4. **Curve evaluation, division by zero & float-to-integer conversion UB (`cmsgamma.c`, `cmsopt.c`,
   `cmsmtrx.c`).**
   Untrusted parametric curves, tone curves, and `XYZ` matrices can contain `0`, `NaN`, `Inf`, or
   huge values that become UB when cast to `cmsUInt16Number` / `cmsInt32Number` in ISO C17
   (§6.3.1.4). Audit and prove finite clamped conversions everywhere.
5. **Transform optimizer & LUT cache aliasing (`cmsopt.c`, `cmsxform.c`).**
   Prove that `OptimizeByResampling` / `OptimizeMatrixShaper` / 1-pixel cache buffers preserve
   channel counts (`InputChannels`, `OutputChannels`) and free intermediate pipelines cleanly.

## Bootstrap & Local Commands

When onboarding into `framework/projects.json`: pin `lcms2/` submodule, copy `lean-toolchain`,
start `Lcms2F/Runtime/Ptr.lean` from `framework/lean/StrictPtr.lean`, wire `Lcms2F/Results.lean`
and `project.json`, then run:

```bash
lake --dir projects/lcms2 build --wfail Lcms2F Lcms2F.Results
python3 framework/check_project.py lcms2 --skip-build
```
