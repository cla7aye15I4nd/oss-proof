# Working rules (`projects/lcms2`)

Inherits every rule of the repository root [`../../AGENTS.md`](../../AGENTS.md), including the strict
ISO C17 undefined-behaviour policy: no `NULL`, wild or dangling pointer `+ 0`, no `NULL - NULL`, no
cross-object pointer subtraction or comparison, no out-of-bounds pointer formation, no zero-length
`memcpy`/`memset` on invalid pointers, every struct pointer field written before it is read, and no
"benign UB" arguments. The runtime starts from `framework/lean/StrictPtr.lean`.

- **Status:** candidate. Upstream submodule `lcms2/` tracks the latest default branch. Not
  registered in `framework/projects.json`; translation and proofs are not done.

## Why it matters

- **Sharp (default path):** when an input carries an embedded ICC profile, Sharp's pipeline
  converts it to sRGB (or P3) with `icc_transform` / `icc_import`, which libvips implements in
  `colour/icc_transform.c` and `colour/profile_load.c` on top of lcms2 (2.19.1 in Sharp 0.35.5).
  CMYK input is always converted. The profile bytes come straight from the upload (JPEG `APP2`,
  PNG `iCCP`, WebP `ICCP`, TIFF tag 34675, HEIF `colr`).
- **Pillow (on request only):** `src/_imagingcms.c` runs only when the application calls
  `PIL.ImageCms`.

## Interfaces to prove (P0)

- **Sharp / libvips:** `cmsOpenProfileFromMem`, `cmsOpenProfileFromFile`, `cmsCloseProfile`,
  `cmsGetColorSpace`, `cmsGetPCS`, `cmsGetDeviceClass`, `cmsGetProfileVersion`,
  `cmsGetHeaderRenderingIntent`, `cmsGetProfileInfoASCII`, `cmsGetSupportedIntents`,
  `cmsIsIntentSupported`, `cmsIsCLUT`, `cmsIsMatrixShaper`, `cmsReadTag`, `cmsCreateLab4Profile`,
  `cmsCreateXYZProfile`, `cmsWhitePointFromTemp`, `cmsCreateTransform`, `cmsDoTransform`,
  `cmsDeleteTransform`, `cmsSetLogErrorHandler`.
- **Pillow, in addition:** `cmsCreate_sRGBProfile`, `cmsCreateLab2Profile`,
  `cmsCreateProofingTransform`, `cmsSaveProfileToMem`, `cmsIsTag`, `cmsMLUgetWide`, the
  `cmsGetHeader*` accessors, `cmsNamedColorCount`, `cmsNamedColorInfo`.

## Verification hazards

1. Tag directory entries with arbitrary offsets and sizes, read lazily by `cmsReadTag`.
2. Tag type readers (LUT8/LUT16, AToB/BToA, curves, parametric curves, MLU, multi-process
   elements) freeing partial structures on error.
3. Colour lookup table size: product of grid points over all input channels times output channels.
4. Pipeline optimisation and interpolation indices; float-to-integer conversions of untrusted
   curve values (out-of-range conversion is undefined in ISO C17).
5. Pixel formatters (`cmsDoTransform` unpack/pack) against the caller's buffer size.

## Not in scope

Threads (build with `CMS_NO_PTHREADS`), plug-in registration, PostScript generation, CGATS/IT8
parsing, CIECAM02, and colour accuracy.

## Local commands

```bash
lake --dir projects/lcms2 build --wfail Lcms2F Lcms2F.Results
python3 framework/check_project.py lcms2 --skip-build
```
