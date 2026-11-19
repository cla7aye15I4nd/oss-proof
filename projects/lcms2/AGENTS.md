# Working rules (`projects/lcms2`)

Inherits every rule of the repository root [`../../AGENTS.md`](../../AGENTS.md), which is
authoritative on proof soundness, allowed axioms and the strict ISO C17 undefined-behaviour policy.
The runtime starts from `framework/lean/StrictPtr.lean`.

**Status:** candidate. Upstream submodule `lcms2/` tracks the latest default branch; not
registered in `framework/projects.json`; translation and proofs are not done.

## Tier 0

Tier 0 is the code that turns untrusted bytes into pixels or metadata on a default path. It is the
whole scope of this project.

**How it is reached.** When an input carries an embedded ICC profile (JPEG `APP2`, PNG `iCCP`,
WebP `ICCP`, TIFF tag 34675), Sharp's `src/pipeline.cc` converts it to sRGB with `icc_transform`
unless the caller keeps the profile; CMYK input is always converted. libvips
`colour/icc_transform.c` `vips_icc_transform` hands the profile bytes to lcms2. Pillow only uses
lcms2 when the application calls `ImageCms`, which is not a default path.

**Functions:** `cmsOpenProfileFromMem`, `cmsCloseProfile`, `cmsGetColorSpace`, `cmsGetPCS`,
`cmsGetDeviceClass`, `cmsGetHeaderRenderingIntent`, `cmsIsIntentSupported`, `cmsReadTag`,
`cmsCreateTransform`, `cmsDoTransform`, `cmsDeleteTransform`.

**What the proofs must cover.**

1. Tag directory offsets and sizes, and every tag reader `cmsCreateTransform` triggers (LUTs,
   curves, MLU, multi-process elements), stay inside the profile and free partial structures.
2. Colour lookup table sizes (grid points over all input channels × output channels) cannot
   overflow.
3. Untrusted curve values never reach an out-of-range float-to-integer conversion.

## Local commands

```bash
lake --dir projects/lcms2 build --wfail Lcms2F Lcms2F.Results
python3 framework/check_project.py lcms2 --skip-build
```
