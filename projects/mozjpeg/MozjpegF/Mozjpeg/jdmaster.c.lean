import MozjpegF.Mozjpeg.«jutils.c»

/-!
# `jdmaster.c` — output dimension & scaling translation (`MozjpegF`)

Source: `mozjpeg/jdmaster.c:34-371` (`use_merged_upsample`, `jpeg_core_output_dimensions`,
`jpeg_calc_output_dimensions`), `WITH_JPEG8 = 1`, `IDCT_SCALING_SUPPORTED`, `UPSAMPLE_MERGING_SUPPORTED`.
-/

set_option autoImplicit false

namespace Mozjpeg.Jdmaster
open C Mozjpeg.MoreCfg Mozjpeg.JerrorH Mozjpeg.JpeglibH Mozjpeg.Jutils

/-- `LOCAL(boolean) use_merged_upsample(j_decompress_ptr cinfo)` (`jdmaster.c:34-82`). -/
def use_merged_upsample (cinfo : DecompPtr) : M Int32 := do
  let dc ← Ptr.load cinfo
  let mst ← Ptr.load dc.master
  if mst.lossless != 0 then
    return FALSE
  if dc.doFancyUpsampling != 0 || dc.ccir601Sampling != 0 then
    return FALSE
  let supportedOut :=
    dc.outColorSpace == JCS_RGB ||
    dc.outColorSpace == JCS_RGB565 ||
    (dc.outColorSpace ≥ JCS_EXT_RGB && dc.outColorSpace ≤ JCS_EXT_ARGB)
  if dc.jpegColorSpace != JCS_YCbCr || dc.numComponents != 3 || !supportedOut then
    return FALSE
  let ps ←
    if dc.outColorSpace == JCS_RGB565 then pure (3 : Int32)
    else rgbPixelSize dc.outColorSpace
  if dc.outColorComponents != ps then
    return FALSE
  let c0 ← Ptr.index dc.compInfo 0
  let c1 ← Ptr.index dc.compInfo 1
  let c2 ← Ptr.index dc.compInfo 2
  if c0.hSampFactor != 2 || c1.hSampFactor != 1 || c2.hSampFactor != 1 ||
     c0.vSampFactor > 2 || c1.vSampFactor != 1 || c2.vSampFactor != 1 then
    return FALSE
  if c0.dctHScaledSize != dc.minDctHScaledSize ||
     c1.dctHScaledSize != dc.minDctHScaledSize ||
     c2.dctHScaledSize != dc.minDctHScaledSize then
    return FALSE
  return TRUE

/-- Helper matching `jdmaster.c:107-235` 1..16 IDCT scale-factor dispatch under C `unsigned int`
multiplication (`cinfo->scale_num * DCTSIZE <= cinfo->scale_denom * k`). -/
def selectIdctScale (scaleNum scaleDenom : UInt32) : UInt32 :=
  let lhs : UInt32 := scaleNum * 8
  go 15 1 lhs scaleDenom
where
  go : Nat → UInt32 → UInt32 → UInt32 → UInt32
    | 0, k, _, _ => k
    | rem + 1, k, lhs, denom =>
      if lhs ≤ denom * k then k else go rem (k + 1) lhs denom

/-- Component loop (`jdmaster.c:238-242`). -/
def setCompScaledSizes (compInfo : CompPtr) (ci n : Nat) (k32 : Int32) : M Unit :=
  if h : ci < n then do
    let compPtr ← Ptr.add compInfo (Int.ofNat ci)
    let comp ← Ptr.load compPtr
    Ptr.store compPtr { comp with dctHScaledSize := k32, dctVScaledSize := k32 }
    setCompScaledSizes compInfo (ci + 1) n k32
  else
    pure ()
termination_by n - ci

/-- `GLOBAL(void) jpeg_core_output_dimensions(j_decompress_ptr cinfo)` (`jdmaster.c:96-253`). -/
def jpeg_core_output_dimensions (cinfo : DecompPtr) : M Unit := do
  let dc ← Ptr.load cinfo
  let mst ← Ptr.load dc.master
  if mst.lossless == 0 then
    let k := selectIdctScale dc.scaleNum dc.scaleDenom
    let k64 : Int64 := Int64.ofNat k.toNat
    let w64 ← i64Mul (Int64.ofNat dc.imageWidth.toNat) k64
    let outW ← jdiv_round_up w64 8
    let h64 ← i64Mul (Int64.ofNat dc.imageHeight.toNat) k64
    let outH ← jdiv_round_up h64 8
    let k32 : Int32 := Int32.ofNat k.toNat
    Ptr.store cinfo {
      dc with
      outputWidth := outW.toInt.toNat.toUInt32
      outputHeight := outH.toInt.toNat.toUInt32
      minDctHScaledSize := k32
      minDctVScaledSize := k32
    }
    let dc ← Ptr.load cinfo
    if dc.numComponents < 0 then
      ub "negative num_components"
    setCompScaledSizes dc.compInfo 0 dc.numComponents.toInt.toNat k32
  else
    Ptr.store cinfo {
      dc with
      outputWidth := dc.imageWidth
      outputHeight := dc.imageHeight
    }

/-- Inner adaptation loop `ssize` of `jpeg_calc_output_dimensions` (`jdmaster.c:289-296`). -/
def adaptComponentDctSize (maxH maxV minDct hSamp vSamp : Int32) : M Int32 := do
  let targetH ← i32Mul maxH minDct
  let targetV ← i32Mul maxV minDct
  cwhile
    (fun s => do
      if s < DCTSIZE then
        let s2 ← i32Mul s 2
        let dh ← i32Mul hSamp s2
        let mh ← i32Mod targetH dh
        if mh == 0 then
          let dv ← i32Mul vSamp s2
          let mv ← i32Mod targetV dv
          return (mv == 0, s)
        else
          return (false, s)
      else
        return (false, s))
    (fun s => i32Mul s 2)
    minDct

/-- Chroma IDCT scaling adaptation loop (`jdmaster.c:287-302`). -/
def adaptCompLoop (compInfo : CompPtr) (ci n : Nat) (maxH maxV minDct : Int32) : M Unit :=
  if h : ci < n then do
    let compPtr ← Ptr.add compInfo (Int.ofNat ci)
    let comp ← Ptr.load compPtr
    let ssize ← adaptComponentDctSize maxH maxV minDct comp.hSampFactor comp.vSampFactor
    Ptr.store compPtr { comp with dctHScaledSize := ssize, dctVScaledSize := ssize }
    adaptCompLoop compInfo (ci + 1) n maxH maxV minDct
  else
    pure ()
termination_by n - ci

/-- Component downsampled dimension loop (`jdmaster.c:307-320`). -/
def downsampleCompLoop (compInfo : CompPtr) (ci n : Nat) (imgW imgH : UInt32) (maxH maxV : Int32) : M Unit :=
  if h : ci < n then do
    let compPtr ← Ptr.add compInfo (Int.ofNat ci)
    let comp ← Ptr.load compPtr
    let sw ← i32Mul comp.hSampFactor comp.dctHScaledSize
    let sh ← i32Mul comp.vSampFactor comp.dctHScaledSize
    let dwNum ← i64Mul (Int64.ofNat imgW.toNat) (Int64.ofInt sw.toInt)
    let dwDen ← i64Mul (Int64.ofInt maxH.toInt) 8
    let dw ← jdiv_round_up dwNum dwDen
    let dhNum ← i64Mul (Int64.ofNat imgH.toNat) (Int64.ofInt sh.toInt)
    let dhDen ← i64Mul (Int64.ofInt maxV.toInt) 8
    let dh ← jdiv_round_up dhNum dhDen
    Ptr.store compPtr {
      comp with
      downsampledWidth := dw.toInt.toNat.toUInt32
      downsampledHeight := dh.toInt.toNat.toUInt32
    }
    downsampleCompLoop compInfo (ci + 1) n imgW imgH maxH maxV
  else
    pure ()
termination_by n - ci

/-- `GLOBAL(void) jpeg_calc_output_dimensions(j_decompress_ptr cinfo)` (`jdmaster.c:263-371`). -/
def jpeg_calc_output_dimensions (cinfo : DecompPtr) : M (JpegRes Unit) := do
  let dc ← Ptr.load cinfo
  if dc.globalState != DSTATE_READY then
    let _ ← errexit1 dc.err JERR_BAD_STATE dc.globalState
    return .errExit JERR_BAD_STATE
  jpeg_core_output_dimensions cinfo
  let dc ← Ptr.load cinfo
  let mst ← Ptr.load dc.master
  if mst.lossless == 0 then
    if dc.numComponents < 0 then
      ub "negative num_components"
    let n := dc.numComponents.toInt.toNat
    adaptCompLoop dc.compInfo 0 n dc.maxHSampFactor dc.maxVSampFactor dc.minDctHScaledSize
    downsampleCompLoop dc.compInfo 0 n dc.imageWidth dc.imageHeight dc.maxHSampFactor dc.maxVSampFactor
  let dc ← Ptr.load cinfo
  let outCC ←
    if dc.outColorSpace == JCS_GRAYSCALE then pure (1 : Int32)
    else if dc.outColorSpace == JCS_RGB ||
            (dc.outColorSpace ≥ JCS_EXT_RGB && dc.outColorSpace ≤ JCS_EXT_ARGB) then
      rgbPixelSize dc.outColorSpace
    else if dc.outColorSpace == JCS_YCbCr || dc.outColorSpace == JCS_RGB565 then pure (3 : Int32)
    else if dc.outColorSpace == JCS_CMYK || dc.outColorSpace == JCS_YCCK then pure (4 : Int32)
    else pure dc.numComponents
  let outComps : Int32 := if dc.quantizeColors != 0 then 1 else outCC
  Ptr.store cinfo { dc with outColorComponents := outCC, outputComponents := outComps }
  let merged ← use_merged_upsample cinfo
  let dc ← Ptr.load cinfo
  let recH : Int32 := if merged != 0 then dc.maxVSampFactor else 1
  Ptr.store cinfo { dc with recOutbufHeight := recH }
  return .ok ()

end Mozjpeg.Jdmaster
