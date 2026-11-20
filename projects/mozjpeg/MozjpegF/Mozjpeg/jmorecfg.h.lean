import MozjpegF.Runtime.Libc

/-!
# `jmorecfg.h` — faithful definitions (`MozjpegF`)

Source: `mozjpeg/jmorecfg.h`, LP64 Linux build with `WITH_JPEG8 = 1`, `BITS_IN_JSAMPLE = 8`.
-/

set_option autoImplicit false

namespace Mozjpeg.MoreCfg
open C

def MAX_COMPONENTS : Int32 := 10
def MAXJSAMPLE : Int32 := 255
def CENTERJSAMPLE : Int32 := 128

def FALSE : Int32 := 0
def TRUE : Int32 := 1

def JPEG_NUMCS : Int32 := 17

/-- `static const int rgb_pixelsize[JPEG_NUMCS]` (`jmorecfg.h:353-358`). -/
def rgb_pixelsize : Array Int32 := #[
  -1, -1, 3, -1, -1, -1,
  3, 4, 3, 4, 4, 4, 4, 4, 4, 4, -1
]

/-- Look up `rgb_pixelsize[cs]` with explicit ISO C17 bounds checking. -/
def rgbPixelSize (cs : Int32) : M Int32 := do
  if cs < 0 || cs ≥ JPEG_NUMCS then
    ub "rgb_pixelsize index out of bounds"
  else
    match rgb_pixelsize[cs.toInt.toNat]? with
    | some v => pure v
    | none => ub "rgb_pixelsize index out of bounds"

end Mozjpeg.MoreCfg
