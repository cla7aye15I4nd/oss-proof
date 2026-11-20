import MozjpegF.Mozjpeg.«jcomapi.c»

/-!
# `jdapimin.c` — initial decompression API translations (`MozjpegF`)

Source: `mozjpeg/jdapimin.c` (`jpeg_destroy_decompress`, `jpeg_abort_decompress`,
`jpeg_input_complete`, `jpeg_has_multiple_scans`).
-/

set_option autoImplicit false

namespace Mozjpeg.Jdapimin
open C Mozjpeg.JpeglibH Mozjpeg.JerrorH Mozjpeg.Jcomapi

/-- `GLOBAL(void) jpeg_destroy_decompress(j_decompress_ptr cinfo)` (`jdapimin.c:106-110`). -/
def jpeg_destroy_decompress (cinfo : DecompPtr) : M Unit :=
  jpeg_destroy cinfo

/-- `GLOBAL(void) jpeg_abort_decompress(j_decompress_ptr cinfo)` (`jdapimin.c:118-122`). -/
def jpeg_abort_decompress (cinfo : DecompPtr) : M Unit :=
  jpeg_abort cinfo

/-- `GLOBAL(boolean) jpeg_input_complete(const j_decompress_ptr cinfo)` (`jdapimin.c:359-367`). -/
def jpeg_input_complete (cinfo : DecompPtr) : M (JpegRes Int32) := do
  let dc ← Ptr.load cinfo
  if dc.globalState < DSTATE_START || dc.globalState > DSTATE_STOPPING then
    let _ ← errexit1 dc.err JERR_BAD_STATE dc.globalState
    return .errExit JERR_BAD_STATE
  let ic ← Ptr.load dc.inputctl
  return .ok ic.eoiReached

/-- `GLOBAL(boolean) jpeg_has_multiple_scans(const j_decompress_ptr cinfo)` (`jdapimin.c:374-382`). -/
def jpeg_has_multiple_scans (cinfo : DecompPtr) : M (JpegRes Int32) := do
  let dc ← Ptr.load cinfo
  if dc.globalState < DSTATE_READY || dc.globalState > DSTATE_STOPPING then
    let _ ← errexit1 dc.err JERR_BAD_STATE dc.globalState
    return .errExit JERR_BAD_STATE
  let ic ← Ptr.load dc.inputctl
  return .ok ic.hasMultipleScans

end Mozjpeg.Jdapimin
