import MozjpegF.Mozjpeg.«jcomapi.c»
import MozjpegF.Mozjpeg.«jdmarker.c»
import MozjpegF.Mozjpeg.«jdinput.c»

/-!
# `jdapimin.c` — decompression API translations (`MozjpegF`)

Source: `mozjpeg/jdapimin.c` (`jpeg_CreateDecompress`, `jpeg_destroy_decompress`,
`jpeg_abort_decompress`, `jpeg_input_complete`, `jpeg_has_multiple_scans`).
-/

set_option autoImplicit false

namespace Mozjpeg.Jdapimin
open C Mozjpeg.MoreCfg Mozjpeg.JpeglibH Mozjpeg.JerrorH Mozjpeg.Jmemmgr Mozjpeg.Jcomapi
open Mozjpeg.Jdmarker Mozjpeg.Jdinput

/-- `GLOBAL(void) jpeg_CreateDecompress(j_decompress_ptr cinfo, int version, size_t structsize)`
(`jdapimin.c:35-99`). -/
def jpeg_CreateDecompress (cinfo : DecompPtr) (version : Int32) (structsize : UInt64) :
    M (JpegRes Unit) := do
  let dc0 ← Ptr.load cinfo
  Ptr.store cinfo { dc0 with mem := .null }
  if version != JPEG_LIB_VERSION then
    let _ ← errexit2 dc0.err JERR_BAD_LIB_VERSION JPEG_LIB_VERSION version
    return .errExit JERR_BAD_LIB_VERSION
  if structsize != sizeof_jpeg_decompress_struct then
    let _ ← errexit2 dc0.err JERR_BAD_STRUCT_SIZE
      (Int32.ofNat sizeof_jpeg_decompress_struct.toNat)
      (Int32.ofNat structsize.toNat)
    return .errExit JERR_BAD_STRUCT_SIZE
  let dc1 ← Ptr.load cinfo
  let err := dc1.err
  let client_data := dc1.clientData
  memsetZeroDecomp cinfo
  let dc2 ← Ptr.load cinfo
  Ptr.store cinfo { dc2 with err := err, clientData := client_data, isDecompressor := TRUE }
  match (← jinit_memory_mgr cinfo) with
  | .errExit code => return .errExit code
  | .ok () =>
    let dc3 ← Ptr.load cinfo
    Ptr.store cinfo {
      dc3 with
      progress := .null
      src := .null
      quantTblPtrs := Array.replicate 4 .null
      dcHuffTblPtrs := Array.replicate 4 .null
      acHuffTblPtrs := Array.replicate 4 .null
      markerList := .null
    }
    match (← jinit_marker_reader cinfo) with
    | .errExit code => return .errExit code
    | .ok () =>
      match (← jinit_input_controller cinfo) with
      | .errExit code => return .errExit code
      | .ok () =>
        let dc4 ← Ptr.load cinfo
        Ptr.store cinfo { dc4 with dataPrecision := 8, globalState := DSTATE_START }
        match (← alloc_small_master cinfo JPOOL_PERMANENT sizeof_my_decomp_master) with
        | .errExit code => return .errExit code
        | .ok mstPtr =>
          let dc5 ← Ptr.load cinfo
          Ptr.store cinfo { dc5 with master := mstPtr }
          memsetZeroMaster mstPtr
          return .ok ()

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
