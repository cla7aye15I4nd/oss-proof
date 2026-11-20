import MozjpegF.Mozjpeg.«jmemmgr.c»

/-!
# `jdatasrc.c` — memory data source translation (`MozjpegF`)

Source: `mozjpeg/jdatasrc.c` (`init_mem_source`, `fill_mem_input_buffer`,
`skip_input_data`, `term_source`, `jpeg_mem_src`).
-/

set_option autoImplicit false

namespace Mozjpeg.Jdatasrc
open C Mozjpeg.MoreCfg Mozjpeg.JpeglibH Mozjpeg.JerrorH Mozjpeg.Jmemmgr

/-- `METHODDEF(void) init_mem_source(j_decompress_ptr cinfo)` (`jdatasrc.c:59-63`). -/
def init_mem_source (_cinfo : DecompPtr) : M Unit :=
  return ()

/-- `METHODDEF(boolean) fill_mem_input_buffer(j_decompress_ptr cinfo)` (`jdatasrc.c:124-143`).
Emits `WARNMS(cinfo, JWRN_JPEG_EOF)`, supplies static 4-byte EOI buffer `{0xFF, 0xD9, 0, 0}` with
`bytes_in_buffer = 2`, and returns `TRUE`. -/
def fill_mem_input_buffer (cinfo : DecompPtr) : M Int32 := do
  let dc ← Ptr.load cinfo
  warnms dc.err JWRN_JPEG_EOF
  let src ← Ptr.load dc.src
  Ptr.store dc.src { src with nextInputByte := .ref .const_eof 0, bytesInBuffer := 2 }
  return TRUE

/-- `METHODDEF(void) skip_input_data(j_decompress_ptr cinfo, long num_bytes)` (`jdatasrc.c:158-178`). -/
def skip_input_data (cinfo : DecompPtr) (num_bytes : Int64) : M Unit := do
  let dc ← Ptr.load cinfo
  if num_bytes > 0 then
    let rem ← cwhile
      (fun (nb : Int64) => do
        let src ← Ptr.load dc.src
        if nb.toInt > Int.ofNat src.bytesInBuffer.toNat then return (true, nb) else return (false, nb))
      (fun (nb : Int64) => do
        let src ← Ptr.load dc.src
        let nb' := Int64.ofInt (nb.toInt - Int.ofNat src.bytesInBuffer.toNat)
        if src.fillInputBuffer == .fn "fill_mem_input_buffer" then
          let _ ← fill_mem_input_buffer cinfo
          return nb'
        else
          ub "unsupported fill_input_buffer")
      num_bytes
    let src ← Ptr.load dc.src
    let nextP ← Ptr.add src.nextInputByte (Int.ofNat rem.toInt.toNat)
    let remU : UInt64 := rem.toInt.toNat.toUInt64
    Ptr.store dc.src {
      src with
      nextInputByte := nextP
      bytesInBuffer := src.bytesInBuffer - remU
    }

/-- `METHODDEF(void) term_source(j_decompress_ptr cinfo)` (`jdatasrc.c:199-203`). -/
def term_source (_cinfo : DecompPtr) : M Unit :=
  return ()

/-- `GLOBAL(void) jpeg_mem_src(j_decompress_ptr cinfo, const unsigned char *inbuffer, unsigned long insize)`
(`jdatasrc.c:257-289`). -/
def jpeg_mem_src (cinfo : DecompPtr) (inbuffer : BPtr) (insize : UInt64) : M (JpegRes Unit) := do
  let dc ← Ptr.load cinfo
  if inbuffer == .null || insize == 0 then
    let _ ← errexit dc.err JERR_INPUT_EMPTY
    return .errExit JERR_INPUT_EMPTY
  if dc.src == .null then
    match (← alloc_small_src cinfo JPOOL_PERMANENT sizeof_jpeg_source_mgr) with
    | .errExit code => return .errExit code
    | .ok p =>
      let dc1 ← Ptr.load cinfo
      Ptr.store cinfo { dc1 with src := p }
  else
    let curSrc ← Ptr.load dc.src
    if curSrc.initSource != .fn "init_mem_source" then
      let _ ← errexit dc.err JERR_BUFFER_SIZE
      return .errExit JERR_BUFFER_SIZE
  let dc2 ← Ptr.load cinfo
  let src ← Ptr.load dc2.src
  Ptr.store dc2.src {
    src with
    initSource := .fn "init_mem_source"
    fillInputBuffer := .fn "fill_mem_input_buffer"
    skipInputData := .fn "skip_input_data"
    resyncToRestart := .fn "jpeg_resync_to_restart"
    termSource := .fn "term_source"
    bytesInBuffer := insize
    nextInputByte := inbuffer
  }
  return .ok ()

end Mozjpeg.Jdatasrc
