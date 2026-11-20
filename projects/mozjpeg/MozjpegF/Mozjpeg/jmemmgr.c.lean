import MozjpegF.Mozjpeg.«jmemnobs.c»

/-!
# `jmemmgr.c` — pooled memory manager translation (`MozjpegF`)

Source: `mozjpeg/jmemmgr.c` (LP64 Linux without `WITH_SIMD`: `ALIGN_SIZE = 8`,
`MAX_ALLOC_CHUNK = 1000000000`).
-/

set_option autoImplicit false

namespace Mozjpeg.Jmemmgr
open C Mozjpeg.JpeglibH Mozjpeg.JerrorH Mozjpeg.Jmemnobs

def ALIGN_SIZE : UInt64 := 8
def MAX_ALLOC_CHUNK : Int64 := 1000000000
def sizeof_small_pool_hdr : UInt64 := 24
def MIN_SLOP : UInt64 := 50

def first_pool_slop : Array UInt64 := #[1600, 16000]
def extra_pool_slop : Array UInt64 := #[0, 5000]

/-- `LOCAL(size_t) round_up_pow2(size_t a, size_t b)` (`jmemmgr.c:41-47`). -/
def round_up_pow2 (a b : UInt64) : UInt64 :=
  (a + b - 1) &&& (~~~(b - 1))

/-- `LOCAL(void) out_of_memory(j_common_ptr cinfo, int which)` (`jmemmgr.c:225-232`). -/
def out_of_memory (cinfo : DecompPtr) (which : Int32) : M (JpegRes Unit) := do
  let dc ← Ptr.load cinfo
  errexit1 dc.err JERR_OUT_OF_MEMORY which

def allocSlopRetry {R : Type} [DecidableEq R] (cinfo : DecompPtr)
    (allocFn : M (Ptr R)) : Nat → UInt64 → M (JpegRes (Ptr R))
  | 0, _ => do
    let _ ← out_of_memory cinfo 2
    return .errExit JERR_OUT_OF_MEMORY
  | k + 1, slop => do
    let p ← allocFn
    if p != .null then
      return .ok p
    else
      let slop' := slop / 2
      if slop' < MIN_SLOP then
        let _ ← out_of_memory cinfo 2
        return .errExit JERR_OUT_OF_MEMORY
      else
        allocSlopRetry cinfo allocFn k slop'

/-- Common `alloc_small` size and pool-ID checks (`jmemmgr.c:265-295`), followed by typed allocation
and `slop` halving fallback when `alloc` fails (`jmemmgr.c:296-345`). -/
def allocSmallCore {R : Type} [DecidableEq R] (cinfo : DecompPtr) (pool_id : Int32)
    (sizeofobject : UInt64) (allocFn : M (Ptr R)) (recordFn : PoolAllocs → Ptr R → PoolAllocs) :
    M (JpegRes (Ptr R)) := do
  let dc ← Ptr.load cinfo
  let maxChunkU : UInt64 := MAX_ALLOC_CHUNK.toInt.toNat.toUInt64
  if sizeofobject > maxChunkU then
    let _ ← out_of_memory cinfo 7
    return .errExit JERR_OUT_OF_MEMORY
  let alignedSize := round_up_pow2 sizeofobject ALIGN_SIZE
  if sizeof_small_pool_hdr + alignedSize + ALIGN_SIZE - 1 > maxChunkU then
    let _ ← out_of_memory cinfo 1
    return .errExit JERR_OUT_OF_MEMORY
  if pool_id < 0 || pool_id ≥ JPOOL_NUMPOOLS then
    let _ ← errexit1 dc.err JERR_BAD_POOL_ID pool_id
    return .errExit JERR_BAD_POOL_ID
  let pid := pool_id.toInt.toNat
  let _ ← Ptr.load dc.mem
  let initSlop := first_pool_slop[pid]!
  let remChunk := maxChunkU - (sizeof_small_pool_hdr + alignedSize + ALIGN_SIZE - 1)
  let slop := if initSlop > remChunk then remChunk else initSlop
  match (← allocSlopRetry cinfo allocFn 16 slop) with
  | .errExit code => return .errExit code
  | .ok p =>
    let dc2 ← Ptr.load cinfo
    let mem2 ← Ptr.load dc2.mem
    let allocs2 := recordFn (mem2.poolAllocs[pid]!) p
    Ptr.store dc2.mem {
      mem2 with
      poolAllocs := mem2.poolAllocs.set! pid allocs2
      totalSpaceAllocated := mem2.totalSpaceAllocated + alignedSize
    }
    return .ok p

/-- Allocate `my_decomp_master` in `pool_id` via `alloc_small`. -/
def alloc_small_master (cinfo : DecompPtr) (pool_id : Int32) (sizeofobject : UInt64) :
    M (JpegRes MasterPtr) :=
  allocSmallCore cinfo pool_id sizeofobject allocMaster (fun pa p =>
    match p with
    | .ref (.master b) _ => { pa with masters := pa.masters.push b }
    | .null => pa)

/-- Allocate `my_marker_reader` in `pool_id` via `alloc_small`. -/
def alloc_small_marker (cinfo : DecompPtr) (pool_id : Int32) (sizeofobject : UInt64) :
    M (JpegRes MarkerPtr) :=
  allocSmallCore cinfo pool_id sizeofobject allocMarker (fun pa p =>
    match p with
    | .ref (.marker b) _ => { pa with markers := pa.markers.push b }
    | .null => pa)

/-- Allocate `my_input_controller` in `pool_id` via `alloc_small`. -/
def alloc_small_inputctl (cinfo : DecompPtr) (pool_id : Int32) (sizeofobject : UInt64) :
    M (JpegRes InputCtlPtr) :=
  allocSmallCore cinfo pool_id sizeofobject allocInputCtl (fun pa p =>
    match p with
    | .ref (.inputctl b) _ => { pa with inputctls := pa.inputctls.push b }
    | .null => pa)

/-- Allocate `struct jpeg_source_mgr` in `pool_id` via `alloc_small`. -/
def alloc_small_src (cinfo : DecompPtr) (pool_id : Int32) (sizeofobject : UInt64) :
    M (JpegRes SrcPtr) :=
  allocSmallCore cinfo pool_id sizeofobject allocSrc (fun pa p =>
    match p with
    | .ref (.src b) _ => { pa with srcs := pa.srcs.push b }
    | .null => pa)

/-- Allocate `num_components` `jpeg_component_info` entries in `pool_id` via `alloc_small`. -/
def alloc_small_comps (cinfo : DecompPtr) (pool_id : Int32) (numComps : Nat) (sizeofobject : UInt64) :
    M (JpegRes CompPtr) :=
  allocSmallCore cinfo pool_id sizeofobject (allocComps numComps) (fun pa p =>
    match p with
    | .ref (.comp b) _ => { pa with comps := pa.comps.push b }
    | .null => pa)

/-- Allocate `JQUANT_TBL` in `pool_id` via `alloc_small`. -/
def alloc_small_quant (cinfo : DecompPtr) (pool_id : Int32) (sizeofobject : UInt64) :
    M (JpegRes QuantPtr) :=
  allocSmallCore cinfo pool_id sizeofobject allocQuant (fun pa p =>
    match p with
    | .ref (.quant b) _ => { pa with quants := pa.quants.push b }
    | .null => pa)

/-- Allocate `JHUFF_TBL` in `pool_id` via `alloc_small`. -/
def alloc_small_huff (cinfo : DecompPtr) (pool_id : Int32) (sizeofobject : UInt64) :
    M (JpegRes HuffPtr) :=
  allocSmallCore cinfo pool_id sizeofobject allocHuff (fun pa p =>
    match p with
    | .ref (.huff b) _ => { pa with huffs := pa.huffs.push b }
    | .null => pa)

/-- `METHODDEF(void *) alloc_large(j_common_ptr cinfo, int pool_id, size_t sizeofobject)` (`jmemmgr.c:362-414`)
specialized for `struct jpeg_marker_struct` + `limit` data bytes. -/
def alloc_large_saved_marker (cinfo : DecompPtr) (pool_id : Int32) (limit : Nat) :
    M (JpegRes (SavedMarkerPtr × BPtr)) := do
  let dc ← Ptr.load cinfo
  let maxChunkU : UInt64 := MAX_ALLOC_CHUNK.toInt.toNat.toUInt64
  let reqSize : UInt64 := sizeof_jpeg_marker_struct.toInt.toNat.toUInt64 + UInt64.ofNat limit
  if reqSize > maxChunkU then
    let _ ← out_of_memory cinfo 8
    return .errExit JERR_OUT_OF_MEMORY
  let sizeofobject := round_up_pow2 reqSize ALIGN_SIZE
  if sizeof_small_pool_hdr + sizeofobject + ALIGN_SIZE - 1 > maxChunkU then
    let _ ← out_of_memory cinfo 3
    return .errExit JERR_OUT_OF_MEMORY
  if pool_id < 0 || pool_id ≥ JPOOL_NUMPOOLS then
    let _ ← errexit1 dc.err JERR_BAD_POOL_ID pool_id
    return .errExit JERR_BAD_POOL_ID
  let pid := pool_id.toInt.toNat
  let (smPtr, dataPtr) ← jpeg_get_large_saved_marker limit
  if smPtr == .null then
    let _ ← out_of_memory cinfo 4
    return .errExit JERR_OUT_OF_MEMORY
  let dc2 ← Ptr.load cinfo
  let mem2 ← Ptr.load dc2.mem
  let pa := mem2.poolAllocs[pid]!
  let pa' :=
    match smPtr, dataPtr with
    | .ref (.savedMarker bs) _, .ref (.heap bd) _ =>
      { pa with savedMarkers := pa.savedMarkers.push bs, bytes := pa.bytes.push bd }
    | _, _ => pa
  Ptr.store dc2.mem {
    mem2 with
    poolAllocs := mem2.poolAllocs.set! pid pa'
    totalSpaceAllocated := mem2.totalSpaceAllocated + sizeofobject + sizeof_small_pool_hdr + ALIGN_SIZE - 1
  }
  return .ok (smPtr, dataPtr)

/-- `METHODDEF(void) free_pool(j_common_ptr cinfo, int pool_id)` (`jmemmgr.c:1096-1159`). -/
def free_pool (cinfo : DecompPtr) (pool_id : Int32) : M Unit := do
  let dc ← Ptr.load cinfo
  if pool_id < 0 || pool_id ≥ JPOOL_NUMPOOLS then
    let _ ← errexit1 dc.err JERR_BAD_POOL_ID pool_id
    return ()
  let pid := pool_id.toInt.toNat
  let mem ← Ptr.load dc.mem
  let pa := mem.poolAllocs[pid]!
  freePoolM pa
  let mem' := {
    mem with
    livePools := mem.livePools.set! pid false
    poolAllocs := mem.poolAllocs.set! pid {}
  }
  Ptr.store dc.mem mem'

/-- `METHODDEF(void) self_destruct(j_common_ptr cinfo)` (`jmemmgr.c:1167-1185`). -/
def self_destruct (cinfo : DecompPtr) : M Unit := do
  -- `for (pool = JPOOL_NUMPOOLS - 1; pool >= JPOOL_PERMANENT; pool--)` -> pool = 1, pool = 0
  free_pool cinfo 1
  free_pool cinfo 0
  let dc ← Ptr.load cinfo
  jpeg_free_small_mem dc.mem
  let dc2 ← Ptr.load cinfo
  Ptr.store cinfo { dc2 with mem := .null }
  jpeg_mem_term cinfo

/-- `GLOBAL(void) jinit_memory_mgr(j_common_ptr cinfo)` (`jmemmgr.c:1193-1289`). -/
def jinit_memory_mgr (cinfo : DecompPtr) : M (JpegRes Unit) := do
  let dc ← Ptr.load cinfo
  Ptr.store cinfo { dc with mem := .null }
  if (ALIGN_SIZE &&& (ALIGN_SIZE - 1)) != 0 then
    let _ ← errexit dc.err JERR_BAD_ALIGN_TYPE
    return .errExit JERR_BAD_ALIGN_TYPE
  if (MAX_ALLOC_CHUNK % (Int64.ofNat ALIGN_SIZE.toNat)) != 0 then
    let _ ← errexit dc.err JERR_BAD_ALLOC_CHUNK
    return .errExit JERR_BAD_ALLOC_CHUNK
  let max_to_use ← jpeg_mem_init cinfo
  let memPtr ← jpeg_get_small_mem
  if memPtr == .null then
    jpeg_mem_term cinfo
    let _ ← errexit1 dc.err JERR_OUT_OF_MEMORY 0
    return .errExit JERR_OUT_OF_MEMORY
  let mem : JpegMemMgr := {
    allocSmall := .fn "alloc_small"
    freePool := .fn "free_pool"
    selfDestruct := .fn "self_destruct"
    maxAllocChunk := MAX_ALLOC_CHUNK
    maxMemoryToUse := max_to_use
    totalSpaceAllocated := 192 -- sizeof(my_memory_mgr)
    livePools := #[true, true]
    poolAllocs := #[{}, {}]
  }
  Ptr.store memPtr mem
  let dc2 ← Ptr.load cinfo
  Ptr.store cinfo { dc2 with mem := memPtr }
  return .ok ()

end Mozjpeg.Jmemmgr
