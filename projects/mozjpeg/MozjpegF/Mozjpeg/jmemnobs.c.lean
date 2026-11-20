import MozjpegF.Mozjpeg.«jpeglib.h»

/-!
# `jmemnobs.c` — faithful statement-by-statement translation (`MozjpegF`)

Source: `mozjpeg/jmemnobs.c` (no backing-store system-dependent memory allocator).
-/

set_option autoImplicit false

namespace Mozjpeg.Jmemnobs
open C Mozjpeg.JpeglibH Mozjpeg.JerrorH

/-- `GLOBAL(void *) jpeg_get_small(j_common_ptr cinfo, size_t sizeofobject)` (`jmemnobs.c:31-35`).
System allocation for the memory manager control block (`MALLOC(sizeof(my_memory_mgr))`). -/
def jpeg_get_small_mem : M MemPtr :=
  allocMemMgr

/-- `GLOBAL(void) jpeg_free_small(j_common_ptr cinfo, void *object, size_t sizeofobject)` (`jmemnobs.c:37-41`). -/
def jpeg_free_small_mem (obj : MemPtr) : M Unit :=
  freeMemMgr obj

/-- `GLOBAL(void *) jpeg_get_large(j_common_ptr cinfo, size_t sizeofobject)` (`jmemnobs.c:55-59`)
paired with `jpeg_marker_struct` + `limit` byte data (`alloc_large` in `save_marker`). -/
def jpeg_get_large_saved_marker (limit : Nat) : M (SavedMarkerPtr × BPtr) :=
  allocSavedMarkerData limit

/-- `GLOBAL(long) jpeg_mem_init(j_common_ptr cinfo)` (`jmemnobs.c:100-104`). -/
def jpeg_mem_init (_cinfo : DecompPtr) : M Int64 :=
  return 0

/-- `GLOBAL(void) jpeg_mem_term(j_common_ptr cinfo)` (`jmemnobs.c:106-110`). -/
def jpeg_mem_term (_cinfo : DecompPtr) : M Unit :=
  return ()

end Mozjpeg.Jmemnobs
