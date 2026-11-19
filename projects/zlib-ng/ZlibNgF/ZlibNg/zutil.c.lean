import ZlibNgF.Runtime.Libc

/-!
# `zutil.c` — faithful statement-by-statement translation (`ZlibNgF`)

Source: `zlib-ng/zutil.c` and `zlib-ng/zbuild.h` (`ALIGN_DIFF`), portable scalar x86_64 Linux LP64 build (`-DZLIB_COMPAT=ON -DWITH_OPTIM=OFF -DWITH_CRC32_CHORBA=OFF -DWITH_RUNTIME_CPU_DETECTION=OFF`).
-/

set_option autoImplicit false

namespace ZlibNg.Zutil
open C

/-- `#define ZLIB_VERSION "1.3.2.zlib-ng"` (`zlib.h`). -/
def ZLIB_VERSION : String := "1.3.2.zlib-ng"

/-- `z_const char * const z_errmsg[10]` (`zutil.c:10-21`). -/
def z_errmsg : Array String := #[
  "need dictionary",     -- Z_NEED_DICT       2
  "stream end",          -- Z_STREAM_END      1
  "",                    -- Z_OK              0
  "file error",          -- Z_ERRNO         (-1)
  "stream error",        -- Z_STREAM_ERROR  (-2)
  "data error",          -- Z_DATA_ERROR    (-3)
  "insufficient memory", -- Z_MEM_ERROR     (-4)
  "buffer error",        -- Z_BUF_ERROR     (-5)
  "incompatible version",-- Z_VERSION_ERROR (-6)
  ""
]

/-- `const char * Z_EXPORT zlibVersion(void)` (`zutil.c:27-29`). -/
def zlibVersion : M BPtr :=
  strLitRef ZLIB_VERSION

/-- `unsigned long Z_EXPORT zlibCompileFlags(void)` (`zutil.c:36-81`, LP64 Linux). Each `switch` is on a
`sizeof` (a `size_t`). -/
def zlibCompileFlags : M UInt64 := do
  let flags : UInt64 := 0
  let sz : UInt64 := 4
  let flags := if sz == 2 then flags else if sz == 4 then flags + 1 else if sz == 8 then flags + 2 else flags + 3
  let sz : UInt64 := 8
  let flags := if sz == 2 then flags else if sz == 4 then flags + ((1 : UInt64) <<< 2)
    else if sz == 8 then flags + ((2 : UInt64) <<< 2) else flags + ((3 : UInt64) <<< 2)
  let sz : UInt64 := 8
  let flags := if sz == 2 then flags else if sz == 4 then flags + ((1 : UInt64) <<< 4)
    else if sz == 8 then flags + ((2 : UInt64) <<< 4) else flags + ((3 : UInt64) <<< 4)
  let sz : UInt64 := 8
  let flags := if sz == 2 then flags else if sz == 4 then flags + ((1 : UInt64) <<< 6)
    else if sz == 8 then flags + ((2 : UInt64) <<< 6) else flags + ((3 : UInt64) <<< 6)
  return flags

/-- `const char * Z_EXPORT zError(z_int32_t err)` (`zutil.c:99-101`).
`ERR_MSG(err)` expands to `z_errmsg[(err) < -6 || (err) > 2 ? 9 : 2 - (err)]`. -/
def zError (err : Int32) : M BPtr := do
  let i : Int32 := if err < -6 || err > 2 then 9 else 2 - err
  match z_errmsg[i.toInt.toNat]? with
  | some s => strLitRef s
  | none => ub "z_errmsg index outside its array"

/-- `void Z_INTERNAL *zcalloc(void *opaque, unsigned items, unsigned size)` (`zutil.c:105-108`). -/
def zcalloc («opaque» : BPtr) (items size : UInt32) : M BPtr := do
  let _ := «opaque»
  allocB (items.toUInt64 * size.toUInt64).toNat

/-- `void Z_INTERNAL zcfree(void *opaque, void *ptr)` (`zutil.c:110-113`). -/
def zcfree («opaque» ptr : BPtr) : M Unit := do
  let _ := «opaque»
  freeB ptr

/-- `#define ALIGN_DIFF(ptr, align) (((uintptr_t)(align) - ((uintptr_t)(ptr) & ((align) - 1))) & ((align) - 1))`
(`zbuild.h:286-287`), with `align` an `unsigned`: `(align) - 1` is computed in `unsigned` and converted to
`uintptr_t` for the `&`. -/
def ALIGN_DIFF (ptr : BPtr) (align : UInt32) : M UInt64 := do
  let addr ← addrOf ptr
  return (align.toUInt64 - (addr &&& (align - 1).toUInt64)) &&& (align - 1).toUInt64

/-- `void Z_INTERNAL *zng_alloc_aligned(unsigned size, unsigned align)` (`zutil.c:116-139`). `alloc_size` is a
`uint32_t`: `sizeof(void *) + size + align` is computed in `size_t` and converted (modulo `2^32`). -/
def zng_alloc_aligned (size align : UInt32) : M BPtr := do
  let alloc_size : UInt32 := (8 + size.toUInt64 + align.toUInt64).toUInt32
  let ptr ← allocB alloc_size.toNat
  if ptr == .null then
    return .null
  let align_diff ← ALIGN_DIFF ptr align
  let return_ptr ← ptr.add (Int.ofNat align_diff.toNat)
  let return_ptr ← if align_diff < 8 then return_ptr.add (Int.ofNat align.toNat) else pure return_ptr
  let original_ptr ← return_ptr.add (-8)
  storePtrSlot original_ptr ptr
  return return_ptr

/-- `void Z_INTERNAL zng_free_aligned(void *ptr)` (`zutil.c:141-151`). -/
def zng_free_aligned (ptr : BPtr) : M Unit := do
  if ptr == .null then
    return ()
  let original_ptr ← ptr.add (-8)
  let free_ptr ← loadPtrSlot original_ptr
  freeB free_ptr

end ZlibNg.Zutil
