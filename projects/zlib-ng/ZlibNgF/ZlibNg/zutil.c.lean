import ZlibNgF.Runtime.Libc

/-!
# `zutil.c` — faithful statement-by-statement translation (`ZlibNgF`)

Source: `zlib-ng/zutil.c` + Patch 0001 (`0001-gzbuffer-aligned-alloc-overflow.patch`),
portable scalar x86_64 Linux LP64 build (`-DZLIB_COMPAT=ON -DWITH_OPTIM=OFF -DWITH_CRC32_CHORBA=OFF -DWITH_RUNTIME_CPU_DETECTION=OFF`).
-/

set_option autoImplicit false

namespace ZlibNg.Zutil
open C

/-- `#define ZLIB_VERSION "1.3.1.zlib-ng"` (`zlib.h`). -/
def ZLIB_VERSION : String := "1.3.1.zlib-ng"

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

/-- `unsigned long Z_EXPORT zlibCompileFlags(void)` (`zutil.c:36-81`, LP64 Linux). -/
def zlibCompileFlags : M UInt64 := do
  let flags : UInt64 := 0
  let sz : Int32 := 4
  let flags := if sz == 2 then flags else if sz == 4 then flags + 1 else if sz == 8 then flags + 2 else flags + 3
  let sz : Int32 := 8
  let flags := if sz == 2 then flags else if sz == 4 then flags + ((1 : UInt64) <<< 2)
    else if sz == 8 then flags + ((2 : UInt64) <<< 2) else flags + ((3 : UInt64) <<< 2)
  let sz : Int32 := 8
  let flags := if sz == 2 then flags else if sz == 4 then flags + ((1 : UInt64) <<< 4)
    else if sz == 8 then flags + ((2 : UInt64) <<< 4) else flags + ((3 : UInt64) <<< 4)
  let sz : Int32 := 8
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

/-- `#define SIZE_MAX UINT64_MAX` on LP64 Linux. -/
def SIZE_MAX_64 : UInt64 := 0xffffffffffffffff

/-- `void Z_INTERNAL *zng_alloc_aligned(unsigned size, unsigned align)` (`zutil.c:116-143`, with Patch 0001). -/
def zng_alloc_aligned (size align : UInt32) : M BPtr := do
  if align == 0 || size.toUInt64 > SIZE_MAX_64 - 8 - align.toUInt64 then
    return .null
  let alloc_size : UInt64 := 8 + size.toUInt64 + align.toUInt64
  let ptr ← allocB alloc_size.toNat
  if ptr == .null then
    return .null
  let ptr_addr ← addrOf ptr
  let align_diff : UInt32 := align - (ptr_addr % align.toUInt64).toUInt32
  let step1 ← ptr.add (Int.ofNat align_diff.toNat)
  let return_ptr ← if align_diff < 8 then step1.add (Int.ofNat align.toNat) else pure step1
  let original_ptr ← return_ptr.add (-8)
  storePtrSlot original_ptr ptr
  return return_ptr

/-- `void Z_INTERNAL zng_free_aligned(void *ptr)` (`zutil.c:145-155`). -/
def zng_free_aligned (ptr : BPtr) : M Unit := do
  if ptr == .null then
    return ()
  let original_ptr ← ptr.add (-8)
  let free_ptr ← loadPtrSlot original_ptr
  freeB free_ptr

end ZlibNg.Zutil
