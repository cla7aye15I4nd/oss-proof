import ZlibNgF.ZlibNg.«zutil.h»
import ZlibNgF.ZlibNg.«deflate.c»

/-!
# `compress.c` — one-shot compression and the compressed size bound (`ZlibNgF`)

Source: `zlib-ng/compress.c`, `ZLIB_COMPAT` LP64 Linux scalar build (`S390_DFLTCC_DEFLATE` and `NO_QUICK_STRATEGY`
undefined); the size macros of `zutil.h` are in `zutil.h.lean`. `PREFIX(deflateInit)(&stream, level)` is the
`zlib.h` macro `deflateInit_(&stream, level, ZLIB_VERSION, (int)sizeof(z_stream))`.

* A pointer to a caller length cell (`z_size_t *destLen`, `unsigned long *destLen`) is modelled as the value of the
  cell (`none` for a NULL pointer); the function returns the value of the cell after the call with its result.
* The local `z_stream stream` is a fresh stream object (`newStream`); the code writes every field it reads
  (`zalloc`, `zfree`, `opaque` here, `msg`, `state`, `total_*`, `adler`, `data_type` in `deflateInit_`, the buffer
  fields before the first `deflate`), so the model starts it at zero / NULL. It ends with the function
  (`dropStream`).
-/

set_option autoImplicit false

namespace ZlibNg.Compress
open C ZlibNg.Zbuild
open ZlibNg.Inflate (rdZ wrZ)

/-- `#define DEFLATE_BOUND_COMPLEN(source_len) 0` (`compress.c:19`). -/
def DEFLATE_BOUND_COMPLEN (_source_len : UInt64) : UInt64 := 0

/-- `#define ULONG_MAX` on LP64 Linux. -/
def ULONG_MAX : UInt64 := 0xffffffffffffffff

/-- `z_size_t Z_EXPORT compressBound_z(z_size_t sourceLen)` (`compress.c:91-115`). -/
def compressBound_z (sourceLen : UInt64) : M UInt64 := do
  let complen : UInt64 := DEFLATE_BOUND_COMPLEN sourceLen
  if complen > 0 then
    let bound := complen + ZLIB_WRAPLEN
    return if bound < sourceLen then (-1 : Int64).toUInt64 else bound
  let bound := sourceLen
    + (if sourceLen == 0 then 1 else 0)
    + (if sourceLen < 9 then 1 else 0)
    + DEFLATE_QUICK_OVERHEAD sourceLen
    + DEFLATE_BLOCK_OVERHEAD
    + ZLIB_WRAPLEN
  return if bound < sourceLen then (-1 : Int64).toUInt64 else bound

/-- `unsigned long Z_EXPORT compressBound(unsigned long sourceLen)` (`compress.c:118-121`). -/
def compressBound (sourceLen : UInt64) : M UInt64 := do
  let bound ← compressBound_z sourceLen
  return MIN ULONG_MAX bound

/-- `UINT_MAX` -/
def UINT_MAX : UInt64 := 0xffffffff

/-- `int Z_EXPORT compress2_z(unsigned char *dest, z_size_t *destLen, const unsigned char *source,
z_size_t sourceLen, int level)` (`compress.c:28-71`). Returns `(result, *destLen)`. -/
def compress2_z (dest : BPtr) (destLen : Option UInt64) (source : BPtr) (sourceLen : UInt64) (level : Int32) :
    M (Int32 × Option UInt64) := do
  match destLen with
  | none => return (ZlibNg.Inflate.Z_STREAM_ERROR, destLen)
  | some dl =>
  if (sourceLen > 0 && source == .null) || (dl > 0 && dest == .null) then
    return (ZlibNg.Inflate.Z_STREAM_ERROR, destLen)
  let left := dl
  let dl : UInt64 := 0
  let stream ← newStream {}
  wrZ stream fun z => { z with zalloc := .null }
  wrZ stream fun z => { z with zfree := .null }
  wrZ stream fun z => { z with «opaque» := .null }
  let ver ← strLitRef "1.3.2.zlib-ng"
  let err ← ZlibNg.Deflate.deflateInit_ stream level ver SIZEOF_Z_STREAM.toInt32
  if err != ZlibNg.Inflate.Z_OK then
    dropStream stream
    return (err, some dl)
  wrZ stream fun z => { z with next_out := dest }
  wrZ stream fun z => { z with avail_out := 0 }
  wrZ stream fun z => { z with next_in := source }
  wrZ stream fun z => { z with avail_in := 0 }
  let (err, _, _) ← cdoWhile
    (fun ((_, left, sourceLen) : Int32 × UInt64 × UInt64) => do
      let mut left := left
      let mut sourceLen := sourceLen
      if (← rdZ stream (·.avail_out)) == 0 then
        wrZ stream fun z => { z with avail_out := (MIN UINT_MAX left).toUInt32 }
        let ao : UInt32 ← rdZ stream (·.avail_out)
        left := left - ao.toUInt64
      if (← rdZ stream (·.avail_in)) == 0 then
        wrZ stream fun z => { z with avail_in := (MIN UINT_MAX sourceLen).toUInt32 }
        let ai : UInt32 ← rdZ stream (·.avail_in)
        sourceLen := sourceLen - ai.toUInt64
      let err ← ZlibNg.Deflate.deflate stream (if sourceLen != 0 then ZlibNg.Deflate.Z_NO_FLUSH else ZlibNg.Inflate.Z_FINISH)
      pure (err, left, sourceLen))
    (fun (x : Int32 × UInt64 × UInt64) => pure (x.1 == ZlibNg.Inflate.Z_OK, x))
    (ZlibNg.Inflate.Z_OK, left, sourceLen)
  let dl ← rdZ stream (·.total_out)
  let _ ← ZlibNg.Deflate.deflateEnd stream
  dropStream stream
  return (if err == ZlibNg.Inflate.Z_STREAM_END then ZlibNg.Inflate.Z_OK else err, some dl)

/-- `int Z_EXPORT compress2(unsigned char *dest, unsigned long *destLen, const unsigned char *source,
unsigned long sourceLen, int level)` (`compress.c:124-131`). Returns `(result, *destLen)`. -/
def compress2 (dest : BPtr) (destLen : Option UInt64) (source : BPtr) (sourceLen : UInt64) (level : Int32) :
    M (Int32 × Option UInt64) := do
  let got := destLen.getD 0
  let (ret, got) ← compress2_z dest (some got) source sourceLen level
  return (ret, if destLen.isSome then got else destLen)

/-- `z_int32_t Z_EXPORT compress(unsigned char *dest, z_uintmax_t *destLen, const unsigned char *source,
z_uintmax_t sourceLen)` (`compress.c:76-78`). Returns `(result, *destLen)`. -/
def compress (dest : BPtr) (destLen : Option UInt64) (source : BPtr) (sourceLen : UInt64) :
    M (Int32 × Option UInt64) :=
  compress2 dest destLen source sourceLen ZlibNg.Deflate.Z_DEFAULT_COMPRESSION

/-- `z_int32_t Z_EXPORT compress_z(unsigned char *dest, z_size_t *destLen, const unsigned char *source,
z_size_t sourceLen)` (`compress.c:133-136`). Returns `(result, *destLen)`. -/
def compress_z (dest : BPtr) (destLen : Option UInt64) (source : BPtr) (sourceLen : UInt64) :
    M (Int32 × Option UInt64) :=
  compress2_z dest destLen source sourceLen ZlibNg.Deflate.Z_DEFAULT_COMPRESSION

end ZlibNg.Compress
