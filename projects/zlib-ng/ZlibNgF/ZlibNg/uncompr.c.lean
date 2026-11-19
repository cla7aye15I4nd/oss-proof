import ZlibNgF.ZlibNg.«inflate.c»

/-!
# `uncompr.c` — one-shot decompression (`ZlibNgF`)

Source: `zlib-ng/uncompr.c`, `ZLIB_COMPAT`. `PREFIX(inflateInit)(&stream)` is the `zlib.h` macro
`inflateInit_(&stream, ZLIB_VERSION, (int)sizeof(z_stream))`.

* The pointers to caller length cells (`z_size_t *destLen`, `*sourceLen`, `unsigned long *...`) are modelled as the
  value of the cell (`none` for a NULL pointer); the function returns the values of the cells after the call
  together with its result.
* The local `z_stream stream` is a fresh stream object (`newStream`), whose fields the code writes before reading
  (the model starts it at zero / NULL); it ends with the function (`dropStream`). The local `unsigned char buf[1]`
  is a local block (`localBlock`, freed at the end).
-/

set_option autoImplicit false

namespace ZlibNg.Uncompr
open C ZlibNg.Inflate

/-- `int Z_EXPORT uncompress2_z(unsigned char *dest, z_size_t *destLen, const unsigned char *source,
z_size_t *sourceLen)` (`uncompr.c:26-86`). Returns `(result, *destLen, *sourceLen)`. -/
def uncompress2_z (dest : BPtr) (destLen : Option UInt64) (source : BPtr) (sourceLen : Option UInt64) :
    M (Int32 × Option UInt64 × Option UInt64) := do
  let max : UInt32 := (-1 : Int32).toUInt32
  let buf ← localBlock 1
  let fin (r : Int32) (dl sl : Option UInt64) : M (Int32 × Option UInt64 × Option UInt64) := do
    dropLocal buf
    return (r, dl, sl)
  match sourceLen, destLen with
  | none, _ => fin Z_STREAM_ERROR destLen sourceLen
  | _, none => fin Z_STREAM_ERROR destLen sourceLen
  | some sl, some dl =>
    if (sl > 0 && source == .null) || (dl > 0 && dest == .null) then
      return ← fin Z_STREAM_ERROR destLen sourceLen
    let mut len := sl
    let mut left : UInt64 := 0  -- `z_size_t left;`: both branches below write it first; the 0 is never read
    let mut dl := dl
    let mut dest := dest
    if dl != 0 then
      left := dl
      dl := 0
    else
      left := 1
      dest := buf
    let stream ← newStream {}
    wrZ stream fun z => { z with next_in := source }
    wrZ stream fun z => { z with avail_in := 0 }
    wrZ stream fun z => { z with zalloc := .null }
    wrZ stream fun z => { z with zfree := .null }
    wrZ stream fun z => { z with «opaque» := .null }
    let ver ← strLitRef "1.3.2.zlib-ng"
    let err ← inflateInit_ stream ver SIZEOF_Z_STREAM.toInt32
    if err != Z_OK then
      dropStream stream
      return ← fin err (some dl) (some sl)
    wrZ stream fun z => { z with next_out := dest }
    wrZ stream fun z => { z with avail_out := 0 }
    let (err, left1, len1) ← cdoWhile
      (fun ((_, left, len) : Int32 × UInt64 × UInt64) => do
        let mut left := left
        let mut len := len
        if (← rdZ stream (·.avail_out)) == 0 then
          let a := if left > max.toUInt64 then max else left.toUInt32
          wrZ stream fun z => { z with avail_out := a }
          left := left - a.toUInt64
        if (← rdZ stream (·.avail_in)) == 0 then
          let a := if len > max.toUInt64 then max else len.toUInt32
          wrZ stream fun z => { z with avail_in := a }
          len := len - a.toUInt64
        let err ← inflate stream 0
        pure (err, left, len))
      (fun ((err, left, len) : Int32 × UInt64 × UInt64) => pure (err == Z_OK, (err, left, len)))
      (Z_OK, left, len)
    left := left1
    len := len1
    let z ← ldStream stream
    let sl := sl - (len + z.avail_in.toUInt64)
    if dest != buf then
      dl := z.total_out
    else if z.total_out != 0 && err == Z_BUF_ERROR then
      left := 1
    let _ ← inflateEnd stream
    let z ← ldStream stream
    dropStream stream
    let r := if err == Z_STREAM_END then Z_OK
      else if err == Z_NEED_DICT then Z_DATA_ERROR
      else if err == Z_BUF_ERROR && left + z.avail_out.toUInt64 != 0 then Z_DATA_ERROR
      else err
    fin r (some dl) (some sl)

/-- `int Z_EXPORT uncompress2(unsigned char *dest, unsigned long *destLen, const unsigned char *source,
unsigned long *sourceLen)` (`uncompr.c:93-102`). Returns `(result, *destLen, *sourceLen)`. -/
def uncompress2 (dest : BPtr) (destLen : Option UInt64) (source : BPtr) (sourceLen : Option UInt64) :
    M (Int32 × Option UInt64 × Option UInt64) := do
  let got := destLen.getD 0
  let used := sourceLen.getD 0
  let (ret, got, used) ← uncompress2_z dest (some got) source (some used)
  let sourceLen := if sourceLen.isSome then used else sourceLen
  let destLen := if destLen.isSome then got else destLen
  return (ret, destLen, sourceLen)

/-- `z_int32_t Z_EXPORT uncompress(unsigned char *dest, z_uintmax_t *destLen, const unsigned char *source,
z_uintmax_t sourceLen)` (`uncompr.c:88-90`). Returns `(result, *destLen)`. -/
def uncompress (dest : BPtr) (destLen : Option UInt64) (source : BPtr) (sourceLen : UInt64) :
    M (Int32 × Option UInt64) := do
  let (r, dl, _) ← uncompress2 dest destLen source (some sourceLen)
  return (r, dl)

/-- `z_int32_t Z_EXPORT uncompress_z(unsigned char *dest, z_size_t *destLen, const unsigned char *source,
z_size_t sourceLen)` (`uncompr.c:104-107`). Returns `(result, *destLen)`. -/
def uncompress_z (dest : BPtr) (destLen : Option UInt64) (source : BPtr) (sourceLen : UInt64) :
    M (Int32 × Option UInt64) := do
  let (r, dl, _) ← uncompress2_z dest destLen source (some sourceLen)
  return (r, dl)

end ZlibNg.Uncompr
