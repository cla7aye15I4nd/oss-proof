import ZlibNgF.ZlibNg.«gzlib.c»

/-!
# `gzwrite.c` — writing gzip files (`ZlibNgF`)

Source: `zlib-ng/gzwrite.c`; `ZLIB_COMPAT`, x86_64 Linux LP64. The `deflateInit2` macro of `zlib.h` calls
`deflateInit2_` with `ZLIB_VERSION` and `sizeof(z_stream)`. `gzprintf(file, format, ...)` is `gzvprintf` with the
caller's arguments, which only `vsnprintf` reads: both are `gzvprintf file format` here (the arguments are the
`vsnprintf` oracle's business, `Runtime/Gz.lean`).
-/

set_option autoImplicit false

namespace ZlibNg.Gz
open C ZlibNg.Inflate ZlibNg.Deflate

/-- `static int gz_write_init(gz_state *state)` (`gzwrite.c:20-50`). -/
def gz_write_init (state : GzPtr) : G Int32 := do
  let strm ← strmOf state
  if (← gz_buffer_alloc state) != 0 then
    gz_error state Z_MEM_ERROR (← (gzLit "out of memory"))
    return -1
  if (← rdG state (·.direct)) == 0 then
    let ret ← lm (deflateInit2_ strm (← rdG state (·.level)) Z_DEFLATED.toUInt32.toInt32 (MAX_WBITS + 16) DEF_MEM_LEVEL
      (← rdG state (·.strategy)) (← lm (strLitRef ZLIB_VERSION)) SIZEOF_Z_STREAM.toInt32)
    if ret != Z_OK then
      gz_buffer_free state
      if ret == Z_MEM_ERROR then
        gz_error state Z_MEM_ERROR (← (gzLit "out of memory"))
      else
        gz_error state Z_STREAM_ERROR (← (gzLit "invalid compression parameters"))
      return -1
    lm (wrZ strm fun z => { z with next_in := .null })
    let sz ← rdG state (·.size)
    lm (wrZ strm fun z => { z with avail_out := sz })
    let o ← (← ldGz state).out.get
    lm (wrZ strm fun z => { z with next_out := o })
    let no ← lm (rdZ strm (·.next_out))
    wrG state fun s => { s with next := .val no }
  return 0

/-- The locals of the loop of `gz_comp`. -/
structure CompLoop where
  ret : Int32
  hv : UInt32
  ctl : Ctl

/-- `static int gz_comp(gz_state *state, int flush)` (`gzwrite.c:58-123`). `got` and `have` are written before they
are read. -/
def gz_comp (state : GzPtr) (flush : Int32) : G Int32 := do
  let strm ← strmOf state
  if (← rdG state (·.size)) == 0 then
    if (← gz_write_init state) == -1 then
      return -1
  if (← rdG state (·.direct)) != 0 then
    let got ← writeG (← rdG state (·.fd)) (← lm (rdZ strm (·.next_in))) (← lm (rdZ strm (·.avail_in))).toUInt64
    if got < 0 || got.toUInt64.toUInt32 != (← lm (rdZ strm (·.avail_in))) then
      gz_error state Z_ERRNO (← zstrerror)
      return -1
    lm (wrZ strm fun z => { z with avail_in := 0 })
    return 0
  if (← rdG state (·.reset)) != 0 then
    if (← lm (rdZ strm (·.avail_in))) == 0 && flush == Z_NO_FLUSH then
      return 0
    let _ ← lm (deflateReset strm)
    wrG state fun s => { s with reset := 0 }
  let ret : Int32 := Z_OK
  let lp ← gdoWhile
    (fun (s : CompLoop) => do
      if (← lm (rdZ strm (·.avail_out))) == 0 ||
          (flush != Z_NO_FLUSH && (flush != Z_FINISH || s.ret == Z_STREAM_END)) then
        let d ← lm (Ptr.diff (← lm (rdZ strm (·.next_out))) (← (← ldGz state).next.get))
        let hv : UInt32 := d.toUInt64.toUInt32
        if hv != 0 then
          let got ← writeG (← rdG state (·.fd)) (← (← ldGz state).next.get) hv.toUInt64
          if got < 0 || got.toUInt64.toUInt32 != hv then
            gz_error state Z_ERRNO (← zstrerror)
            return { s with ctl := .ret }
        if (← lm (rdZ strm (·.avail_out))) == 0 then
          let sz ← rdG state (·.size)
          lm (wrZ strm fun z => { z with avail_out := sz })
          let o ← (← ldGz state).out.get
          lm (wrZ strm fun z => { z with next_out := o })
          let o ← (← ldGz state).out.get
          wrG state fun st => { st with next := .val o }
        let no ← lm (rdZ strm (·.next_out))
        wrG state fun st => { st with next := .val no }
      let hv ← lm (rdZ strm (·.avail_out))
      let ret ← lm (deflate strm flush)
      if ret == Z_STREAM_ERROR then
        gz_error state Z_STREAM_ERROR (← (gzLit "internal error: deflate stream corrupt"))
        return { s with ret := ret, ctl := .ret }
      let hv := hv - (← lm (rdZ strm (·.avail_out)))
      return { s with ret := ret, hv := hv })
    (fun (s : CompLoop) => do
      if s.ctl != .go then return (false, s)
      return (s.hv != 0, s))
    ⟨ret, 0, .go⟩
  if lp.ctl == .ret then
    return -1
  if flush == Z_FINISH then
    wrG state fun s => { s with reset := 1 }
  return 0

/-- `static int gz_zero(gz_state *state)` (`gzwrite.c:127-158`). -/
def gz_zero (state : GzPtr) : G Int32 := do
  let strm ← strmOf state
  if (← rdG state (·.size)) == 0 then
    if (← gz_write_init state) == -1 then
      return -1
  if (← lm (rdZ strm (·.avail_in))) != 0 then
    if (← gz_comp state Z_NO_FLUSH) == -1 then
      return -1
  let first : Int32 := 1
  let lp ← gdoWhile
    (fun (s : Int32 × Ctl) => do
      let mut first := s.1
      let sz ← rdG state (·.size)
      let sk ← rdG state (·.skip)
      let n : UInt32 := if GT_OFF sz || Int64.ofNat sz.toNat > sk then sk.toUInt64.toUInt32 else sz
      if first != 0 then
        lm (Ptr.memset (← (← ldGz state).«in».get) 0 n.toNat)
        first := 0
      lm (wrZ strm fun z => { z with avail_in := n })
      let i ← (← ldGz state).«in».get
      lm (wrZ strm fun z => { z with next_in := i })
      let np ← lm (chkI64 ((← rdG state (·.pos)).toInt + n.toNat))
      wrG state fun st => { st with pos := np }
      if (← gz_comp state Z_NO_FLUSH) == -1 then
        return (first, .ret)
      let sk ← lm (chkI64 ((← rdG state (·.skip)).toInt - n.toNat))
      wrG state fun st => { st with skip := sk }
      return (first, .go))
    (fun (s : Int32 × Ctl) => do
      if s.2 != .go then return (false, s)
      return ((← rdG state (·.skip)) != 0, s))
    (first, .go)
  if lp.2 == .ret then
    return -1
  return 0

/-- The locals of the loops of `gz_write`. -/
structure WriteLoop where
  buf : BPtr
  len : UInt64
  ctl : Ctl

/-- `static size_t gz_write(gz_state *state, void const *buf, size_t len)` (`gzwrite.c:162-219`, with patch 0014:
after the direct path, and when it fails, `strm.next_in` is `state->in` and `strm.avail_in` is 0). -/
def gz_write (state : GzPtr) (buf : BPtr) (len : UInt64) : G UInt64 := do
  let put := len
  if len == 0 then
    return 0
  if (← rdG state (·.size)) == 0 then
    if (← gz_write_init state) == -1 then
      return 0
  if (← rdG state (·.skip)) != 0 then
    if (← gz_zero state) == -1 then
      return 0
  let strm ← strmOf state
  if len < (← rdG state (·.size)).toUInt64 then
    let lp ← gdoWhile
      (fun (s : WriteLoop) => do
        if (← lm (rdZ strm (·.avail_in))) == 0 then
          let i ← (← ldGz state).«in».get
          lm (wrZ strm fun z => { z with next_in := i })
        let e ← lm ((← lm (rdZ strm (·.next_in))).add (Int.ofNat (← lm (rdZ strm (·.avail_in))).toNat))
        let d ← lm (Ptr.diff e (← (← ldGz state).«in».get))
        let hv : UInt32 := d.toUInt64.toUInt32
        let mut copy : UInt32 := (← rdG state (·.size)) - hv
        if copy.toUInt64 > s.len then
          copy := s.len.toUInt32
        lm (Ptr.memcpy (← lm ((← (← ldGz state).«in».get).add (Int.ofNat hv.toNat))) s.buf copy.toNat)
        lm (wrZ strm fun z => { z with avail_in := z.avail_in + copy })
        let np ← lm (chkI64 ((← rdG state (·.pos)).toInt + copy.toNat))
        wrG state fun st => { st with pos := np }
        let buf ← lm (s.buf.add (Int.ofNat copy.toNat))
        let len := s.len - copy.toUInt64
        if len != 0 then
          if (← gz_comp state Z_NO_FLUSH) == -1 then
            return { s with buf := buf, len := len, ctl := .ret }
        return { s with buf := buf, len := len })
      (fun (s : WriteLoop) => do
        if s.ctl != .go then return (false, s)
        return (s.len != 0, s))
      ⟨buf, len, .go⟩
    if lp.ctl == .ret then
      return 0
  else
    if (← lm (rdZ strm (·.avail_in))) != 0 then
      if (← gz_comp state Z_NO_FLUSH) == -1 then
        return 0
    lm (wrZ strm fun z => { z with next_in := buf })
    let lp ← gdoWhile
      (fun (s : WriteLoop) => do
        let mut n : UInt32 := 0xFFFFFFFF
        if n.toUInt64 > s.len then
          n := s.len.toUInt32
        lm (wrZ strm fun z => { z with avail_in := n })
        let np ← lm (chkI64 ((← rdG state (·.pos)).toInt + n.toNat))
        wrG state fun st => { st with pos := np }
        if (← gz_comp state Z_NO_FLUSH) == -1 then
          lm (wrZ strm fun z => { z with avail_in := 0 })
          let i ← (← ldGz state).«in».get
          lm (wrZ strm fun z => { z with next_in := i })
          return { s with ctl := .ret }
        return { s with len := s.len - n.toUInt64 })
      (fun (s : WriteLoop) => do
        if s.ctl != .go then return (false, s)
        return (s.len != 0, s))
      ⟨buf, len, .go⟩
    if lp.ctl == .ret then
      return 0
    let i ← (← ldGz state).«in».get
    lm (wrZ strm fun z => { z with next_in := i })
  return put

/-- `z_int32_t Z_EXPORT PREFIX(gzwrite)(gzFile file, void const *buf, z_uint32_t len)` (`gzwrite.c:222-243`). -/
def gzwrite (file : GzPtr) (buf : BPtr) (len : UInt32) : G Int32 := do
  if file == none then
    return 0
  let state := file
  if (← rdG state (·.mode)) != GZ_WRITE || (← rdG state (·.err)) != Z_OK then
    return 0
  if len.toInt32 < 0 then
    gz_error state Z_DATA_ERROR (← (gzLit "requested length does not fit in int"))
    return 0
  return (← gz_write state buf len.toUInt64).toUInt32.toInt32

/-- `size_t Z_EXPORT PREFIX(gzfwrite)(void const *buf, size_t size, size_t nitems, gzFile file)`
(`gzwrite.c:246-272`). -/
def gzfwrite (buf : BPtr) (size nitems : UInt64) (file : GzPtr) : G UInt64 := do
  if size == 0 then
    return 0
  if file == none then
    return 0
  let state := file
  if (← rdG state (·.mode)) != GZ_WRITE || (← rdG state (·.err)) != Z_OK then
    return 0
  let len := nitems * size
  if len / size != nitems then
    gz_error state Z_STREAM_ERROR (← (gzLit "request does not fit in a size_t"))
    return 0
  if len != 0 then
    return (← gz_write state buf len) / size
  else
    return 0

/-- `z_int32_t Z_EXPORT PREFIX(gzputc)(gzFile file, z_int32_t c)` (`gzwrite.c:275-314`). `unsigned char buf[1]` is
a local array (`localBlock`). -/
def gzputc (file : GzPtr) (c : Int32) : G Int32 := do
  if file == none then
    return -1
  let state := file
  let strm ← strmOf state
  if (← rdG state (·.mode)) != GZ_WRITE || (← rdG state (·.err)) != Z_OK then
    return -1
  if (← rdG state (·.skip)) != 0 then
    if (← gz_zero state) == -1 then
      return -1
  if (← rdG state (·.size)) != 0 then
    if (← lm (rdZ strm (·.avail_in))) == 0 then
      let i ← (← ldGz state).«in».get
      lm (wrZ strm fun z => { z with next_in := i })
    let e ← lm ((← lm (rdZ strm (·.next_in))).add (Int.ofNat (← lm (rdZ strm (·.avail_in))).toNat))
    let d ← lm (Ptr.diff e (← (← ldGz state).«in».get))
    let hv : UInt32 := d.toUInt64.toUInt32
    if hv < (← rdG state (·.size)) then
      lm (store8 (← lm ((← (← ldGz state).«in».get).add (Int.ofNat hv.toNat))) c.toUInt32.toUInt8)
      lm (wrZ strm fun z => { z with avail_in := z.avail_in + 1 })
      let np ← lm (chkI64 ((← rdG state (·.pos)).toInt + 1))
      wrG state fun st => { st with pos := np }
      return c &&& 0xff
  let buf ← lm (localBlock 1)
  lm (store8 (← lm (buf.add 0)) c.toUInt32.toUInt8)
  let r ← if (← gz_write state buf 1) != 1 then pure (-1) else pure (c &&& 0xff)
  lm (dropLocal buf)
  return r

/-- `z_int32_t Z_EXPORT PREFIX(gzputs)(gzFile file, const char *s)` (`gzwrite.c:317-338`). `(int)len` of a value
above `INT_MAX` is GCC's modulo-2^32 conversion. -/
def gzputs (file : GzPtr) (s : BPtr) : G Int32 := do
  if file == none then
    return -1
  let state := file
  if (← rdG state (·.mode)) != GZ_WRITE || (← rdG state (·.err)) != Z_OK then
    return -1
  let len ← lm (strlenB s)
  if len.toUInt32.toInt32 < 0 || len.toUInt32.toUInt64 != len then
    gz_error state Z_STREAM_ERROR (← (gzLit "string length does not fit in int"))
    return -1
  let put ← gz_write state s len
  return if put < len then -1 else len.toUInt32.toInt32

/-- `z_int32_t Z_EXPORTVA PREFIX(gzvprintf)(gzFile file, const char *format, va_list va)` (`gzwrite.c:341-392`);
also `gzprintf` (`gzwrite.c:394-402`). -/
def gzvprintf (file : GzPtr) (format : BPtr) : G Int32 := do
  if file == none then
    return Z_STREAM_ERROR
  let state := file
  let strm ← strmOf state
  if (← rdG state (·.mode)) != GZ_WRITE || (← rdG state (·.err)) != Z_OK then
    return Z_STREAM_ERROR
  if (← rdG state (·.size)) == 0 then
    if (← gz_write_init state) == -1 then
      return (← rdG state (·.err))
  if (← rdG state (·.skip)) != 0 then
    if (← gz_zero state) == -1 then
      return (← rdG state (·.err))
  if (← lm (rdZ strm (·.avail_in))) == 0 then
    let i ← (← ldGz state).«in».get
    lm (wrZ strm fun z => { z with next_in := i })
  let d ← lm (Ptr.diff (← lm (rdZ strm (·.next_in))) (← (← ldGz state).«in».get))
  let a ← lm ((← (← ldGz state).«in».get).add d.toInt)
  let next ← lm (a.add (Int.ofNat (← lm (rdZ strm (·.avail_in))).toNat))
  lm (store8 (← lm (next.add (Int.ofNat ((← rdG state (·.size)) - 1).toNat))) 0)
  let len ← vsnprintfG next (← rdG state (·.size)).toUInt64 format
  let bad ← if len == 0 || len.toUInt32 ≥ (← rdG state (·.size)) then pure true
    else do pure ((← lm (index8 next (Int.ofNat ((← rdG state (·.size)) - 1).toNat))) != 0)
  if bad then
    return 0
  lm (wrZ strm fun z => { z with avail_in := z.avail_in + len.toUInt32 })
  let np ← lm (chkI64 ((← rdG state (·.pos)).toInt + len.toInt))
  wrG state fun st => { st with pos := np }
  if (← lm (rdZ strm (·.avail_in))) ≥ (← rdG state (·.size)) then
    let left := (← lm (rdZ strm (·.avail_in))) - (← rdG state (·.size))
    let sz ← rdG state (·.size)
    lm (wrZ strm fun z => { z with avail_in := sz })
    if (← gz_comp state Z_NO_FLUSH) == -1 then
      return (← rdG state (·.err))
    let i ← (← ldGz state).«in».get
    lm (Ptr.memmove i (← lm (i.add (Int.ofNat (← rdG state (·.size)).toNat))) left.toNat)
    let i ← (← ldGz state).«in».get
    lm (wrZ strm fun z => { z with next_in := i })
    lm (wrZ strm fun z => { z with avail_in := left })
  return len

/-- `z_int32_t Z_EXPORTVA PREFIX(gzprintf)(gzFile file, const char *format, ...)` (`gzwrite.c:394-402`). -/
def gzprintf (file : GzPtr) (format : BPtr) : G Int32 := do
  let ret ← gzvprintf file format
  return ret

/-- `z_int32_t Z_EXPORT PREFIX(gzflush)(gzFile file, z_int32_t flush)` (`gzwrite.c:405-428`). -/
def gzflush (file : GzPtr) (flush : Int32) : G Int32 := do
  if file == none then
    return Z_STREAM_ERROR
  let state := file
  if (← rdG state (·.mode)) != GZ_WRITE || (← rdG state (·.err)) != Z_OK then
    return Z_STREAM_ERROR
  if flush < 0 || flush > Z_FINISH then
    return Z_STREAM_ERROR
  if (← rdG state (·.skip)) != 0 then
    if (← gz_zero state) == -1 then
      return (← rdG state (·.err))
  let _ ← gz_comp state flush
  rdG state (·.err)

/-- `z_int32_t Z_EXPORT PREFIX(gzsetparams)(gzFile file, z_int32_t level, z_int32_t strategy)`
(`gzwrite.c:431-480`). -/
def gzsetparams (file : GzPtr) (level strategy : Int32) : G Int32 := do
  if file == none then
    return Z_STREAM_ERROR
  let state := file
  let strm ← strmOf state
  if (← rdG state (·.mode)) != GZ_WRITE || (← rdG state (·.err)) != Z_OK || (← rdG state (·.direct)) != 0 then
    return Z_STREAM_ERROR
  if (level < 0 && level != Z_DEFAULT_COMPRESSION) || level > 9 ||
      strategy < Z_DEFAULT_STRATEGY || strategy > Z_FIXED then
    return Z_STREAM_ERROR
  if level == (← rdG state (·.level)) && strategy == (← rdG state (·.strategy)) then
    return Z_OK
  if (← rdG state (·.skip)) != 0 then
    if (← gz_zero state) == -1 then
      return (← rdG state (·.err))
  if (← rdG state (·.size)) != 0 then
    if (← lm (rdZ strm (·.avail_in))) != 0 then
      if (← gz_comp state Z_BLOCK) == -1 then
        return (← rdG state (·.err))
    let lp ← gdoWhile
      (fun (s : Int32 × Ctl) => do
        let ret ← lm (deflateParams strm level strategy)
        if ret != Z_BUF_ERROR || (← lm (rdZ strm (·.avail_out))) != 0 then
          return (ret, .brk)
        if (← gz_comp state Z_BLOCK) == -1 then
          return (ret, .ret)
        return (ret, s.2))
      (fun (s : Int32 × Ctl) => do
        if s.2 != .go then return (false, s)
        return (s.1 == Z_BUF_ERROR, s))
      (0, .go)
    if lp.2 == .ret then
      return (← rdG state (·.err))
    if lp.1 != Z_OK then
      return lp.1
  wrG state fun s => { s with level := level }
  wrG state fun s => { s with strategy := strategy }
  return Z_OK

/-- `z_int32_t Z_EXPORT PREFIX(gzclose_w)(gzFile file)` (`gzwrite.c:483-515`). -/
def gzclose_w (file : GzPtr) : G Int32 := do
  let mut ret : Int32 := Z_OK
  if file == none then
    return Z_STREAM_ERROR
  let state := file
  if (← rdG state (·.mode)) != GZ_WRITE then
    return Z_STREAM_ERROR
  if (← rdG state (·.skip)) != 0 then
    if (← gz_zero state) == -1 then
      ret := (← rdG state (·.err))
  if (← gz_comp state Z_FINISH) == -1 then
    ret := (← rdG state (·.err))
  if (← rdG state (·.size)) != 0 then
    if (← rdG state (·.direct)) == 0 then
      let _ ← lm (deflateEnd (← strmOf state))
    gz_buffer_free state
  gz_error state Z_OK .null
  lm (freeB (← (← ldGz state).path.get))
  if (← closeG (← rdG state (·.fd))) == -1 then
    ret := Z_ERRNO
  gz_state_free state
  return ret

end ZlibNg.Gz
