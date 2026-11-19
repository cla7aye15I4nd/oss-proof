import ZlibNgF.ZlibNg.«gzlib.c»

/-!
# `gzread.c` — reading gzip files (`ZlibNgF`)

Source: `zlib-ng/gzread.c`; `ZLIB_COMPAT`, x86_64 Linux LP64, no `ZLIB_DEBUG` (`Assert` is empty). The
`inflateInit2` macro of `zlib.h` calls `inflateInit2_` with `ZLIB_VERSION` and `sizeof(z_stream)`.

`gz_load`'s out-parameter `have` points either to a local of the caller or to `state->x.have` (from `gz_fetch`).
Because `gz_error` also writes `state->x.have`, the second case is not an independent out-parameter: `gz_load` takes
`toX` and then reads and writes `state->x.have` itself at each `*have` of the C; otherwise `*have` is a local and its
final value is the second result (normalisation 1).
-/

set_option autoImplicit false

namespace ZlibNg.Gz
open C ZlibNg.Inflate ZlibNg.Deflate

/-- `static int gz_read_init(gz_state *state)` (`gzread.c:21-40`). -/
def gz_read_init (state : GzPtr) : G Int32 := do
  if (← gz_buffer_alloc state) != 0 then
    gz_error state Z_MEM_ERROR (← lm (gzLit "out of memory"))
    return -1
  let ret ← lm (inflateInit2_ (← strmOf state) (MAX_WBITS + 16) (← lm (strLitRef ZLIB_VERSION))
    SIZEOF_Z_STREAM.toInt32)
  if ret != Z_OK then
    gz_buffer_free state
    if ret == Z_MEM_ERROR then
      gz_error state Z_MEM_ERROR (← lm (gzLit "out of memory"))
    else
      gz_error state Z_STREAM_ERROR (← lm (gzLit "invalid compression parameters"))
    return -1
  return 0

/-- The locals of the read loop of `gz_load`. -/
structure LoadLoop where
  ret : Int64
  hv : UInt32
  ctl : Ctl

/-- `static int gz_load(gz_state *state, unsigned char *buf, unsigned len, unsigned *have)` (`gzread.c:46-63`).
`ret` is written before it is read. -/
def gz_load (state : GzPtr) (buf : BPtr) (len : UInt32) (toX : Bool) : G (Int32 × UInt32) := do
  let getH : UInt32 → G UInt32 := fun hv => if toX then rdG state (·.«have») else pure hv
  let setH : UInt32 → G UInt32 := fun v => do
    if toX then
      wrG state fun s => { s with «have» := v }
      return 0
    else return v
  let hv ← setH 0
  let lp ← gdoWhile
    (fun (s : LoadLoop) => do
      let h0 ← getH s.hv
      let ret ← readG (← rdG state (·.fd)) (← lm (buf.add (Int.ofNat h0.toNat))) (len - (← getH s.hv)).toUInt64
      if ret ≤ 0 then
        return { s with ret := ret, ctl := .brk }
      let hv ← setH ((← getH s.hv) + ret.toUInt64.toUInt32)
      return { s with ret := ret, hv := hv })
    (fun (s : LoadLoop) => do
      if s.ctl != .go then return (false, s)
      return ((← getH s.hv) < len, s))
    ⟨0, hv, .go⟩
  if lp.ret < 0 then
    gz_error state Z_ERRNO (← zstrerror)
    return (-1, lp.hv)
  if lp.ret == 0 then
    wrG state fun s => { s with eof := 1 }
  return (0, lp.hv)

/-- The locals of the copy loop of `gz_avail`. -/
structure CopyLoop where
  p : BPtr
  q : BPtr
  n : UInt32

/-- `static int gz_avail(gz_state *state)` (`gzread.c:72-95`). -/
def gz_avail (state : GzPtr) : G Int32 := do
  let strm ← strmOf state
  if (← rdG state (·.err)) != Z_OK && (← rdG state (·.err)) != Z_BUF_ERROR then
    return -1
  if (← rdG state (·.eof)) == 0 then
    if (← lm (rdZ strm (·.avail_in))) != 0 then
      let p ← (← ldGz state).«in».get
      let q ← lm (rdZ strm (·.next_in))
      if q != p then
        let n ← lm (rdZ strm (·.avail_in))
        let _ ← gdoWhile
          (fun (s : CopyLoop) => do
            let v ← lm (load8 s.q)
            lm (store8 s.p v)
            return { s with p := ← lm (s.p.add 1), q := ← lm (s.q.add 1) })
          (fun (s : CopyLoop) => do
            let n := s.n - 1
            return (n != 0, { s with n := n }))
          ⟨p, q, n⟩
    let inb ← (← ldGz state).«in».get
    let ai ← lm (rdZ strm (·.avail_in))
    let (r, got) ← gz_load state (← lm (inb.add (Int.ofNat ai.toNat)))
      ((← rdG state (·.size)) - (← lm (rdZ strm (·.avail_in)))) false
    if r == -1 then
      return -1
    lm (wrZ strm fun z => { z with avail_in := z.avail_in + got })
    let inb ← (← ldGz state).«in».get
    lm (wrZ strm fun z => { z with next_in := inb })
  return 0

/-- `static int gz_look(gz_state *state)` (`gzread.c:106-165`). -/
def gz_look (state : GzPtr) : G Int32 := do
  let strm ← strmOf state
  if (← rdG state (·.size)) == 0 then
    if (← gz_read_init state) == -1 then
      return -1
  if (← rdG state (·.direct)) == -1 then
    let _ ← lm (inflateReset strm)
    wrG state fun s => { s with how := GZIP }
    wrG state fun s => { s with direct := 0 }
    return 0
  if (← lm (rdZ strm (·.avail_in))) < 2 then
    if (← gz_avail state) == -1 then
      return -1
    if (← lm (rdZ strm (·.avail_in))) == 0 then
      return 0
  let magic ← if (← lm (rdZ strm (·.avail_in))) > 1 then do
      if (← lm (index8 (← lm (rdZ strm (·.next_in))) 0)) == 31 then do
        pure ((← lm (index8 (← lm (rdZ strm (·.next_in))) 1)) == 139)
      else pure false
    else pure false
  if magic then
    let _ ← lm (inflateReset strm)
    wrG state fun s => { s with how := GZIP }
    wrG state fun s => { s with direct := 0 }
    return 0
  if (← rdG state (·.direct)) == 0 then
    lm (wrZ strm fun z => { z with avail_in := 0 })
    wrG state fun s => { s with eof := 1 }
    wrG state fun s => { s with «have» := 0 }
    return 0
  let o ← (← ldGz state).out.get
  wrG state fun s => { s with next := .val o }
  lm (Ptr.memcpy (← (← ldGz state).next.get) (← lm (rdZ strm (·.next_in))) (← lm (rdZ strm (·.avail_in))).toNat)
  let ai ← lm (rdZ strm (·.avail_in))
  wrG state fun s => { s with «have» := ai }
  lm (wrZ strm fun z => { z with avail_in := 0 })
  wrG state fun s => { s with how := COPY }
  wrG state fun s => { s with direct := 1 }
  return 0

/-- The locals of the loop of `gz_decomp`. -/
structure DecompLoop where
  ret : Int32
  ctl : Ctl

/-- `static int gz_decomp(gz_state *state)` (`gzread.c:172-214`). -/
def gz_decomp (state : GzPtr) : G Int32 := do
  let ret : Int32 := Z_OK
  let strm ← strmOf state
  let had ← lm (rdZ strm (·.avail_out))
  let lp ← gdoWhile
    (fun (s : DecompLoop) => do
      if (← lm (rdZ strm (·.avail_in))) == 0 then
        if (← gz_avail state) == -1 then
          return { s with ctl := .ret }
      if (← lm (rdZ strm (·.avail_in))) == 0 then
        gz_error state Z_BUF_ERROR (← lm (gzLit "unexpected end of file"))
        return { s with ctl := .brk }
      let ret ← lm (inflate strm Z_NO_FLUSH)
      if ret == Z_STREAM_ERROR || ret == Z_NEED_DICT then
        gz_error state Z_STREAM_ERROR (← lm (gzLit "internal error: inflate stream corrupt"))
        return { s with ret := ret, ctl := .ret }
      if ret == Z_MEM_ERROR then
        gz_error state Z_MEM_ERROR (← lm (gzLit "out of memory"))
        return { s with ret := ret, ctl := .ret }
      if ret == Z_DATA_ERROR then
        let m ← lm (rdZ strm (·.msg))
        gz_error state Z_DATA_ERROR (← if m == .null then lm (gzLit "compressed data error") else lm (rdZ strm (·.msg)))
        return { s with ret := ret, ctl := .ret }
      return { s with ret := ret })
    (fun (s : DecompLoop) => do
      if s.ctl != .go then return (false, s)
      return ((← lm (rdZ strm (·.avail_out))) != 0 && s.ret != Z_STREAM_END, s))
    ⟨ret, .go⟩
  if lp.ctl == .ret then
    return -1
  let ao ← lm (rdZ strm (·.avail_out))
  wrG state fun s => { s with «have» := had - ao }
  let nx ← lm ((← lm (rdZ strm (·.next_out))).add (-(Int.ofNat (← rdG state (·.«have»)).toNat)))
  wrG state fun s => { s with next := .val nx }
  if lp.ret == Z_STREAM_END then
    wrG state fun s => { s with how := LOOK }
  return 0

/-- `static int gz_fetch(gz_state *state)` (`gzread.c:222-254`). The `default:` case is `Z_UNREACHABLE()`
(`__builtin_unreachable()`): reaching it is undefined. -/
def gz_fetch (state : GzPtr) : G Int32 := do
  let strm ← strmOf state
  let lp ← gdoWhile
    (fun (c : Ctl × Int32) => do
      let how ← rdG state (·.how)
      if how == LOOK then
        if (← gz_look state) == -1 then
          return (.ret, -1)
        if (← rdG state (·.how)) == LOOK then
          return (.ret, 0)
        return c
      else if how == COPY then
        let (r, _) ← gz_load state (← (← ldGz state).out.get) ((← rdG state (·.size)) <<< 1) true
        if r == -1 then
          return (.ret, -1)
        let o ← (← ldGz state).out.get
        wrG state fun s => { s with next := .val o }
        return (.ret, 0)
      else if how == GZIP then
        let sz ← rdG state (·.size)
        lm (wrZ strm fun z => { z with avail_out := sz <<< 1 })
        let o ← (← ldGz state).out.get
        lm (wrZ strm fun z => { z with next_out := o })
        if (← gz_decomp state) == -1 then
          return (.ret, -1)
        return c
      else
        gub "Z_UNREACHABLE() reached")
    (fun (c : Ctl × Int32) => do
      if c.1 != .go then return (false, c)
      if (← rdG state (·.«have»)) != 0 then return (false, c)
      return ((← rdG state (·.eof)) == 0 || (← lm (rdZ strm (·.avail_in))) != 0, c))
    (.go, 0)
  if lp.1 == .ret then
    return lp.2
  return 0

/-- `static int gz_skip(gz_state *state)` (`gzread.c:259-284`). -/
def gz_skip (state : GzPtr) : G Int32 := do
  let lp ← gdoWhile
    (fun (c : Ctl) => do
      if (← rdG state (·.«have»)) != 0 then
        let hv ← rdG state (·.«have»)
        let sk ← rdG state (·.skip)
        let n : UInt32 := if GT_OFF hv || Int64.ofNat hv.toNat > sk then sk.toUInt64.toUInt32 else hv
        wrG state fun s => { s with «have» := s.«have» - n }
        let nx ← lm ((← (← ldGz state).next.get).add (Int.ofNat n.toNat))
        wrG state fun s => { s with next := .val nx }
        let np ← lm (chkI64 ((← rdG state (·.pos)).toInt + n.toNat))
        wrG state fun s => { s with pos := np }
        let sk ← lm (chkI64 ((← rdG state (·.skip)).toInt - n.toNat))
        wrG state fun s => { s with skip := sk }
        return c
      else if (← rdG state (·.eof)) != 0 && (← lm (rdZ (← strmOf state) (·.avail_in))) == 0 then
        return .brk
      else
        if (← gz_fetch state) == -1 then
          return .ret
        return c)
    (fun (c : Ctl) => do
      if c != .go then return (false, c)
      return ((← rdG state (·.skip)) != 0, c))
    .go
  if lp == .ret then
    return -1
  return 0

/-- The locals of the loop of `gz_read`. -/
structure ReadLoop where
  buf : BPtr
  len : UInt64
  got : UInt64
  ctl : Ctl

/-- `static size_t gz_read(gz_state *state, void *buf, size_t len)` (`gzread.c:290-361`). -/
def gz_read (state : GzPtr) (buf : BPtr) (len : UInt64) : G UInt64 := do
  if len == 0 then
    return 0
  if (← rdG state (·.skip)) != 0 then
    if (← gz_skip state) == -1 then
      return 0
  let got : UInt64 := 0
  let lp ← gdoWhile
    (fun (s : ReadLoop) => do
      let mut n : UInt32 := 0xFFFFFFFF
      if n.toUInt64 > s.len then
        n := s.len.toUInt32
      if (← rdG state (·.«have»)) != 0 then
        if (← rdG state (·.«have»)) < n then
          n := (← rdG state (·.«have»))
        lm (Ptr.memcpy s.buf (← (← ldGz state).next.get) n.toNat)
        let nx ← lm ((← (← ldGz state).next.get).add (Int.ofNat n.toNat))
        wrG state fun st => { st with next := .val nx }
        wrG state fun st => { st with «have» := st.«have» - n }
      else if (← rdG state (·.eof)) != 0 && (← lm (rdZ (← strmOf state) (·.avail_in))) == 0 then
        wrG state fun st => { st with past := 1 }
        return { s with ctl := .brk }
      else if (← rdG state (·.how)) == LOOK || n < ((← rdG state (·.size)) <<< 1) then
        if (← gz_fetch state) == -1 then
          return { s with ctl := .ret }
        return s
      else if (← rdG state (·.how)) == COPY then
        let (r, n') ← gz_load state s.buf n false
        n := n'
        if r == -1 then
          return { s with ctl := .ret }
      else
        lm (wrZ (← strmOf state) fun z => { z with avail_out := n })
        lm (wrZ (← strmOf state) fun z => { z with next_out := s.buf })
        if (← gz_decomp state) == -1 then
          return { s with ctl := .ret }
        n := (← rdG state (·.«have»))
        wrG state fun st => { st with «have» := 0 }
      let len := s.len - n.toUInt64
      let buf ← lm (s.buf.add (Int.ofNat n.toNat))
      let got := s.got + n.toUInt64
      let np ← lm (chkI64 ((← rdG state (·.pos)).toInt + n.toNat))
      wrG state fun st => { st with pos := np }
      return { s with buf := buf, len := len, got := got })
    (fun (s : ReadLoop) => do
      if s.ctl != .go then return (false, s)
      return (s.len != 0, s))
    ⟨buf, len, got, .go⟩
  if lp.ctl == .ret then
    return 0
  return lp.got

/-- `z_int32_t Z_EXPORT PREFIX(gzread)(gzFile file, void *buf, z_uint32_t len)` (`gzread.c:364-393`). `(z_int32_t)len`
of a value above `INT_MAX` is GCC's modulo-2^32 conversion. -/
def gzread (file : GzPtr) (buf : BPtr) (len : UInt32) : G Int32 := do
  if file == none then
    return -1
  let state := file
  if (← rdG state (·.mode)) != GZ_READ ||
      ((← rdG state (·.err)) != Z_OK && (← rdG state (·.err)) != Z_BUF_ERROR) then
    return -1
  if len.toInt32 < 0 then
    gz_error state Z_STREAM_ERROR (← lm (gzLit "request does not fit in an int"))
    return -1
  let len := (← gz_read state buf len.toUInt64).toUInt32
  if len == 0 && (← rdG state (·.err)) != Z_OK && (← rdG state (·.err)) != Z_BUF_ERROR then
    return -1
  return len.toInt32

/-- `size_t Z_EXPORT PREFIX(gzfread)(void *buf, size_t size, size_t nitems, gzFile file)` (`gzread.c:396-423`). -/
def gzfread (buf : BPtr) (size nitems : UInt64) (file : GzPtr) : G UInt64 := do
  if size == 0 then
    return 0
  if file == none then
    return 0
  let state := file
  if (← rdG state (·.mode)) != GZ_READ ||
      ((← rdG state (·.err)) != Z_OK && (← rdG state (·.err)) != Z_BUF_ERROR) then
    return 0
  if size != 0 && 0xFFFFFFFFFFFFFFFF / size < nitems then
    gz_error state Z_STREAM_ERROR (← lm (gzLit "request does not fit in a size_t"))
    return 0
  let len := nitems * size
  if len != 0 then
    return (← gz_read state buf len) / size
  else
    return 0

/-- `z_int32_t Z_EXPORT PREFIX(gzgetc)(gzFile file)` (`gzread.c:426-448`). `unsigned char buf[1]` is a local
array (`localBlock`). -/
def gzgetc (file : GzPtr) : G Int32 := do
  if file == none then
    return -1
  let state := file
  if (← rdG state (·.mode)) != GZ_READ ||
      ((← rdG state (·.err)) != Z_OK && (← rdG state (·.err)) != Z_BUF_ERROR) then
    return -1
  if (← rdG state (·.«have»)) != 0 then
    wrG state fun s => { s with «have» := s.«have» - 1 }
    let np ← lm (chkI64 ((← rdG state (·.pos)).toInt + 1))
    wrG state fun s => { s with pos := np }
    let p ← (← ldGz state).next.get
    let nx ← lm (p.add 1)
    wrG state fun s => { s with next := .val nx }
    return (← lm (load8 p)).toUInt32.toInt32
  let buf ← lm (localBlock 1)
  let r ← if (← gz_read state buf 1) < 1 then pure (-1) else do pure (← lm (index8 buf 0)).toUInt32.toInt32
  lm (dropLocal buf)
  return r

/-- `int Z_EXPORT PREFIX(gzgetc_)(gzFile file)` (`gzread.c:451-453`). -/
def gzgetc_ (file : GzPtr) : G Int32 :=
  gzgetc file

/-- The locals of the slide loop of `gzungetc`. -/
structure SlideLoop where
  src : BPtr
  dest : BPtr

/-- `z_int32_t Z_EXPORT PREFIX(gzungetc)(z_int32_t c, gzFile file)` (`gzread.c:457-511`). -/
def gzungetc (c : Int32) (file : GzPtr) : G Int32 := do
  if file == none then
    return -1
  let state := file
  if (← rdG state (·.mode)) == GZ_READ then
    if (← rdG state (·.how)) == LOOK then
      if (← rdG state (·.«have»)) == 0 then
        let _ ← gz_look state
  if (← rdG state (·.mode)) != GZ_READ ||
      ((← rdG state (·.err)) != Z_OK && (← rdG state (·.err)) != Z_BUF_ERROR) then
    return -1
  if (← rdG state (·.skip)) != 0 then
    if (← gz_skip state) == -1 then
      return -1
  if c < 0 then
    return -1
  if (← rdG state (·.«have»)) == 0 then
    wrG state fun s => { s with «have» := 1 }
    let e ← lm ((← (← ldGz state).out.get).add (Int.ofNat ((← rdG state (·.size)) <<< 1).toNat))
    let nx ← lm (e.add (-1))
    wrG state fun s => { s with next := .val nx }
    lm (store8 (← lm ((← (← ldGz state).next.get).add 0)) c.toUInt32.toUInt8)
    let np ← lm (chkI64 ((← rdG state (·.pos)).toInt - 1))
    wrG state fun s => { s with pos := np }
    wrG state fun s => { s with past := 0 }
    return c
  if (← rdG state (·.«have»)) == ((← rdG state (·.size)) <<< 1) then
    gz_error state Z_DATA_ERROR (← lm (gzLit "out of room to push characters"))
    return -1
  if (← (← ldGz state).next.get) == (← (← ldGz state).out.get) then
    let src ← lm ((← (← ldGz state).out.get).add (Int.ofNat (← rdG state (·.«have»)).toNat))
    let dest ← lm ((← (← ldGz state).out.get).add (Int.ofNat ((← rdG state (·.size)) <<< 1).toNat))
    let lp ← gwhile
      (fun (s : SlideLoop) => do
        return (← lm (Ptr.lt (← (← ldGz state).out.get) s.src), s))
      (fun (s : SlideLoop) => do
        let dest ← lm (s.dest.add (-1))
        let src ← lm (s.src.add (-1))
        lm (store8 dest (← lm (load8 src)))
        return ⟨src, dest⟩)
      ⟨src, dest⟩
    wrG state fun s => { s with next := .val lp.dest }
  wrG state fun s => { s with «have» := s.«have» + 1 }
  let nx ← lm ((← (← ldGz state).next.get).add (-1))
  wrG state fun s => { s with next := .val nx }
  lm (store8 (← lm ((← (← ldGz state).next.get).add 0)) c.toUInt32.toUInt8)
  let np ← lm (chkI64 ((← rdG state (·.pos)).toInt - 1))
  wrG state fun s => { s with pos := np }
  wrG state fun s => { s with past := 0 }
  return c

/-- The locals of the loop of `gzgets`. -/
structure GetsLoop where
  buf : BPtr
  left : UInt32
  eol : BPtr
  ctl : Ctl

/-- `char * Z_EXPORT PREFIX(gzgets)(gzFile file, char *buf, z_int32_t len)` (`gzread.c:514-569`). `eol` is written
before it is read. -/
def gzgets (file : GzPtr) (buf : BPtr) (len : Int32) : G BPtr := do
  if file == none || buf == .null || len < 1 then
    return .null
  let state := file
  if (← rdG state (·.mode)) != GZ_READ ||
      ((← rdG state (·.err)) != Z_OK && (← rdG state (·.err)) != Z_BUF_ERROR) then
    return .null
  if (← rdG state (·.skip)) != 0 then
    if (← gz_skip state) == -1 then
      return .null
  let str := buf
  let left : UInt32 := len.toUInt32 - 1
  let mut buf := buf
  if left != 0 then
    let lp ← gdoWhile
      (fun (s : GetsLoop) => do
        if (← rdG state (·.«have»)) == 0 then
          if (← gz_fetch state) == -1 then
            return { s with ctl := .ret }
        if (← rdG state (·.«have»)) == 0 then
          wrG state fun st => { st with past := 1 }
          return { s with ctl := .brk }
        let mut n : UInt32 := min (← rdG state (·.«have»)) s.left
        let eol ← lm (memchrB (← (← ldGz state).next.get) 10 n.toNat)
        if eol != .null then
          let d ← lm (Ptr.diff eol (← (← ldGz state).next.get))
          n := d.toUInt64.toUInt32 + 1
        lm (Ptr.memcpy s.buf (← (← ldGz state).next.get) n.toNat)
        wrG state fun st => { st with «have» := st.«have» - n }
        let nx ← lm ((← (← ldGz state).next.get).add (Int.ofNat n.toNat))
        wrG state fun st => { st with next := .val nx }
        let np ← lm (chkI64 ((← rdG state (·.pos)).toInt + n.toNat))
        wrG state fun st => { st with pos := np }
        let buf ← lm (s.buf.add (Int.ofNat n.toNat))
        return { s with buf := buf, left := s.left - n, eol := eol })
      (fun (s : GetsLoop) => do
        if s.ctl != .go then return (false, s)
        return (s.left != 0 && s.eol == .null, s))
      ⟨buf, left, .null, .go⟩
    if lp.ctl == .ret then
      return .null
    buf := lp.buf
  if buf == str then
    return .null
  lm (store8 (← lm (buf.add 0)) 0)
  return str

/-- `z_int32_t Z_EXPORT PREFIX(gzdirect)(gzFile file)` (`gzread.c:572-588`). -/
def gzdirect (file : GzPtr) : G Int32 := do
  if file == none then
    return 0
  let state := file
  if (← rdG state (·.mode)) == GZ_READ then
    if (← rdG state (·.how)) == LOOK then
      if (← rdG state (·.«have»)) == 0 then
        let _ ← gz_look state
  return if (← rdG state (·.direct)) == 1 then 1 else 0

/-- `z_int32_t Z_EXPORT PREFIX(gzclose_r)(gzFile file)` (`gzread.c:591-616`). -/
def gzclose_r (file : GzPtr) : G Int32 := do
  if file == none then
    return Z_STREAM_ERROR
  let state := file
  if (← rdG state (·.mode)) != GZ_READ then
    return Z_STREAM_ERROR
  if (← rdG state (·.size)) != 0 then
    let _ ← lm (inflateEnd (← strmOf state))
    gz_buffer_free state
  let err := if (← rdG state (·.err)) == Z_BUF_ERROR then Z_BUF_ERROR else Z_OK
  gz_error state Z_OK .null
  lm (freeB (← (← ldGz state).path.get))
  let ret ← closeG (← rdG state (·.fd))
  gzStateFree state
  return if ret != 0 then Z_ERRNO else err

end ZlibNg.Gz
