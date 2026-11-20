import ZlibNgF.ZlibNg.«gzguts.h»

/-!
# `gzlib.c` — functions common to reading and writing gzip files (`ZlibNgF`)

Source: `zlib-ng/gzlib.c` with patch 0002 (`gzseek64`); `ZLIB_COMPAT`, x86_64 Linux LP64 (`LSEEK` is `lseek64`,
`O_CLOEXEC` and `O_EXCL` defined, no `WIDECHAR`, no `_WIN32`, no `O_BINARY`). `gzclose` calls `gzclose_r` /
`gzclose_w` and is in `gzlib.c.gzclose.lean`, after the translations of `gzread.c` and `gzwrite.c`.

`z_off_t` and `z_off64_t` are both `long`: `gzseek`, `gztell` and `gzoffset` return their `64` variant's value
(`ret == (z_off_t)ret` always holds). `gzerror`'s out-parameter `errnum` (a caller's `int *`) is the flag `hasErrnum`
(`NULL` or not) and the second result (the value stored), as for `inflateGetDictionary`'s `dictLength`.
-/

set_option autoImplicit false

namespace ZlibNg.Gz
open C ZlibNg.Inflate ZlibNg.Deflate

/-- `void Z_INTERNAL PREFIX(gz_error)(gz_state *state, int err, const char *msg)` (`gzlib.c:587-614`). -/
def gz_error (state : GzPtr) (err : Int32) (msg : BPtr) : G Unit := do
  if (← (← ldGz state).msg.get) != .null then
    if (← rdG state (·.err)) != Z_MEM_ERROR then
      lm (freeB (← (← ldGz state).msg.get))
    wrG state fun s => { s with msg := .val .null }
  if err != Z_OK && err != Z_BUF_ERROR then
    wrG state fun s => { s with «have» := 0 }
  wrG state fun s => { s with err := err }
  if msg == .null then
    return
  if err == Z_MEM_ERROR then
    return
  let m ← lm (allocB ((← lm (strlenB (← (← ldGz state).path.get))) + (← lm (strlenB msg)) + 3).toNat)
  wrG state fun s => { s with msg := .val m }
  if m == .null then
    wrG state fun s => { s with err := Z_MEM_ERROR }
    return
  let path ← (← ldGz state).path.get
  let n := (← lm (strlenB path)) + (← lm (strlenB msg)) + 3
  let _ ← lm (snprintfSSS (← (← ldGz state).msg.get) n path (← (gzLit ": ")) msg)

/-- `static gzFile gz_state_init(void)` (`gzlib.c:27-52`). -/
def gz_state_init : G GzPtr := do
  let state ← gzStateAlloc
  if state == none then
    return none
  let strm ← strmOf state
  lm (wrZ strm fun z => { z with zalloc := .null })
  lm (wrZ strm fun z => { z with zfree := .null })
  lm (wrZ strm fun z => { z with «opaque» := .null })
  lm (wrZ strm fun z => { z with next_in := .null })
  wrG state fun s => { s with size := 0 }
  wrG state fun s => { s with want := GZBUFSIZE }
  wrG state fun s => { s with «in» := .val .null }
  wrG state fun s => { s with out := .val .null }
  wrG state fun s => { s with direct := 0 }
  wrG state fun s => { s with mode := GZ_NONE }
  wrG state fun s => { s with level := Z_DEFAULT_COMPRESSION }
  wrG state fun s => { s with strategy := Z_DEFAULT_STRATEGY }
  wrG state fun s => { s with msg := .val .null }
  wrG state fun s => { s with past := 0 }
  wrG state fun s => { s with skip := 0 }
  return state

/-- `void Z_INTERNAL gz_state_free(gz_state *state)` (`gzlib.c:54-56`). -/
def gz_state_free (state : GzPtr) : G Unit :=
  gzStateFree state

/-- `static void gz_reset(gz_state *state)` (`gzlib.c:59-72`). -/
def gz_reset (state : GzPtr) : G Unit := do
  wrG state fun s => { s with «have» := 0 }
  if (← rdG state (·.mode)) == GZ_READ then
    wrG state fun s => { s with eof := 0 }
    wrG state fun s => { s with past := 0 }
    wrG state fun s => { s with how := LOOK }
  else
    wrG state fun s => { s with reset := 0 }
  wrG state fun s => { s with skip := 0 }
  gz_error state Z_OK .null
  wrG state fun s => { s with pos := 0 }
  lm (wrZ (← strmOf state) fun z => { z with avail_in := 0 })

/-- `void Z_INTERNAL gz_buffer_free(gz_state *state)` (`gzlib.c:104-110`). -/
def gz_buffer_free (state : GzPtr) : G Unit := do
  lm (ZlibNg.Zutil.zng_free_aligned (← (← ldGz state).buffers.get))
  wrG state fun s => { s with buffers := .val .null }
  wrG state fun s => { s with out := .val .null }
  wrG state fun s => { s with «in» := .val .null }
  wrG state fun s => { s with size := 0 }

/-- `int Z_INTERNAL gz_buffer_alloc(gz_state *state)` (`gzlib.c:75-102`, with patch 0012: the null check comes before
`state->out = state->buffers + in_size`). -/
def gz_buffer_alloc (state : GzPtr) : G Int32 := do
  let want ← rdG state (·.want)
  let mut in_size := want
  let mut out_size := want
  if (← rdG state (·.mode)) == GZ_WRITE then
    in_size := want * 2
    if (← rdG state (·.direct)) != 0 then
      out_size := 0
  else if (← rdG state (·.mode)) == GZ_READ then
    out_size := want * 2
  let b ← lm (ZlibNg.Zutil.zng_alloc_aligned (in_size + out_size) 64)
  wrG state fun s => { s with buffers := .val b }
  let b ← (← ldGz state).buffers.get
  wrG state fun s => { s with «in» := .val b }
  if (← (← ldGz state).«in».get) == .null then
    gz_buffer_free state
    gz_error state Z_MEM_ERROR (← (gzLit "out of memory"))
    return -1
  if out_size != 0 then
    let o ← lm ((← (← ldGz state).buffers.get).add (Int.ofNat in_size.toNat))
    wrG state fun s => { s with out := .val o }
  wrG state fun s => { s with size := want }
  return 0

/-- The locals of the mode loop of `gz_open`. -/
structure OpenLoop where
  mode : BPtr
  cloexec : Int32
  exclusive : Int32
  ctl : Ctl

/-- `static gzFile gz_open(const void *path, int fd, const char *mode)` (`gzlib.c:113-291`). -/
def gz_open (path : BPtr) (fd : Int32) (mode : BPtr) : G GzPtr := do
  let cloexec : Int32 := 0
  let exclusive : Int32 := 0
  if path == .null || mode == .null then
    return none
  let state ← gz_state_init
  if state == none then
    return none
  let lp ← gwhile
    (fun (s : OpenLoop) => do
      if s.ctl != .go then return (false, s)
      return ((← lm (load8 s.mode)) != 0, s))
    (fun (s : OpenLoop) => do
      let c ← lm (load8 s.mode)
      let mut s := s
      if c ≥ '0'.toNat.toUInt8 && c ≤ '9'.toNat.toUInt8 then
        let c ← lm (load8 s.mode)
        wrG state fun st => { st with level := c.toUInt32.toInt32 - '0'.toNat.toInt32 }
      else
        if c == 'r'.toNat.toUInt8 then
          wrG state fun st => { st with mode := GZ_READ }
        else if c == 'w'.toNat.toUInt8 then
          wrG state fun st => { st with mode := GZ_WRITE }
        else if c == 'a'.toNat.toUInt8 then
          wrG state fun st => { st with mode := GZ_APPEND }
        else if c == '+'.toNat.toUInt8 then
          gz_state_free state
          return { s with ctl := .ret }
        else if c == 'b'.toNat.toUInt8 then
          pure ()
        else if c == 'e'.toNat.toUInt8 then
          s := { s with cloexec := 1 }
        else if c == 'x'.toNat.toUInt8 then
          s := { s with exclusive := 1 }
        else if c == 'f'.toNat.toUInt8 then
          wrG state fun st => { st with strategy := Z_FILTERED }
        else if c == 'h'.toNat.toUInt8 then
          wrG state fun st => { st with strategy := Z_HUFFMAN_ONLY }
        else if c == 'R'.toNat.toUInt8 then
          wrG state fun st => { st with strategy := Z_RLE }
        else if c == 'F'.toNat.toUInt8 then
          wrG state fun st => { st with strategy := Z_FIXED }
        else if c == 'G'.toNat.toUInt8 then
          wrG state fun st => { st with direct := -1 }
        else if c == 'T'.toNat.toUInt8 then
          wrG state fun st => { st with direct := 1 }
        else
          pure ()
      let m ← lm (s.mode.add 1)
      return { s with mode := m })
    ⟨mode, cloexec, exclusive, .go⟩
  if lp.ctl == .ret then
    return none
  let cloexec := lp.cloexec
  let exclusive := lp.exclusive
  if (← rdG state (·.mode)) == GZ_NONE then
    gz_state_free state
    return none
  if (← rdG state (·.mode)) == GZ_READ then
    if (← rdG state (·.direct)) == 1 then
      gz_state_free state
      return none
    if (← rdG state (·.direct)) == 0 then
      wrG state fun s => { s with direct := 1 }
  else if (← rdG state (·.direct)) == -1 then
    gz_state_free state
    return none
  let len ← lm (strlenB path)
  let p ← lm (allocB (len + 1).toNat)
  wrG state fun s => { s with path := .val p }
  if (← (← ldGz state).path.get) == .null then
    gz_state_free state
    return none
  let _ ← lm (snprintfS (← (← ldGz state).path.get) (len + 1) path)
  let smode ← rdG state (·.mode)
  let oflag : Int32 :=
    O_LARGEFILE |||
    (if cloexec != 0 then O_CLOEXEC else 0) |||
    (if smode == GZ_READ then O_RDONLY else
      (O_WRONLY ||| O_CREAT ||| (if exclusive != 0 then O_EXCL else 0) |||
        (if smode == GZ_WRITE then O_TRUNC else O_APPEND)))
  let sfd ← if fd > -1 then pure fd else openG path oflag
  wrG state fun s => { s with fd := sfd }
  if (← rdG state (·.fd)) == -1 then
    lm (freeB (← (← ldGz state).path.get))
    gz_state_free state
    return none
  if (← rdG state (·.mode)) == GZ_APPEND then
    let _ ← lseekG (← rdG state (·.fd)) 0 SEEK_END
    wrG state fun s => { s with mode := GZ_WRITE }
  if (← rdG state (·.mode)) == GZ_READ then
    let st ← lseekG (← rdG state (·.fd)) 0 SEEK_CUR
    wrG state fun s => { s with start := st }
    if (← rdG state (·.start)) == -1 then
      wrG state fun s => { s with start := 0 }
  gz_reset state
  return state

/-- `gzFile Z_EXPORT PREFIX(gzopen)(const char *path, const char *mode)` (`gzlib.c:294-296`). -/
def gzopen (path mode : BPtr) : G GzPtr :=
  gz_open path (-1) mode

/-- `gzFile Z_EXPORT PREFIX4(gzopen)(const char *path, const char *mode)` (`gzlib.c:299-301`). -/
def gzopen64 (path mode : BPtr) : G GzPtr :=
  gz_open path (-1) mode

/-- `gzFile Z_EXPORT PREFIX(gzdopen)(int fd, const char *mode)` (`gzlib.c:305-314`). `char path[32]` is a local
array (`localBlock`). -/
def gzdopen (fd : Int32) (mode : BPtr) : G GzPtr := do
  if fd == -1 then
    return none
  let path ← lm (localBlock 32)
  let _ ← lm (snprintfFd path 32 fd)
  let gz ← gz_open path fd mode
  lm (dropLocal path)
  return gz

/-- `z_int32_t Z_EXPORT PREFIX(gzbuffer)(gzFile file, z_uint32_t size)` (`gzlib.c:338-365`). -/
def gzbuffer (file : GzPtr) (size : UInt32) : G Int32 := do
  if file == none then
    return -1
  let state := file
  if (← rdG state (·.mode)) != GZ_READ && (← rdG state (·.mode)) != GZ_WRITE then
    return -1
  if (← rdG state (·.size)) != 0 then
    return -1
  let mut size := size
  if size > GZBUFSIZE_MAX then
    size := GZBUFSIZE_MAX
  if size < 8 then
    size := 8
  wrG state fun s => { s with want := size }
  return 0

/-- `z_int32_t Z_EXPORT PREFIX(gzrewind)(gzFile file)` (`gzlib.c:368-385`). -/
def gzrewind (file : GzPtr) : G Int32 := do
  if file == none then
    return -1
  let state := file
  if (← rdG state (·.mode)) != GZ_READ ||
      ((← rdG state (·.err)) != Z_OK && (← rdG state (·.err)) != Z_BUF_ERROR) then
    return -1
  if (← lseekG (← rdG state (·.fd)) (← rdG state (·.start)) SEEK_SET) == -1 then
    return -1
  gz_reset state
  return 0

/-- `z_off64_t Z_EXPORT PREFIX4(gzseek)(gzFile file, z_off64_t offset, int whence)` (`gzlib.c:388-461` with patch
0002). The locals `n` and `ret` are written before they are read. `pos = whence == SEEK_SET ? 0 : state->x.pos +
(state->past ? 0 : state->skip)` is the `if` that computes `pos`; `(z_off64_t)state->x.have` is the value of
`x.have`. -/
def gzseek64 (file : GzPtr) (offset : Int64) (whence : Int32) : G Int64 := do
  if file == none then
    return -1
  let state := file
  if (← rdG state (·.mode)) != GZ_READ && (← rdG state (·.mode)) != GZ_WRITE then
    return -1
  if (← rdG state (·.err)) != Z_OK && (← rdG state (·.err)) != Z_BUF_ERROR then
    return -1
  if whence != SEEK_SET && whence != SEEK_CUR then
    return -1
  let mut offset := offset
  let mut pos : Int64 ← if whence == SEEK_SET then pure 0 else do
      let add : Int64 ← if (← rdG state (·.past)) != 0 then pure 0 else rdG state (·.skip)
      lm (chkI64 ((← rdG state (·.pos)).toInt + add.toInt))
  if pos > 0 then
    if offset > (← lm (chkI64 (GZ_OFF_MAX.toInt - pos.toInt))) then
      return -1
  if offset < (← lm (chkI64 (-pos.toInt))) then
    return -1
  pos ← lm (chkI64 (pos.toInt + offset.toInt))
  if (← rdG state (·.pos)) < 0 then
    if pos > (← lm (chkI64 (GZ_OFF_MAX.toInt + (← rdG state (·.pos)).toInt))) then
      return -1
  if (← rdG state (·.mode)) == GZ_READ then
    if (← rdG state (·.how)) == COPY then
      let ret ← lseekG (← rdG state (·.fd))
        (← lm (chkI64 ((← lm (chkI64 (pos.toInt - (← rdG state (·.pos)).toInt))).toInt -
          Int.ofNat (← rdG state (·.«have»)).toNat))) SEEK_CUR
      if ret == -1 then
        return -1
      wrG state fun s => { s with «have» := 0 }
      wrG state fun s => { s with eof := 0 }
      wrG state fun s => { s with past := 0 }
      wrG state fun s => { s with skip := 0 }
      gz_error state Z_OK .null
      lm (wrZ (← strmOf state) fun z => { z with avail_in := 0 })
      wrG state fun s => { s with pos := pos }
      return pos
  if pos < (← rdG state (·.pos)) then
    if (← rdG state (·.mode)) != GZ_READ then
      return -1
    if (← gzrewind file) == -1 then
      return -1
  offset ← lm (chkI64 (pos.toInt - (← rdG state (·.pos)).toInt))
  if (← rdG state (·.mode)) == GZ_READ then
    if (← rdG state (·.«have»)) != 0 then
      if offset != 0 then
        let hv ← rdG state (·.«have»)
        let n : UInt32 := if GT_OFF hv || (Int64.ofNat hv.toNat) > offset then offset.toUInt64.toUInt32 else hv
        wrG state fun s => { s with «have» := s.«have» - n }
        let nx ← lm ((← (← ldGz state).next.get).add (Int.ofNat n.toNat))
        wrG state fun s => { s with next := .val nx }
        let np ← lm (chkI64 ((← rdG state (·.pos)).toInt + n.toNat))
        wrG state fun s => { s with pos := np }
        offset ← lm (chkI64 (offset.toInt - n.toNat))
  wrG state fun s => { s with skip := offset }
  return pos

/-- `z_off_t Z_EXPORT PREFIX(gzseek)(gzFile file, z_off_t offset, int whence)` (`gzlib.c:465-470`). -/
def gzseek (file : GzPtr) (offset : Int64) (whence : Int32) : G Int64 := do
  let ret ← gzseek64 file offset whence
  return ret

/-- `z_off64_t Z_EXPORT PREFIX4(gztell)(gzFile file)` (`gzlib.c:474-486`). -/
def gztell64 (file : GzPtr) : G Int64 := do
  if file == none then
    return -1
  let state := file
  if (← rdG state (·.mode)) != GZ_READ && (← rdG state (·.mode)) != GZ_WRITE then
    return -1
  let add : Int64 ← if (← rdG state (·.past)) != 0 then pure 0 else rdG state (·.skip)
  lm (chkI64 ((← rdG state (·.pos)).toInt + add.toInt))

/-- `z_off_t Z_EXPORT PREFIX(gztell)(gzFile file)` (`gzlib.c:490-496`). -/
def gztell (file : GzPtr) : G Int64 := do
  let ret ← gztell64 file
  return ret

/-- `z_off64_t Z_EXPORT PREFIX4(gzoffset)(gzFile file)` (`gzlib.c:500-518`). `offset -= strm.avail_in` converts the
`unsigned` to `long`. -/
def gzoffset64 (file : GzPtr) : G Int64 := do
  if file == none then
    return -1
  let state := file
  if (← rdG state (·.mode)) != GZ_READ && (← rdG state (·.mode)) != GZ_WRITE then
    return -1
  let mut offset ← lseekG (← rdG state (·.fd)) 0 SEEK_CUR
  if offset == -1 then
    return -1
  if (← rdG state (·.mode)) == GZ_READ then
    let ai ← lm (rdZ (← strmOf state) (·.avail_in))
    offset ← lm (chkI64 (offset.toInt - Int.ofNat ai.toNat))
  return offset

/-- `z_off_t Z_EXPORT PREFIX(gzoffset)(gzFile file)` (`gzlib.c:522-527`). -/
def gzoffset (file : GzPtr) : G Int64 := do
  let ret ← gzoffset64 file
  return ret

/-- `z_int32_t Z_EXPORT PREFIX(gzeof)(gzFile file)` (`gzlib.c:531-543`). -/
def gzeof (file : GzPtr) : G Int32 := do
  if file == none then
    return 0
  let state := file
  if (← rdG state (·.mode)) != GZ_READ && (← rdG state (·.mode)) != GZ_WRITE then
    return 0
  if (← rdG state (·.mode)) == GZ_READ then rdG state (·.past) else return 0

/-- `const char * Z_EXPORT PREFIX(gzerror)(gzFile file, z_int32_t *errnum)` (`gzlib.c:546-560`). -/
def gzerror (file : GzPtr) (hasErrnum : Bool) : G (BPtr × Option Int32) := do
  if file == none then
    return (.null, none)
  let state := file
  if (← rdG state (·.mode)) != GZ_READ && (← rdG state (·.mode)) != GZ_WRITE then
    return (.null, none)
  let en : Option Int32 ← if hasErrnum then do pure (some (← rdG state (·.err))) else pure none
  if (← rdG state (·.err)) == Z_MEM_ERROR then
    return (← (gzLit "out of memory"), en)
  let m ← (← ldGz state).msg.get
  if m == .null then
    return (← (gzLit ""), en)
  return (← (← ldGz state).msg.get, en)

/-- `void Z_EXPORT PREFIX(gzclearerr)(gzFile file)` (`gzlib.c:563-579`). -/
def gzclearerr (file : GzPtr) : G Unit := do
  if file == none then
    return
  let state := file
  if (← rdG state (·.mode)) != GZ_READ && (← rdG state (·.mode)) != GZ_WRITE then
    return
  if (← rdG state (·.mode)) == GZ_READ then
    wrG state fun s => { s with eof := 0 }
    wrG state fun s => { s with past := 0 }
  gz_error state Z_OK .null

/-- `unsigned Z_INTERNAL gz_intmax(void)` (`gzlib.c:617-619`). -/
def gz_intmax : G UInt32 :=
  return 2147483647

end ZlibNg.Gz
