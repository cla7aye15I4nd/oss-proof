import ZlibNgF.Runtime.Fs
import ZlibNgF.Runtime.Inflate

/-!
# The gz monad, the `gz_state` object and the libc calls of the gz* functions (`ZlibNgF`, trusted base)

A gz computation is `G α = StateT World M α`: the world (`World`) holds the file system and OS-call oracles of
`Runtime/Fs.lean`, the `strerror` and `vsnprintf` oracles, and the `gz_state` objects. A heap computation (`M`, the
inflate and deflate translations) lifts into `G`; a fault is still `Fault.ub`.

## `gz_state`
`gz_state_init` gets the state from `malloc(sizeof(gz_state))` (`zng_alloc`). The model allocates the block (the
allocation oracle decides success) and carves a typed `GzState` from all of it, keyed by the block number
(`World.gzs`), as the inflate state is carved from its block. `malloc` returns memory aligned for every object type
(ISO C17 §7.22.3p1), so the carve has no alignment check. The state's pointer fields start `Ival.uninit` (reading one
faults), its integers come from `Heap.garbage`. The embedded `z_stream` is a fresh entry of `Heap.streams`; its
integer fields come from `Heap.garbage`, its pointer fields are `NULL` in the record (weaker than C: the C writes
`zalloc`, `zfree`, `opaque` and `next_in` in `gz_state_init`, and `inflateInit2_` / `deflateInit2_` write the others
before they are read; the translation does not read a field of the embedded stream before one of these writes).
`free(state)` (`zng_free`) ends the block, the `GzState` and the embedded `z_stream` together. A `gzFile` is a
pointer to the state (`GzPtr`, the block number): its first member is the public `struct gzFile_s` (`have`, `next`,
`pos`), which the `gzgetc` macro of `zlib.h` reads and writes in the caller.

## String literals and `strerror`
The string literals of the gz* files are static arrays: `gzLit` returns a pointer to a read-only block of
`Heap.consts`, made at a fresh key the first time the literal is used and found again through `World.litKeys`.
`strerror(errno)` returns a pointer to a fresh read-only block of `Heap.consts` holding the text the oracle
`strerrorText` gives for the number: trusted to be a string of the C library that stays valid until the C copies it (`gz_error` copies it at once).

## `snprintf` and `vsnprintf`
`snprintf` with the fixed formats of `gzlib.c` (`"%s"`, `"<fd:%d>"`, `"%s%s%s"`) is modelled exactly: the arguments
are read as strings (`strlen`), then `min(len, size - 1)` bytes and a terminating zero are written, and the length of
the full output is returned. `vsnprintf(next, size, format, va)` of `gzvprintf` formats the caller's arguments, which
the model does not represent: the oracle (`printfRet`, `printfOut`, numbered by `nprintf`) gives the result. Trusted:
the caller's format and arguments match (as `zlib.h` requires of `printf`-style formats), and the C library's
`vsnprintf` then reads the format (the model checks that it is a string) and writes only inside
`[next, next + size)`: for a result `r ≥ 0`, `min(r, size - 1)` bytes of output and a zero after them, for a
failure (`r < 0`), any `size` bytes. The oracle's bytes are those bytes.

## OS calls
`open`, `read`, `write`, `lseek`, `close` act on the world as `Runtime/Fs.lean` says. `read` and `write` access the
caller's buffer like a library function: the whole range `[buf, buf + n)` must be inside a live object (writable for
`read`) when `n > 0`; with `n == 0` the buffer is not accessed (POSIX, not ISO C, governs these calls).
-/

set_option autoImplicit false

namespace C

instance : Junk Int64 := ⟨fun x => x.toInt64⟩

/-- `gz_state` (`gzguts.h`). `x.have`, `x.next`, `x.pos` are the public `struct gzFile_s`. `strm` is the embedded
`z_stream`: the number of its entry of `Heap.streams`. -/
structure GzState where
  «have» : UInt32
  next : Ival BPtr
  pos : Int64
  mode : Int32
  fd : Int32
  path : Ival BPtr
  size : UInt32
  want : UInt32
  «in» : Ival BPtr
  out : Ival BPtr
  buffers : Ival BPtr
  direct : Int32
  how : Int32
  start : Int64
  eof : Int32
  past : Int32
  level : Int32
  strategy : Int32
  reset : Int32
  skip : Int64
  err : Int32
  msg : Ival BPtr
  strm : Nat
  deriving Inhabited

/-- `sizeof(gz_state)` on LP64, measured on the built configuration. -/
def SIZEOF_GZ_STATE : Nat := 248

/-- A `gz_state` whose fields are unset: integers from the garbage stream `g`. -/
def GzState.garbage (g : Nat → UInt64) (strm : Nat) : GzState where
  «have» := Junk.of (g 0)
  next := .uninit
  pos := Junk.of (g 1)
  mode := Junk.of (g 2)
  fd := Junk.of (g 3)
  path := .uninit
  size := Junk.of (g 4)
  want := Junk.of (g 5)
  «in» := .uninit
  out := .uninit
  buffers := .uninit
  direct := Junk.of (g 6)
  how := Junk.of (g 7)
  start := Junk.of (g 8)
  eof := Junk.of (g 9)
  past := Junk.of (g 10)
  level := Junk.of (g 11)
  strategy := Junk.of (g 12)
  reset := Junk.of (g 13)
  skip := Junk.of (g 14)
  err := Junk.of (g 15)
  msg := .uninit
  strm := strm

/-- The text glibc's `strerror` gives for the numbers the drivers use (the default `strerrorText`; goals quantify over
every text). -/
def linuxStrerror (e : Int32) : Array UInt8 :=
  let s := match e.toInt with
    | 0 => "Success"
    | 2 => "No such file or directory"
    | 4 => "Interrupted system call"
    | 5 => "Input/output error"
    | 9 => "Bad file descriptor"
    | 11 => "Resource temporarily unavailable"
    | 13 => "Permission denied"
    | 17 => "File exists"
    | 22 => "Invalid argument"
    | 28 => "No space left on device"
    | 29 => "Illegal seek"
    | 32 => "Broken pipe"
    | 75 => "Value too large for defined data type"
    | n => s!"Unknown error {n}"
  s.toUTF8.data

/-- The world of a gz computation. -/
structure World where
  fs : Fs := {}
  /-- the text of `strerror(e)` (no zero byte inside) -/
  strerrorText : Int32 → Array UInt8 := linuxStrerror
  /-- the `Heap.consts` key of each string literal of `gzLits` made so far -/
  litKeys : List (Nat × Nat) := []
  /-- the result of the caller-format `vsnprintf` call `n` -/
  printfRet : Nat → Int32 := fun _ => 0
  /-- the bytes that call `n` writes (see the module doc) -/
  printfOut : Nat → Array UInt8 := fun _ => #[]
  nprintf : Nat := 0
  /-- the `gz_state` carved from heap block `b` -/
  gzs : Tbl (Option GzState) := .empty
  deriving Inhabited

/-- A gz computation. -/
abbrev G (α : Type) : Type := StateT World M α

/-- Undefined behaviour inside `G`. -/
def gub {α : Type} (what : String) : G α := fun _ => C.ub what

/-- A heap computation inside `G`. -/
def lm {α : Type} (m : M α) : G α := StateT.lift m

/-- The heap, read inside `G`. -/
def getHeap : G Heap := lm (fun h => .ok (h, h) : M Heap)

/-- A pointer to a `gz_state`: null, or the heap block that holds it. -/
abbrev GzPtr := Option Nat

/-- The `gz_state` of block `b`, while the block is alive. -/
def World.gz (w : World) (h : Heap) (b : Nat) : Option GzState :=
  match h.bytes b with
  | some _ => w.gzs b
  | none => none

def ldGz (p : GzPtr) : G GzState := do
  match p with
  | none => gub "null gz_state pointer"
  | some b =>
    match (← get).gz (← getHeap) b with
    | some s => return s
    | none => gub "dangling gz_state pointer"

def stGz (p : GzPtr) (s : GzState) : G Unit := do
  let _ ← ldGz p
  match p with
  | none => gub "null gz_state pointer"
  | some b => modify fun w => { w with gzs := upd w.gzs b (some s) }

/-- `state->f`. -/
def rdG {α : Type} (p : GzPtr) (f : GzState → α) : G α := do return f (← ldGz p)
/-- `state->f = ...`. -/
def wrG (p : GzPtr) (f : GzState → GzState) : G Unit := do stGz p (f (← ldGz p))

/-- `&(state->strm)`. -/
def strmOf (p : GzPtr) : G StreamPtr := do return some (← ldGz p).strm

/-- `(gz_state *)zng_alloc(sizeof(gz_state))`: `NULL`, or a fresh `gz_state` with unset fields. -/
def gzStateAlloc : G GzPtr := do
  let p ← lm (allocB SIZEOF_GZ_STATE)
  match p with
  | .ref (.heap b) 0 =>
    if ((← get).gzs b).isSome then gub "second gz_state in one block (not modelled)"
    lm (cutBytes b 0)
    let h ← getHeap
    let z : ZStream := {
      avail_in := Junk.of (h.garbage (2 ^ 43 + b) 100), total_in := h.garbage (2 ^ 43 + b) 101,
      avail_out := Junk.of (h.garbage (2 ^ 43 + b) 102), total_out := h.garbage (2 ^ 43 + b) 103,
      data_type := Junk.of (h.garbage (2 ^ 43 + b) 104), adler := h.garbage (2 ^ 43 + b) 105,
      reserved := h.garbage (2 ^ 43 + b) 106 }
    let s ← lm (newStream z)
    match s with
    | some i =>
      modify fun w => { w with gzs := upd w.gzs b (some (GzState.garbage (h.garbage (2 ^ 43 + b)) i)) }
      return some b
    | none => gub "unreachable: newStream"
  | .null => return none
  | _ => gub "unreachable: malloc result"

/-- `zng_free(state)` (`free`): ends the block, the `gz_state` and its embedded `z_stream`. -/
def gzStateFree (p : GzPtr) : G Unit := do
  let s ← ldGz p
  match p with
  | none => gub "unreachable"
  | some b =>
    lm (freeB (.ref (.heap b) 0))
    modify fun w => { w with gzs := upd w.gzs b none }
    lm (dropStream (some s.strm))

/-! ## Checked signed 64-bit arithmetic and loops -/

/-- A `long` (`z_off64_t`, `ssize_t`) result: faults on signed overflow (ISO C17 §6.5p5). -/
def chkI64 (v : Int) : M Int64 :=
  if -(2 ^ 63 : Int) ≤ v ∧ v < 2 ^ 63 then pure (Int64.ofInt v) else ub "signed integer overflow"

/-- `while (cond) body` in `G`. -/
def gwhile {σ : Type} (cond : σ → G (Bool × σ)) (body : σ → G σ) (s : σ) : G σ :=
  go fuel s
where
  go : Nat → σ → G σ
    | 0, _ => fun _ _ => .error .outOfFuel
    | n + 1, s => do
      let (c, s) ← cond s
      if c then go n (← body s) else pure s

/-- `do body while (cond)` in `G`. -/
def gdoWhile {σ : Type} (body : σ → G σ) (cond : σ → G (Bool × σ)) (s : σ) : G σ :=
  go fuel s
where
  go : Nat → σ → G σ
    | 0, _ => fun _ _ => .error .outOfFuel
    | n + 1, s => do
      let s ← body s
      let (c, s) ← cond s
      if c then go n s else pure s

/-! ## Bytes of objects -/

/-- The `n` bytes at `p` (all inside a live object). -/
def loadBytes (p : BPtr) (n : Nat) : M (Array UInt8) := fun h =>
  match p with
  | .null => .error (.ub "read through a null pointer")
  | .ref r off =>
    match Space.get h r with
    | none => .error (.ub "read through a dangling pointer")
    | some a => if off + n ≤ a.size then .ok (a.extract off (off + n), h) else .error (.ub "read outside its object")

/-- Store `bs` at `p`; the object must be writable and hold `cap ≥ bs.size` bytes from `p` on. -/
def storeBytes (p : BPtr) (bs : Array UInt8) (cap : Nat) : M Unit := fun h =>
  match p with
  | .null => .error (.ub "store through a null pointer")
  | .ref r off =>
    match Space.get h r with
    | none => .error (.ub "store through a dangling pointer")
    | some a =>
      if Space.ro h r then .error (.ub "store into a read-only object")
      else if off + cap ≤ a.size ∧ bs.size ≤ cap then
        let out := Id.run do
          let mut out := a
          for i in [0:bs.size] do
            out := out.set! (off + i) bs[i]!
          return out
        .ok ((), Space.modify h r (fun _ => out))
      else .error (.ub "store outside its object")

/-- `strlen(p)` (ISO C17 §7.24.6.3): the bytes before the first zero byte, which must lie inside the object. -/
def strBytes (p : BPtr) : M (Array UInt8) := fun h =>
  match p with
  | .null => .error (.ub "strlen of a null pointer")
  | .ref r off =>
    match Space.get h r with
    | none => .error (.ub "strlen of a dangling pointer")
    | some a =>
      let rest := a.extract off a.size
      match rest.findIdx? (· == 0) with
      | some i => .ok (rest.extract 0 i, h)
      | none => .error (.ub "strlen without a terminating zero in the object")

/-- `strlen(p)`. -/
def strlenB (p : BPtr) : M UInt64 := do return UInt64.ofNat (← strBytes p).size

/-- `memchr(p, c, n)` (ISO C17 §7.24.5.1): reads the bytes in order and stops at the first `c`; `p` must point into
a live object even for `n == 0`. Returns `NULL` or a pointer to the byte. -/
def memchrB (p : BPtr) (c : UInt8) (n : Nat) : M BPtr := fun h =>
  match p with
  | .null => .error (.ub "memchr of a null pointer")
  | .ref r off =>
    match Space.get h r with
    | none => .error (.ub "memchr of a dangling pointer")
    | some a =>
      if off > a.size then .error (.ub "memchr outside its object") else
      let avail := min n (a.size - off)
      match ((a.extract off (off + avail)).findIdx? (· == c)) with
      | some i => .ok (.ref r (off + i), h)
      | none => if n ≤ a.size - off then .ok (.null, h) else .error (.ub "memchr reads outside its object")

/-- `snprintf(dst, size, ...)` whose full output is `out`: writes `min(len, size - 1)` bytes and a zero when
`size > 0`, returns the length (`-1` if it does not fit in an `int`). -/
def snprintfOut (dst : BPtr) (size : UInt64) (out : Array UInt8) : M Int32 := do
  if size != 0 then
    let k := min out.size (size.toNat - 1)
    storeBytes dst ((out.extract 0 k).push 0) size.toNat
  return if out.size < 2 ^ 31 then Int32.ofNat out.size else -1

/-- `snprintf(dst, size, "%s", s)`. -/
def snprintfS (dst : BPtr) (size : UInt64) (s : BPtr) : M Int32 := do
  snprintfOut dst size (← strBytes s)

/-- `snprintf(dst, size, "<fd:%d>", fd)`. -/
def snprintfFd (dst : BPtr) (size : UInt64) (fd : Int32) : M Int32 := do
  snprintfOut dst size s!"<fd:{fd.toInt}>".toUTF8.data

/-- `snprintf(dst, size, "%s%s%s", a, b, c)`. -/
def snprintfSSS (dst : BPtr) (size : UInt64) (a b c : BPtr) : M Int32 := do
  let x ← strBytes a
  let y ← strBytes b
  let z ← strBytes c
  snprintfOut dst size (x ++ y ++ z)

/-- `vsnprintf(next, size, format, va)` with the caller's format: the oracle's call (see the module doc). -/
def vsnprintfG (dst : BPtr) (size : UInt64) (format : BPtr) : G Int32 := do
  let _ ← lm (strBytes format)
  let w ← get
  let n := w.nprintf
  set { w with nprintf := n + 1 }
  let r := w.printfRet n
  let out := w.printfOut n
  if size != 0 then
    if r ≥ 0 then
      let k := min r.toNatClampNeg (size.toNat - 1)
      let body := (out.extract 0 k) ++ Array.replicate (k - min k out.size) 0
      lm (storeBytes dst (body.push 0) size.toNat)
    else
      lm (storeBytes dst (out.extract 0 size.toNat) size.toNat)
  return r

/-! ## String literals and `strerror` -/

/-- The string literals of the gz* files. -/
def gzLits : Array String := #[
  "out of memory",
  "invalid compression parameters",
  "unexpected end of file",
  "internal error: inflate stream corrupt",
  "compressed data error",
  "request does not fit in an int",
  "request does not fit in a size_t",
  "out of room to push characters",
  "requested length does not fit in int",
  "string length does not fit in int",
  "internal error: deflate stream corrupt",
  ": ",
  "",
  "write position does not fit in z_off64_t",
  "read position does not fit in z_off64_t"
]

/-- A fresh read-only block of `Heap.consts` holding `a`. -/
def newConst (a : Array UInt8) : M BPtr := fun h =>
  let k := h.consts.arr.size
  .ok (.ref (.const k) 0, { h with consts := upd h.consts k (some a) })

/-- A pointer to the string literal `s` of a gz* file (see the module doc). -/
def gzLit (s : String) : G BPtr := do
  match gzLits.findIdx? (· == s) with
  | some i =>
    match ((← get).litKeys.find? (·.1 == i)) with
    | some (_, k) => return .ref (.const k) 0
    | none =>
      let p ← lm (newConst (Heap.litBytes s))
      match p with
      | .ref (.const k) _ => modify fun w => { w with litKeys := (i, k) :: w.litKeys }
      | _ => pure ()
      return p
  | none => gub "unknown gz string literal"

/-- `zstrerror()`, that is `strerror(errno)`. -/
def zstrerror : G BPtr := do
  let w ← get
  lm (newConst ((w.strerrorText w.fs.errno).push 0))

/-! ## OS calls -/

def modifyFs {α : Type} (f : Fs → α × Fs) : G α := do
  let w ← get
  let (a, fs) := f w.fs
  set { w with fs := fs }
  return a

/-- `open(path, oflag, 0666)`. -/
def openG (path : BPtr) (oflag : Int32) : G Int32 := do
  let p ← lm (strBytes path)
  modifyFs fun fs => fs.openCall p oflag

/-- `read(fd, buf, len)`. -/
def readG (fd : Int32) (buf : BPtr) (len : UInt64) : G Int64 := do
  if len != 0 then
    lm (storeBytes buf #[] len.toNat)
  let (r, bs) ← modifyFs fun fs => let (r, bs, fs) := fs.readCall fd len; ((r, bs), fs)
  if r > 0 then
    lm (storeBytes buf bs len.toNat)
  return r

/-- `write(fd, buf, len)`. -/
def writeG (fd : Int32) (buf : BPtr) (len : UInt64) : G Int64 := do
  let bs ← if len != 0 then lm (loadBytes buf len.toNat) else pure #[]
  modifyFs fun fs => fs.writeCall fd bs

/-- `lseek(fd, off, whence)` (`LSEEK`). -/
def lseekG (fd : Int32) (off : Int64) (whence : Int32) : G Int64 :=
  modifyFs fun fs => fs.lseekCall fd off whence

/-- `close(fd)`. -/
def closeG (fd : Int32) : G Int32 :=
  modifyFs fun fs => fs.closeCall fd

end C
