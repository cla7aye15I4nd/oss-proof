import ZlibNgF.Runtime.Libc

/-!
# The file system and the OS-call oracles of the gz* functions (`ZlibNgF`, trusted base)

The gz* functions call `open`, `read`, `write`, `lseek` and `close` (POSIX, not ISO C) and read `errno`. This file
is the model of what those calls do; `Runtime/Gz.lean` runs them inside the gz monad. Values are those of x86_64
Linux (glibc): the `open` flags and the `errno` numbers below.

What a call does is chosen per call by an oracle of the world (`Fs`), numbered by the count `ncall` of OS calls so
far. Each oracle has a `regular` choice, which acts on the in-memory file system as Linux does on a regular file,
and other choices that give every other result the call may give on some descriptor (a pipe, a socket, a device):

* `read`: `fail e` returns `-1` with `errno = e` (any `e`); `short k` reads as a regular read of at most `k` bytes
  (a pipe or socket that has fewer bytes ready); `bytes bs` returns a prefix of `bs` of at most the
  requested length (so any count from 0, end of file, to the request, with any data), taken from the world's
  `budget` of such bytes. The budget is a natural number: a world delivers finitely many bytes in all. An endless
  input (a pipe that is never closed) is outside the model; on it `gzread` may wait forever, as any reader would.
* `write`: `fail e` returns `-1` with `errno = e`; `count k` writes the first `min k len` bytes as a regular write
  would and returns that count (a short write).
* `lseek`: `fail e` returns `-1` with `errno = e`; `value v` returns any 64-bit `v` without moving the descriptor
  (a device whose `lseek` succeeds without moving, such as Linux `/dev/zero`, returns 0; a file with unsigned offsets
  returns values the regular model cannot).
* `open`: `some e` fails with `errno = e` before anything is created.
* `close`: `some e` returns `-1` with `errno = e`; the descriptor is released anyway (Linux).

A successful call leaves `errno` unchanged (the C reads `errno` only after a failed call, or after a short write, where
it sees the stale value). Paths are flat byte strings without directories.
-/

set_option autoImplicit false

namespace C

/-- An open file description: the file, the offset, the access mode and `O_APPEND`. -/
structure OFile where
  node : Nat
  pos : Nat
  rd : Bool
  wr : Bool
  append : Bool
  deriving Inhabited, Repr

/-- What `read` call `n` does. -/
inductive ReadChoice where
  | regular
  | fail (e : Int32)
  | short (k : Nat)
  | bytes (bs : Array UInt8)
  deriving Inhabited

/-- What `write` call `n` does. -/
inductive WriteChoice where
  | regular
  | fail (e : Int32)
  | count (k : Nat)
  deriving Inhabited

/-- What `lseek` call `n` does. -/
inductive LseekChoice where
  | regular
  | fail (e : Int32)
  | value (v : Int64)
  deriving Inhabited

/-- Linux x86_64 `errno` values. -/
def ENOENT : Int32 := 2
def EIO : Int32 := 5
def EBADF : Int32 := 9
def EEXIST : Int32 := 17
def EINVAL : Int32 := 22
def EOVERFLOW : Int32 := 75

/-- Linux x86_64 `open` flags. `O_LARGEFILE` is 0 in user space on x86_64 (glibc adds the kernel flag itself). -/
def O_RDONLY : Int32 := 0
def O_WRONLY : Int32 := 1
def O_CREAT : Int32 := 64
def O_EXCL : Int32 := 128
def O_TRUNC : Int32 := 512
def O_APPEND : Int32 := 1024
def O_CLOEXEC : Int32 := 524288
def O_LARGEFILE : Int32 := 0
def SEEK_SET : Int32 := 0
def SEEK_CUR : Int32 := 1
def SEEK_END : Int32 := 2

/-- The file system, the descriptor table, `errno` and the OS-call oracles. The defaults of the oracle fields are
the regular-file model and serve the executable drivers; every goal quantifies over all worlds. -/
structure Fs where
  /-- the directory: a name and its file -/
  names : Array (Array UInt8 × Nat) := #[]
  /-- the files (their bytes) -/
  nodes : Array (Array UInt8) := #[]
  /-- the descriptor table: entry `i` is descriptor `i` -/
  fds : Array (Option OFile) := #[]
  errno : Int32 := 0
  /-- the number of OS calls so far: it numbers the entries of the oracles -/
  ncall : Nat := 0
  readChoice : Nat → ReadChoice := fun _ => .regular
  writeChoice : Nat → WriteChoice := fun _ => .regular
  lseekChoice : Nat → LseekChoice := fun _ => .regular
  openFail : Nat → Option Int32 := fun _ => none
  closeFail : Nat → Option Int32 := fun _ => none
  /-- the bytes that `bytes` read choices may still deliver -/
  budget : Nat := 0
  /-- the flags of the last successful `open` (observed by the drivers only) -/
  lastOflag : Int32 := 0
  deriving Inhabited

namespace Fs

/-- The descriptor `fd` if it is open. -/
def ofile? (w : Fs) (fd : Int32) : Option OFile :=
  if fd < 0 then none else (w.fds[fd.toNatClampNeg]?).join

/-- The lowest descriptor number from 3 on that is not open (0, 1, 2 are the standard streams, not files of the
model). -/
def lowestFd (w : Fs) : Nat :=
  go 3 (w.fds.size + 3)
where
  go (i : Nat) : Nat → Nat
    | 0 => i
    | k + 1 => if (w.fds[i]?).join.isSome then go (i + 1) k else i

def setFd (w : Fs) (i : Nat) (o : Option OFile) : Fs :=
  let fds := if i < w.fds.size then w.fds else w.fds ++ Array.replicate (i + 1 - w.fds.size) none
  { w with fds := fds.set! i o }

def lookup (w : Fs) (path : Array UInt8) : Option Nat :=
  (w.names.find? (·.1 == path)).map (·.2)

/-- Regular `open(path, oflag, 0666)`: the result and the new world. -/
def openReg (w : Fs) (path : Array UInt8) (oflag : Int32) : Int32 × Fs :=
  let wr := oflag &&& 3 == O_WRONLY
  let creat := oflag &&& O_CREAT != 0
  let excl := oflag &&& O_EXCL != 0
  let trunc := oflag &&& O_TRUNC != 0
  let app := oflag &&& O_APPEND != 0
  match w.lookup path with
  | some n =>
    if creat && excl then (-1, { w with errno := EEXIST }) else
    let w := if trunc && wr then { w with nodes := w.nodes.set! n #[] } else w
    let fd := w.lowestFd
    (Int32.ofNat fd, { w.setFd fd (some ⟨n, 0, !wr, wr, app⟩) with lastOflag := oflag })
  | none =>
    if !creat then (-1, { w with errno := ENOENT }) else
    let n := w.nodes.size
    let w := { w with nodes := w.nodes.push #[], names := w.names.push (path, n) }
    let fd := w.lowestFd
    (Int32.ofNat fd, { w.setFd fd (some ⟨n, 0, !wr, wr, app⟩) with lastOflag := oflag })

/-- Regular `read(fd, buf, n)`: the bytes read (or `-1`) and the new world. -/
def readReg (w : Fs) (fd : Int32) (n : UInt64) : Int64 × Array UInt8 × Fs :=
  match w.ofile? fd with
  | some o =>
    if !o.rd then (-1, #[], { w with errno := EBADF }) else
    let data := w.nodes[o.node]?.getD #[]
    let k := min n.toNat (data.size - o.pos)
    let bs := data.extract o.pos (o.pos + k)
    (Int64.ofNat k, bs, w.setFd fd.toNatClampNeg (some { o with pos := o.pos + k }))
  | none => (-1, #[], { w with errno := EBADF })

/-- `data` with `bs` written at `pos` (a gap is filled with zero bytes). -/
def writeAt (data bs : Array UInt8) (pos : Nat) : Array UInt8 :=
  let data := if data.size < pos then data ++ Array.replicate (pos - data.size) 0 else data
  let pre := data.extract 0 pos
  let post := data.extract (pos + bs.size) data.size
  pre ++ bs ++ post

/-- Regular `write(fd, buf, len)` of the bytes `bs`. -/
def writeReg (w : Fs) (fd : Int32) (bs : Array UInt8) : Int64 × Fs :=
  match w.ofile? fd with
  | some o =>
    if !o.wr then (-1, { w with errno := EBADF }) else
    let data := w.nodes[o.node]?.getD #[]
    let pos := if o.append then data.size else o.pos
    let w := { w with nodes := w.nodes.set! o.node (writeAt data bs pos) }
    (Int64.ofNat bs.size, w.setFd fd.toNatClampNeg (some { o with pos := pos + bs.size }))
  | none => (-1, { w with errno := EBADF })

/-- Regular `lseek(fd, off, whence)`. -/
def lseekReg (w : Fs) (fd : Int32) (off : Int64) (whence : Int32) : Int64 × Fs :=
  match w.ofile? fd with
  | some o =>
    let size := (w.nodes[o.node]?.getD #[]).size
    let base : Option Int :=
      if whence == SEEK_SET then some 0 else if whence == SEEK_CUR then some o.pos
      else if whence == SEEK_END then some size else none
    match base with
    | none => (-1, { w with errno := EINVAL })
    | some b =>
      let np := b + off.toInt
      if np < 0 then (-1, { w with errno := EINVAL })
      else if np ≥ 2 ^ 63 then (-1, { w with errno := EOVERFLOW })
      else (Int64.ofInt np, w.setFd fd.toNatClampNeg (some { o with pos := np.toNat }))
  | none => (-1, { w with errno := EBADF })

/-- Regular `close(fd)`. -/
def closeReg (w : Fs) (fd : Int32) : Int32 × Fs :=
  match w.ofile? fd with
  | some _ => (0, w.setFd fd.toNatClampNeg none)
  | none => (-1, { w with errno := EBADF })

/-- `errno` of a failure chosen by an oracle: `0` reads as `EIO` (a failed call sets a nonzero `errno`). -/
def failErrno (e : Int32) : Int32 := if e == 0 then EIO else e

def tick (w : Fs) : Fs := { w with ncall := w.ncall + 1 }

/-- `open` call: the oracle, then the regular model. -/
def openCall (w : Fs) (path : Array UInt8) (oflag : Int32) : Int32 × Fs :=
  let n := w.ncall
  let w := w.tick
  match w.openFail n with
  | some e => (-1, { w with errno := failErrno e })
  | none => w.openReg path oflag

/-- `read` call. -/
def readCall (w : Fs) (fd : Int32) (len : UInt64) : Int64 × Array UInt8 × Fs :=
  let n := w.ncall
  let w := w.tick
  match w.readChoice n with
  | .regular => w.readReg fd len
  | .fail e => (-1, #[], { w with errno := failErrno e })
  | .short k => w.readReg fd (min len (UInt64.ofNat k))
  | .bytes bs =>
    let k := min (min bs.size len.toNat) w.budget
    (Int64.ofNat k, bs.extract 0 k, { w with budget := w.budget - k })

/-- `write` call of the bytes `bs`. -/
def writeCall (w : Fs) (fd : Int32) (bs : Array UInt8) : Int64 × Fs :=
  let n := w.ncall
  let w := w.tick
  match w.writeChoice n with
  | .regular => w.writeReg fd bs
  | .fail e => (-1, { w with errno := failErrno e })
  | .count k => w.writeReg fd (bs.extract 0 k)

/-- `lseek` call. -/
def lseekCall (w : Fs) (fd : Int32) (off : Int64) (whence : Int32) : Int64 × Fs :=
  let n := w.ncall
  let w := w.tick
  match w.lseekChoice n with
  | .regular => w.lseekReg fd off whence
  | .fail e => (-1, { w with errno := failErrno e })
  | .value v => (v, w)

/-- `close` call. -/
def closeCall (w : Fs) (fd : Int32) : Int32 × Fs :=
  let n := w.ncall
  let w := w.tick
  let (r, w) := w.closeReg fd
  match w.closeFail n with
  | some e => if r == 0 then (-1, { w with errno := failErrno e }) else (r, w)
  | none => (r, w)

end Fs

end C
