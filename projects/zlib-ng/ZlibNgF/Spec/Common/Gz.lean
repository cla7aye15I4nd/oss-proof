import ZlibNgF.Spec.Common.Deflate
import ZlibNgF.ZlibNg.«gzlib.c.gzclose»

/-!
# gz* specification vocabulary (`ZlibNgF`)

The files that the gz* functions accept, the well-formedness of the world and heap they run in, and the frame of a
call. No `Goal.*` definitions live here; the goals are in `ZlibNgF.Spec.Safety.Gz`.

A gz call runs in the gz monad (`Runtime/Gz.lean`): it takes a world (file system, OS-call oracles, `strerror` and
`vsnprintf` oracles, `gz_state` objects) and a heap. Every goal quantifies over all worlds and heaps that satisfy
`GzWF`: every allocation outcome (`Heap.allocOk`), every garbage value, every address (`Heap.baseAddr`), every result
of `open`, `read`, `write`, `lseek`, `close` the oracles allow, every `strerror` text and every `vsnprintf` result.

**The representation invariant.** A `gzFile` is accepted when it is `NULL` or *reachable* (`GzReachable`): returned
by a successful `gzopen` / `gzopen64` / `gzdopen`, then changed only by public gz calls on it with valid arguments
(`GzStep`, `gzclose*` excluded: they end it), and by the caller (`GzCallerStep`): the `gzgetc()` macro of `zlib.h`, and
any change that leaves the file's own objects alone (other gz files, other memory, the file system and the
oracles). A closed handle is not accepted (using it is the caller's undefined behaviour).

**Termination.** The read oracle delivers finitely many bytes (`Fs.budget` is a natural number) and regular files are
finite: every loop of the gz* functions is bounded by the input they read, the output they write and the skip they
were asked for. `GzWF` bounds these by `2^62` so that the model's loop fuel (`2^64` iterations) is never the limit.
An endless input (a pipe whose writer never stops) is outside the model; on it `gzread` may not return, as any reader
would not.

**Positions.** `x.pos` is kept below `2^63` by the code (patches 0004, 0016 and 0017), not by `GzWF`: the input bound
does not limit a writer's position, which grows with every write, failed ones included.

**`lseek` results.** POSIX `lseek` returns the resulting offset or `-1`. `GzWF` admits every oracle value of that
form: `-1` or not negative. Linux files with unsigned offsets (`/dev/mem`, `/proc/<pid>/mem`) can return offsets of
`2^63` and more as negative numbers, on which `gzoffset64`'s `offset - avail_in` can overflow; reads at those offsets
fail (deviations page).

**Narrowings** (deviations page): caller buffers lie outside the file's own blocks; the `vsnprintf` arguments of
`gzprintf` match the format (as `zlib.h` requires of a `printf` format).
-/

set_option autoImplicit false

namespace ZlibNgF.Spec
open C

/-- `C.run (m.run w) h = .ok ((r, w'), h')`: the gz computation `m` returns `r` and leaves `w'`, `h'`. -/
def GzRun {α : Type} (m : G α) (w : World) (h : Heap) (r : α) (w' : World) (h' : Heap) : Prop :=
  C.run (m.run w) h = .ok ((r, w'), h')

/-- `p` points to a NUL-terminated string. -/
def CStr (h : Heap) (p : BPtr) : Prop := ∃ n, CStringLen h p n

/-- The world and heap are those of a C program: CRC tables, no object in an unallocated block, objects below
`2^63` bytes, the `gz_state` objects in allocated blocks with their embedded `z_stream` alive, the inputs (the
read budget and the files) below `2^62` bytes, and every `lseek` value the oracle chooses `-1` or not negative. -/
def GzWF (w : World) (h : Heap) : Prop :=
  CrcGlobals h ∧ DFreshBlocks h ∧ ObjBound h ∧
  (∀ b, h.nextBlk ≤ b → w.gzs b = none) ∧
  (∀ b s, w.gz h b = some s → ∃ z, h.streams s.strm = some z) ∧
  w.fs.budget < 2 ^ 62 ∧ (∀ d ∈ w.fs.nodes, d.size < 2 ^ 62) ∧
  (∀ n v, w.fs.lseekChoice n = .value v → v = -1 ∨ 0 ≤ v)

/-- The heap blocks that belong to the open file `f` in `w`, `h`: the block of its `gz_state`, its `path`, its
`msg`, its buffer block and the block of its inflate or deflate state. -/
def GzOwned (w : World) (h : Heap) (f : GzPtr) : List Nat :=
  match f with
  | none => []
  | some b =>
    match w.gz h b with
    | none => []
    | some s =>
      let blk : Ival BPtr → List Nat := fun p => match p with | .val (.ref (.heap c) _) => [c] | _ => []
      let st : List Nat := match h.streams s.strm with | some z => (match z.state with | some c => [c] | none => []) | none => []
      [b] ++ blk s.path ++ blk s.msg ++ blk s.buffers ++ st

/-- The byte range `[p, p + n)` lies outside every block of the file `f`. -/
def OutsideGz (w : World) (h : Heap) (f : GzPtr) (p : BPtr) : Prop :=
  ∀ b ∈ GzOwned w h f, NotInBlock b p

/-- A caller buffer for `n` bytes the call reads: no bytes needed when `n = 0`. -/
def GzIn (w : World) (h : Heap) (f : GzPtr) (p : BPtr) (n : Nat) : Prop :=
  n = 0 ∨ (ReadSlice h p n ∧ OutsideGz w h f p)

/-- A caller buffer for `n` bytes the call writes. -/
def GzOut (w : World) (h : Heap) (f : GzPtr) (p : BPtr) (n : Nat) : Prop :=
  n = 0 ∨ (WriteSlice h p n ∧ OutsideGz w h f p)

/-- The caller's `gzgetc()` macro on `f` (`zlib.h`): with bytes available, `have--`, `pos++` (without overflow, else the
caller's program is undefined), and `next++`; nothing else changes. -/
def GzGetcMacro (w : World) (h : Heap) (w' : World) (h' : Heap) (f : GzPtr) : Prop :=
  ∃ b s nx, f = some b ∧ w.gz h b = some s ∧ s.«have» ≠ 0 ∧ s.pos.toInt + 1 < 2 ^ 63 ∧ s.next = .val nx ∧
    ∃ nx', C.run (Ptr.add nx 1) h = .ok (nx', h) ∧
      w' = { w with gzs := upd w.gzs b (some { s with «have» := s.«have» - 1, pos := s.pos + 1, next := .val nx' }) } ∧
      h' = h

/-- A change by the caller that leaves the objects of `f` alone: its `gz_state`, its blocks (`GzOwned`) and its
embedded `z_stream`; anything else (other memory, other gz files, the file system, the oracles) may change, the
heap stays well formed and blocks are never reused. -/
def GzKeeps (w : World) (h : Heap) (w' : World) (h' : Heap) (f : GzPtr) : Prop :=
  GzWF w' h' ∧ h.nextBlk ≤ h'.nextBlk ∧ h'.baseAddr = h.baseAddr ∧
  ∃ b s, f = some b ∧ w.gz h b = some s ∧ w'.gz h' b = some s ∧ h'.streams s.strm = h.streams s.strm ∧
    ∀ c ∈ GzOwned w h f, h'.bytes c = h.bytes c ∧ h'.istates c = h.istates c ∧ h'.iallocs c = h.iallocs c ∧
      h'.dstates c = h.dstates c ∧ h'.dallocs c = h.dallocs c ∧ h'.savedPtrs c = h.savedPtrs c

/-- A step of the caller (see the module comment). -/
def GzCallerStep (w : World) (h : Heap) (w' : World) (h' : Heap) (f : GzPtr) : Prop :=
  GzGetcMacro w h w' h' f ∨ GzKeeps w h w' h' f

open ZlibNg.Gz in
/-- One public gz call on `f` with valid arguments that returns (any result), `gzclose*` excluded. -/
def GzStep (w : World) (h : Heap) (w' : World) (h' : Heap) (f : GzPtr) : Prop :=
  (∃ n r, GzRun (gzbuffer f n) w h r w' h') ∨
  (∃ buf len r, (len.toInt32 ≥ 0 → GzOut w h f buf len.toNat) ∧ GzRun (gzread f buf len) w h r w' h') ∨
  (∃ buf size nitems r, (size.toNat * nitems.toNat < 2 ^ 64 → GzOut w h f buf (size.toNat * nitems.toNat)) ∧
    GzRun (gzfread buf size nitems f) w h r w' h') ∨
  (∃ r, GzRun (gzgetc f) w h r w' h') ∨
  (∃ r, GzRun (gzgetc_ f) w h r w' h') ∨
  (∃ c r, GzRun (gzungetc c f) w h r w' h') ∨
  (∃ buf len r, (len ≥ 1 → GzOut w h f buf len.toNatClampNeg ∨ buf = .null) ∧ GzRun (gzgets f buf len) w h r w' h') ∨
  (∃ r, GzRun (gzdirect f) w h r w' h') ∨
  (∃ buf len r, (len.toInt32 ≥ 0 → GzIn w h f buf len.toNat) ∧ GzRun (gzwrite f buf len) w h r w' h') ∨
  (∃ buf size nitems r, (size.toNat * nitems.toNat < 2 ^ 64 → GzIn w h f buf (size.toNat * nitems.toNat)) ∧
    GzRun (gzfwrite buf size nitems f) w h r w' h') ∨
  (∃ c r, GzRun (gzputc f c) w h r w' h') ∨
  (∃ s r, CStr h s ∧ OutsideGz w h f s ∧ GzRun (gzputs f s) w h r w' h') ∨
  (∃ fmt r, CStr h fmt ∧ GzRun (gzprintf f fmt) w h r w' h') ∨
  (∃ fmt r, CStr h fmt ∧ GzRun (gzvprintf f fmt) w h r w' h') ∨
  (∃ fl r, GzRun (gzflush f fl) w h r w' h') ∨
  (∃ l s r, GzRun (gzsetparams f l s) w h r w' h') ∨
  (∃ off wh r, GzRun (gzseek64 f off wh) w h r w' h') ∨
  (∃ off wh r, GzRun (gzseek f off wh) w h r w' h') ∨
  (∃ r, GzRun (gzrewind f) w h r w' h') ∨
  (∃ r, GzRun (gztell64 f) w h r w' h') ∨
  (∃ r, GzRun (gztell f) w h r w' h') ∨
  (∃ r, GzRun (gzoffset64 f) w h r w' h') ∨
  (∃ r, GzRun (gzoffset f) w h r w' h') ∨
  (∃ r, GzRun (gzeof f) w h r w' h') ∨
  (∃ e r, GzRun (gzerror f e) w h r w' h') ∨
  (∃ r, GzRun (gzclearerr f) w h r w' h')

open ZlibNg.Gz in
/-- The gz files reachable through `zlib.h` (see the module comment). -/
inductive GzReachable : World → Heap → GzPtr → Prop where
  | gzopen (w h w' h' : _) (path mode : BPtr) (f : GzPtr) :
      GzWF w h → CStr h path → CStr h mode → GzRun (gzopen path mode) w h f w' h' → f ≠ none →
      GzReachable w' h' f
  | gzopen64 (w h w' h' : _) (path mode : BPtr) (f : GzPtr) :
      GzWF w h → CStr h path → CStr h mode → GzRun (gzopen64 path mode) w h f w' h' → f ≠ none →
      GzReachable w' h' f
  | gzdopen (w h w' h' : _) (fd : Int32) (mode : BPtr) (f : GzPtr) :
      GzWF w h → CStr h mode → GzRun (gzdopen fd mode) w h f w' h' → f ≠ none → GzReachable w' h' f
  | step (w h w' h' : _) (f : GzPtr) : GzReachable w h f → GzStep w h w' h' f → GzReachable w' h' f
  | caller (w h w' h' : _) (f : GzPtr) : GzReachable w h f → GzCallerStep w h w' h' f → GzReachable w' h' f

/-- A file that every gz function accepts: `NULL` or reachable. -/
def GzHandle (w : World) (h : Heap) (f : GzPtr) : Prop := f = none ∨ GzReachable w h f

/-- What a gz call on `f` may change: the heap blocks of `f` and blocks it allocates (`DFrame` with `f`'s blocks as
the library's and `f`'s embedded stream), the caller ranges `writes`, `f`'s `gz_state`, and the file system; the
other `gz_state` objects stay. Static strings (`Heap.consts`) are only added, never changed: the string literals of
the gz* files and the texts of `strerror` are static data in C, which the model makes at their first use
(`Runtime/Gz.lean`). -/
def GzFrame (w : World) (h : Heap) (w' : World) (h' : Heap) (f : GzPtr) (writes : List (BPtr × Nat)) : Prop :=
  let strm : List Nat := match f with
    | some b => (match w.gz h b with | some s => [s.strm] | none => [])
    | none => []
  DFrame h { h' with consts := h.consts } strm (GzOwned w h f) [] writes ∧
  (∀ k a, h.consts k = some a → h'.consts k = some a) ∧
  ∀ b, f ≠ some b → b < h.nextBlk → w'.gzs b = w.gzs b

/-- After `gzclose*` of the reachable file `f`, nothing of it is left: its blocks are freed, its `gz_state` and
embedded `z_stream` are gone, and its descriptor is closed. -/
def GzReleased (w : World) (h : Heap) (w' : World) (h' : Heap) (f : GzPtr) : Prop :=
  ∀ b s, f = some b → w.gz h b = some s →
    (∀ c ∈ GzOwned w h f, h'.bytes c = none) ∧ w'.gzs b = none ∧ h'.streams s.strm = none ∧
    w'.fs.ofile? s.fd = none

end ZlibNgF.Spec
