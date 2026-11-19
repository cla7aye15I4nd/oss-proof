import ZlibNgF.Spec.Common.Types
import ZlibNgF.ZlibNg.«uncompr.c»

/-!
# Inflate specification vocabulary (`ZlibNgF`)

Caller buffers, the streams that the inflate functions accept, and the frame of what a call may change. No `Goal.*`
definitions live here; the goals are in `ZlibNgF.Spec.Safety.Inflate`.

**The representation invariant.** An inflate stream is accepted when it is *reachable*
(`InflateReachable`): made by a successful `inflateInit_` / `inflateInit2_` (or `inflateCopy`) and then changed only
by public inflate calls with valid arguments and by the caller, who may change the four buffer fields of the
`z_stream` (`next_in`, `avail_in`, `next_out`, `avail_out`) and any memory the library does not own (including every
field of a registered `gz_header`, as another stream sharing it does), but not the other `z_stream` fields or the
block of the stream's state, and a registered `gz_header` record stays allocated. This is the set of
states a C program can reach through `zlib.h` without breaking its rules. The proofs establish a concrete
invariant of the state record (decoding tables, window, bit buffer) that holds on every reachable stream; the goals
state the claim on reachable streams so that they do not depend on how that concrete invariant is written.

**Narrowings** (listed in the deviations page): the default allocator only (`zalloc` / `zfree` are `Z_NULL` at
`inflateInit*`, or already `zcalloc` / `zcfree`); caller buffers pairwise disjoint and outside the library's own
block; a `NULL` `next_in` only with `avail_in == 0` for `inflateSync`; `inflateGetDictionary` writes into a buffer of
at least 32768 bytes, the size `zlib.h` names as always enough; `inflateCopy` with distinct source and destination.
-/

set_option autoImplicit false

namespace ZlibNgF.Spec
open C

/-! ## Caller buffers -/

/-- `p` points to `n` readable bytes of a live object (`[off, off + n)` in bounds). -/
def ReadSlice (h : Heap) (p : BPtr) (n : Nat) : Prop :=
  ∃ r off data, p = .ref r off ∧ Space.get h r = some data ∧ off + n ≤ data.size

/-- `p` points to `n` writable bytes of a live heap block. -/
def WriteSlice (h : Heap) (p : BPtr) (n : Nat) : Prop :=
  ∃ b off data, p = .ref (.heap b) off ∧ h.bytes b = some data ∧ off + n ≤ data.size

/-- `NULL`, or `n` readable bytes. -/
def NullOrRead (h : Heap) (p : BPtr) (n : Nat) : Prop := p = .null ∨ ReadSlice h p n

/-- `NULL`, or `n` writable bytes. -/
def NullOrWrite (h : Heap) (p : BPtr) (n : Nat) : Prop := p = .null ∨ WriteSlice h p n

/-- The byte ranges `[p, p + n)` and `[q, q + m)` do not overlap (different objects, or disjoint offsets); a null
pointer overlaps nothing. -/
def Disjoint (p : BPtr) (n : Nat) (q : BPtr) (m : Nat) : Prop :=
  match p, q with
  | .ref r o, .ref s o' => r ≠ s ∨ o + n ≤ o' ∨ o' + m ≤ o
  | _, _ => True

/-- Every range of the list is disjoint from every other one. -/
def PairwiseDisjoint (rs : List (BPtr × Nat)) : Prop :=
  ∀ (i j : Nat) (a b : BPtr × Nat), i ≠ j → rs[i]? = some a → rs[j]? = some b → Disjoint a.1 a.2 b.1 b.2

/-- `p` does not point into heap block `b`. -/
def NotInBlock (b : Nat) (p : BPtr) : Prop := ∀ off, p ≠ .ref (.heap b) off

/-! ## Streams -/

/-- The `z_stream` that `s` points to. -/
def StreamAt (h : Heap) (s : StreamPtr) (z : ZStream) : Prop :=
  ∃ i, s = some i ∧ h.streams i = some z

/-- The state of the stream `s` is the typed object of heap block `b`. -/
def StateBlock (h : Heap) (s : StreamPtr) (b : Nat) : Prop :=
  ∃ z, StreamAt h s z ∧ z.state = some b

/-- The `gz_header` registered on the state of `s` by `inflateGetHeader` (`none`: no header). -/
def RegisteredHeader (h : Heap) (s : StreamPtr) (hp : HeaderPtr) : Prop :=
  ∃ b st, StateBlock h s b ∧ h.istate b = some st ∧ st.head = .val hp

/-- A `gz_header` the caller may register: `Z_NULL`, or a live record whose `extra`, `name` and `comment` are each
`Z_NULL` or a writable buffer of `extra_max`, `name_max`, `comm_max` bytes. -/
def HeaderOk (h : Heap) (hp : HeaderPtr) : Prop :=
  hp = none ∨ ∃ k g, hp = some k ∧ h.gzheaders k = some g ∧
    NullOrWrite h g.extra g.extra_max.toNat ∧ NullOrWrite h g.name g.name_max.toNat ∧
    NullOrWrite h g.comment g.comm_max.toNat

/-- The caller buffers of a header: its three buffers with their sizes (none for `Z_NULL`). -/
def headerRanges (h : Heap) (hp : HeaderPtr) : List (BPtr × Nat) :=
  match hp with
  | none => []
  | some k => match h.gzheaders k with
    | none => []
    | some g => [(g.extra, g.extra_max.toNat), (g.name, g.name_max.toNat), (g.comment, g.comm_max.toNat)]

/-- A stream ready for `inflateInit*`: `Z_NULL`, or a live `z_stream` whose `zalloc` / `zfree` are `Z_NULL` or the
library's defaults. -/
def InitReady (h : Heap) (s : StreamPtr) : Prop :=
  s = none ∨ ∃ z, StreamAt h s z ∧ (z.zalloc = .null ∨ z.zalloc = .zcalloc) ∧ (z.zfree = .null ∨ z.zfree = .zcfree)

/-- No typed object (`inflate_state`, `inflate_allocs`) lives in a block that the allocator has not handed out yet.
Every heap a C program reaches has this property (blocks are numbered in allocation order and never reused, and the
carve primitives place objects only into allocated blocks); it is a well-formedness condition of the heap model, not
a restriction of the C inputs. The functions that allocate the inflate state (`inflateInit*`, `inflateCopy`, and
`uncompress*` through `inflateInit`) need it: the carve of a fresh block faults if a stale object is recorded there. -/
def FreshBlocks (h : Heap) : Prop := ∀ b, h.nextBlk ≤ b → h.istates b = none ∧ h.iallocs b = none

/-- The `version` argument of `inflateInit_` / `inflateInit2_`: `NULL`, or a readable string (its first byte is
read). -/
def VersionOk (h : Heap) (version : BPtr) : Prop := NullOrRead h version 1

/-- The buffers of a stream are valid for a call that reads input and writes output: `next_in` is `NULL` or has
`avail_in` readable bytes, `next_out` is `NULL` or has `avail_out` writable bytes, and these two ranges and the
buffers of the registered header are pairwise disjoint and outside the library's block `b`. -/
def StreamIO (h : Heap) (s : StreamPtr) : Prop :=
  ∃ z b hp, StreamAt h s z ∧ z.state = some b ∧ RegisteredHeader h s hp ∧ HeaderOk h hp ∧
    NullOrRead h z.next_in z.avail_in.toNat ∧ NullOrWrite h z.next_out z.avail_out.toNat ∧
    PairwiseDisjoint ((z.next_in, z.avail_in.toNat) :: (z.next_out, z.avail_out.toNat) :: headerRanges h hp) ∧
    ∀ r ∈ (z.next_in, z.avail_in.toNat) :: (z.next_out, z.avail_out.toNat) :: headerRanges h hp, NotInBlock b r.1

/-- `inflateSync` also needs `next_in` to be non-null when `avail_in` is not zero (it searches the input). -/
def SyncInput (h : Heap) (s : StreamPtr) : Prop :=
  ∃ z, StreamAt h s z ∧ (z.next_in = .null → z.avail_in = 0)

/-- The caller's changes between library calls, seen from stream `s`: only the four buffer fields of the
`z_stream` change; the other fields, the library's block `b` (bytes and typed objects) and the origin addresses
stay; the registered header record stays allocated (any of its fields may change: the caller, or another stream
that shares the record, may write it; `StreamIO` checks its buffers at each `inflate` call); blocks are never
reused. -/
def CallerStep (h h' : Heap) (s : StreamPtr) : Prop :=
  ∃ i z z' b, s = some i ∧ h.streams i = some z ∧ h'.streams i = some z' ∧ z.state = some b ∧
    z' = { z with next_in := z'.next_in, avail_in := z'.avail_in, next_out := z'.next_out,
                  avail_out := z'.avail_out } ∧
    h'.bytes b = h.bytes b ∧ h'.istates b = h.istates b ∧ h'.iallocs b = h.iallocs b ∧
    (∀ k g, RegisteredHeader h s (some k) → h.gzheaders k = some g → ∃ g', h'.gzheaders k = some g') ∧
    h'.baseAddr = h.baseAddr ∧ h.nextBlk ≤ h'.nextBlk

/-- One public inflate call on stream `s` with valid arguments that returns (any result); `inflateEnd` is not a
step (it ends the stream). -/
def InflateStep (h h' : Heap) (s : StreamPtr) : Prop :=
  (∃ flush r, StreamIO h s ∧ C.run (ZlibNg.Inflate.inflate s flush) h = .ok (r, h')) ∨
  (∃ r, StreamIO h s ∧ SyncInput h s ∧ C.run (ZlibNg.Inflate.inflateSync s) h = .ok (r, h')) ∨
  (∃ r, C.run (ZlibNg.Inflate.inflateSyncPoint s) h = .ok (r, h')) ∨
  (∃ d n r, NullOrRead h d n.toNat ∧ (∀ b, StateBlock h s b → NotInBlock b d) ∧
    C.run (ZlibNg.Inflate.inflateSetDictionary s d n) h = .ok (r, h')) ∨
  (∃ d hasLen r, NullOrWrite h d 32768 ∧ (∀ b, StateBlock h s b → NotInBlock b d) ∧
    C.run (ZlibNg.Inflate.inflateGetDictionary s d hasLen) h = .ok (r, h')) ∨
  (∃ hp r, HeaderOk h hp ∧ C.run (ZlibNg.Inflate.inflateGetHeader s hp) h = .ok (r, h')) ∨
  (∃ bits value r, C.run (ZlibNg.Inflate.inflatePrime s bits value) h = .ok (r, h')) ∨
  (∃ r, C.run (ZlibNg.Inflate.inflateReset s) h = .ok (r, h')) ∨
  (∃ r, C.run (ZlibNg.Inflate.inflateResetKeep s) h = .ok (r, h')) ∨
  (∃ w r, C.run (ZlibNg.Inflate.inflateReset2 s w) h = .ok (r, h')) ∨
  (∃ c r, C.run (ZlibNg.Inflate.inflateValidate s c) h = .ok (r, h')) ∨
  (∃ v r, C.run (ZlibNg.Inflate.inflateUndermine s v) h = .ok (r, h')) ∨
  (∃ r, C.run (ZlibNg.Inflate.inflateMark s) h = .ok (r, h')) ∨
  (∃ r, C.run (ZlibNg.Inflate.inflateCodesUsed s) h = .ok (r, h')) ∨
  (∃ dst r, InitReady h dst ∧ dst ≠ s ∧ C.run (ZlibNg.Inflate.inflateCopy dst s) h = .ok (r, h'))

/-- The inflate streams reachable through `zlib.h` (see the module comment). -/
inductive InflateReachable : Heap → StreamPtr → Prop where
  | init (h h' : Heap) (s : StreamPtr) (version : BPtr) (size : Int32) :
      InitReady h s → VersionOk h version →
      C.run (ZlibNg.Inflate.inflateInit_ s version size) h = .ok (ZlibNg.Inflate.Z_OK, h') →
      InflateReachable h' s
  | init2 (h h' : Heap) (s : StreamPtr) (windowBits : Int32) (version : BPtr) (size : Int32) :
      InitReady h s → VersionOk h version →
      C.run (ZlibNg.Inflate.inflateInit2_ s windowBits version size) h = .ok (ZlibNg.Inflate.Z_OK, h') →
      InflateReachable h' s
  | copy (h h' : Heap) (src dst : StreamPtr) :
      InflateReachable h src → InitReady h dst → dst ≠ src →
      C.run (ZlibNg.Inflate.inflateCopy dst src) h = .ok (ZlibNg.Inflate.Z_OK, h') →
      InflateReachable h' dst
  | step (h h' : Heap) (s : StreamPtr) : InflateReachable h s → InflateStep h h' s → InflateReachable h' s
  | caller (h h' : Heap) (s : StreamPtr) : InflateReachable h s → CallerStep h h' s → InflateReachable h' s

/-- A stream that any inflate function accepts: `Z_NULL`, a live `z_stream` with no state (never initialised with
the zero `state` field, or after `inflateEnd`), or a reachable stream. -/
def InflateHandle (h : Heap) (s : StreamPtr) : Prop :=
  s = none ∨ (∃ z, StreamAt h s z ∧ z.state = none) ∨ InflateReachable h s

/-! ## Frames -/

/-- From `h` to `h'` only these changed: the `z_stream` records of `streams`, the heap blocks (bytes and typed
objects) in `lib`, the `gz_header` records of `headers`, the bytes in the ranges `writes` (each block keeps its
size), and blocks numbered from `h.nextBlk` on (fresh blocks of the call); static data and origin addresses stay. -/
def Frame (h h' : Heap) (streams : List Nat) (lib : List Nat) (headers : List Nat) (writes : List (BPtr × Nat)) :
    Prop :=
  (∀ i, i ∉ streams → h'.streams i = h.streams i) ∧
  (∀ k, k ∉ headers → h'.gzheaders k = h.gzheaders k) ∧
  (∀ b, b < h.nextBlk → b ∉ lib → h'.istates b = h.istates b ∧ h'.iallocs b = h.iallocs b) ∧
  (∀ b, b < h.nextBlk → b ∉ lib → ∀ data, h.bytes b = some data →
    ∃ data', h'.bytes b = some data' ∧ data'.size = data.size ∧
      ∀ j, j < data.size → (∀ w ∈ writes, ∀ off, w.1 = .ref (.heap b) off → j < off ∨ off + w.2 ≤ j) →
        data'[j]! = data[j]!) ∧
  (∀ b, b < h.nextBlk → b ∉ lib → h.bytes b = none → h'.bytes b = none) ∧
  h'.consts = h.consts ∧ h'.crcTable = h.crcTable ∧ h'.x2nTable = h.x2nTable ∧ h'.baseAddr = h.baseAddr ∧
  h.nextBlk ≤ h'.nextBlk

/-- The stream number of `s` (empty for `Z_NULL`). -/
def streamIds (s : StreamPtr) : List Nat := match s with | none => [] | some i => [i]

/-- The state block of `s` in `h`, if any. -/
def stateIds (h : Heap) (s : StreamPtr) : List Nat :=
  match s with
  | none => []
  | some i => match h.streams i with
    | some z => match z.state with | some b => [b] | none => []
    | none => []

/-- The registered header of `s` in `h`, if any. -/
def headerIds (h : Heap) (s : StreamPtr) : List Nat :=
  match stateIds h s with
  | [b] => match h.istate b with
    | some st => match st.head with | .val (some k) => [k] | _ => []
    | none => []
  | _ => []

/-- The caller ranges an `inflate` call may write: the output buffer and the registered header's buffers. -/
def outputRanges (h : Heap) (s : StreamPtr) : List (BPtr × Nat) :=
  match s with
  | none => []
  | some i => match h.streams i with
    | some z => (z.next_out, z.avail_out.toNat) ::
        (match headerIds h s with | [k] => headerRanges h (some k) | _ => [])
    | none => []

end ZlibNgF.Spec
