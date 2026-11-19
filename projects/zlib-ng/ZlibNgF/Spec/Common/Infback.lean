import ZlibNgF.Spec.Common.Inflate
import ZlibNgF.ZlibNg.«infback.c»

/-!
# Call-back decoder specification vocabulary (`ZlibNgF`)

The streams that `inflateBack` and `inflateBackEnd` accept, and what the goals assume of the caller's call-backs. No
`Goal.*` definitions live here; the goals are in `ZlibNgF.Spec.Safety.Infback`.

**Reachable call-back streams** (`BackReachable h s w n`): made by a successful `inflateBackInit_` with the window
`w` of `n = 2^windowBits` writable bytes, then changed only by `inflateBack` calls whose call-backs are well behaved
(`BackCallPre`) and by the caller, who may change the four buffer fields of the `z_stream` and any memory the library
does not own, keeps the window allocated with its size, and does not free or write the library's block
(`BackCallerStep`).

**Well-behaved call-backs** (`BackCallbacks`). `zlib.h` says what `in()` and `out()` do; the goals state the part of
it that the safety of `inflateBack` needs, through an invariant `I h p m t` that the caller chooses: `(p, m)` is the
input chunk that `in()` handed out last (or the first chunk of `next_in` / `avail_in`), `t` how many more input bytes
`in()` will hand out in all.

* While `I` holds, a non-empty chunk is readable, does not overlap the window and is not inside the library's block
  (`chunk`). `zlib.h` asks that the input stays unchanged until the next `in()` call; the goals need it readable.
* `I` survives what the library itself does between call-back calls: changes of the stream record, of the library's
  block and of the window bytes (`stable`).
* `in()` returns, hands out at most `t` bytes, and leaves `I` true of its new chunk; `out()` (called on the window,
  with at most `n` bytes) returns and leaves `I` true of the current chunk. Neither frees or writes the library's
  block or the stream record, nor frees the window or changes its size (`BackKeep`). `zlib.h` forbids them to change
  the window's contents; the goals do not need that.
* The descriptors are the ones the call passes.

The bound `t` is the termination premise: one `inflateBack` call is offered fewer than `2^48` input bytes in all, the
first chunk included (`BackCallPre`); with an endless input `inflateBack` does not return in C either.
-/

set_option autoImplicit false

namespace ZlibNgF.Spec
open C

/-- What a call-back keeps, for stream `i` with the library's block `b` and the window `w` of `n` bytes: the stream
record, the bytes and typed objects of block `b`, the window's block (alive, same size), the origin addresses, and
no block is reused. -/
def BackKeep (h h' : Heap) (i b : Nat) (w : BPtr) : Prop :=
  h'.streams i = h.streams i ∧ h'.bytes b = h.bytes b ∧ h'.istates b = h.istates b ∧ h'.iallocs b = h.iallocs b ∧
  (∀ wb off d, w = .ref (.heap wb) off → h.bytes wb = some d → ∃ d', h'.bytes wb = some d' ∧ d'.size = d.size) ∧
  h'.baseAddr = h.baseAddr ∧ h.nextBlk ≤ h'.nextBlk

/-- The call-backs of an `inflateBack` call on stream `i` (library block `b`, window `w` of `n` bytes) with the
descriptors `inDesc` / `outDesc` are well behaved for the invariant `I` (see the module comment). -/
structure BackCallbacks (i b : Nat) (w : BPtr) (n : Nat) (inCb : ZlibNg.Infback.InCb) (inDesc : BPtr)
    (outCb : ZlibNg.Infback.OutCb) (outDesc : BPtr) (I : Heap → BPtr → Nat → Nat → Prop) : Prop where
  chunk : ∀ h p m t, I h p m t → m ≠ 0 → ReadSlice h p m ∧ Disjoint p m w n ∧ NotInBlock b p
  stable : ∀ h h' p m t, I h p m t → Frame h h' [i] [b] [] [(w, n)] → h'.nextBlk = h.nextBlk → I h' p m t
  input : ∀ h cur p m t, I h p m t →
    ∃ k q h', inCb inDesc cur h = .ok ((k, q), h') ∧ k.toNat ≤ t ∧ I h' q k.toNat (t - k.toNat) ∧
      BackKeep h h' i b w
  output : ∀ h len p m t, len.toNat ≤ n → I h p m t →
    ∃ r h', outCb outDesc w len h = .ok (r, h') ∧ I h' p m t ∧ BackKeep h h' i b w

/-- The premises of one `inflateBack` call on stream `s` with window `w` of `n` bytes: the call-backs are well behaved
for `I`, which holds of the first chunk (`next_in` with `avail_in` bytes, or nothing when `next_in` is `NULL`) with
fewer than `2^48` input bytes in all. -/
def BackCallPre (h : Heap) (s : StreamPtr) (w : BPtr) (n : Nat) (inCb : ZlibNg.Infback.InCb) (inDesc : BPtr)
    (outCb : ZlibNg.Infback.OutCb) (outDesc : BPtr) (I : Heap → BPtr → Nat → Nat → Prop) : Prop :=
  ∃ i z b t, s = some i ∧ h.streams i = some z ∧ z.state = some b ∧
    BackCallbacks i b w n inCb inDesc outCb outDesc I ∧
    I h z.next_in (if z.next_in = .null then 0 else z.avail_in.toNat) t ∧
    (if z.next_in = .null then 0 else z.avail_in.toNat) + t < 2 ^ 48

/-- The caller's changes between calls on a call-back stream: those of `CallerStep` (only the four buffer fields of
the `z_stream` change; the library's block stays), and the window stays allocated with its size. -/
def BackCallerStep (h h' : Heap) (s : StreamPtr) (w : BPtr) : Prop :=
  CallerStep h h' s ∧
  ∀ wb off d, w = .ref (.heap wb) off → h.bytes wb = some d → ∃ d', h'.bytes wb = some d' ∧ d'.size = d.size

/-- The call-back streams reachable through `zlib.h` (see the module comment), with their window and its size. -/
inductive BackReachable : Heap → StreamPtr → BPtr → Nat → Prop where
  | init (h h' : Heap) (s : StreamPtr) (windowBits : Int32) (w version : BPtr) (size : Int32) :
      InitReady h s → VersionOk h version → WriteSlice h w (2 ^ windowBits.toInt.toNat) →
      C.run (ZlibNg.Infback.inflateBackInit_ s windowBits w version size) h = .ok (ZlibNg.Inflate.Z_OK, h') →
      BackReachable h' s w (2 ^ windowBits.toInt.toNat)
  | back (h h' : Heap) (s : StreamPtr) (w : BPtr) (n : Nat) (inCb : ZlibNg.Infback.InCb) (inDesc : BPtr)
      (outCb : ZlibNg.Infback.OutCb) (outDesc : BPtr) (I : Heap → BPtr → Nat → Nat → Prop) (r : Int32) :
      BackReachable h s w n → BackCallPre h s w n inCb inDesc outCb outDesc I →
      C.run (ZlibNg.Infback.inflateBack s inCb inDesc outCb outDesc) h = .ok (r, h') →
      BackReachable h' s w n
  | caller (h h' : Heap) (s : StreamPtr) (w : BPtr) (n : Nat) :
      BackReachable h s w n → BackCallerStep h h' s w → BackReachable h' s w n

/-- A stream that `inflateBack` and `inflateBackEnd` accept: `Z_NULL`, a live `z_stream` with no state, or a
reachable call-back stream. -/
def BackHandle (h : Heap) (s : StreamPtr) : Prop :=
  s = none ∨ (∃ z, StreamAt h s z ∧ z.state = none) ∨ ∃ w n, BackReachable h s w n

end ZlibNgF.Spec
