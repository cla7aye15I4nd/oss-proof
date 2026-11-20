import ZlibNgF.Proof.«gzlib.c.mode»

/-!
# What the write side needs of the deflate calls (`ZlibNgF`)

`gzwrite.c` keeps a deflate stream between calls whose buffers are the file's own (`GzWBuf`): `next_in` inside `in`,
`next_out + avail_out` at the end of `out`, `x.next` before `next_out`. `DeflateParams.DeflateOk` (the field of
`DeflateReach.DPending`) says that `deflate` keeps the invariant and `DSide` and writes only the output range, but
not where it leaves the four buffer fields, nor that the loops of `gz_comp` and `gzsetparams` end. `DeflateGz`
lists these facts about the translated deflate calls; they are obligations of the deflate side, taken as a
hypothesis here (as `DPending`) until they are theorems.

* `init`: `deflateInit2_` leaves the four buffer fields, and when it fails also the `state` field, with the
  allocator fields ready for another call (`gz_write_init` keeps `avail_in`; a failed call is retried by the next
  write).
* `reset`: `deflateReset` leaves the four buffer fields and the `state` field (`gz_comp` after `Z_FINISH`).
* `io`: `deflate` and `deflateParams` move `next_in` / `next_out` by the bytes they consume and produce (`BufAdv`).
* `done`: with a flush other than `Z_FINISH`, a `deflate` that does not return `Z_STREAM_ERROR` consumed all its
  input or filled the output (`zlib.h`: "if deflate returns with avail_out == 0, this function must be called
  again"); after the loop of `gz_comp`, which stops when no output was produced, the input is consumed, so
  `gz_write` can point `next_in` back at `in` (patch 0014).
* `prog`: a measure `μ` of the deflate state, below `2^32`, that a call consuming no input does not increase and a
  call producing output while consuming no input decreases: the loops of `gz_comp` (`do ... while (have)`) and of
  `gzsetparams` end within the model's fuel.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.GzWriteNeeds
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInv
open ZlibNgF.Proof.DeflateSide (DSide)

/-- `p'` is `p` advanced by `k` bytes (`NULL` stays, and only by 0). -/
def Adv (p p' : BPtr) (k : Nat) : Prop :=
  match p with
  | .null => k = 0 ∧ p' = .null
  | .ref r o => p' = .ref r (o + k)

/-- The buffer fields move by the input consumed and the output produced; the `state` field stays. -/
def BufAdv (z z' : ZStream) : Prop :=
  z'.avail_in ≤ z.avail_in ∧ z'.avail_out ≤ z.avail_out ∧
  Adv z.next_in z'.next_in (z.avail_in.toNat - z'.avail_in.toNat) ∧
  Adv z.next_out z'.next_out (z.avail_out.toNat - z'.avail_out.toNat) ∧ z'.state = z.state

/-- The four buffer fields and the `state` field agree. -/
def BufSame (z z' : ZStream) : Prop :=
  z'.next_in = z.next_in ∧ z'.avail_in = z.avail_in ∧ z'.next_out = z.next_out ∧ z'.avail_out = z.avail_out ∧
    z'.state = z.state

/-- The measure `μ` of the state of `s` in `h'` is at most (`strict`: below) that in `h`. -/
def MuLe (μ : DeflateState → Nat) (h h' : Heap) (s : StreamPtr) (strict : Bool) : Prop :=
  ∀ b st st', DStateOf h s b st → DStateOf h' s b st' → if strict then μ st' < μ st else μ st' ≤ μ st

/-- The facts of a call `m` of the deflate stream `s` on `h` that ends in `r`, `h'`: the buffer fields move, and
consuming no input it does not increase `μ`, decreasing it when it produced output. -/
def CallOk (μ : DeflateState → Nat) (h h' : Heap) (s : StreamPtr) : Prop :=
  ∀ z, StreamAt h s z → ∃ z', StreamAt h' s z' ∧ BufAdv z z' ∧
    (z'.avail_in = z.avail_in → MuLe μ h h' s (decide (z'.avail_out < z.avail_out)))

/-- **The obligations of the deflate side** that the write side uses (see the module comment). -/
def DeflateGz : Prop :=
  -- `deflateInit2_`
  (∀ (h h' : Heap) (s : StreamPtr) (level method wb ml strat : Int32) (version : BPtr) (size r : Int32) (z : ZStream),
    StreamAt h s z → DInitReady h s → DFreshBlocks h →
    C.run (deflateInit2_ s level method wb ml strat version size) h = .ok (r, h') →
    ∃ z', StreamAt h' s z' ∧ z'.next_in = z.next_in ∧ z'.avail_in = z.avail_in ∧ z'.next_out = z.next_out ∧
      z'.avail_out = z.avail_out ∧
      (r ≠ Z_OK → z'.state = z.state ∧ (z'.zalloc = .null ∨ z'.zalloc = .zcalloc) ∧
        (z'.zfree = .null ∨ z'.zfree = .zcfree))) ∧
  -- `deflateReset`
  (∀ (h h' : Heap) (s : StreamPtr) (r : Int32) (z : ZStream), DInv h s → StreamAt h s z →
    C.run (deflateReset s) h = .ok (r, h') → ∃ z', StreamAt h' s z' ∧ BufSame z z') ∧
  ∃ μ : DeflateState → Nat,
    -- the bound
    (∀ (h : Heap) (s : StreamPtr) (b : Nat) (st : DeflateState), DInv h s → DStateOf h s b st → μ st < 2 ^ 32) ∧
    -- `deflate`
    (∀ (h h' : Heap) (s : StreamPtr) (flush r : Int32), DInv h s → DSide h s → CrcGlobals h → DStreamIO h s →
      C.run (deflate s flush) h = .ok (r, h') →
      CallOk μ h h' s ∧ (flush ≠ Z_FINISH → r ≠ Z_STREAM_ERROR →
        ∀ z', StreamAt h' s z' → z'.avail_in = 0 ∨ z'.avail_out = 0)) ∧
    -- `deflateParams`
    (∀ (h h' : Heap) (s : StreamPtr) (level strategy r : Int32), DInv h s → DSide h s → CrcGlobals h →
      DStreamIO h s → C.run (deflateParams s level strategy) h = .ok (r, h') → CallOk μ h h' s)

end ZlibNgF.Proof.GzWriteNeeds
