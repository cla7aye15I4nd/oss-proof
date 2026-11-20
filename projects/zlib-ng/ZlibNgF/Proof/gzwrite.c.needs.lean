import ZlibNgF.Proof.«gzlib.c.mode»

/-!
# What the write side needs of the deflate calls (`ZlibNgF`)

`gzwrite.c` keeps a deflate stream between calls whose buffers are the file's own (`GzWBuf`): `next_in` inside `in`,
`next_out + avail_out` at the end of `out`, `x.next` before `next_out`. `DeflateParams.DeflateOk` (the field of
`DeflateReach.DPending`) says that `deflate` keeps the invariant and `DSide` and writes only the output range, but
not where it leaves the four buffer fields, nor that the loops of `gz_comp` and `gzsetparams` end. `DeflateGz`
lists these facts about the translated deflate calls; they are obligations of the deflate side, proved about the
translated C code in `deflate.c.gzneeds` (`deflateGz`).

* `init`: `deflateInit2_` leaves the four buffer fields, and when it fails also the `state` field, with the
  allocator fields ready for another call (`gz_write_init` keeps `avail_in`; a failed call is retried by the next
  write).
* `reset`: `deflateReset` leaves the four buffer fields and the `state` field (`gz_comp` after `Z_FINISH`).
* `io`: `deflate` and `deflateParams` move `next_in` / `next_out` by the bytes they consume and produce (`BufAdv`).
* `done`: with a flush other than `Z_FINISH`, a `deflate` that does not return `Z_STREAM_ERROR` consumed all its
  input or filled the output (`zlib.h`: "if deflate returns with avail_out == 0, this function must be called
  again"); after the loop of `gz_comp`, which stops when no output was produced, the input is consumed, so
  `gz_write` can point `next_in` back at `in` (patch 0014).
* `keep` (`DKeep`): every call keeps the saved pointers of the blocks other than the stream's state block (the gz
  buffers are an aligned block whose saved pointer `zng_free_aligned` reads), `DFreshBlocks`, and registers no
  `gz_header`; a successful `deflateInit2_` puts the state into a fresh block.
* `prog`: a potential `ψ flush` of the deflate state (at most `2^48`) that bounds the output still owed for that flush
  without further input: a call lowers it by the bytes it produces, may raise it by at most `G ≤ 2^28` per input byte
  consumed, plus 5 when it fills the output (`CallOk`; 0 for `deflateParams`). These facts are asked only of
  streams with no `gz_header` registered (`gz*` never calls `deflateSetHeader`): the header bytes still owed live in
  the caller's `gz_header`, which no function of the state can bound. With the gz buffer of `8 ≤ S ≤ 2^30`
  bytes, the loop of `gz_comp` ends by `(2^31 + 2^30) avail_in + 3 ψ + 2 (S - avail_out')` (`avail_out'` is `S` when
  `avail_out` is 0), below `2^64` even for `avail_in < 2^32`; that of `gzsetparams` by `2^50 reset + 2 ψ + [avail_out
  = 0]`.
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

/-- The facts of a call of the deflate stream `s` from `h` to `h'`: the buffer fields move, and the potential `ψ` of
the state drops by at least the bytes produced, less `G` per input byte consumed and `K` when the call fills the
output. -/
def CallOk (ψ : DeflateState → Nat) (G K : Nat) (h h' : Heap) (s : StreamPtr) : Prop :=
  ∀ z, StreamAt h s z → ∃ z', StreamAt h' s z' ∧ BufAdv z z' ∧
    ∀ b st st', DStateOf h s b st → DStateOf h' s b st' →
      ψ st' + (z.avail_out.toNat - z'.avail_out.toNat) ≤
        ψ st + G * (z.avail_in.toNat - z'.avail_in.toNat) + (if z'.avail_out = 0 then K else 0)

/-- What a deflate call keeps besides its stream: the saved pointers of every block other than the stream's state
block already handed out, `DFreshBlocks`, and no `gz_header` registered that was not registered before. -/
def DKeep (h h' : Heap) (s : StreamPtr) : Prop :=
  (∀ c, c < h.nextBlk → (∀ z, StreamAt h s z → z.state ≠ some c) → h'.savedPtrs c = h.savedPtrs c) ∧
  (DFreshBlocks h → DFreshBlocks h') ∧
  (∀ hp, DRegisteredHeader h' s hp → hp = none ∨ DRegisteredHeader h s hp)

/-- **The obligations of the deflate side** that the write side uses (see the module comment). -/
def DeflateGz : Prop :=
  -- `deflateInit2_`
  (∀ (h h' : Heap) (s : StreamPtr) (level method wb ml strat : Int32) (version : BPtr) (size r : Int32) (z : ZStream),
    StreamAt h s z → DInitReady h s → DFreshBlocks h →
    C.run (deflateInit2_ s level method wb ml strat version size) h = .ok (r, h') →
    ∃ z', StreamAt h' s z' ∧ z'.next_in = z.next_in ∧ z'.avail_in = z.avail_in ∧ z'.next_out = z.next_out ∧
      z'.avail_out = z.avail_out ∧
      (r ≠ Z_OK → z'.state = z.state ∧ (z'.zalloc = .null ∨ z'.zalloc = .zcalloc) ∧
        (z'.zfree = .null ∨ z'.zfree = .zcfree)) ∧ DKeep h h' s ∧
      (r = Z_OK → ∃ sb, z'.state = some sb ∧ h.nextBlk ≤ sb)) ∧
  -- `deflateReset`
  (∀ (h h' : Heap) (s : StreamPtr) (r : Int32) (z : ZStream), DInv h s → StreamAt h s z →
    C.run (deflateReset s) h = .ok (r, h') → ∃ z', StreamAt h' s z' ∧ BufSame z z' ∧ DKeep h h' s) ∧
  ∃ (ψ : Int32 → DeflateState → Nat) (G : Nat), G ≤ 2 ^ 28 ∧
    -- the bound
    (∀ (h : Heap) (s : StreamPtr) (b : Nat) (st : DeflateState) (f : Int32), DInv h s → DRegisteredHeader h s none →
      DStateOf h s b st →
      ψ f st ≤ 2 ^ 48) ∧
    -- `deflate`
    (∀ (h h' : Heap) (s : StreamPtr) (flush r : Int32), DInv h s → DSide h s → CrcGlobals h → DStreamIO h s →
      DRegisteredHeader h s none →
      C.run (deflate s flush) h = .ok (r, h') →
      CallOk (ψ flush) G 5 h h' s ∧ DKeep h h' s ∧ (flush ≠ Z_FINISH → r ≠ Z_STREAM_ERROR →
        ∀ z', StreamAt h' s z' → z'.avail_in = 0 ∨ z'.avail_out = 0)) ∧
    -- `deflateParams`
    (∀ (h h' : Heap) (s : StreamPtr) (level strategy r : Int32), DInv h s → DSide h s → CrcGlobals h →
      DRegisteredHeader h s none →
      DStreamIO h s → C.run (deflateParams s level strategy) h = .ok (r, h') → CallOk (ψ Z_BLOCK) G 0 h h' s ∧ DKeep h h' s)

end ZlibNgF.Proof.GzWriteNeeds
