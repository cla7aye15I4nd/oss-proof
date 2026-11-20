import ZlibNgF.Spec.Safety.Gz
import ZlibNgF.Proof.«inflate.c.invariant»
import ZlibNgF.Proof.«deflate.c.invariant»
import ZlibNgF.Proof.«public-deflate-init»

/-!
# The structural invariant of an open gz file (`ZlibNgF`)

`GzInv w h f`: the `gz_state` of the open file `f` is live and its fields are those that `gz_open` and the public gz
calls leave between two calls (`gzlib.c`, `gzread.c`, `gzwrite.c` with patches 0004, 0014-0017). The clauses are
grouped in small structures (`GzPos`, `GzBufs`, `GzRead`, `GzWrite`, `GzMsg`) behind the interface lemmas at the end,
so that a proof about one function opens only the clauses it needs.

* the mode is `GZ_READ` or `GZ_WRITE` (`gz_open` turns `GZ_APPEND` into `GZ_WRITE`);
* `path` is an owned heap string (`malloc` in `gz_open`), `msg` is `NULL` or an owned heap block, and `NULL` when
  `err` is `Z_MEM_ERROR` (`gz_error` does not allocate for that error and does not free on it);
* the embedded `z_stream` is an entry of `Heap.streams`;
* `want` is in `[8, 2^30]` (`gzbuffer`, `GZBUFSIZE`); `size` is 0 (no buffers yet) or `want`, and then the buffers
  are one live block (from `zng_alloc_aligned`, with its saved pointer), `in` at its start and `out` after the `in` part: `want` and `2 * want` bytes when reading,
  `2 * want` and `want` (none when `direct`) when writing (`gz_buffer_alloc`);
* positions: `skip ≥ 0` and `pos + skip ≤ GZ_OFF_MAX` (patch 0004), `pos ≥ -2^31` (only `gzungetc` lowers it, by at
  most the `2 * want` bytes of the output buffer), `pos ≥ 0` when writing;
* reading: `how ∈ {LOOK, COPY, GZIP}`; with buffers, the inflate stream has the inflate invariant (`gz_look` called
  `inflateInit2`) and no `gz_header` registered, `x.have` bytes from `x.next` lie inside `out`, and `avail_in` bytes
  from `next_in` inside `in`; without buffers `x.have` is 0; a pending skip and the bytes `gzungetc` pushed back
  after it keep `pos + skip + have ≤ GZ_OFF_MAX`;
* writing: with buffers and not `direct`, the deflate stream has the deflate invariant (`gz_write_init`) and no
  `gz_header` registered, and `next_in` is `in` plus at most `size` with `avail_in` bytes after it inside `in`
  (patch 0014: no pointer into a caller's buffer is left between calls);
* the blocks the file frees (`ownL`: the state, `path`, `msg`, and with buffers the buffers and the block of the
  stream's state) are pairwise distinct.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.GzInv
open C ZlibNgF.Spec ZlibNg.Gz

/-- An owned heap string: offset 0 of a live heap block that holds a C string. -/
def OwnedStr (h : Heap) (p : Ival BPtr) : Prop :=
  ∃ c n, p = .val (.ref (.heap c) 0) ∧ CStringLen h (.ref (.heap c) 0) n

/-- An owned heap block: offset 0 of a live heap block. -/
def OwnedBlk (h : Heap) (p : Ival BPtr) : Prop :=
  ∃ c d, p = .val (.ref (.heap c) 0) ∧ h.bytes c = some d

/-- The sizes of the two buffers of `gz_buffer_alloc` for the mode and `direct` of `s`. -/
def inSize (s : GzState) : Nat := if s.mode = GZ_WRITE then 2 * s.want.toNat else s.want.toNat
def outSize (s : GzState) : Nat :=
  if s.mode = GZ_WRITE then (if s.direct ≠ 0 then 0 else s.want.toNat) else 2 * s.want.toNat

/-- `n` bytes from `p` lie inside `[base + lo, base + hi)` of block `c`. -/
def Inside (c base lo hi : Nat) (p : BPtr) (n : Nat) : Prop :=
  ∃ k, p = .ref (.heap c) (base + k) ∧ lo ≤ k ∧ k + n ≤ hi

/-- Positions (`x.pos`, `skip`). -/
structure GzPos (s : GzState) : Prop where
  skip_nonneg : 0 ≤ s.skip.toInt
  pos_skip : s.pos.toInt + s.skip.toInt ≤ GZ_OFF_MAX.toInt
  pos_lower : -(2 ^ 31 : Int) ≤ s.pos.toInt
  write_pos : s.mode = GZ_WRITE → 0 ≤ s.pos.toInt

/-- The buffers: none (`size == 0`), or one live block carved into `in` and `out`. -/
structure GzBufs (h : Heap) (s : GzState) (c base : Nat) : Prop where
  size : s.size = s.want
  buffers : s.buffers = .val (.ref (.heap c) base)
  inp : s.«in» = .val (.ref (.heap c) base)
  out : outSize s ≠ 0 → s.out = .val (.ref (.heap c) (base + inSize s))
  fits : ∃ d, h.bytes c = some d ∧ base + inSize s + outSize s ≤ d.size
  /-- the header of the aligned allocation (`zng_alloc_aligned`): the pointer to the block is saved before `base` -/
  hdr : 8 ≤ base ∧ h.savedPtrs c = some (base - 8, .ref (.heap c) 0)

/-- Reading. -/
structure GzRead (h : Heap) (s : GzState) : Prop where
  how : s.how = LOOK ∨ s.how = COPY ∨ s.how = GZIP
  bufs : s.size ≠ 0 → ∃ c base z, GzBufs h s c base ∧ InflateInv.Inv h (some s.strm) ∧
    h.streams s.strm = some z ∧
    (s.«have» = 0 ∨ ∃ p, s.next = .val p ∧ Inside c base (inSize s) (inSize s + outSize s) p s.«have».toNat) ∧
    (z.avail_in = 0 ∨ Inside c base 0 (inSize s) z.next_in z.avail_in.toNat) ∧
    (∀ hp, RegisteredHeader h (some s.strm) hp → hp = none)
  /-- no output is buffered before the buffers exist -/
  nobuf : s.size = 0 → s.«have» = 0
  /-- a pending skip and the bytes pushed back by `gzungetc` after it stay below `GZ_OFF_MAX` -/
  skip_have : s.skip ≠ 0 → s.pos.toInt + s.skip.toInt + s.«have».toNat ≤ GZ_OFF_MAX.toInt

/-- Writing. -/
structure GzWrite (h : Heap) (s : GzState) : Prop where
  bufs : s.size ≠ 0 → ∃ c base z, GzBufs h s c base ∧ h.streams s.strm = some z ∧
    (s.direct = 0 → DeflateInv.DInv h (some s.strm)) ∧
    (z.avail_in = 0 ∨ Inside c base 0 s.size.toNat z.next_in z.avail_in.toNat) ∧
    (∀ sb st k, z.state = some sb → h.dstate sb = some st → st.gzhead ≠ .val (some k))

/-- The error message. -/
structure GzMsg (h : Heap) (s : GzState) : Prop where
  msg : s.msg = .val .null ∨ OwnedBlk h s.msg
  mem : s.err = ZlibNg.Inflate.Z_MEM_ERROR → s.msg = .val .null

/-- The block of the inflate or deflate state of the embedded stream of `s`, if any. -/
def stBlk (h : Heap) (s : GzState) : List Nat :=
  match h.streams s.strm with | some z => (match z.state with | some c => [c] | none => []) | none => []

/-- The heap block of an owned pointer field, if any. -/
def blkOf (p : Ival BPtr) : List Nat := match p with | .val (.ref (.heap c) _) => [c] | _ => []

/-- The fields of a live `gz_state` between two public calls. -/
structure GzShape (h : Heap) (s : GzState) : Prop where
  mode : s.mode = GZ_READ ∨ s.mode = GZ_WRITE
  path : OwnedStr h s.path
  strm : ∃ z, h.streams s.strm = some z
  want_lo : 8 ≤ s.want.toNat
  want_hi : s.want.toNat ≤ 2 ^ 30
  size : s.size = 0 ∨ s.size = s.want
  pos : GzPos s
  msg : GzMsg h s
  read : s.mode = GZ_READ → GzRead h s
  write : s.mode = GZ_WRITE → GzWrite h s
  /-- without buffers, no buffer block and no stream state is live (none made yet, or freed) -/
  dead : s.size = 0 → ∀ c ∈ blkOf s.buffers ++ stBlk h s, h.bytes c = none ∧ c < h.nextBlk

/-- The blocks the file `b` owns and frees: its state, `path`, `msg` and, once the buffers exist, the buffers and the
block of the stream's state. -/
def ownL (h : Heap) (b : Nat) (s : GzState) : List Nat :=
  [b] ++ blkOf s.path ++ blkOf s.msg ++ (if s.size = 0 then [] else blkOf s.buffers ++ stBlk h s)

/-- **The invariant** of an open file: the fields, and its blocks are pairwise distinct. -/
def GzInv (w : World) (h : Heap) (f : GzPtr) : Prop :=
  ∃ b s, f = some b ∧ w.gz h b = some s ∧ GzShape h s ∧ (ownL h b s).Nodup

/-! ## Interface lemmas -/

theorem live {w : World} {h : Heap} {f : GzPtr} (hv : GzInv w h f) :
    ∃ b s, f = some b ∧ w.gz h b = some s ∧ GzShape h s := by
  obtain ⟨b, s, e, hs, sh, -⟩ := hv; exact ⟨b, s, e, hs, sh⟩

/-- Reading a field of the live state changes nothing. -/
theorem rdG_app {α : Type} {w : World} {h : Heap} {b : Nat} {s : GzState} (hs : w.gz h b = some s)
    (g : GzState → α) : C.run ((rdG (some b) g).run w) h = .ok ((g s, w), h) := by
  simp only [C.run, rdG, ldGz, getHeap, lm, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get,
    StateT.get, StateT.lift, pure, StateT.pure]
  simp [hs, StateT.pure, pure]

/-- The mode of an open file is `GZ_READ` or `GZ_WRITE`. -/
theorem mode {w : World} {h : Heap} {b : Nat} {s : GzState} (hs : w.gz h b = some s)
    (hv : GzInv w h (some b)) : s.mode = GZ_READ ∨ s.mode = GZ_WRITE := by
  obtain ⟨b', s', e, hs', sh, -⟩ := hv
  cases e
  rw [hs] at hs'
  cases hs'
  exact sh.mode

/-- The positions of an open file. -/
theorem pos {w : World} {h : Heap} {b : Nat} {s : GzState} (hs : w.gz h b = some s)
    (hv : GzInv w h (some b)) : GzPos s := by
  obtain ⟨b', s', e, hs', sh, -⟩ := hv
  cases e
  rw [hs] at hs'
  cases hs'
  exact sh.pos

/-- A call that changes neither the world nor the heap stays in the frame of any file. -/
theorem gzframe_refl (w : World) (h : Heap) (f : GzPtr) (W : List (BPtr × Nat)) : GzFrame w h w h f W :=
  ⟨DeflateInitPublic.dframe_refl h _ _ _ W, fun _ _ e => e, fun _ _ _ => rfl⟩

end ZlibNgF.Proof.GzInv
