import ZlibNgF.Proof.«deflate.c.init»

/-!
# The pending-byte output of the deflate state (`ZlibNgF`)

Runs on `SH` heaps (`Proof/deflate.c.init.lean`) of the byte stores into `pending_buf`: `zng_memwrite_2/4/8`,
`put_byte`, `put_short`, `put_short_msb`, `put_uint32`, `put_uint32_msb`, `put_uint64` and `zng_tr_flush_bits`.
Each one stores at `pending_buf + pending` within the block and changes the block's bytes only in the range it
writes (`WrIn`), and the state only in `pending` (and, for `zng_tr_flush_bits`, `bi_buf` / `bi_valid`).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.DeflateBits
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNgF.Proof.ChunkMem (modify_heap)
open ZlibNgF.Proof.InflateInv (upd_upd)
open ZlibNgF.Proof.InflateAlloc (space_get_heap)
open ZlibNgF.Proof.DeflateAlloc (pure_bind_M ite_t ite_f)

/-- `d'` has the size of `d` and differs from it at most in `[lo, hi)`. -/
def WrIn (d : Array UInt8) (lo hi : Nat) (d' : Array UInt8) : Prop :=
  d'.size = d.size ∧ ∀ j, (j < lo ∨ hi ≤ j) → d'[j]! = d[j]!

theorem WrIn.refl (d : Array UInt8) (lo hi : Nat) : WrIn d lo hi d := ⟨rfl, fun _ _ => rfl⟩

/-- A second change inside the range of the first. -/
theorem WrIn.trans {d d' d'' : Array UInt8} {lo hi lo' hi' : Nat} (a : WrIn d lo hi d') (b : WrIn d' lo' hi' d'')
    (h1 : lo ≤ lo') (h2 : hi' ≤ hi) : WrIn d lo hi d'' :=
  ⟨b.1.trans a.1, fun j hj => (b.2 j (by omega)).trans (a.2 j hj)⟩

theorem WrIn.widen {d d' : Array UInt8} {lo hi lo' hi' : Nat} (a : WrIn d lo hi d') (h1 : lo' ≤ lo) (h2 : hi ≤ hi') :
    WrIn d lo' hi' d' := ⟨a.1, fun j hj => a.2 j (by omega)⟩

theorem WrIn.set (d : Array UInt8) (off : Nat) (v : UInt8) : WrIn d off (off + 1) (d.set! off v) := by
  refine ⟨by simp, fun j hj => ?_⟩
  have hx : off ≠ j := by omega
  simp only [Array.set!_eq_setIfInBounds, getElem!_def, Array.getElem?_setIfInBounds]
  simp [hx]

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8}

theorem store_SH {off : Nat} (v : UInt8) (h : off < d.size) :
    Ptr.store (Ptr.ref (BRef.heap b) off) v (SH H i z b st d) = .ok ((), SH H i z b st (d.set! off v)) := by
  simp only [Ptr.store, space_get_heap, SH_bytes, Space.ro, Heap.isRo, Bool.false_eq_true, ↓reduceIte, h]
  rw [modify_heap _ _ d (SH_bytes H i z b st d)]
  simp [SH, upd_upd]

theorem addI_SH {off : Nat} (k : Int) (h0 : 0 ≤ k) (hk : (off : Int) + k ≤ d.size) :
    Ptr.add (Ptr.ref (BRef.heap b) off) k (SH H i z b st d) =
      .ok (.ref (.heap b) ((off : Int) + k).toNat, SH H i z b st d) := by
  have : off ≤ d.size := by omega
  simp only [Ptr.add, space_get_heap, SH_bytes, this, show 0 ≤ (off : Int) + k by omega, hk, and_self,
    ↓reduceIte]

/-- One byte store at `off + k` (`k` a literal offset of `zng_memwrite_*`) followed by the rest `f`. -/
theorem st1 {off : Nat} (k : Int) (h0 : 0 ≤ k) (v : UInt8) (hk : off + k.toNat < d.size) {β : Type}
    {f : Unit → M β} {Q : β → Heap → Prop} (q : Sat (SH H i z b st (d.set! (off + k.toNat) v)) (f ()) Q) :
    Sat (SH H i z b st d) ((Ptr.ref (BRef.heap b) off).add k >>= fun p => Ptr.store p v >>= f) Q := by
  refine Sat.bind (Sat.of_eq (addI_SH k h0 (by omega)) ?_)
  rw [show ((off : Int) + k).toNat = off + k.toNat by omega]
  exact Sat.bind (Sat.of_eq (store_SH v hk) q)

/-- The last byte store of a `zng_memwrite_*`. -/
theorem st1e {off : Nat} (k : Int) (h0 : 0 ≤ k) (v : UInt8) (hk : off + k.toNat < d.size) {Q : Unit → Heap → Prop}
    (q : Q () (SH H i z b st (d.set! (off + k.toNat) v))) :
    Sat (SH H i z b st d) ((Ptr.ref (BRef.heap b) off).add k >>= fun p => Ptr.store p v) Q := by
  refine Sat.bind (Sat.of_eq (addI_SH k h0 (by omega)) ?_)
  rw [show ((off : Int) + k).toNat = off + k.toNat by omega]
  exact Sat.of_eq (store_SH v hk) q

theorem set_size (d : Array UInt8) (o : Nat) (v : UInt8) : (d.set! o v).size = d.size := by simp

/-- A byte store at `off + k`, `k < n`, inside `[off, off + n)`. -/
theorem wr_seq {d d' : Array UInt8} {off n : Nat} (k : Nat) (v : UInt8) (hk : k < n)
    (a : WrIn d off (off + n) d') : WrIn d off (off + n) (d'.set! (off + k) v) :=
  a.trans ((WrIn.set d' (off + k) v).widen (lo' := off) (hi' := off + n) (by omega) (by omega)) (by omega)
    (by omega)

theorem memwrite2_SH {off : Nat} (v : UInt16) (h : off + 2 ≤ d.size) :
    Sat (SH H i z b st d) (memwrite2 (.ref (.heap b) off) v)
      (fun _ H' => ∃ d', H' = SH H i z b st d' ∧ WrIn d off (off + 2) d') := by
  unfold memwrite2
  refine st1 0 (by decide) _ (by simp; omega) ?_
  refine st1e 1 (by decide) _ (by simp; omega) ⟨_, rfl, ?_⟩
  exact wr_seq 1 _ (by omega) (wr_seq 0 _ (by omega) (WrIn.refl _ _ _))

theorem memwrite4_SH {off : Nat} (v : UInt32) (h : off + 4 ≤ d.size) :
    Sat (SH H i z b st d) (memwrite4 (.ref (.heap b) off) v)
      (fun _ H' => ∃ d', H' = SH H i z b st d' ∧ WrIn d off (off + 4) d') := by
  unfold memwrite4
  refine st1 0 (by decide) _ (by simp; omega) ?_
  refine st1 1 (by decide) _ (by simp; omega) ?_
  refine st1 2 (by decide) _ (by simp; omega) ?_
  refine st1e 3 (by decide) _ (by simp; omega) ⟨_, rfl, ?_⟩
  exact wr_seq 3 _ (by omega) (wr_seq 2 _ (by omega) (wr_seq 1 _ (by omega) (wr_seq 0 _ (by omega)
    (WrIn.refl _ _ _))))

theorem memwrite8_SH {off : Nat} (v : UInt64) (h : off + 8 ≤ d.size) :
    Sat (SH H i z b st d) (memwrite8 (.ref (.heap b) off) v)
      (fun _ H' => ∃ d', H' = SH H i z b st d' ∧ WrIn d off (off + 8) d') := by
  unfold memwrite8
  refine st1 0 (by decide) _ (by simp; omega) ?_
  refine st1 1 (by decide) _ (by simp; omega) ?_
  refine st1 2 (by decide) _ (by simp; omega) ?_
  refine st1 3 (by decide) _ (by simp; omega) ?_
  refine st1 4 (by decide) _ (by simp; omega) ?_
  refine st1 5 (by decide) _ (by simp; omega) ?_
  refine st1 6 (by decide) _ (by simp; omega) ?_
  refine st1e 7 (by decide) _ (by simp; omega) ⟨_, rfl, ?_⟩
  exact wr_seq 7 _ (by omega) (wr_seq 6 _ (by omega) (wr_seq 5 _ (by omega) (wr_seq 4 _ (by omega)
    (wr_seq 3 _ (by omega) (wr_seq 2 _ (by omega) (wr_seq 1 _ (by omega) (wr_seq 0 _ (by omega)
    (WrIn.refl _ _ _))))))))


/-- The pending-byte stores of `put_*`: `pending_buf + pending` within the block, a store of `n` bytes there
through `mw`, then `pending += n`. -/
theorem put_gen {pbo : Nat} (hpb : st.pending_buf = .val (.ref (.heap b) pbo)) (n : Nat) (mw : BPtr → M Unit)
    (hmw : ∀ (d0 : Array UInt8), pbo + st.pending.toNat + n ≤ d0.size →
      Sat (SH H i z b st d0) (mw (.ref (.heap b) (pbo + st.pending.toNat)))
        (fun _ H' => ∃ d', H' = SH H i z b st d' ∧ WrIn d0 (pbo + st.pending.toNat) (pbo + st.pending.toNat + n) d'))
    (hroom : pbo + st.pending.toNat + n ≤ d.size) (k : UInt32) :
    Sat (SH H i z b st d) (do
        let s ← ldDState (some b)
        mw (← (← s.pending_buf.get).add s.pending.toNat)
        wrD (some b) fun s => { s with pending := s.pending + k })
      (fun _ H' => ∃ d', H' = SH H i z b { st with pending := st.pending + k } d' ∧
        WrIn d (pbo + st.pending.toNat) (pbo + st.pending.toNat + n) d') := by
  refine Sat.bind (Sat.of_eq ldDState_SH ?_)
  simp only [hpb, Ival.get, pure_bind_M]
  refine Sat.bind (Sat.of_eq (addI_SH (st.pending.toNat : Int) (by omega) (by omega)) ?_)
  rw [show ((pbo : Int) + (st.pending.toNat : Int)).toNat = pbo + st.pending.toNat by omega]
  refine Sat.bind (Sat.mono (hmw d hroom) ?_)
  rintro _ _ ⟨d', rfl, w⟩
  exact Sat.of_eq (wrD_SH _) ⟨d', by simp only [hpb], w⟩

theorem put_byte_SH {pbo : Nat} (hpb : st.pending_buf = .val (.ref (.heap b) pbo)) (c : UInt8)
    (hroom : pbo + st.pending.toNat + 1 ≤ d.size) :
    Sat (SH H i z b st d) (put_byte (some b) c)
      (fun _ H' => ∃ d', H' = SH H i z b { st with pending := st.pending + 1 } d' ∧
        WrIn d (pbo + st.pending.toNat) (pbo + st.pending.toNat + 1) d') :=
  put_gen hpb 1 (fun p => store8 p c) (fun d0 h0 => by
    refine Sat.of_eq (store_SH c (by omega)) ⟨_, rfl, WrIn.set _ _ _⟩) hroom 1

theorem put_short_SH {pbo : Nat} (hpb : st.pending_buf = .val (.ref (.heap b) pbo)) (w : UInt16)
    (hroom : pbo + st.pending.toNat + 2 ≤ d.size) :
    Sat (SH H i z b st d) (put_short (some b) w)
      (fun _ H' => ∃ d', H' = SH H i z b { st with pending := st.pending + 2 } d' ∧
        WrIn d (pbo + st.pending.toNat) (pbo + st.pending.toNat + 2) d') :=
  put_gen hpb 2 (fun p => memwrite2 p w) (fun _ h0 => memwrite2_SH w h0) hroom 2

theorem put_short_msb_SH {pbo : Nat} (hpb : st.pending_buf = .val (.ref (.heap b) pbo)) (w : UInt16)
    (hroom : pbo + st.pending.toNat + 2 ≤ d.size) :
    Sat (SH H i z b st d) (put_short_msb (some b) w)
      (fun _ H' => ∃ d', H' = SH H i z b { st with pending := st.pending + 2 } d' ∧
        WrIn d (pbo + st.pending.toNat) (pbo + st.pending.toNat + 2) d') :=
  put_gen hpb 2 (fun p => memwrite2 p _) (fun _ h0 => memwrite2_SH _ h0) hroom 2

theorem put_uint32_SH {pbo : Nat} (hpb : st.pending_buf = .val (.ref (.heap b) pbo)) (w : UInt32)
    (hroom : pbo + st.pending.toNat + 4 ≤ d.size) :
    Sat (SH H i z b st d) (put_uint32 (some b) w)
      (fun _ H' => ∃ d', H' = SH H i z b { st with pending := st.pending + 4 } d' ∧
        WrIn d (pbo + st.pending.toNat) (pbo + st.pending.toNat + 4) d') :=
  put_gen hpb 4 (fun p => memwrite4 p w) (fun _ h0 => memwrite4_SH w h0) hroom 4

theorem put_uint32_msb_SH {pbo : Nat} (hpb : st.pending_buf = .val (.ref (.heap b) pbo)) (w : UInt32)
    (hroom : pbo + st.pending.toNat + 4 ≤ d.size) :
    Sat (SH H i z b st d) (put_uint32_msb (some b) w)
      (fun _ H' => ∃ d', H' = SH H i z b { st with pending := st.pending + 4 } d' ∧
        WrIn d (pbo + st.pending.toNat) (pbo + st.pending.toNat + 4) d') :=
  put_gen hpb 4 (fun p => memwrite4 p _) (fun _ h0 => memwrite4_SH _ h0) hroom 4

theorem put_uint64_SH {pbo : Nat} (hpb : st.pending_buf = .val (.ref (.heap b) pbo)) (w : UInt64)
    (hroom : pbo + st.pending.toNat + 8 ≤ d.size) :
    Sat (SH H i z b st d) (put_uint64 (some b) w)
      (fun _ H' => ∃ d', H' = SH H i z b { st with pending := st.pending + 8 } d' ∧
        WrIn d (pbo + st.pending.toNat) (pbo + st.pending.toNat + 8) d') :=
  put_gen hpb 8 (fun p => memwrite8 p w) (fun _ h0 => memwrite8_SH w h0) hroom 8


end

/-! ## `zng_tr_flush_bits` -/

theorem sub_toInt (x k : Int32) (hk : k.toInt ≤ x.toInt) (h0 : 0 ≤ k.toInt) : (x - k).toInt = x.toInt - k.toInt := by
  rw [Int32.toInt_sub]
  have := x.le_toInt; have := x.toInt_lt; have := k.toInt_lt
  rw [Int.bmod_eq_of_le] <;> omega

theorem ge_toInt (x : Int32) (k : Int32) : x ≥ k ↔ k.toInt ≤ x.toInt := Int32.le_iff_toInt_le

theorem add_toNat (p : UInt32) (k : Nat) (hk : k < 2 ^ 32) (h : p.toNat + k < 2 ^ 32) :
    (p + UInt32.ofNat k).toNat = p.toNat + k := by
  rw [UInt32.toNat_add, UInt32.toNat_ofNat_of_lt' hk]; omega

/-- The last statement of `zng_tr_flush_bits`: `if (s->bi_valid >= 8) { put_byte; ... }`. -/
def fbLast (st : StatePtr) : M Unit := do
  if (← rdD st (·.bi_valid)) >= 8 then
    put_byte st (← rdD st (·.bi_buf)).toUInt8
    wrD st fun s => { s with bi_buf := s.bi_buf >>> 8 }
    wrD st fun s => { s with bi_valid := s.bi_valid - 8 }

/-- The last two statements of `zng_tr_flush_bits`. -/
def fbTail (st : StatePtr) : M Unit := do
  if (← rdD st (·.bi_valid)) >= 16 then
    put_short st (← rdD st (·.bi_buf)).toUInt16
    wrD st fun s => { s with bi_buf := s.bi_buf >>> 16 }
    wrD st fun s => { s with bi_valid := s.bi_valid - 16 }
  if (← rdD st (·.bi_valid)) >= 8 then
    put_byte st (← rdD st (·.bi_buf)).toUInt8
    wrD st fun s => { s with bi_buf := s.bi_buf >>> 8 }
    wrD st fun s => { s with bi_valid := s.bi_valid - 8 }

/-- What `zng_tr_flush_bits` leaves: the complete bytes of the bit buffer appended at `pending_buf + pending`, fewer
than 8 bits left, and nothing else of the state or the block changed. -/
def FBPost (H : Heap) (i : Nat) (z : ZStream) (b : Nat) (st : DeflateState) (d : Array UInt8) (pbo : Nat)
    (H' : Heap) : Prop :=
  ∃ d' bb bv np, H' = SH H i z b { st with pending := np, bi_buf := bb, bi_valid := bv } d' ∧
    WrIn d (pbo + st.pending.toNat) (pbo + np.toNat) d' ∧ 0 ≤ bv.toInt ∧ bv.toInt < 8 ∧
    np.toNat * 8 + bv.toInt.toNat = st.pending.toNat * 8 + st.bi_valid.toInt.toNat

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8}

theorem FBPost.refl {pbo : Nat} (h0 : 0 ≤ st.bi_valid.toInt) (h8 : st.bi_valid.toInt < 8) :
    FBPost H i z b st d pbo (SH H i z b st d) :=
  ⟨d, st.bi_buf, st.bi_valid, st.pending, rfl, WrIn.refl _ _ _, h0, h8, rfl⟩

/-- A step that writes `k` bytes and takes `8 k` bits, followed by a run that reaches `FBPost`. -/
theorem FBPost.step {pbo k : Nat} {st1 : DeflateState} {d1 : Array UInt8} {H' : Heap}
    (hs : st1 = { st with pending := st1.pending, bi_buf := st1.bi_buf, bi_valid := st1.bi_valid })
    (w : WrIn d (pbo + st.pending.toNat) (pbo + st.pending.toNat + k) d1)
    (hp : st1.pending.toNat = st.pending.toNat + k) (hv : st1.bi_valid.toInt = st.bi_valid.toInt - 8 * k)
    (hv0 : 0 ≤ st1.bi_valid.toInt) (q : FBPost H i z b st1 d1 pbo H') : FBPost H i z b st d pbo H' := by
  obtain ⟨d', bb, bv, np, rfl, w', h0, h8, he⟩ := q
  refine ⟨d', bb, bv, np, ?_, ?_, h0, h8, by omega⟩
  · rw [hs]
  · rw [hp] at w'
    have hle : st.pending.toNat + k ≤ np.toNat := by omega
    exact w.widen (Nat.le_refl _) (by omega : pbo + st.pending.toNat + k ≤ pbo + np.toNat) |>.trans
      (w'.widen (by omega) (Nat.le_refl _)) (Nat.le_refl _) (Nat.le_refl _)

theorem fbLast_SH {pbo : Nat} (hpb : st.pending_buf = .val (.ref (.heap b) pbo)) (h0 : 0 ≤ st.bi_valid.toInt)
    (h16 : st.bi_valid.toInt < 16) (hroom : pbo + st.pending.toNat + st.bi_valid.toInt.toNat / 8 ≤ d.size)
    (hp : st.pending.toNat + 8 < 2 ^ 32) :
    Sat (SH H i z b st d) (fbLast (some b)) (fun _ H' => FBPost H i z b st d pbo H') := by
  unfold fbLast
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_); try dsimp only
  by_cases c : st.bi_valid ≥ 8
  · rw [ite_t c]
    have c' := (ge_toInt _ _).mp c
    have e8 : (8 : Int32).toInt = 8 := rfl
    refine Sat.bind (Sat.of_eq (rdD_SH _) ?_); try dsimp only
    refine Sat.bind (Sat.mono (put_byte_SH hpb _ (by omega)) ?_)
    rintro _ _ ⟨d1, rfl, w1⟩
    refine Sat.bind (Sat.of_eq (wrD_SH _) ?_); try dsimp only
    refine Sat.of_eq (wrD_SH _) ?_
    refine FBPost.step (k := 1) rfl w1 (add_toNat _ 1 (by decide) (by omega))
      (by try dsimp only; rw [sub_toInt _ _ (by omega) (by omega)]; omega)
      (by try dsimp only; rw [sub_toInt _ _ (by omega) (by omega)]; omega) (FBPost.refl ?_ ?_)
    · simp only []; rw [sub_toInt _ _ (by omega) (by omega)]; omega
    · simp only []; rw [sub_toInt _ _ (by omega) (by omega)]; omega
  · rw [ite_f c]
    have c' : ¬ (8 : Int32).toInt ≤ st.bi_valid.toInt := fun h => c ((ge_toInt _ _).mpr h)
    have e8 : (8 : Int32).toInt = 8 := rfl
    exact Sat.pure (FBPost.refl h0 (by omega))


theorem fbTail_SH {pbo : Nat} (hpb : st.pending_buf = .val (.ref (.heap b) pbo)) (h0 : 0 ≤ st.bi_valid.toInt)
    (h32 : st.bi_valid.toInt < 32) (hroom : pbo + st.pending.toNat + st.bi_valid.toInt.toNat / 8 ≤ d.size)
    (hp : st.pending.toNat + 16 < 2 ^ 32) :
    Sat (SH H i z b st d) (fbTail (some b)) (fun _ H' => FBPost H i z b st d pbo H') := by
  unfold fbTail
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_); try dsimp only
  have e16 : (16 : Int32).toInt = 16 := rfl
  by_cases c : st.bi_valid ≥ 16
  · rw [ite_t c]
    have c' := (ge_toInt _ _).mp c
    refine Sat.bind (Sat.of_eq (rdD_SH _) ?_); try dsimp only
    refine Sat.bind (Sat.mono (put_short_SH hpb _ (by omega)) ?_)
    rintro _ _ ⟨d1, rfl, w1⟩
    refine Sat.bind (Sat.of_eq (wrD_SH _) ?_); try dsimp only
    refine Sat.bind (Sat.of_eq (wrD_SH _) ?_); try dsimp only
    have hv : (st.bi_valid - 16).toInt = st.bi_valid.toInt - 16 := by rw [sub_toInt _ _ (by omega) (by omega)]; rfl
    have hp2 : (st.pending + 2).toNat = st.pending.toNat + 2 := add_toNat _ 2 (by decide) (by omega)
    refine Sat.mono (fbLast_SH (pbo := pbo) (by exact hpb) (by try dsimp only; omega) (by try dsimp only; omega)
      (by try dsimp only; rw [hp2, w1.1, hv]; omega) (by try dsimp only; rw [hp2]; omega)) ?_
    intro _ _ q
    exact FBPost.step (k := 2) rfl w1 hp2 (by try dsimp only; omega) (by try dsimp only; omega) q
  · rw [ite_f c]
    have c' : ¬ (16 : Int32).toInt ≤ st.bi_valid.toInt := fun h => c ((ge_toInt _ _).mpr h)
    exact fbLast_SH hpb h0 (by omega) (by omega) (by omega)

/-- `zng_tr_flush_bits` on a state with at most 64 bits in `bi_buf` and 8 bytes of room after the pending bytes. -/
theorem flush_bits_SH {pbo : Nat} (hpb : st.pending_buf = .val (.ref (.heap b) pbo)) (h0 : 0 ≤ st.bi_valid.toInt)
    (h64 : st.bi_valid.toInt ≤ 64) (hroom : pbo + st.pending.toNat + st.bi_valid.toInt.toNat / 8 ≤ d.size)
    (hp : st.pending.toNat + 32 < 2 ^ 32) :
    Sat (SH H i z b st d) (ZlibNg.Trees.zng_tr_flush_bits (some b)) (fun _ H' => FBPost H i z b st d pbo H') := by
  unfold ZlibNg.Trees.zng_tr_flush_bits
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_); try dsimp only
  have e48 : (48 : Int32).toInt = 48 := rfl
  have e32 : (32 : Int32).toInt = 32 := rfl
  by_cases c : st.bi_valid ≥ 48
  · rw [ite_t c]
    have c' := (ge_toInt _ _).mp c
    refine Sat.bind (Sat.of_eq (rdD_SH _) ?_); try dsimp only
    refine Sat.bind (Sat.mono (put_uint32_SH hpb _ (by omega)) ?_)
    rintro _ _ ⟨d1, rfl, w1⟩
    have hp4 : (st.pending + 4).toNat = st.pending.toNat + 4 := add_toNat _ 4 (by decide) (by omega)
    refine Sat.bind (Sat.of_eq (rdD_SH _) ?_); try dsimp only
    refine Sat.bind (Sat.mono (put_short_SH (pbo := pbo) (by exact hpb) _ (by try dsimp only; rw [hp4, w1.1]; omega)) ?_)
    rintro _ _ ⟨d2, rfl, w2⟩
    have hp6 : (st.pending + 4 + 2).toNat = st.pending.toNat + 6 := by
      have h2 := add_toNat (st.pending + 4) 2 (by decide) (by omega)
      rw [hp4] at h2; exact h2
    refine Sat.bind (Sat.of_eq (wrD_SH _) ?_); try dsimp only
    refine Sat.bind (Sat.of_eq (wrD_SH _) ?_); try dsimp only
    have hv : (st.bi_valid - 48).toInt = st.bi_valid.toInt - 48 := by rw [sub_toInt _ _ (by omega) (by omega)]; rfl
    simp only [hp4] at w2
    have w12 : WrIn d (pbo + st.pending.toNat) (pbo + st.pending.toNat + 6) d2 :=
      (w1.widen (Nat.le_refl _) (by omega)).trans (w2.widen (by omega) (by omega)) (Nat.le_refl _) (Nat.le_refl _)
    refine Sat.mono (fbTail_SH (pbo := pbo) (by exact hpb) (by try dsimp only; omega) (by try dsimp only; omega)
      (by try dsimp only; rw [hp6, w12.1, hv]; omega)
      (by show (st.pending + 4 + 2).toNat + 16 < 2 ^ 32; rw [hp6]; omega)) ?_
    intro _ _ q
    exact FBPost.step (k := 6) rfl w12 hp6 (by try dsimp only; omega) (by try dsimp only; omega) q
  · rw [ite_f c]
    have c' : ¬ (48 : Int32).toInt ≤ st.bi_valid.toInt := fun h => c ((ge_toInt _ _).mpr h)
    refine Sat.bind (Sat.of_eq (rdD_SH _) ?_); try dsimp only
    by_cases c2 : st.bi_valid ≥ 32
    · rw [ite_t c2]
      have c2' := (ge_toInt _ _).mp c2
      refine Sat.bind (Sat.of_eq (rdD_SH _) ?_); try dsimp only
      refine Sat.bind (Sat.mono (put_uint32_SH hpb _ (by omega)) ?_)
      rintro _ _ ⟨d1, rfl, w1⟩
      have hp4 : (st.pending + 4).toNat = st.pending.toNat + 4 := add_toNat _ 4 (by decide) (by omega)
      refine Sat.bind (Sat.of_eq (wrD_SH _) ?_); try dsimp only
      refine Sat.bind (Sat.of_eq (wrD_SH _) ?_); try dsimp only
      have hv : (st.bi_valid - 32).toInt = st.bi_valid.toInt - 32 := by
        rw [sub_toInt _ _ (by omega) (by omega)]; rfl
      refine Sat.mono (fbTail_SH (pbo := pbo) (by exact hpb) (by try dsimp only; omega) (by try dsimp only; omega)
        (by try dsimp only; rw [hp4, w1.1, hv]; omega) (by try dsimp only; rw [hp4]; omega)) ?_
      intro _ _ q
      exact FBPost.step (k := 4) rfl w1 hp4 (by try dsimp only; omega) (by try dsimp only; omega) q
    · rw [ite_f c2]
      have c2' : ¬ (32 : Int32).toInt ≤ st.bi_valid.toInt := fun h => c2 ((ge_toInt _ _).mpr h)
      exact fbTail_SH hpb h0 (by omega) (by omega) (by omega)

end

end ZlibNgF.Proof.DeflateBits
