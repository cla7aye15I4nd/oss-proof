import ZlibNgF.Proof.«trees_emit.h.emit»

/-!
# The block emitters of `deflate_quick` and `trees.c` that need no tree construction (`ZlibNgF`)

`zng_tr_emit_lit`, `zng_tr_emit_dist` (static trees), `zng_tr_emit_tree`, `zng_tr_emit_end_block` (static tree),
`zng_tr_emit_align`, `zng_tr_align` and `zng_tr_stored_block`, each as `EmitOkP` (`Proof/trees_emit.h.emit.lean`)
with a bound on the bytes it adds. Counting bits gives the bounds: a symbol of at most 32 bits and at most 63 bits
already in `bi_buf` make at most 8 bytes.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.TreesEmitP
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.DeflateBits ZlibNgF.Proof.DeflateFacts
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNgF.Proof.DeflateAlloc (pure_bind_M ite_t ite_f)

/-- Two consecutive changes. -/
theorem WrIn.cat {d d1 d2 : Array UInt8} {a m e : Nat} (w1 : WrIn d a m d1) (w2 : WrIn d1 m e d2) (h1 : a ≤ m)
    (h2 : m ≤ e) : WrIn d a e d2 :=
  (w1.widen (Nat.le_refl _) h2).trans (w2.widen h1 (Nat.le_refl _)) (Nat.le_refl _) (Nat.le_refl _)

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8}

theorem emit_dist_SH {pbo : Nat} (hpb : st.pending_buf = .val (.ref (.heap b) pbo)) (h0 : 0 ≤ st.bi_valid.toInt)
    (h64 : st.bi_valid.toInt < 64) (hroom : pbo + st.pending.toNat + 8 ≤ d.size) (hp : st.pending.toNat + 8 < 2 ^ 32)
    (lc dist : UInt32) (hlc : lc.toNat < 256) (hd1 : 1 ≤ dist.toNat) (hd2 : dist.toNat ≤ 32768) :
    Sat (SH H i z b st d) (ZlibNg.TreesEmit.zng_tr_emit_dist (some b) (.ref .static_ltree 0) (.ref .static_dtree 0)
      lc dist) (fun _ H' => EPost H i z b st d pbo 16 H') := by
  unfold ZlibNg.TreesEmit.zng_tr_emit_dist ZlibNg.TreesEmit.zng_emit_dist
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_); try dsimp only
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_); try dsimp only
  have hv := toU32 _ h0
  refine Sat.bind (Sat.bind (Sat.mono (assemble_static _ lc dist hlc hd1 hd2) ?_))
  rintro ⟨mb, ml⟩ _ ⟨rfl, hml⟩
  dsimp only at hml
  refine Sat.bind (Sat.mono (send_bits_SH hpb _ _ _ _ (by omega) (by dsimp only; omega) hroom hp) ?_)
  rintro ⟨r1, r2⟩ _ ⟨np, d1, rfl, w, hacc, hr, hle, hge⟩
  refine Sat.pure ?_
  exact Sat.of_eq (wrD_SH _) (epost_mk np d1 r1 r2 w hle (by rw [hv] at hacc; dsimp only at hacc; omega) hr)

theorem align_SH {pbo : Nat} (hpb : st.pending_buf = .val (.ref (.heap b) pbo)) (h0 : 0 ≤ st.bi_valid.toInt)
    (h64 : st.bi_valid.toInt < 64) (hroom : pbo + st.pending.toNat + 24 ≤ d.size)
    (hp : st.pending.toNat + 64 < 2 ^ 32) :
    Sat (SH H i z b st d) (ZlibNg.Trees.zng_tr_align (some b)) (fun _ H' => EPost H i z b st d pbo 16 H') := by
  unfold ZlibNg.Trees.zng_tr_align
  refine Sat.bind (Sat.mono (emit_tree_SH hpb h0 h64 (by omega) (by omega) _ _ (by decide) (by decide)
    (by decide)) ?_)
  rintro _ _ ⟨np, bb, bv, d1, rfl, w1, hacc1, hbv1, hle1, hge1⟩
  have e1 := toInt32_toInt bv hbv1
  refine Sat.bind (Sat.mono (end_block_SH (pbo := pbo) (by exact hpb) (by dsimp only; omega) (by dsimp only; omega)
    (by dsimp only; rw [w1.1]; omega) (by dsimp only; omega) 0) ?_)
  rintro _ _ ⟨q, -⟩
  obtain ⟨np2, bb2, bv2, d2, rfl, w2, hacc2, hbv2, hle2, hge2⟩ := q rfl
  dsimp only at w2 hacc2 hle2 hge2
  rw [e1] at hacc2
  have e2 := toInt32_toInt bv2 hbv2
  refine Sat.mono (flush_bits_SH (pbo := pbo) (by exact hpb) (by dsimp only; omega) (by dsimp only; omega)
    (by dsimp only; rw [e2, w2.1, w1.1]; omega) (by dsimp only; omega)) ?_
  rintro _ _ ⟨d3, bb3, bv3, np3, rfl, w3, h30, h38, he3⟩
  dsimp only at w3 he3
  rw [e2] at he3
  try dsimp only at w2
  refine ⟨_, d3, rfl, WrIn.cat (WrIn.cat w1 w2 (by omega) (by omega)) w3 (by dsimp only at *; omega) (by dsimp only at *; omega), rfl, rfl, by dsimp only; omega,
    by dsimp only; omega, h30, by dsimp only; omega⟩

/-- `memcpy`'s result differs from the destination only in the copied range. -/
theorem copy_wrin (a : Array UInt8) (od os n : Nat) :
    WrIn a od (od + n) (InflateDict.copyFold a od os (List.range' 0 n) a) :=
  ⟨InflateDict.copyFold_size _ _ _ _ _, fun j hj =>
    InflateDict.copyFold_get _ _ _ _ _ _ (fun x hx => by simp only [List.mem_range'] at hx; omega)⟩

theorem ival_get {α : Type} {v : Ival α} {x : α} (h : v = .val x) (H : Heap) : v.get H = .ok (x, H) := by
  subst h; rfl

/-- `memcpy` inside block `b` from below the destination. -/
theorem memcpy_SH {od os n : Nat} (h1 : od + n ≤ d.size) (hdis : os + n ≤ od) :
    Ptr.memcpy (Ptr.ref (BRef.heap b) od) (Ptr.ref (BRef.heap b) os) n (SH H i z b st d) =
      .ok ((), SH H i z b st (InflateDict.copyFold d od os (List.range' 0 n) d)) := by
  have h2 : os + n ≤ d.size := by omega
  have hno : ¬ (n > 0 ∧ ¬ (od + n ≤ os ∨ os + n ≤ od)) := fun h => h.2 (Or.inr hdis)
  simp only [Ptr.memcpy, InflateAlloc.space_get_heap, SH_bytes, Space.ro, Heap.isRo, Bool.false_eq_true,
    ↓reduceIte, h1, h2, and_self, true_and, hno]
  rw [ChunkMem.modify_heap _ _ d (SH_bytes H i z b st d), InflateDict.memcpy_loop]
  simp [SH, InflateInv.upd_upd]

theorem stored_block_SH {pbo : Nat} (hpb : st.pending_buf = .val (.ref (.heap b) pbo)) (h0 : 0 ≤ st.bi_valid.toInt)
    (h64 : st.bi_valid.toInt < 64) (buf : BPtr) (len : UInt32)
    (hbuf : (buf = .null ∧ len = 0) ∨ ∃ os, buf = .ref (.heap b) os ∧ os + len.toNat ≤ pbo)
    (hroom : pbo + st.pending.toNat + len.toNat + 16 ≤ d.size) (hp : st.pending.toNat + len.toNat + 64 < 2 ^ 32)
    (last : Int32) :
    Sat (SH H i z b st d) (ZlibNg.Trees.zng_tr_stored_block (some b) buf len last)
      (fun _ H' => EPost H i z b st d pbo (storedRoom st len) H') := by
  have hsr : storedRoom st len = len.toNat + (st.bi_valid.toInt.toNat + 42) / 8 := rfl
  unfold ZlibNg.Trees.zng_tr_stored_block
  have hl := last.toInt_lt
  refine Sat.bind (Sat.mono (emit_tree_SH hpb h0 h64 (by omega) (by omega) _ last (by decide) (by decide)
    (by show 2 * (0 : Int32).toInt + last.toInt < _; simp; omega)) ?_)
  rintro _ _ ⟨np, bb, bv, d1, rfl, w1, hacc1, hbv1, hle1, hge1⟩
  have e1 := toInt32_toInt bv hbv1
  unfold ZlibNg.TreesEmit.zng_tr_emit_align
  refine Sat.bind (Sat.mono (windup_SH (pbo := pbo) (by exact hpb) (by dsimp only; omega) (by dsimp only; omega)
    (by dsimp only; rw [w1.1]; omega) (by dsimp only; omega)) ?_)
  rintro _ _ ⟨np2, bu, d2, rfl, w2, hle2, hge2⟩
  dsimp only at w2 hle2 hge2
  rw [e1] at hge2
  have hb2 : np2.toNat * 8 ≤ st.pending.toNat * 8 + st.bi_valid.toInt.toNat + 10 := by
    have e7 : ((bv.toNat : Int) + 7).toNat = bv.toNat + 7 := by omega
    rw [e7] at hge2; omega
  refine Sat.bind (Sat.mono (put_short_SH (pbo := pbo) (by exact hpb) _ (by dsimp only; rw [w2.1, w1.1]; omega)) ?_)
  rintro _ _ ⟨d3, rfl, w3⟩
  have hp3 : (np2 + 2).toNat = np2.toNat + 2 := add_toNat _ 2 (by decide) (by omega)
  refine Sat.bind (Sat.mono (put_short_SH (pbo := pbo) (by exact hpb) _
    (by dsimp only; rw [hp3, w3.1, w2.1, w1.1]; omega)) ?_)
  rintro _ _ ⟨d4, rfl, w4⟩
  dsimp only at w3 w4
  rw [hp3] at w4
  have hp4 : (np2 + 2 + 2).toNat = np2.toNat + 4 := by
    have := add_toNat (np2 + 2) 2 (by decide) (by omega); rw [hp3] at this; exact this
  have hs4 : d4.size = d.size := by rw [w4.1, w3.1, w2.1, w1.1]
  have w14 : WrIn d (pbo + st.pending.toNat) (pbo + (np2.toNat + 4)) d4 :=
    (WrIn.cat (WrIn.cat (WrIn.cat w1 w2 (by omega) (by omega)) w3 (by omega) (by omega)) w4 (by omega) (by omega)).widen (Nat.le_refl _)
      (by omega)
  have hz0 : (0 : Int32).toInt.toNat = 0 := rfl
  by_cases hz : len = 0
  · subst hz
    have hc : ¬ ((0 : UInt32) != 0) = true := by decide
    rw [ite_f hc]
    refine Sat.pure ⟨_, d4, rfl, by dsimp only; rw [hp4]; exact w14, rfl, rfl, by dsimp only; omega,
      by dsimp only; rw [hp4, hz0, hsr, UInt32.toNat_zero]; omega,
      show 0 ≤ (0 : Int32).toInt by decide, show (0 : Int32).toInt < 64 by decide⟩
  · have hc : (len != 0) = true := by simpa using hz
    simp only [hc, ↓reduceIte]
    have hl0 : len.toNat ≠ 0 := fun e => hz (UInt32.toNat_inj.mp (by rw [e]; rfl))
    obtain ⟨os, rfl, hos⟩ : ∃ os, buf = .ref (.heap b) os ∧ os + len.toNat ≤ pbo := by
      rcases hbuf with ⟨-, e⟩ | h
      · exact absurd e hz
      · exact h
    refine Sat.bind (Sat.of_eq (rdD_SH _) ?_); try dsimp only
    refine Sat.bind (Sat.of_eq (ival_get hpb _) ?_)
    refine Sat.bind (Sat.of_eq (rdD_SH _) ?_); try dsimp only
    refine Sat.bind (Sat.of_eq (addI_SH _ (by omega) (by rw [hp4]; omega)) ?_)
    rw [show ((pbo : Int) + ((np2 + 2 + 2).toNat : Int)).toNat = pbo + (np2 + 2 + 2).toNat by omega]
    refine Sat.bind (Sat.of_eq (memcpy_SH (by rw [hp4]; omega) (by rw [hp4]; omega)) ?_)
    refine Sat.of_eq (wrD_SH _) ?_
    have hp5 : (np2 + 2 + 2 + len).toNat = np2.toNat + 4 + len.toNat := by
      rw [UInt32.toNat_add, hp4]; omega
    have wc := copy_wrin d4 (pbo + (np2 + 2 + 2).toNat) os len.toNat
    have w15 : WrIn d (pbo + st.pending.toNat) (pbo + (np2.toNat + 4 + len.toNat)) _ :=
      WrIn.cat w14 (wc.widen (by omega) (by omega)) (by omega) (by omega)
    refine ⟨_, _, rfl, by dsimp only; rw [hp5]; exact w15, rfl, rfl, by dsimp only; omega,
      by dsimp only; rw [hp5, hz0, hsr]; omega, show 0 ≤ (0 : Int32).toInt by decide,
      show (0 : Int32).toInt < 64 by decide⟩

end

/-! ## The emitters as `EmitOk`: the fields of `TreesFacts` except `flush_block` -/

section
variable (s : StreamPtr) (b : Nat)

theorem emit_lit_ok (c : UInt32) (hc : c < 256) :
    EmitOk s b (fun _ => True) (fun _ => 16) (fun _ => 16)
      (ZlibNg.TreesEmit.zng_tr_emit_lit (some b) ZlibNg.DeflateQuick.static_ltree_p c) :=
  emit_of (fun _ => Nat.le_refl _) fun _ _ _ _ _ _ W _ hr =>
    emit_lit_SH W (by omega) c (by have := UInt32.lt_iff_toNat_lt.mp hc; simpa using this)

theorem emit_lit_shape (c : UInt32) (hc : c < 256) :
    EmitShape s b (fun _ => True) (fun _ => 16)
      (ZlibNg.TreesEmit.zng_tr_emit_lit (some b) ZlibNg.DeflateQuick.static_ltree_p c) :=
  shape_of (grow := (fun _ => 16)) fun _ _ _ _ _ _ W _ hr =>
    emit_lit_SH W (by omega) c (by have := UInt32.lt_iff_toNat_lt.mp hc; simpa using this)

theorem emit_dist_ok (lc dist : UInt32) (hlc : lc ≤ 255) (hd1 : 1 ≤ dist) (hd2 : dist ≤ 32768) :
    EmitOk s b (fun _ => True) (fun _ => 16) (fun _ => 16)
      (ZlibNg.TreesEmit.zng_tr_emit_dist (some b) ZlibNg.DeflateQuick.static_ltree_p
        ZlibNg.DeflateQuick.static_dtree_p lc dist) :=
  emit_of (fun _ => Nat.le_refl _) fun _ _ _ _ _ _ W _ hr => by
    have := W.pad; have := W.lb
    exact emit_dist_SH W.hpb W.v0 W.v64 (by omega) (by omega) lc dist
      (by have := UInt32.le_iff_toNat_le.mp hlc; simp at this; omega)
      (by have := UInt32.le_iff_toNat_le.mp hd1; simpa using this)
      (by have := UInt32.le_iff_toNat_le.mp hd2; simpa using this)

theorem emit_dist_shape (lc dist : UInt32) (hlc : lc ≤ 255) (hd1 : 1 ≤ dist) (hd2 : dist ≤ 32768) :
    EmitShape s b (fun _ => True) (fun _ => 16)
      (ZlibNg.TreesEmit.zng_tr_emit_dist (some b) ZlibNg.DeflateQuick.static_ltree_p
        ZlibNg.DeflateQuick.static_dtree_p lc dist) :=
  shape_of (grow := (fun _ => 16)) fun _ _ _ _ _ _ W _ hr => by
    have := W.pad; have := W.lb
    exact emit_dist_SH W.hpb W.v0 W.v64 (by omega) (by omega) lc dist
      (by have := UInt32.le_iff_toNat_le.mp hlc; simp at this; omega)
      (by have := UInt32.le_iff_toNat_le.mp hd1; simpa using this)
      (by have := UInt32.le_iff_toNat_le.mp hd2; simpa using this)

theorem emit_tree_ok (last : Int32) (_h0 : 0 ≤ last) (h1 : last ≤ 1) :
    EmitOk s b (fun _ => True) (fun _ => 16) (fun _ => 16)
      (ZlibNg.TreesEmit.zng_tr_emit_tree (some b) ZlibNg.Trees.STATIC_TREES last) :=
  emit_of (fun _ => Nat.le_refl _) fun _ _ _ _ _ _ W _ hr => by
    have := W.pad; have := W.lb; have := W.v64
    have hl := Int32.le_iff_toInt_le.mp h1
    exact Sat.mono (emit_tree_SH W.hpb W.v0 W.v64 (by omega) (by omega) _ last (by decide) (by decide)
      (by show 2 * (1 : Int32).toInt + last.toInt < _; simp at hl ⊢; omega))
      fun _ _ q => q.epost (by omega)

theorem emit_tree_shape (last : Int32) (_h0 : 0 ≤ last) (h1 : last ≤ 1) :
    EmitShape s b (fun _ => True) (fun _ => 16)
      (ZlibNg.TreesEmit.zng_tr_emit_tree (some b) ZlibNg.Trees.STATIC_TREES last) :=
  shape_of (grow := (fun _ => 16)) fun _ _ _ _ _ _ W _ hr => by
    have := W.pad; have := W.lb; have := W.v64
    have hl := Int32.le_iff_toInt_le.mp h1
    exact Sat.mono (emit_tree_SH W.hpb W.v0 W.v64 (by omega) (by omega) _ last (by decide) (by decide)
      (by show 2 * (1 : Int32).toInt + last.toInt < _; simp at hl ⊢; omega))
      fun _ _ q => q.epost (by omega)

theorem emit_end_block_ok (last : Int32) :
    EmitOk s b (fun _ => True) (fun _ => 16) (fun _ => 16)
      (ZlibNg.TreesEmit.zng_tr_emit_end_block (some b) ZlibNg.DeflateQuick.static_ltree_p last) :=
  emit_of (fun _ => Nat.le_refl _) fun _ _ _ _ _ _ W _ hr => by
    have := W.pad; have := W.lb
    exact Sat.mono (end_block_SH W.hpb W.v0 W.v64 (by omega) (by omega) last) fun _ _ q => q.2

theorem emit_end_block_shape (last : Int32) :
    EmitShape s b (fun _ => True) (fun _ => 16)
      (ZlibNg.TreesEmit.zng_tr_emit_end_block (some b) ZlibNg.DeflateQuick.static_ltree_p last) :=
  shape_of (grow := (fun _ => 16)) fun _ _ _ _ _ _ W _ hr => by
    have := W.pad; have := W.lb
    exact Sat.mono (end_block_SH W.hpb W.v0 W.v64 (by omega) (by omega) last) fun _ _ q => q.2

theorem emit_align_ok : EmitOk s b (fun _ => True) (fun _ => 16) (fun _ => 16)
    (ZlibNg.TreesEmit.zng_tr_emit_align (some b)) :=
  emit_of (fun _ => Nat.le_refl _) fun _ _ _ _ _ _ W _ hr => by
    have := W.pad; have := W.lb; have := W.v0; have := W.v64
    exact Sat.mono (windup_SH W.hpb W.v0 W.v64 (by omega) (by omega))
      fun _ _ q => WDPost.epost rfl (WrIn.refl _ _ _) (Nat.le_refl _) (by omega) q

theorem emit_align_shape : EmitShape s b (fun _ => True) (fun _ => 16)
    (ZlibNg.TreesEmit.zng_tr_emit_align (some b)) :=
  shape_of (grow := (fun _ => 16)) fun _ _ _ _ _ _ W _ hr => by
    have := W.pad; have := W.lb; have := W.v0; have := W.v64
    exact Sat.mono (windup_SH W.hpb W.v0 W.v64 (by omega) (by omega))
      fun _ _ q => WDPost.epost rfl (WrIn.refl _ _ _) (Nat.le_refl _) (by omega) q

theorem align_ok : EmitOk s b (fun _ => True) (fun _ => 16) (fun _ => 16) (ZlibNg.Trees.zng_tr_align (some b)) :=
  emit_of (fun _ => Nat.le_refl _) fun _ _ _ _ _ _ W _ hr => by
    have := W.pad; have := W.lb
    exact align_SH W.hpb W.v0 W.v64 (by omega) (by omega)

theorem align_shape : EmitShape s b (fun _ => True) (fun _ => 16) (ZlibNg.Trees.zng_tr_align (some b)) :=
  shape_of (grow := (fun _ => 16)) fun _ _ _ _ _ _ W _ hr => by
    have := W.pad; have := W.lb
    exact align_SH W.hpb W.v0 W.v64 (by omega) (by omega)

theorem stored_block_ok (buf : BPtr) (len : UInt32) (last : Int32) :
    EmitOk s b (fun st => WindowBuf b st buf len) (fun st => storedRoom st len) (fun st => storedRoom st len)
      (ZlibNg.Trees.zng_tr_stored_block (some b) buf len last) :=
  emit_of (fun _ => Nat.le_refl _) fun _ _ _ st _ pbo W hw hr => by
    have := W.pad; have := W.lb
    have hsr : storedRoom st len = len.toNat + (st.bi_valid.toInt.toNat + 42) / 8 := rfl
    refine stored_block_SH W.hpb W.v0 W.v64 buf len ?_ (by omega) (by omega) last
    rcases hw with h | ⟨wo, k, hwo, rfl, hk⟩
    · exact Or.inl h
    · exact Or.inr ⟨wo + k, rfl, by have := W.win wo hwo; omega⟩

theorem stored_block_shape (buf : BPtr) (len : UInt32) (last : Int32) :
    EmitShape s b (fun st => WindowBuf b st buf len) (fun st => storedRoom st len)
      (ZlibNg.Trees.zng_tr_stored_block (some b) buf len last) :=
  shape_of (grow := (fun st => storedRoom st len)) fun _ _ _ st _ pbo W hw hr => by
    have := W.pad; have := W.lb
    have hsr : storedRoom st len = len.toNat + (st.bi_valid.toInt.toNat + 42) / 8 := rfl
    refine stored_block_SH W.hpb W.v0 W.v64 buf len ?_ (by omega) (by omega) last
    rcases hw with h | ⟨wo, k, hwo, rfl, hk⟩
    · exact Or.inl h
    · exact Or.inr ⟨wo + k, rfl, by have := W.win wo hwo; omega⟩

end

end ZlibNgF.Proof.TreesEmitP
