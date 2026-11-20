import ZlibNgF.Proof.«deflate.c.reset»

/-!
# What `deflateInit2_` leaves for the gz write side (`ZlibNgF`)

`deflateInit2` changes the caller's stream record only in the fields it initialises (`msg`, `zalloc`, `opaque`,
`zfree`, and on success `state`, `total_in`, `total_out`, `data_type`, `adler`): the four buffer fields stay, and a
call that does not return `Z_OK` leaves `state` as it was (it returns before `strm->state = s`, or `alloc_deflate`
failed). On success the state is the fresh block `h.nextBlk`, with no `gz_header` registered; every other block keeps
its bytes, objects and saved pointer. The runs are those of `Proof/deflate.c.init.lean` (`tail_sat`, `decode_sat`,
`init2_sat`), repeated here with this post-condition (`TailPost`) in place of `InitPost`.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.DeflateGzInit
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate
open ZlibNgF.Proof.DeflateInit ZlibNgF.Proof.DeflateAlloc
open ZlibNgF.Proof.InflateInv (upd_upd ldStream_app)
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)

/-- The four buffer fields and the `state` field agree. -/
def BufKeep (z z' : ZStream) : Prop :=
  z'.next_in = z.next_in ∧ z'.avail_in = z.avail_in ∧ z'.next_out = z.next_out ∧ z'.avail_out = z.avail_out ∧
    z'.state = z.state

/-- What the part of `deflateInit2` after the allocator set-up leaves, from `h` with stream `i` set to `z1`: a failure
with only the stream record (and the allocation counter) changed, or success with the fresh block as the state. -/
def TailPost (h : Heap) (i : Nat) (z1 : ZStream) (r : Int32) (h' : Heap) : Prop :=
  (r ≠ Z_OK ∧ ∃ n, h' = { h with streams := upd h.streams i (some z1), nalloc := n }) ∨
  (r = Z_OK ∧ ∃ z' st, h'.streams i = some z' ∧
    (z'.next_in = z1.next_in ∧ z'.avail_in = z1.avail_in ∧ z'.next_out = z1.next_out ∧ z'.avail_out = z1.avail_out) ∧
    z'.state = some h.nextBlk ∧ h'.dstate h.nextBlk = some st ∧ st.gzhead = .val none ∧ h'.nextBlk = h.nextBlk + 1 ∧
    (∀ c, c ≠ h.nextBlk → h'.savedPtrs c = h.savedPtrs c ∧ h'.bytes c = h.bytes c ∧ h'.dstates c = h.dstates c ∧
      h'.dallocs c = h.dallocs c) ∧
    h'.istates = h.istates ∧ h'.iallocs = h.iallocs ∧ (∀ j, j ≠ i → h'.streams j = h.streams j))

theorem tail_shape {h : Heap} {i : Nat} (z1 : ZStream) (hza : z1.zalloc = .zcalloc) (hzf : z1.zfree = .zcfree)
    (level method wb ml strat wrap : Int32) (hw : wrap = 0 ∨ wrap = 1 ∨ wrap = 2) :
    SF (h.dstates h.nextBlk = none ∧ h.dallocs h.nextBlk = none) { h with streams := upd h.streams i (some z1) } (init2Tail (some i) level method wb ml strat wrap)
      (fun r h' => TailPost h i z1 r h') := by
  unfold init2Tail
  by_cases hc : (decide (ml < 1) || decide (ml > MAX_MEM_LEVEL) || method.toInt64.toUInt64 != Z_DEFLATED ||
      decide (wb < MIN_WBITS) || decide (wb > MAX_WBITS) || decide (level < 0) || decide (level > 9) ||
      decide (strat < 0) || decide (strat > Z_FIXED) || (wb == 8 && wrap != 1)) = true
  · rw [ite_t hc]
    exact SF.pure (Or.inl ⟨by decide, _, rfl⟩)
  rw [ite_f hc]
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, bne_iff_ne, ne_eq, Bool.and_eq_true, beq_iff_eq,
    not_and, Decidable.not_not] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hm1, hm9⟩, hmeth⟩, hw8⟩, hw15⟩, hl0⟩, hl9⟩, hs0⟩, hs4⟩, hw81⟩ := hc
  have tw8 := Int32.not_lt.mp hw8
  have tw15 := Int32.not_lt.mp hw15
  have tm1 := Int32.not_lt.mp hm1
  have tm9 := Int32.not_lt.mp hm9
  rw [Int32.le_iff_toInt_le] at tw8 tw15 tm1 tm9
  have e8 : (MIN_WBITS).toInt = 8 := rfl
  have e15 : (MAX_WBITS).toInt = 15 := rfl
  have e9 : (MAX_MEM_LEVEL).toInt = 9 := rfl
  have e1 : (1 : Int32).toInt = 1 := rfl
  rw [e8] at tw8; rw [e15] at tw15; rw [e9] at tm9; rw [e1] at tm1
  dsimp only
  obtain ⟨n, hn, hn1, hn2⟩ : ∃ n : Nat, (if (wb == 8) = true then (9 : Int32) else wb).toInt = n ∧ 9 ≤ n ∧ n ≤ 15 := by
    by_cases e : wb = 8
    · subst e; exact ⟨9, rfl, by omega, by omega⟩
    · have : (wb == 8) = false := by simpa using e
      rw [this]
      have : wb.toInt ≠ 8 := fun h' => e (Int32.toInt_inj.mp (by rw [h']; rfl))
      exact ⟨wb.toInt.toNat, by show wb.toInt = (wb.toInt.toNat : Int); omega, by omega, by omega⟩
  generalize (if (wb == 8) = true then (9 : Int32) else wb) = W at hn
  have hml : (ml + 6).toInt = (ml.toInt.toNat + 6 : Nat) := by
    rw [Int32.toInt_add]; rw [Int.bmod_eq_of_le (by have : (6 : Int32).toInt = 6 := rfl; omega)
      (by have : (6 : Int32).toInt = 6 := rfl; omega)]
    have : (6 : Int32).toInt = 6 := rfl
    omega
  rw [shl1_eq (ml + 6) _ hml (by omega), pure_bind_M]
  have pl1 : 2 ^ 7 ≤ 2 ^ (ml.toInt.toNat + 6) := Nat.pow_le_pow_right (by omega) (by omega)
  have pl2 : 2 ^ (ml.toInt.toNat + 6) ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) (by omega)
  have pl3 : 2 ^ (ml.toInt.toNat + 6) % 16 = 0 := by
    have : 2 ^ (ml.toInt.toNat + 6) = 2 ^ (ml.toInt.toNat + 2) * 2 ^ 4 := by rw [← Nat.pow_add]
    rw [this]; simp
  have pl4 : ∃ k, 7 ≤ k ∧ k ≤ 15 ∧ 2 ^ (ml.toInt.toNat + 6) = 2 ^ k := ⟨_, by omega, by omega, rfl⟩
  have hl := i32_ofNat_toInt (k := 2 ^ (ml.toInt.toNat + 6)) (by omega)
  generalize 2 ^ (ml.toInt.toNat + 6) = l at *
  cases hok : h.allocOk h.nalloc
  · refine Or.inl ?_
    refine Sat.bind (Sat.of_eq (alloc_fail (h := { h with streams := upd h.streams i (some z1) }) (z := z1)
      (by simp) hza hok W (Int32.ofNat l) n l hn hn1 hn2 hl pl1 pl2 pl3) ?_)
    exact Sat.pure (Or.inl ⟨by decide, _, rfl⟩)
  by_cases hfr : ¬ (h.dstates h.nextBlk = none ∧ h.dallocs h.nextBlk = none)
  · refine Or.inr ⟨hfr, Fl.bind_now (alloc_fault (h := { h with streams := upd h.streams i (some z1) }) (z := z1)
      (by simp) hza hok ?_ W (Int32.ofNat l) n l hn hn1 hn2 hl pl1 pl2 pl3)⟩
    by_cases a : h.dstates h.nextBlk = none
    · exact Or.inr (fun b => hfr ⟨a, b⟩)
    · exact Or.inl a
  obtain ⟨hfs, hfa⟩ := Classical.not_not.mp hfr
  refine Or.inl ?_
  refine Sat.bind (Sat.mono (alloc_ok (h := { h with streams := upd h.streams i (some z1) }) (z := z1) (by simp) hza
    hfs hfa hok W (Int32.ofNat l) n l hn hn1 hn2 hl pl1 pl2 pl3) ?_)
  rintro _ _ ⟨rfl, d, rfl, hdsz, hdz⟩
  have ⟨g1, g2, g3⟩ := garbage_sizes (h.garbage (2 ^ 43 + h.nextBlk))
  have gs := garbage_scratch (h.garbage (2 ^ 43 + h.nextBlk))
  simp only [gState] at *
  generalize DeflateState.garbage (h.garbage (2 ^ 43 + h.nextBlk)) = g0 at *
  rw [AH_SH]
  simp only [show (some h.nextBlk == none) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  have hY : (AH { h with streams := upd h.streams i (some z1) } d (upd h.dallocs h.nextBlk (some
      (dAllocRec h.nextBlk (PADSZ (h.baseAddr (.heap h.nextBlk)) 64).toNat (dWS (2 ^ n)) (2 ^ n) z1.zfree)))
      h.dstates).dallocs h.nextBlk = some (dAllocRec h.nextBlk (PADSZ (h.baseAddr (.heap h.nextBlk)) 64).toNat
        (dWS (2 ^ n)) (2 ^ n) z1.zfree) := by rw [AH_dallocs]; exact upd_same _ _ _
  sstep ldDAllocs_SH hY
  simp only [dAllocRec, Ival.get, pure_bind_M]
  sstep wrD_SH _
  sstep ldDAllocs_SH hY
  simp only [dAllocRec, pure_bind_M]
  sstep wrD_SH _
  sstep ldDAllocs_SH hY
  simp only [dAllocRec, pure_bind_M]
  sstep wrD_SH _
  sstep ldDAllocs_SH hY
  simp only [dAllocRec, pure_bind_M]
  sstep wrD_SH _
  sstep ldDAllocs_SH hY
  simp only [dAllocRec, pure_bind_M]
  sstep wrD_SH _
  sstep wrZ_SH _
  sstep wrD_SH _
  sstep wrD_SH _
  sstep wrD_SH _
  rw [shl1_eq W n hn (by omega), pure_bind_M]
  sstep wrD_SH _
  sstep wrD_SH _
  sstep wrD_SH _
  sstep wrD_SH _
  sstep ldDState_SH
  simp only [pure_bind_M]
  have hl32 : (Int32.ofNat l).toUInt32.toNat = l := by
    rw [Int32.toNat_toUInt32_of_le (by rw [Int32.le_iff_toInt_le, hl]; simp)]
    show (Int32.ofNat l).toInt.toNat = l
    rw [hl]; simp
  rw [hl32]
  sstep add_SH l (by omega)
  sstep add_SH 8 (by omega)
  sstep wrD_SH _
  sstep wrD_SH _
  sstep wrD_SH _
  sstep wrD_SH _
  sstep wrD_SH _
  sstep wrD_SH _
  refine Sat.mono (reset_SH (pb := .ref (.heap h.nextBlk)
      ((PADSZ (h.baseAddr (BRef.heap h.nextBlk)) 64).toNat + dWS (2 ^ n) + 2 * 2 ^ n + 131072))
    (ho := (PADSZ (h.baseAddr (BRef.heap h.nextBlk)) 64).toNat + dWS (2 ^ n) + 2 * 2 ^ n)
    ⟨by simp [hza], by simp [hzf], rfl, ⟨_, rfl⟩, rfl, by show INIT_STATE ≤ INIT_STATE; decide,
      by show INIT_STATE ≤ MAX_STATE; decide⟩ (by simpa using hw) rfl
    (by simpa using g1) (by simpa using g2) (by simpa using g3) rfl (by omega) ?_ ?_ ?_) ?_
  · exact Int32.not_lt.mp hl0
  · exact Int32.not_lt.mp hl9
  · have p9 : 2 ^ 9 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn1
    have p15 : 2 ^ n ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) hn2
    have hw32 : (Int32.ofNat (2 ^ n)).toUInt32.toNat = 2 ^ n := wsize_toNat n hn2
    refine ⟨?_, ?_, ?_, ?_, ⟨_, _, _, _, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · simp only [hw32]; omega
    · simp only [hl32]; omega
    · simp only [UInt32.toNat_mul, hl32]; simp; omega
    · simp only [UInt32.toNat_mul, UInt32.toNat_sub_of_le _ _ (lb_one_le l hl32 (by omega)), hl32]; simp; omega
    · simp only [wbuf_toNat _ (by rw [hw32]; omega), hw32]; omega
    · simp only [hw32]; omega
    · omega
    · simp only [hl32]; omega
    · simp only [hl32]
    · exact ⟨Int32.not_lt.mp hs0, Int32.not_lt.mp hs4⟩
  rintro r H' ⟨rfl, A, B, C, c, lm, ib, hib, d', rfl, -⟩
  refine Or.inr ⟨rfl, _, _, SH_streams _ _ _ _ _ _, by simp [rkZ], by simp [rkZ], SH_dstate _ _ _ _ _ _,
    by simp [lmS, trS, rkS], by simp [SH, AH], fun c hc => ?_, rfl, rfl, fun j hj => ?_⟩
  · simp [SH, AH, upd_ne _ _ _ _ hc]
  · simp [SH, AH, upd_ne _ _ _ _ hj]


theorem decode_shape {h : Heap} {i : Nat} (z1 : ZStream) (hza : z1.zalloc = .zcalloc) (hzf : z1.zfree = .zcfree)
    (level method wb ml strat : Int32) :
    SF (h.dstates h.nextBlk = none ∧ h.dallocs h.nextBlk = none) { h with streams := upd h.streams i (some z1) } (do
        let (wrap, windowBits, bad) ←
          if wb < 0 then do
            if wb < -MAX_WBITS then pure (0, wb, true)
            else pure ((0 : Int32), ← chkI32 (-wb.toInt), false)
          else if wb > MAX_WBITS then pure (2, wb - 16, false)
          else pure ((1 : Int32), wb, false)
        if bad then return Z_STREAM_ERROR
        init2Tail (some i) level method windowBits ml strat wrap : M Int32)
      (fun r h' => TailPost h i z1 r h') := by
  dsimp only
  by_cases h1 : wb < 0
  · rw [ite_t h1]
    by_cases h2 : wb < -MAX_WBITS
    · rw [ite_t h2]
      refine SF.bind_sat (Sat.of_eq rfl ?_)
      exact SF.pure (Or.inl ⟨by decide, _, rfl⟩)
    · rw [ite_f h2]
      have t1 := Int32.lt_iff_toInt_lt.mp h1
      have t2 := Int32.not_lt.mp h2
      rw [Int32.le_iff_toInt_le] at t2
      have e15 : (-MAX_WBITS).toInt = -15 := rfl
      rw [e15] at t2
      have t1' : wb.toInt < 0 := by simpa using t1
      have ec : (Int32.ofInt (-wb.toInt)).toInt = -wb.toInt := by
        have : Int32.size = 4294967296 := rfl
        rw [Int32.toInt_ofInt, this]; exact Int.bmod_eq_of_le (by omega) (by omega)
      rw [chk_eq (Int32.ofInt (-wb.toInt)) ec, pure_bind_M]
      refine SF.bind_sat (Sat.of_eq rfl ?_)
      exact (tail_shape z1 hza hzf level method _ ml strat 0 (Or.inl rfl))
  · rw [ite_f h1]
    by_cases h2 : wb > MAX_WBITS
    · rw [ite_t h2]
      refine SF.bind_sat (Sat.of_eq rfl ?_)
      exact (tail_shape z1 hza hzf level method _ ml strat 2 (Or.inr (Or.inr rfl)))
    · rw [ite_f h2]
      refine SF.bind_sat (Sat.of_eq rfl ?_)
      exact (tail_shape z1 hza hzf level method _ ml strat 1 (Or.inr (Or.inl rfl)))

theorem init2_shape {h : Heap} {i : Nat} {z : ZStream} (hz : h.streams i = some z)
    (hza : z.zalloc = .null ∨ z.zalloc = .zcalloc) (hzf : z.zfree = .null ∨ z.zfree = .zcfree)
    (level method wb ml strat : Int32) :
    SF (h.dstates h.nextBlk = none ∧ h.dallocs h.nextBlk = none) h (deflateInit2 (some i) level method wb ml strat)
      (fun r h' => ∃ z1, BufKeep z z1 ∧ z1.zalloc = .zcalloc ∧ z1.zfree = .zcfree ∧ TailPost h i z1 r h') := by
  rw [init2_eq]
  simp only [show (some i == none) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  try dsimp only
  refine SF.bind_sat (Sat.of_eq (wrZ_app hz _) ?_)
  refine SF.bind_sat (Sat.of_eq (rdZ_upd _) ?_)
  dsimp only
  rcases hza with ha | ha <;> rcases hzf with hf | hf
  · simp only [ha, show (FnPtr.null == FnPtr.null) = true from rfl, ↓reduceIte]
    refine SF.bind_sat (Sat.of_eq (wrZ_upd _) ?_)
    refine SF.bind_sat (Sat.of_eq (wrZ_upd _) ?_)
    refine SF.bind_sat (Sat.of_eq (rdZ_upd _) ?_)
    dsimp only
    simp only [hf, show (FnPtr.null == FnPtr.null) = true from rfl, ↓reduceIte]
    refine SF.bind_sat (Sat.of_eq (wrZ_upd _) ?_)
    refine SF.mono (decode_shape _ (by simp) (by simp) _ method wb ml strat) ?_
    exact fun r h' p => by refine ⟨_, ?_, ?_, ?_, p⟩ <;> first | exact ⟨rfl, rfl, rfl, rfl, rfl⟩ | rfl | exact ha | exact hf | simp [ha, hf]
  · simp only [ha, show (FnPtr.null == FnPtr.null) = true from rfl, ↓reduceIte]
    refine SF.bind_sat (Sat.of_eq (wrZ_upd _) ?_)
    refine SF.bind_sat (Sat.of_eq (wrZ_upd _) ?_)
    refine SF.bind_sat (Sat.of_eq (rdZ_upd _) ?_)
    dsimp only
    simp only [hf, show (FnPtr.zcfree == FnPtr.null) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    refine SF.mono (decode_shape _ (by simp) (by simp) _ method wb ml strat) ?_
    exact fun r h' p => by refine ⟨_, ?_, ?_, ?_, p⟩ <;> first | exact ⟨rfl, rfl, rfl, rfl, rfl⟩ | rfl | exact ha | exact hf | simp [ha, hf]
  · simp only [ha, show (FnPtr.zcalloc == FnPtr.null) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    refine SF.bind_sat (Sat.of_eq (rdZ_upd _) ?_)
    dsimp only
    simp only [hf, show (FnPtr.null == FnPtr.null) = true from rfl, ↓reduceIte]
    refine SF.bind_sat (Sat.of_eq (wrZ_upd _) ?_)
    refine SF.mono (decode_shape _ (by simp) (by simp) _ method wb ml strat) ?_
    exact fun r h' p => by refine ⟨_, ?_, ?_, ?_, p⟩ <;> first | exact ⟨rfl, rfl, rfl, rfl, rfl⟩ | rfl | exact ha | exact hf | simp [ha, hf]
  · simp only [ha, show (FnPtr.zcalloc == FnPtr.null) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    refine SF.bind_sat (Sat.of_eq (rdZ_upd _) ?_)
    dsimp only
    simp only [hf, show (FnPtr.zcfree == FnPtr.null) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    refine SF.mono (decode_shape _ (by simp) (by simp) _ method wb ml strat) ?_
    exact fun r h' p => by refine ⟨_, ?_, ?_, ?_, p⟩ <;> first | exact ⟨rfl, rfl, rfl, rfl, rfl⟩ | rfl | exact ha | exact hf | simp [ha, hf]

/-! ## `deflateReset` on an invariant stream -/

open ZlibNgF.Proof.DeflateInv (DInv live DLive DCore) in
open ZlibNgF.Proof.DeflateReset (rlay_of resetKeep_neg SH_self) in
/-- `deflateReset` on a stream with the invariant changes only the stream record (not its buffer fields nor `state`)
and the state block's bytes and `deflate_state`, which then has no `gz_header` registered. -/
theorem reset_shape {h : Heap} {s : StreamPtr} (hv : DInv h s) :
    ∃ i z b, s = some i ∧ h.streams i = some z ∧ z.state = some b ∧
      Sat h (deflateReset s) (fun _ h' => ∃ z' st' d', h' = SH h i z' b st' d' ∧ BufKeep z z' ∧
        st'.gzhead = .val none) := by
  obtain ⟨i, z, b, st, al, rfl, L, hal, c⟩ := live hv
  obtain ⟨pb, hpb⟩ := c.pbuf
  obtain ⟨ho, d, hd, hh, hho⟩ := c.head
  refine ⟨i, z, b, rfl, L.hz, L.hb, ?_⟩
  have k : DOk i z b st := ⟨L.za, L.zf, L.hb, L.ab, L.sm, L.lo, L.hi⟩
  by_cases hn : st.wrap = -1 ∨ st.wrap = -2
  · obtain ⟨w, hw⟩ : ∃ w : Int32, (st.wrap = -1 ∧ w = 1) ∨ (st.wrap = -2 ∧ w = 2) := by
      rcases hn with e | e
      · exact ⟨1, Or.inl ⟨e, rfl⟩⟩
      · exact ⟨2, Or.inr ⟨e, rfl⟩⟩
    have hw3 : w = 1 ∨ w = 2 := by rcases hw with ⟨-, e⟩ | ⟨-, e⟩ <;> simp [e]
    have k' : DOk i z b { st with wrap := w } := ⟨k.za, k.zf, k.hb, k.ab, k.sm, k.lo, k.hi⟩
    have R := rlay_of c hd
    have R' : RLay b { st with wrap := w } d.size := ⟨R.ws, R.lb, R.pbs, R.se, R.lay, R.strat⟩
    have S := reset_SH (H := h) k' (by rcases hw3 with e | e <;> simp [e]) hpb c.trees.1 c.trees.2.1 c.trees.2.2
      hh hho c.level.1 c.level.2 R'
    have e0 : deflateReset (some i) (SH h i z b st d) = deflateReset (some i) (SH h i z b { st with wrap := w } d) := by
      unfold deflateReset; rw [bind_app, bind_app, resetKeep_neg k hpb w hw]
    obtain ⟨r0, h0, e1, q⟩ := S
    rw [← e0, SH_self L.hz L.hst hd] at e1
    refine ⟨r0, h0, e1, ?_⟩
    obtain ⟨-, A, B, C, cf, lm, ib, -, d', rfl, -⟩ := q
    exact ⟨_, _, d', rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, by simp [lmS, trS, rkS]⟩
  · have hw : st.wrap = 0 ∨ st.wrap = 1 ∨ st.wrap = 2 := by
      rcases c.wrap with e | e | e | e | e
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr e)
      · exact absurd (Or.inl e) hn
      · exact absurd (Or.inr e) hn
    have S := reset_SH (H := h) k hw hpb c.trees.1 c.trees.2.1 c.trees.2.2 hh hho c.level.1 c.level.2 (rlay_of c hd)
    rw [SH_self L.hz L.hst hd] at S
    refine Sat.mono S ?_
    rintro r h' ⟨-, A, B, C, cf, lm, ib, -, d', rfl, -⟩
    exact ⟨_, _, d', rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, by simp [lmS, trS, rkS]⟩

/-! ## The statements of the gz write side

`BufSameL` and `DKeepL` are `GzWriteNeeds.BufSame` and `GzWriteNeeds.DKeep` (`Proof/gzwrite.c.needs.lean`), repeated
here so that this file does not depend on the gz layer; `Proof/deflate.c.gz.lean` states the results with those. -/

/-- `GzWriteNeeds.BufSame`. -/
def BufSameL (z z' : ZStream) : Prop :=
  z'.next_in = z.next_in ∧ z'.avail_in = z.avail_in ∧ z'.next_out = z.next_out ∧ z'.avail_out = z.avail_out ∧
    z'.state = z.state

/-- `GzWriteNeeds.DKeep`. -/
def DKeepL (h h' : Heap) (s : StreamPtr) : Prop :=
  (∀ c, c < h.nextBlk → (∀ z, StreamAt h s z → z.state ≠ some c) → h'.savedPtrs c = h.savedPtrs c) ∧
  (DFreshBlocks h → DFreshBlocks h') ∧
  (∀ hp, DRegisteredHeader h' s hp → hp = none ∨ DRegisteredHeader h s hp)

theorem dkeep_refl (h : Heap) (s : StreamPtr) : DKeepL h h s :=
  ⟨fun _ _ _ => rfl, id, fun _ hp => Or.inr hp⟩

theorem add_same {p : BPtr} {k : Int} {h h1 : Heap} {q : BPtr} (e : Ptr.add p k h = .ok (q, h1)) : h1 = h := by
  unfold Ptr.add at e
  (repeat' split at e) <;> first | (cases e; rfl) | cases e

theorem load_same {p : BPtr} {h h1 : Heap} {v : UInt8} (e : (Ptr.load p : M UInt8) h = .ok (v, h1)) : h1 = h := by
  unfold Ptr.load at e
  (repeat' split at e) <;> first | (cases e; rfl) | cases e

/-- `CHECK_VER_STSIZE` only reads. -/
theorem checkVer_same {version : BPtr} {size : Int32} {h h1 : Heap} {c : Bool}
    (e : CHECK_VER_STSIZE version size h = .ok (c, h1)) : h1 = h := by
  unfold CHECK_VER_STSIZE index8 Ptr.index at e
  split at e
  · cases e; rfl
  · simp only [bind_app] at e
    rcases ha : Ptr.add version 0 h with _ | ⟨q, h2⟩ <;> rw [ha] at e
    · cases e
    rw [← add_same ha]
    dsimp only at e
    rcases hl : (Ptr.load q : M UInt8) h2 with _ | ⟨v, h3⟩ <;> rw [hl] at e
    · cases e
    rw [← load_same hl]
    dsimp only at e
    split at e <;> (cases e; rfl)

/-- **`deflateInit2_` for the gz write side** (the first part of `GzWriteNeeds.DeflateGz`). -/
theorem init2_gz (h h' : Heap) (s : StreamPtr) (level method wb ml strat : Int32) (version : BPtr) (size r : Int32)
    (z : ZStream) (hz : StreamAt h s z) (hi : DInitReady h s) (hfr : DFreshBlocks h)
    (e : C.run (deflateInit2_ s level method wb ml strat version size) h = .ok (r, h')) :
    ∃ z', StreamAt h' s z' ∧ z'.next_in = z.next_in ∧ z'.avail_in = z.avail_in ∧ z'.next_out = z.next_out ∧
      z'.avail_out = z.avail_out ∧
      (r ≠ Z_OK → z'.state = z.state ∧ (z'.zalloc = .null ∨ z'.zalloc = .zcalloc) ∧
        (z'.zfree = .null ∨ z'.zfree = .zcfree)) ∧ DKeepL h h' s ∧
      (r = Z_OK → ∃ sb, z'.state = some sb ∧ h.nextBlk ≤ sb) := by
  obtain ⟨i, rfl, hzi⟩ := hz
  obtain ⟨hza, hzf⟩ : (z.zalloc = .null ∨ z.zalloc = .zcalloc) ∧ (z.zfree = .null ∨ z.zfree = .zcfree) := by
    rcases hi with h0 | ⟨z0, ⟨i0, e0, hz0⟩, ha, hf⟩
    · cases h0
    · obtain rfl := Option.some.inj e0
      obtain rfl := Option.some.inj (hz0.symm.trans hzi)
      exact ⟨ha, hf⟩
  simp only [C.run, deflateInit2_, bind_app] at e
  rcases hc : CHECK_VER_STSIZE version size h with x | ⟨c, h1⟩
  · rw [hc] at e; cases e
  rw [hc] at e
  rw [checkVer_same hc] at e
  cases c
  · simp only [Bool.false_eq_true, ↓reduceIte] at e
    obtain ⟨r2, h2, e2, z1, hk, ha1, hf1, post⟩ :=
      (init2_shape hzi hza hzf level method wb ml strat).sat (hfr.2 _ (Nat.le_refl _))
    rw [e] at e2
    obtain ⟨rfl, rfl⟩ : r = r2 ∧ h' = h2 := by simpa using e2
    obtain ⟨k1, k2, k3, k4, k5⟩ := hk
    rcases post with ⟨hr, n, rfl⟩ | ⟨rfl, z', st, hz', ⟨f1, f2, f3, f4⟩, hst, hds, hgz, hnb, hoth, his, hia, hstr⟩
    · refine ⟨z1, ⟨i, rfl, upd_same _ _ _⟩, k1, k2, k3, k4, fun _ => ⟨k5, Or.inr ha1, Or.inr hf1⟩,
        ⟨fun _ _ _ => rfl, fun f => f, fun hp hreg => Or.inr ?_⟩, fun e => absurd e hr⟩
      obtain ⟨b, st, ⟨⟨z2, ⟨i2, e2, e3⟩, e4⟩, e5⟩, e6⟩ := hreg
      obtain rfl := Option.some.inj e2
      simp only [upd_same] at e3
      obtain rfl := Option.some.inj e3
      exact ⟨b, st, ⟨⟨z, ⟨i, rfl, hzi⟩, by rw [← k5]; exact e4⟩, e5⟩, e6⟩
    · refine ⟨z', ⟨i, rfl, hz'⟩, f1.trans k1, f2.trans k2, f3.trans k3, f4.trans k4, fun e => absurd rfl e,
        ⟨fun c hc _ => (hoth c (Nat.ne_of_lt hc)).1, fun f => ⟨fun b hb => ?_, fun b hb => ?_⟩, fun hp hreg => ?_⟩,
        fun _ => ⟨_, hst, Nat.le_refl _⟩⟩
      · have hne : b ≠ h.nextBlk := by omega
        rw [his, hia, (hoth b hne).2.1]; exact f.1 b (by omega)
      · have hne : b ≠ h.nextBlk := by omega
        rw [(hoth b hne).2.2.1, (hoth b hne).2.2.2]; exact f.2 b (by omega)
      · obtain ⟨b, st2, ⟨⟨z2, ⟨i2, e2, e3⟩, e4⟩, e5⟩, e6⟩ := hreg
        obtain rfl := Option.some.inj e2
        obtain rfl := Option.some.inj (e3.symm.trans hz')
        obtain rfl := Option.some.inj (e4.symm.trans hst)
        obtain rfl := Option.some.inj (e5.symm.trans hds)
        rw [hgz] at e6
        exact Or.inl (Ival.val.inj e6).symm
  · simp only [↓reduceIte, pure_app] at e
    obtain ⟨rfl, rfl⟩ : Z_VERSION_ERROR = r ∧ h = h' := by simpa using e
    exact ⟨z, ⟨i, rfl, hzi⟩, rfl, rfl, rfl, rfl, fun _ => ⟨rfl, hza, hzf⟩, dkeep_refl _ _, fun e => absurd e (by decide)⟩

open ZlibNgF.Proof.DeflateInv (DInv live) in
/-- **`deflateReset` for the gz write side** (the second part of `GzWriteNeeds.DeflateGz`). -/
theorem reset_gz (h h' : Heap) (s : StreamPtr) (r : Int32) (z : ZStream) (hv : DInv h s) (hz : StreamAt h s z)
    (e : C.run (deflateReset s) h = .ok (r, h')) : ∃ z', StreamAt h' s z' ∧ BufSameL z z' ∧ DKeepL h h' s := by
  obtain ⟨i, z0, b, st, al, rfl, L, -, -⟩ := live hv
  obtain ⟨i1, z1, b1, e1, hz1, hb1, r0, h0, e0, z', st', d', rfl, hk, hg⟩ := reset_shape hv
  have ei : i = i1 := Option.some.inj e1
  subst ei
  have ez : z0 = z1 := Option.some.inj (L.hz.symm.trans hz1)
  subst ez
  have eb : b = b1 := Option.some.inj (L.hb.symm.trans hb1)
  subst eb
  obtain ⟨i2, e2, hzi⟩ := hz
  have ei2 : i = i2 := Option.some.inj e2
  subst ei2
  have ez2 : z0 = z := Option.some.inj (L.hz.symm.trans hzi)
  subst ez2
  have e' : deflateReset (some i) h = .ok (r, h') := e
  rw [e0] at e'
  obtain ⟨rfl, rfl⟩ : r0 = r ∧ SH h i z' b st' d' = h' := by simpa using e'
  obtain ⟨d, hd⟩ := L.hd
  refine ⟨z', ⟨i, rfl, by simp [SH]⟩, hk, ⟨fun _ _ _ => rfl, fun f => ?_, fun hp hreg => ?_⟩⟩
  · have hlt : b < h.nextBlk := by
      refine Nat.lt_of_not_le fun hle => ?_
      rw [(f.1 b hle).2.2] at hd; cases hd
    refine ⟨fun c hc => ?_, fun c hc => ?_⟩
    · have hne : c ≠ b := by simp only [SH] at hc; omega
      have := f.1 c hc
      refine ⟨this.1, this.2.1, ?_⟩
      show upd h.bytes b (some d') c = none
      rw [upd_ne _ _ _ _ hne]; exact this.2.2
    · have hne : c ≠ b := by simp only [SH] at hc; omega
      have := f.2 c hc
      refine ⟨?_, this.2⟩
      show upd h.dstates b (some st') c = none
      rw [upd_ne _ _ _ _ hne]; exact this.1
  · obtain ⟨b2, st2, ⟨⟨z2, ⟨i2, e2, e3⟩, e4⟩, e5⟩, e6⟩ := hreg
    obtain rfl := Option.some.inj e2
    simp only [SH_streams] at e3
    obtain rfl := Option.some.inj e3
    rw [hk.2.2.2.2, L.hb] at e4
    obtain rfl := Option.some.inj e4
    simp only [SH_dstate] at e5
    obtain rfl := Option.some.inj e5
    rw [hg] at e6
    exact Or.inl (Ival.val.inj e6).symm

end ZlibNgF.Proof.DeflateGzInit
