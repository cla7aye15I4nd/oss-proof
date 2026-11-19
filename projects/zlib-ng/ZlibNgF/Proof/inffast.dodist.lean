import ZlibNgF.Proof.«inffast.steps»

/-!
# `inflate_fast`: the `dodist:` step (`ZlibNgF`)

`stepDodist` preserves the label-loop invariant `PI` with a smaller rank: the distance code, the safe-mode bail to
`MATCH`, the copy from the window (`wnext == 0`, contiguous, wrapped; then `CHUNKUNROLL` + `CHUNKCOPY_SAFE` or
`chunkcopy_safe` for the part of the match inside the output), and the copy inside the output (`CHUNKCOPY` /
`CHUNKMEMSET` / `chunkcopy_safe`). `winJp` is the join point of the window branch, equal by definition to the code of
the translation.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InffastDodist
open C ZlibNg.Inffast ZlibNg.InflateP ZlibNg.Chunkset
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono sat_cwhile)
open ZlibNgF.Proof.ChunkMem
open ZlibNgF.Proof.ChunkCopy (B)
open ZlibNgF.Proof.InffastBase
open ZlibNgF.Proof.InffastInv

/-- The join point of the window branch of `dodist:` (`inffast_tpl.h`), after `from` is set. -/
def winJp (c : FC) (l : FL) : M (FL × Lbl) := do
  let mut l := l
  if l.op < l.len then
    l := { l with len := l.len - l.op }
    if !c.safeMode then
      Ptr.memcpy l.out l.from_ l.op.toNat
      l := { l with out := ← l.out.add (Int.ofNat l.op.toNat) }
      let (out, dist, len) ← CHUNKUNROLL l.out l.dist l.len
      l := { l with out, dist, len }
      let src ← l.out.add (-(Int.ofNat l.dist.toNat))
      l := { l with out := ← CHUNKCOPY_SAFE l.out src l.len.toUInt64 c.safe }
    else
      Ptr.memcpy l.out l.from_ l.op.toNat
      l := { l with out := ← l.out.add (Int.ofNat l.op.toNat) }
      let src ← l.out.add (-(Int.ofNat l.dist.toNat))
      l := { l with out := ← chunkcopy_safe l.out src l.len.toUInt64 c.safe }
  else
    Ptr.memcpy l.out l.from_ l.len.toNat
    l := { l with out := ← l.out.add (Int.ofNat l.len.toNat) }
  return (l, .cont)

theorem u32_sub (x y : UInt32) (h : y.toNat ≤ x.toNat) : (x - y).toNat = x.toNat - y.toNat :=
  UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; exact h)

theorem win_get {H0 G : Heap} {c : FC} {e : FE} (EV : EnvOK H0 c e) (r : RH H0 e G) :
    ∃ wd, Space.get H0 (BRef.heap e.wb) = some wd ∧ Space.get G (BRef.heap e.wb) = some wd ∧
      e.woff + c.wsize.toNat ≤ wd.size := by
  obtain ⟨wd, hw, hs⟩ := EV.wdata
  refine ⟨wd, hw, ?_, hs⟩
  rw [r.get_ne (fun h => EV.wbob (BRef.heap.inj h))]; exact hw

/-- The window tail: copy from the window, then (when the match is longer than the window part) from the output. -/
theorem sat_winJp {H0 G : Heap} {c : FC} {e : FE} (EV : EnvOK H0 c e) (r : RH H0 e G) (l : FL) {o fo : Nat}
    (hout : l.out = B e.ob o) (hfrom : l.from_ = B e.wb fo) (hL1 : 1 ≤ l.len.toNat) (hD1 : 1 ≤ l.dist.toNat)
    (hwin : fo + min l.op.toNat l.len.toNat ≤ e.woff + c.wsize.toNat)
    (hPL : l.op.toNat < l.len.toNat → o + l.op.toNat = e.begO + l.dist.toNat) (ho0 : e.o0 ≤ o)
    (hos : o + l.len.toNat ≤ e.s) (hun : c.safeMode = false → e.begO + 22 ≤ e.s) :
    Sat G (winJp c l) (fun x G' => x.2 = .cont ∧ x.1.in_ = l.in_ ∧ x.1.bits = l.bits ∧
      x.1.out = B e.ob (o + l.len.toNat) ∧ RH H0 e G') := by
  obtain ⟨wd, hw0, hwG, hwsz⟩ := win_get EV r
  have hne : BRef.heap e.wb ≠ BRef.heap e.ob := fun h => EV.wbob (BRef.heap.inj h)
  have hbo := EV.begle
  have hsN := EV.sN
  have hN := EV.N63
  rcases l with ⟨in_, out, hold, bits, here, op, len, from_, dist, old⟩
  simp only at hout hfrom hL1 hD1 hwin hPL hos ⊢
  subst hout hfrom
  unfold winJp
  rw [EV.safe]
  by_cases hlt : op < len
  · simp only [hlt, ↓reduceIte]
    have hlt' : op.toNat < len.toNat := by rw [UInt32.lt_iff_toNat_lt] at hlt; exact hlt
    have hm : min op.toNat len.toNat = op.toNat := by omega
    have hsub := u32_sub len op (by omega)
    have hpl := hPL hlt'
    cases hsm : c.safeMode
    · have h22 := hun hsm
      simp only [Bool.not_false, ↓reduceIte]
      refine Sat.bind (Sat.mono (r.sat_memcpy_ext hne hw0 op.toNat (od := o) (os := fo) ho0 (by omega) (by omega)
        (by omega)) ?_)
      intro _ G1 r1
      obtain ⟨a1, ha1, ha1N⟩ := r1.cur
      refine Sat.bind (Sat.mono (sat_add (space_heap G1 e.ob ▸ ha1) (by omega) _ (o + op.toNat) (by simp)
        (by omega)) ?_)
      rintro p G2 ⟨rfl, rfl⟩
      refine Sat.bind (Sat.mono (ZlibNgF.Proof.ChunkCopy.sat_CHUNKUNROLL r1 dist (len - op) hD1 (by omega)
        (by omega) (fun _ => by have := Nat.min_le_right ((len - op).toNat + 6) 14; omega) hsN (by omega)) ?_)
      rintro res G2 ⟨L', D', rfl, hL'le, hD', hL'1, -, r2⟩
      obtain ⟨a2, ha2, ha2N⟩ := r2.cur
      refine Sat.bind (Sat.mono (sat_add (space_heap G2 e.ob ▸ ha2) (by omega) _ e.begO (by simp; omega)
        (by omega)) ?_)
      rintro p G3 ⟨rfl, rfl⟩
      have hL'u : L'.toUInt64.toNat = L'.toNat := by simp
      refine Sat.bind (Sat.mono (ZlibNgF.Proof.ChunkCopy.sat_CHUNKCOPY_SAFE r2 L'.toUInt64 (o := o + op.toNat +
        (len - op).toNat - L'.toNat) (by omega) (by omega) (by omega) (by omega) (Nat.le_refl _) hsN hN) ?_)
      rintro p G4 ⟨rfl, r4⟩
      refine Sat.pure ⟨rfl, rfl, rfl, ?_, r4⟩
      show B e.ob _ = B e.ob _
      congr 1
      omega
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      refine Sat.bind (Sat.mono (r.sat_memcpy_ext hne hw0 op.toNat (od := o) (os := fo) ho0 (by omega) (by omega)
        (by omega)) ?_)
      intro _ G1 r1
      obtain ⟨a1, ha1, ha1N⟩ := r1.cur
      refine Sat.bind (Sat.mono (sat_add (space_heap G1 e.ob ▸ ha1) (by omega) _ (o + op.toNat) (by simp)
        (by omega)) ?_)
      rintro p G2 ⟨rfl, rfl⟩
      refine Sat.bind (Sat.mono (sat_add (space_heap _ e.ob ▸ ha1) (by omega) _ e.begO (by simp; omega)
        (by omega)) ?_)
      rintro p G3 ⟨rfl, rfl⟩
      refine Sat.bind (Sat.mono (ZlibNgF.Proof.ChunkcopySafe.sat_chunkcopy_safe r1 (len - op).toUInt64
        (o := o + op.toNat) (by omega) (by omega) (by omega) (Nat.le_refl _) hsN hN) ?_)
      rintro p G4 ⟨rfl, r4⟩
      refine Sat.pure ⟨rfl, rfl, rfl, ?_, r4⟩
      show B e.ob _ = B e.ob _
      congr 1
      simp only [UInt32.toNat_toUInt64]
      omega
  · simp only [hlt, ↓reduceIte]
    have hlt' : len.toNat ≤ op.toNat := by rw [UInt32.lt_iff_toNat_lt] at hlt; omega
    refine Sat.bind (Sat.mono (r.sat_memcpy_ext hne hw0 len.toNat (od := o) (os := fo) ho0 (by omega) (by omega)
      (by omega)) ?_)
    intro _ G1 r1
    obtain ⟨a1, ha1, ha1N⟩ := r1.cur
    refine Sat.bind (Sat.mono (sat_add (space_heap G1 e.ob ▸ ha1) (by omega) _ (o + len.toNat) (by simp)
      (by omega)) ?_)
    rintro p G2 ⟨rfl, rfl⟩
    exact Sat.pure ⟨rfl, rfl, rfl, rfl, r1⟩

theorem sat_stepDodist {H0 G : Heap} {c : FC} {e : FE} {ot n : Nat} (EV : EnvOK H0 c e) {l : FL}
    (hP : PI H0 c e ot n (l, .dodist) G) :
    Sat G (stepDodist c l) (fun x G' => ∃ m, m < n ∧ PI H0 c e ot m x G') := by
  simp only [PI] at hP
  obtain ⟨w, hw, ho, hin, r, hl1, hl258, hph⟩ := hP
  have hent : ∃ pre, DistEnt pre l.here ∧ (n = 2 ∨ n = 1) ∧ l.here.bits.toNat ≤ l.bits.toNat := by
    rcases hph with ⟨rfl, hr, h28⟩ | ⟨rfl, ⟨pre, he, _⟩, hle⟩
    · exact ⟨0, RootD.ent EV.dtab hr, Or.inl rfl, by have := (RootD.ent EV.dtab hr).1; omega⟩
    · exact ⟨pre, he, Or.inr rfl, hle⟩
  obtain ⟨pre, he, hn, hbl⟩ := hent
  have hd28 := he.1
  obtain ⟨hout, ho0, hroom⟩ := ho
  have hsN := EV.sN
  have hN := EV.N63
  have hbo := EV.begle
  have hspan := EV.span
  have hows : ot + w + 1 ≤ e.s := by split at hroom <;> omega
  have hcont : ∀ (x : FL) (G' : Heap) (po : Nat), x.in_ = l.in_ → x.bits.toNat ≤ l.bits.toNat →
      x.out = B e.ob po → ot < po → po ≤ e.s → RH H0 e G' → ∃ m, m < n ∧ PI H0 c e ot m (x, .cont) G' :=
    fun x G' po h1 h2 h3 h4 h5 h6 => ⟨0, by omega, po, h3, h4, h5, hin.mono h1 h2 (Nat.le_refl _), h6⟩
  have hbrk : ∀ (x : FL) (G' : Heap), x.in_ = l.in_ → x.bits.toNat ≤ l.bits.toNat →
      x.out = l.out → BrkHeap H0 e G' → ∃ m, m < n ∧ PI H0 c e ot m (x, .brk) G' :=
    fun x G' h1 h2 h3 h6 => ⟨0, by omega, ot + w, h3.trans hout, by omega, by split at hroom <;> omega,
      hin.mono h1 h2 (Nat.le_refl _), h6⟩
  unfold stepDodist
  refine Sat.bind (Sat.mono (sat_oldDrop l hbl (by omega)) ?_)
  rintro l1 G1 ⟨rfl, hin1, hout1, hh1, hlen1, hbits1⟩
  extract_lets l2 jc jw
  have hjw : jw = fun _ l => winJp c l := rfl
  split
  · rename_i hbase
    have e2 : l2.op = l1.here.op.toUInt32 := rfl
    rw [e2, hh1] at hbase
    have hB : Base l.here := by simpa [Base] using hbase
    have hv1 := he.2 hB
    have eh : l2.here = l.here := hh1
    refine Sat.bind (Sat.mono (sat_EXTRA_BITS l2.old l2.here _ (by rw [eh]; omega)) ?_)
    rintro x G2 ⟨rfl, hx⟩
    rw [eh, e2, hh1, ZlibNgF.Proof.InffastSteps.op15] at hx
    have hx28 : x.toNat < 2 ^ 28 := Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega))
    have hD := ZlibNgF.Proof.InffastSteps.add_val l.here.val x hx28
    extract_lets l3 jp
    have e3d : l3.dist.toNat = l.here.val.toNat + x.toNat := by
      show (l2.here.val.toUInt32 + x.toUInt32).toNat = _; rw [eh]; exact hD
    have e3o : l3.out = B e.ob (ot + w) := hout1.trans hout
    have e3l : l3.len = l.len := hlen1
    have e3i : l3.in_ = l.in_ := hin1
    have e3b : l3.bits.toNat ≤ l.bits.toNat := by show l1.bits.toNat ≤ _; omega
    clear_value l3
    have hjp : ot + w + l.len.toNat ≤ e.s → Sat G2 (jp ()) (fun x G' => ∃ m, m < n ∧ PI H0 c e ot m x G') := by
      intro hlen
      simp only [jp]
      rw [e3o, EV.beg, EV.win, EV.safe]
      have hD1 : 1 ≤ l3.dist.toNat := by omega
      rcases l3 with ⟨in3, out3, hold3, bits3, here3, op3, len3, from3, dist3, old3⟩
      simp only at e3d e3o e3l e3i e3b hD1 hjw ⊢
      subst e3l
      have hun : c.safeMode = false → e.begO + 22 ≤ e.s := fun h => by rw [h] at hroom; simp at hroom; omega
      have hwfin : ∀ (x : FL × Lbl) (G' : Heap), (x.2 = .cont ∧ x.1.in_ = in3 ∧ x.1.bits = bits3 ∧
          x.1.out = B e.ob (ot + w + l.len.toNat) ∧ RH H0 e G') → ∃ m, m < n ∧ PI H0 c e ot m x G' := by
        rintro ⟨x1, x2⟩ G' ⟨h1, h2, h3, h4, h5⟩
        simp only at h1; subst h1
        exact hcont x1 G' _ (h2.trans e3i) (by rw [h3]; exact e3b) h4 (by omega) hlen h5
      obtain ⟨a, ha, haN⟩ := r.cur
      have hg : Space.get G2 (BRef.heap e.ob) = some a := ha
      obtain ⟨wd, hw0, hwG, hwsz⟩ := win_get EV r
      have hne : BRef.heap e.wb ≠ BRef.heap e.ob := fun h => EV.wbob (BRef.heap.inj h)
      have hwh : c.whave.toNat ≤ c.wsize.toNat := UInt32.le_iff_toNat_le.mp EV.whave
      have hwn : c.wnext.toNat ≤ c.whave.toNat := UInt32.le_iff_toNat_le.mp EV.wnext
      refine Sat.bind (Sat.mono (sat_diff hg (o1 := ot + w) (o2 := e.begO) (by omega) (by omega) (by omega)) ?_)
      rintro d G3 ⟨rfl, rfl⟩
      have hop : (Int64.ofInt ((ot + w : Nat) - (e.begO : Int))).toUInt64.toUInt32.toNat = ot + w - e.begO := by
        rw [UInt64.toNat_toUInt32, toNat_ofInt_nonneg _ (by omega) (by omega)]; omega
      generalize (Int64.ofInt ((ot + w : Nat) - (e.begO : Int))).toUInt64.toUInt32 = op4 at hop ⊢
      split
      · rename_i hfar
        rw [GT.gt, UInt32.lt_iff_toNat_lt] at hfar
        have h5 := u32_sub dist3 op4 (by omega)
        generalize dist3 - op4 = op5 at h5 ⊢
        split
        · refine Sat.bind (Sat.mono (ZlibNgF.Proof.InffastSteps.sat_SET_BAD EV r _ (by simp [strTable])) ?_)
          rintro _ G4 hb
          exact Sat.pure (hbrk _ _ e3i e3b hout.symm hb)
        rename_i hwh5
        rw [GT.gt, UInt32.lt_iff_toNat_lt] at hwh5
        split
        · rename_i hw0'
          have hwn0 : c.wnext.toNat = 0 := by simp at hw0'; simp [hw0']
          have h6 := u32_sub c.wsize op5 (by omega)
          refine Sat.bind (Sat.mono (sat_add hwG (by omega) _ (e.woff + (c.wsize.toNat - op5.toNat))
            (by rw [h6]; simp) (by omega)) ?_)
          rintro p G4 ⟨rfl, rfl⟩
          exact Sat.mono (sat_winJp EV r _ (o := ot + w) (fo := e.woff + (c.wsize.toNat - op5.toNat)) rfl rfl
            (by simpa using hl1) hD1 (by simp; omega) (by simp; omega) (by omega) (by simpa using hlen) hun) hwfin
        rename_i hw0'
        split
        · rename_i hge
          rw [GE.ge, UInt32.le_iff_toNat_le] at hge
          have h6 := u32_sub c.wnext op5 (by omega)
          refine Sat.bind (Sat.mono (sat_add hwG (by omega) _ (e.woff + (c.wnext.toNat - op5.toNat))
            (by rw [h6]; simp) (by omega)) ?_)
          rintro p G4 ⟨rfl, rfl⟩
          exact Sat.mono (sat_winJp EV r _ (o := ot + w) (fo := e.woff + (c.wnext.toNat - op5.toNat)) rfl rfl
            (by simpa using hl1) hD1 (by simp; omega) (by simp; omega) (by omega) (by simpa using hlen) hun) hwfin
        rename_i hge
        rw [GE.ge, UInt32.le_iff_toNat_le] at hge
        have h6 := u32_sub op5 c.wnext (by omega)
        generalize op5 - c.wnext = op6 at h6 ⊢
        have h7 := u32_sub c.wsize op6 (by omega)
        refine Sat.bind (Sat.mono (sat_add hwG (by omega) _ (e.woff + (c.wsize.toNat - op6.toNat))
          (by rw [h7]; simp) (by omega)) ?_)
        rintro p G4 ⟨rfl, rfl⟩
        split
        · rename_i h6l
          rw [UInt32.lt_iff_toNat_lt] at h6l
          refine Sat.bind (Sat.mono (r.sat_memcpy_ext hne hw0 op6.toNat (od := ot + w)
            (os := e.woff + (c.wsize.toNat - op6.toNat)) (by omega) (by omega) (by omega) (by omega)) ?_)
          intro _ G5 r5
          obtain ⟨a5, ha5, ha5N⟩ := r5.cur
          refine Sat.bind (Sat.mono (sat_add (space_heap G5 e.ob ▸ ha5) (by omega) _ (ot + w + op6.toNat) (by simp)
            (by omega)) ?_)
          rintro p G6 ⟨rfl, rfl⟩
          have h8 := u32_sub l.len op6 (by omega)
          refine Sat.mono (sat_winJp EV r5 _ (o := ot + w + op6.toNat) (fo := e.woff) rfl rfl
            (by simp only; omega) hD1 (by simp only; omega) (by simp only; omega) (by omega) (by simp only; omega) hun) ?_
          rintro x G' ⟨h1, h2, h3, h4, h5⟩
          refine hwfin x G' ⟨h1, h2, h3, ?_, h5⟩
          rw [h4]; simp only [h8]; congr 1; omega
        · rename_i h6l
          rw [UInt32.lt_iff_toNat_lt] at h6l
          exact Sat.mono (sat_winJp EV r _ (o := ot + w) (fo := e.woff + (c.wsize.toNat - op6.toNat)) rfl rfl
            (by simpa using hl1) hD1 (by simp only; omega) (by simp only; omega) (by omega) (by simpa using hlen) hun)
            hwfin
      · rename_i hnear
        rw [GT.gt, UInt32.lt_iff_toNat_lt] at hnear
        have hsrc := sat_add hg (off := ot + w) (by omega) (-(Int.ofNat dist3.toNat)) (ot + w - dist3.toNat)
          (by simp; omega) (by omega)
        have hlu : l.len.toUInt64.toNat = l.len.toNat := by simp
        have := Nat.le_max_left l.len.toNat 8
        have := Nat.le_max_right l.len.toNat 8
        cases hsm : c.safeMode
        · simp only [Bool.not_false, ↓reduceIte]
          refine Sat.bind (Sat.mono hsrc ?_)
          rintro p G4 ⟨rfl, rfl⟩
          have hns : ot + 260 ≤ e.s := by rw [hsm] at hroom; simpa using hroom
          split
          · refine Sat.bind (Sat.mono (ZlibNgF.Proof.ChunkCopy.sat_CHUNKCOPY r l.len.toUInt64 (by omega)
              (o := ot + w) (f := ot + w - dist3.toNat) (by omega) (by rw [hlu]; omega) (by rw [hlu]; omega)
              (by rw [hlu]; omega)) ?_)
            rintro p G5 ⟨rfl, r5⟩
            exact Sat.pure (hcont _ _ _ e3i e3b rfl (by omega) (by rw [hlu]; omega) r5)
          · refine Sat.bind (Sat.mono (ZlibNgF.Proof.ChunkCopy.sat_CHUNKMEMSET r l.len.toUInt64
              (o := ot + w) (f := ot + w - dist3.toNat) (by omega) (by omega) (by omega) (by rw [hlu]; omega)
              hsN (by omega)) ?_)
            rintro p G5 ⟨rfl, r5⟩
            exact Sat.pure (hcont _ _ _ e3i e3b rfl (by omega) (by rw [hlu]; omega) r5)
        · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          refine Sat.bind (Sat.mono hsrc ?_)
          rintro p G4 ⟨rfl, rfl⟩
          refine Sat.bind (Sat.mono (ZlibNgF.Proof.ChunkcopySafe.sat_chunkcopy_safe r l.len.toUInt64
            (o := ot + w) (f := ot + w - dist3.toNat) (s := e.s) (by omega) (by omega) (by omega) (Nat.le_refl _)
            hsN hN) ?_)
          rintro p G5 ⟨rfl, r5⟩
          refine Sat.pure (hcont _ _ (ot + w + l.len.toNat) e3i e3b ?_ (by omega) hlen r5)
          show B e.ob _ = B e.ob _
          rw [hlu]; congr 1; omega
    cases hsm : c.safeMode
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact hjp (by rw [hsm] at hroom; simp at hroom; omega)
    · simp only [↓reduceIte]
      rw [EV.safe, e3o]
      obtain ⟨a, ha, haN⟩ := r.cur
      refine Sat.bind (Sat.mono (sat_diff (space_heap _ e.ob ▸ ha) (o1 := e.s) (o2 := ot + w) (by omega) (by omega)
        (by omega)) ?_)
      rintro d G3 ⟨rfl, rfl⟩
      have hroomv : (Int64.ofInt ((e.s : Int) - ((ot + w : Nat) : Int))).toUInt64.toUInt32.toNat = e.s - (ot + w) := by
        rw [UInt64.toNat_toUInt32, toNat_ofInt_nonneg _ (by omega) (by omega)]; omega
      generalize (Int64.ofInt ((e.s : Int) - ((ot + w : Nat) : Int))).toUInt64.toUInt32 = room at hroomv ⊢
      split
      · refine Sat.bind (Sat.mono (ZlibNgF.Proof.InffastSteps.sat_ldState_e EV r) ?_)
        rintro st G4 ⟨rfl, rfl⟩
        refine Sat.bind (Sat.mono (ZlibNgF.Proof.InffastSteps.sat_stState_e EV r _) ?_)
        rintro _ G4 rfl
        exact Sat.pure (hbrk _ _ e3i e3b (e3o.trans hout.symm)
          (ZlibNgF.Proof.InffastSteps.brk_state EV r _ (Or.inr (Or.inr ⟨_, _, rfl⟩))))
      · rename_i hle
        rw [GT.gt, UInt32.lt_iff_toNat_lt, e3l] at hle
        exact hjp (by omega)
  · rename_i hbase
    have e2 : l2.op = l1.here.op.toUInt32 := rfl
    rw [e2, hh1] at hbase
    split
    · rename_i h64
      rw [e2, hh1] at h64
      have hlink : DistLink l.here := ⟨by simpa using hbase, by simpa using h64⟩
      rcases hph with ⟨rfl, hr, h28⟩ | ⟨rfl, ⟨_, _, hnl⟩, _⟩
      · obtain ⟨k, hk, hk'⟩ := hr
        obtain ⟨_, hlk⟩ := EV.dtab.2 k hk
        rw [← hk'] at hlk
        obtain ⟨hop16, hsz, hsub⟩ := hlk hlink
        refine Sat.bind (Sat.mono (sat_BITS l2 l2.op (by rw [e2, hh1]; simp; omega)) ?_)
        rintro bv G2 ⟨rfl, hbv⟩
        rw [e2, hh1] at hbv
        simp only [UInt8.toNat_toUInt32] at hbv
        have hg := (code_get r EV.dnot).trans EV.dget
        rw [EV.dcode]
        have eh : l2.here = l.here := hh1
        rw [eh]
        have hidx := ZlibNgF.Proof.InffastSteps.add_val64 l.here.val bv (by
          have : 2 ^ l.here.op.toNat ≤ 2 ^ 16 := Nat.pow_le_pow_right (by decide) (by omega)
          omega)
        refine Sat.bind (Sat.mono (sat_index_code hg _ (by rw [hidx]; omega)) ?_)
        rintro d G2 ⟨rfl, rfl⟩
        obtain ⟨hsd, hnl⟩ := hsub bv.toNat hbv
        have hd28' := hsd.1
        refine Sat.pure ⟨1, by omega, w, hw, ⟨hout1.trans hout, ho0, hroom⟩, hin.mono hin1 (by show l1.bits.toNat ≤ _; omega) (Nat.le_refl _),
          r, by rw [hlen1]; exact hl1, by rw [hlen1]; exact hl258, Or.inr ⟨rfl, ⟨l.here.bits.toNat, ?_, ?_⟩, ?_⟩⟩
        · dsimp only; rw [hidx, ← Nat.add_assoc]; exact hsd
        · dsimp only; rw [hidx, ← Nat.add_assoc]; exact hnl
        · dsimp only; rw [hidx, ← Nat.add_assoc, hbits1]; omega
      · exact absurd hlink hnl
    · refine Sat.bind (Sat.mono (ZlibNgF.Proof.InffastSteps.sat_SET_BAD EV r _ (by simp [strTable])) ?_)
      rintro _ G2 hb
      exact Sat.pure (hbrk _ _ hin1 (by show l1.bits.toNat ≤ _; omega) hout1 hb)

end ZlibNgF.Proof.InffastDodist
