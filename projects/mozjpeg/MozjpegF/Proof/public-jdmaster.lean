import MozjpegF.Spec.Safety.Goals
import MozjpegF.Spec.Functional.Goals
import MozjpegF.Proof.«public-jutils»

/-!
# Proofs of `jdmaster.c` output dimension and Sharp shrink-on-load theorems (`MozjpegF`)
-/

set_option autoImplicit false

namespace MozjpegF.Proof.Jdmaster
open C MozjpegF.Spec MozjpegF.Spec.Safety MozjpegF.Spec.Functional
open Mozjpeg.MoreCfg Mozjpeg.JerrorH Mozjpeg.JpeglibH Mozjpeg.Jutils Mozjpeg.Jdmaster

private theorem int32_toInt_ofNat {n : Nat} (hn : n < 2 ^ 31) :
    (Int32.ofNat n).toInt = (n : Int) := by
  rw [Int32.toInt_ofNat']
  have hsz : Int32.size = 2 ^ 32 := rfl
  rw [hsz]
  exact Int.bmod_eq_of_le (by omega) (by omega)

private theorem int64_toInt_ofNat {n : Nat} (hn : n < 2 ^ 63) :
    (Int64.ofNat n).toInt = (n : Int) := by
  rw [Int64.toInt_ofNat']
  have hsz : Int64.size = 2 ^ 64 := rfl
  rw [hsz]
  exact Int.bmod_eq_of_le (by omega) (by omega)

private theorem run_bind {α β : Type} (m : C.M α) (f : α → C.M β) (h h' : C.Heap) (a : α)
    (hm : C.run m h = .ok (a, h')) :
    C.run (m >>= f) h = C.run (f a) h' := by
  simp only [C.run, bind] at hm ⊢; rw [hm]

private theorem run_bind_pure {α : Type} (m : C.M α) (h : C.Heap) :
    C.run (m >>= pure) h = C.run m h := by
  change (match m h with | .ok (a, h') => .ok (a, h') | .error e => .error e) = m h
  cases m h <;> rfl

private theorem put_comp_self (h : C.Heap) (bc : Nat) (comps : Array C.JpegCompInfo)
    (hget : h.comps bc = some comps) :
    C.Space.put h (C.CompRef.comp bc) comps = h := by
  cases h
  simp only [C.Space.put]
  congr 1
  exact upd_self _ bc comps hget

private theorem put_comp_put (h : C.Heap) (bc : Nat) (a b : Array C.JpegCompInfo) :
    C.Space.put (C.Space.put h (C.CompRef.comp bc) a) (C.CompRef.comp bc) b =
      C.Space.put h (C.CompRef.comp bc) b := by
  cases h
  simp only [C.Space.put]
  congr 1
  exact upd_upd _ bc _ _

private theorem int_mul_bounds {a b A B : Int}
    (ha0 : 0 ≤ a) (haA : a ≤ A) (hb0 : 0 ≤ b) (hbB : b ≤ B) :
    0 ≤ a * b ∧ a * b ≤ A * B := by
  refine ⟨Int.mul_nonneg ha0 hb0, ?_⟩
  have h1 : a * b ≤ A * b := Int.mul_le_mul_of_nonneg_right haA hb0
  have h2 : A * b ≤ A * B := Int.mul_le_mul_of_nonneg_left hbB (Int.le_trans ha0 haA)
  exact Int.le_trans h1 h2

private theorem rgbPixelSize_ok (cs : Int32) (hcs : 0 ≤ cs.toInt ∧ cs.toInt < 17) :
    ∃ ps, rgbPixelSize cs = pure ps := by
  unfold rgbPixelSize
  have hc1 : (cs < 0 || cs ≥ JPEG_NUMCS) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h
    have h0 : (0 : Int32).toInt = 0 := rfl
    have h17 : JPEG_NUMCS.toInt = 17 := rfl
    rcases h with hlt | hge
    · have : cs.toInt < (0 : Int32).toInt := Int32.lt_iff_toInt_lt.mp hlt
      omega
    · have : JPEG_NUMCS.toInt ≤ cs.toInt := Int32.le_iff_toInt_le.mp hge
      omega
  simp only [hc1, Bool.false_eq_true, ↓reduceIte]
  have hidx : cs.toInt.toNat < rgb_pixelsize.size := by
    have : rgb_pixelsize.size = 17 := rfl
    omega
  rw [Array.getElem?_eq_getElem hidx]
  exact ⟨rgb_pixelsize[cs.toInt.toNat], rfl⟩

theorem selectIdctScale_bounds (sNum sDen : UInt32) :
    1 ≤ (selectIdctScale sNum sDen).toNat ∧ (selectIdctScale sNum sDen).toNat ≤ 16 := by
  unfold selectIdctScale
  suffices h : ∀ (rem : Nat) (k : UInt32), 1 ≤ k.toNat → k.toNat + rem = 16 →
      1 ≤ (selectIdctScale.go rem k (sNum * 8) sDen).toNat ∧
      (selectIdctScale.go rem k (sNum * 8) sDen).toNat ≤ 16 from
    h 15 1 (by decide) (by decide)
  intro rem
  induction rem with
  | zero =>
    intro k hk1 hsum
    simp only [selectIdctScale.go]
    omega
  | succ rem ih =>
    intro k hk1 hsum
    simp only [selectIdctScale.go]
    split
    · omega
    · have hk1' : (k + 1).toNat = k.toNat + 1 := by
        rw [UInt32.toNat_add, UInt32.toNat_one]
        exact Nat.mod_eq_of_lt (by omega)
      exact ih (k + 1) (by omega) (by omega)

theorem setCompScaledSizes_ok (h : C.Heap) (bc : Nat) (comps : Array C.JpegCompInfo)
    (n : Nat) (k32 : Int32)
    (hget : h.comps bc = some comps) (hn : n ≤ comps.size) :
    ∀ ci, ci ≤ n →
      ∃ comps',
        comps'.size = comps.size ∧
        (∀ i, i < comps.size →
          (comps'[i]!).hSampFactor = (comps[i]!).hSampFactor ∧
          (comps'[i]!).vSampFactor = (comps[i]!).vSampFactor) ∧
        C.run (setCompScaledSizes (.ref (C.CompRef.comp bc) 0) ci n k32) h =
          .ok ((), C.Space.put h (C.CompRef.comp bc) comps') := by
  intro ci hcin
  obtain ⟨d, hd⟩ : ∃ d, d = n - ci := ⟨n - ci, rfl⟩
  induction d generalizing ci h comps with
  | zero =>
    have hge : ¬ (ci < n) := by omega
    refine ⟨comps, rfl, fun _ _ => ⟨rfl, rfl⟩, ?_⟩
    unfold setCompScaledSizes
    simp only [hge, ↓reduceDIte, C.run, pure, put_comp_self h bc comps hget]
  | succ d ih =>
    have hlt : ci < n := by omega
    have hci_sz : ci < comps.size := by omega
    have hget_ci : C.Space.get h (C.CompRef.comp bc) = some comps := hget
    have hro : C.Space.ro h (C.CompRef.comp bc) = false := rfl
    have hb_add : 0 ≤ comps.size ∧ 0 ≤ ((0 : Nat) : Int) + (ci : Int) ∧
        ((0 : Nat) : Int) + (ci : Int) ≤ (comps.size : Int) :=
      ⟨Nat.zero_le _, by omega, by omega⟩
    have hci_eq : (((0 : Nat) : Int) + (ci : Int)).toNat = ci := by omega
    let comp1 := { comps[ci] with dctHScaledSize := k32, dctVScaledSize := k32 }
    let comps1 := comps.set! ci comp1
    let h1 := C.Space.put h (C.CompRef.comp bc) comps1
    have hsz1 : comps1.size = comps.size := by simp [comps1, Array.set!_eq_setIfInBounds]
    have hget1 : h1.comps bc = some comps1 := by simp [h1, C.Space.put]
    obtain ⟨comps', hsz', hfields', hrun'⟩ :=
      ih h1 comps1 hget1 (by omega) (ci + 1) (by omega) (by omega)
    refine ⟨comps', by omega, fun i hi => ?_, ?_⟩
    · obtain ⟨hhs, hvs⟩ := hfields' i (by omega)
      by_cases hic : i = ci
      · subst hic
        have heq : comps1[i]! = comp1 := by
          rw [getElem!_pos comps1 i (by omega)]
          dsimp only [comps1]; simp only [Array.set!_eq_setIfInBounds]
          rw [Array.getElem_setIfInBounds hi]; simp
        refine ⟨?_, ?_⟩
        · rw [hhs, heq]; simp only [comp1]; rw [getElem!_pos comps i hi]
        · rw [hvs, heq]; simp only [comp1]; rw [getElem!_pos comps i hi]
      · have heq : comps1[i]! = comps[i]! := by
          rw [getElem!_pos comps1 i (by omega), getElem!_pos comps i hi]
          dsimp only [comps1]; simp only [Array.set!_eq_setIfInBounds]
          rw [Array.getElem_setIfInBounds hi]
          have hne : ci ≠ i := Ne.symm hic
          simp [hne]
        exact ⟨by rw [hhs, heq], by rw [hvs, heq]⟩
    · unfold setCompScaledSizes
      simp only [hlt, ↓reduceDIte, Int.ofNat_eq_natCast]
      rw [Ptr.add_bind h _ 0 _ comps _ hget_ci hb_add, hci_eq]
      rw [Ptr.load_bind h _ ci comps _ hget_ci hci_sz]
      rw [Ptr.store_bind h _ ci comp1 comps _ hget_ci hro hci_sz]
      simpa only [h1, comps1, put_comp_put] using hrun'

private theorem adaptWhile_ok (maxH maxV minDct hSamp vSamp : Int32)
    (hmaxH : 1 ≤ maxH.toInt ∧ maxH.toInt ≤ 4)
    (hmaxV : 1 ≤ maxV.toInt ∧ maxV.toInt ≤ 4)
    (hh : 1 ≤ hSamp.toInt ∧ hSamp.toInt ≤ 4)
    (hv : 1 ≤ vSamp.toInt ∧ vSamp.toInt ≤ 4)
    (hmind : 1 ≤ minDct.toInt ∧ minDct.toInt ≤ 16) :
    ∀ k s fuel h,
      1 ≤ s.toInt → s.toInt ≤ 16 →
      (s.toInt < 8 → (8 - s.toInt).toNat ≤ k) →
      k < fuel →
      ∃ s', 1 ≤ s'.toInt ∧ s'.toInt ≤ 16 ∧
        C.run (C.cwhile.go
          (fun s => do
            if s < DCTSIZE then
              let s2 ← i32Mul s 2
              let dh ← i32Mul hSamp s2
              let mh ← i32Mod (Int32.ofInt (maxH.toInt * minDct.toInt)) dh
              if mh == 0 then
                let dv ← i32Mul vSamp s2
                let mv ← i32Mod (Int32.ofInt (maxV.toInt * minDct.toInt)) dv
                return (mv == 0, s)
              else return (false, s)
            else return (false, s))
          (fun s => i32Mul s 2) fuel s) h = .ok (s', h) := by
  intro k
  induction k with
  | zero =>
    intro s fuel h hs1 hs16 hk hltf
    obtain ⟨f', rfl⟩ : ∃ f', fuel = f' + 1 := ⟨fuel - 1, by omega⟩
    have hs8F : ¬ (s < DCTSIZE) := by
      intro hlt
      have : s.toInt < 8 := Int32.lt_iff_toInt_lt.mp hlt
      have := hk this; omega
    unfold C.cwhile.go
    simp only [C.run, bind, pure, hs8F, ↓reduceIte]
    exact ⟨s, hs1, hs16, rfl⟩
  | succ k ih =>
    intro s fuel h hs1 hs16 hk hltf
    obtain ⟨f', rfl⟩ : ∃ f', fuel = f' + 1 := ⟨fuel - 1, by omega⟩
    by_cases hs8 : s < DCTSIZE
    · have hs_lt8 : s.toInt < 8 := Int32.lt_iff_toInt_lt.mp hs8
      have h2_val : (2 : Int32).toInt = 2 := rfl
      have hs2_ok := i32Mul_eq s 2 (by rw [h2_val]; omega) (by rw [h2_val]; omega)
      have hs2_val : (Int32.ofInt (s.toInt * (2 : Int32).toInt)).toInt = s.toInt * 2 :=
        toInt_ofInt32 (by rw [h2_val]; omega) (by rw [h2_val]; omega)
      let s2 := Int32.ofInt (s.toInt * (2 : Int32).toInt)
      have hs2_pos : 1 ≤ s2.toInt := by rw [hs2_val]; omega
      have hs2_le : s2.toInt ≤ 16 := by rw [hs2_val]; omega
      have hmul_h := int_mul_bounds (A := 4) (B := 16) (by omega) hh.2 (by omega) hs2_le
      have hdh_ok := i32Mul_eq hSamp s2 (by omega) (by omega)
      have hdh_val : (Int32.ofInt (hSamp.toInt * s2.toInt)).toInt = hSamp.toInt * s2.toInt :=
        toInt_ofInt32 (by omega) (by omega)
      have hdh_pos : 0 < (Int32.ofInt (hSamp.toInt * s2.toInt)).toInt := by
        rw [hdh_val, hs2_val]; exact Int.mul_pos (by omega) (by omega)
      let dh := Int32.ofInt (hSamp.toInt * s2.toInt)
      have htmH := int_mul_bounds (A := 4) (B := 16) (by omega) hmaxH.2 (by omega) hmind.2
      let tH := Int32.ofInt (maxH.toInt * minDct.toInt)
      have htH_val : tH.toInt = maxH.toInt * minDct.toInt :=
        toInt_ofInt32 (by omega) (by omega)
      have hmh_ok := i32Mod_nonneg_eq tH dh (by rw [htH_val]; exact htmH.1) hdh_pos
      let mh := Int32.ofInt (Int.tmod tH.toInt dh.toInt)
      unfold C.cwhile.go
      dsimp only
      simp only [hs8, ↓reduceIte]
      rw [bind_assoc_m, hs2_ok, pure_bind_m]
      rw [bind_assoc_m, hdh_ok, pure_bind_m]
      rw [bind_assoc_m, hmh_ok, pure_bind_m]
      by_cases hmh0 : (mh == 0) = true
      · have hmul_v := int_mul_bounds (A := 4) (B := 16) (by omega) hv.2 (by omega) hs2_le
        have hdv_ok := i32Mul_eq vSamp s2 (by omega) (by omega)
        have hdv_val : (Int32.ofInt (vSamp.toInt * s2.toInt)).toInt = vSamp.toInt * s2.toInt :=
          toInt_ofInt32 (by omega) (by omega)
        have hdv_pos : 0 < (Int32.ofInt (vSamp.toInt * s2.toInt)).toInt := by
          rw [hdv_val, hs2_val]; exact Int.mul_pos (by omega) (by omega)
        let dv := Int32.ofInt (vSamp.toInt * s2.toInt)
        have htmV := int_mul_bounds (A := 4) (B := 16) (by omega) hmaxV.2 (by omega) hmind.2
        let tV := Int32.ofInt (maxV.toInt * minDct.toInt)
        have htV_val : tV.toInt = maxV.toInt * minDct.toInt :=
          toInt_ofInt32 (by omega) (by omega)
        have hmv_ok := i32Mod_nonneg_eq tV dv (by rw [htV_val]; exact htmV.1) hdv_pos
        let mv := Int32.ofInt (Int.tmod tV.toInt dv.toInt)
        dsimp only [mh] at hmh0
        simp only [hmh0, ↓reduceIte]
        rw [bind_assoc_m, hdv_ok, pure_bind_m]
        rw [bind_assoc_m, hmv_ok, pure_bind_m]
        simp only [pure_bind_m]
        by_cases hmv0 : (mv == 0) = true
        · dsimp only [mv] at hmv0
          simp only [hmv0, ↓reduceIte]
          have hk' : s2.toInt < 8 → (8 - s2.toInt).toNat ≤ k := by
            intro hlt2
            have := hk hs_lt8
            rw [hs2_val] at hlt2 ⊢; omega
          rw [hs2_ok, pure_bind_m]
          exact ih s2 f' h hs2_pos hs2_le hk' (by omega)
        · have hmvF := Bool.eq_false_iff.mpr hmv0
          dsimp only [mv] at hmvF
          simp only [hmvF, Bool.false_eq_true, ↓reduceIte]
          exact ⟨s, hs1, hs16, rfl⟩
      · have hmhF := Bool.eq_false_iff.mpr hmh0
        dsimp only [mh] at hmhF
        simp only [hmhF, Bool.false_eq_true, ↓reduceIte, pure_bind_m]
        exact ⟨s, hs1, hs16, rfl⟩
    · unfold C.cwhile.go
      simp only [C.run, bind, pure, hs8, ↓reduceIte]
      exact ⟨s, hs1, hs16, rfl⟩

theorem adaptComponentDctSize_ok (h : C.Heap) (maxH maxV minDct hSamp vSamp : Int32)
    (hmaxH : 1 ≤ maxH.toInt ∧ maxH.toInt ≤ 4)
    (hmaxV : 1 ≤ maxV.toInt ∧ maxV.toInt ≤ 4)
    (hh : 1 ≤ hSamp.toInt ∧ hSamp.toInt ≤ 4)
    (hv : 1 ≤ vSamp.toInt ∧ vSamp.toInt ≤ 4)
    (hmind : 1 ≤ minDct.toInt ∧ minDct.toInt ≤ 16) :
    ∃ s', 1 ≤ s'.toInt ∧ s'.toInt ≤ 16 ∧
      C.run (adaptComponentDctSize maxH maxV minDct hSamp vSamp) h = .ok (s', h) := by
  unfold adaptComponentDctSize
  have hbH := int_mul_bounds (by omega) hmaxH.2 (by omega) hmind.2
  have hbV := int_mul_bounds (by omega) hmaxV.2 (by omega) hmind.2
  have htH := i32Mul_eq maxH minDct (by omega) (by omega)
  have htV := i32Mul_eq maxV minDct (by omega) (by omega)
  rw [htH, pure_bind_m, htV, pure_bind_m]
  unfold C.cwhile
  have hk_lt : 8 < C.fuel := by unfold C.fuel; decide
  exact adaptWhile_ok maxH maxV minDct hSamp vSamp hmaxH hmaxV hh hv hmind 8 minDct C.fuel h
    hmind.1 hmind.2 (fun _ => by omega) hk_lt

theorem adaptCompLoop_ok (h : C.Heap) (bc : Nat) (comps : Array C.JpegCompInfo) (n : Nat)
    (maxH maxV minDct : Int32)
    (hget : h.comps bc = some comps) (hn : n ≤ comps.size)
    (hmaxH : 1 ≤ maxH.toInt ∧ maxH.toInt ≤ 4)
    (hmaxV : 1 ≤ maxV.toInt ∧ maxV.toInt ≤ 4)
    (hmind : 1 ≤ minDct.toInt ∧ minDct.toInt ≤ 16)
    (hsamp : ∀ i, i < n →
      1 ≤ (comps[i]!).hSampFactor.toInt ∧ (comps[i]!).hSampFactor.toInt ≤ 4 ∧
      1 ≤ (comps[i]!).vSampFactor.toInt ∧ (comps[i]!).vSampFactor.toInt ≤ 4) :
    ∀ ci, ci ≤ n →
      ∃ comps',
        comps'.size = comps.size ∧
        (∀ i, i < ci → comps'[i]! = comps[i]!) ∧
        (∀ i, i < n →
          1 ≤ (comps'[i]!).hSampFactor.toInt ∧ (comps'[i]!).hSampFactor.toInt ≤ 4 ∧
          1 ≤ (comps'[i]!).vSampFactor.toInt ∧ (comps'[i]!).vSampFactor.toInt ≤ 4) ∧
        (∀ i, i < n → ci ≤ i →
          1 ≤ (comps'[i]!).dctHScaledSize.toInt ∧ (comps'[i]!).dctHScaledSize.toInt ≤ 16) ∧
        C.run (adaptCompLoop (.ref (C.CompRef.comp bc) 0) ci n maxH maxV minDct) h =
          .ok ((), C.Space.put h (C.CompRef.comp bc) comps') := by
  intro ci hcin
  obtain ⟨d, hd⟩ : ∃ d, d = n - ci := ⟨n - ci, rfl⟩
  induction d generalizing ci h comps with
  | zero =>
    have hge : ¬ (ci < n) := by omega
    refine ⟨comps, rfl, fun _ _ => rfl, hsamp, fun i hi hle => by omega, ?_⟩
    unfold adaptCompLoop
    simp only [hge, ↓reduceDIte, C.run, pure, put_comp_self h bc comps hget]
  | succ d ih =>
    have hlt : ci < n := by omega
    have hci_sz : ci < comps.size := by omega
    have hget_ci : C.Space.get h (C.CompRef.comp bc) = some comps := hget
    have hro : C.Space.ro h (C.CompRef.comp bc) = false := rfl
    have hb_add : 0 ≤ comps.size ∧ 0 ≤ ((0 : Nat) : Int) + (ci : Int) ∧
        ((0 : Nat) : Int) + (ci : Int) ≤ (comps.size : Int) :=
      ⟨Nat.zero_le _, by omega, by omega⟩
    have hci_eq : (((0 : Nat) : Int) + (ci : Int)).toNat = ci := by omega
    obtain ⟨hh1, hh4, hv1, hv4⟩ := hsamp ci hlt
    have hci_pos : comps[ci] = comps[ci]! := (getElem!_pos comps ci hci_sz).symm
    obtain ⟨ssize, hss1, hss16, hadapt⟩ :=
      adaptComponentDctSize_ok h maxH maxV minDct comps[ci].hSampFactor comps[ci].vSampFactor
        hmaxH hmaxV ⟨by rw [hci_pos]; exact hh1, by rw [hci_pos]; exact hh4⟩
        ⟨by rw [hci_pos]; exact hv1, by rw [hci_pos]; exact hv4⟩ hmind
    let comp1 := { comps[ci] with dctHScaledSize := ssize, dctVScaledSize := ssize }
    let comps1 := comps.set! ci comp1
    let h1 := C.Space.put h (C.CompRef.comp bc) comps1
    have hsz1 : comps1.size = comps.size := by simp [comps1, Array.set!_eq_setIfInBounds]
    have hget1 : h1.comps bc = some comps1 := by simp [h1, C.Space.put]
    have hsamp1 : ∀ i, i < n →
        1 ≤ (comps1[i]!).hSampFactor.toInt ∧ (comps1[i]!).hSampFactor.toInt ≤ 4 ∧
        1 ≤ (comps1[i]!).vSampFactor.toInt ∧ (comps1[i]!).vSampFactor.toInt ≤ 4 := by
      intro i hi
      by_cases hic : i = ci
      · subst hic
        have heq : comps1[i]! = comp1 := by
          rw [getElem!_pos comps1 i (by omega)]
          dsimp only [comps1]; simp only [Array.set!_eq_setIfInBounds]
          rw [Array.getElem_setIfInBounds hci_sz]; simp
        rw [heq]; simp only [comp1]; rw [← getElem!_pos comps i hci_sz]; exact ⟨hh1, hh4, hv1, hv4⟩
      · have heq : comps1[i]! = comps[i]! := by
          have hi_sz : i < comps.size := by omega
          rw [getElem!_pos comps1 i (by omega), getElem!_pos comps i hi_sz]
          dsimp only [comps1]; simp only [Array.set!_eq_setIfInBounds]
          rw [Array.getElem_setIfInBounds hi_sz]
          have hne : ci ≠ i := Ne.symm hic
          simp [hne]
        rw [heq]; exact hsamp i hi
    obtain ⟨comps', hsz', hpres', hsamp', hdct', hrun'⟩ :=
      ih h1 comps1 hget1 (by omega) hsamp1 (ci + 1) (by omega) (by omega)
    refine ⟨comps', by omega, ?_, hsamp', ?_, ?_⟩
    · intro i hi
      have h1_i := hpres' i (by omega)
      have heq : comps1[i]! = comps[i]! := by
        have hi_sz : i < comps.size := by omega
        rw [getElem!_pos comps1 i (by omega), getElem!_pos comps i hi_sz]
        dsimp only [comps1]; simp only [Array.set!_eq_setIfInBounds]
        rw [Array.getElem_setIfInBounds hi_sz]
        have hne : ci ≠ i := by omega
        simp [hne]
      rw [h1_i, heq]
    · intro i hi hle
      by_cases hic : i = ci
      · subst hic
        have hself : comps'[i]! = comps1[i]! := hpres' i (by omega)
        have heq : comps1[i]! = comp1 := by
          rw [getElem!_pos comps1 i (by omega)]
          dsimp only [comps1]; simp only [Array.set!_eq_setIfInBounds]
          rw [Array.getElem_setIfInBounds hci_sz]; simp
        rw [hself, heq]; exact ⟨hss1, hss16⟩
      · exact hdct' i hi (by omega)
    · unfold adaptCompLoop
      simp only [hlt, ↓reduceDIte, Int.ofNat_eq_natCast]
      rw [Ptr.add_bind h _ 0 _ comps _ hget_ci hb_add, hci_eq]
      rw [Ptr.load_bind h _ ci comps _ hget_ci hci_sz]
      have hadapt_bind : ∀ (f : Int32 → M Unit),
          C.run (adaptComponentDctSize maxH maxV minDct comps[ci].hSampFactor comps[ci].vSampFactor >>= f) h =
            C.run (f ssize) h := by
        intro f; simp only [C.run, bind] at hadapt ⊢; rw [hadapt]
      rw [hadapt_bind]
      rw [Ptr.store_bind h _ ci comp1 comps _ hget_ci hro hci_sz]
      simpa only [h1, comps1, put_comp_put] using hrun'

theorem downsampleCompLoop_ok (h : C.Heap) (bc : Nat) (comps : Array C.JpegCompInfo) (n : Nat)
    (imgW imgH : UInt32) (maxH maxV : Int32)
    (hget : h.comps bc = some comps) (hn : n ≤ comps.size)
    (hdim : imgW.toNat ≤ 65500 ∧ imgH.toNat ≤ 65500)
    (hmaxH : 1 ≤ maxH.toInt ∧ maxH.toInt ≤ 4)
    (hmaxV : 1 ≤ maxV.toInt ∧ maxV.toInt ≤ 4)
    (hsamp : ∀ i, i < n →
      1 ≤ (comps[i]!).hSampFactor.toInt ∧ (comps[i]!).hSampFactor.toInt ≤ 4 ∧
      1 ≤ (comps[i]!).vSampFactor.toInt ∧ (comps[i]!).vSampFactor.toInt ≤ 4 ∧
      1 ≤ (comps[i]!).dctHScaledSize.toInt ∧ (comps[i]!).dctHScaledSize.toInt ≤ 16) :
    ∀ ci, ci ≤ n →
      ∃ comps',
        comps'.size = comps.size ∧
        (∀ i, i < n →
          1 ≤ (comps'[i]!).hSampFactor.toInt ∧ (comps'[i]!).hSampFactor.toInt ≤ 4 ∧
          1 ≤ (comps'[i]!).vSampFactor.toInt ∧ (comps'[i]!).vSampFactor.toInt ≤ 4) ∧
        C.run (downsampleCompLoop (.ref (C.CompRef.comp bc) 0) ci n imgW imgH maxH maxV) h =
          .ok ((), C.Space.put h (C.CompRef.comp bc) comps') := by
  intro ci hcin
  obtain ⟨d, hd⟩ : ∃ d, d = n - ci := ⟨n - ci, rfl⟩
  induction d generalizing ci h comps with
  | zero =>
    have hge : ¬ (ci < n) := by omega
    refine ⟨comps, rfl, fun i hi => by obtain ⟨a, b, c, d, _⟩ := hsamp i hi; exact ⟨a, b, c, d⟩, ?_⟩
    unfold downsampleCompLoop
    simp only [hge, ↓reduceDIte, C.run, pure, put_comp_self h bc comps hget]
  | succ d ih =>
    have hlt : ci < n := by omega
    have hci_sz : ci < comps.size := by omega
    have hget_ci : C.Space.get h (C.CompRef.comp bc) = some comps := hget
    have hro : C.Space.ro h (C.CompRef.comp bc) = false := rfl
    have hb_add : 0 ≤ comps.size ∧ 0 ≤ ((0 : Nat) : Int) + (ci : Int) ∧
        ((0 : Nat) : Int) + (ci : Int) ≤ (comps.size : Int) :=
      ⟨Nat.zero_le _, by omega, by omega⟩
    have hci_eq : (((0 : Nat) : Int) + (ci : Int)).toNat = ci := by omega
    obtain ⟨hh1, hh4, hv1, hv4, hd1, hd16⟩ := hsamp ci hlt
    have hci_pos : comps[ci] = comps[ci]! := (getElem!_pos comps ci hci_sz).symm
    let c := comps[ci]
    have hc_h : 1 ≤ c.hSampFactor.toInt ∧ c.hSampFactor.toInt ≤ 4 := by
      dsimp [c]; rw [hci_pos]; exact ⟨hh1, hh4⟩
    have hc_v : 1 ≤ c.vSampFactor.toInt ∧ c.vSampFactor.toInt ≤ 4 := by
      dsimp [c]; rw [hci_pos]; exact ⟨hv1, hv4⟩
    have hc_d : 1 ≤ c.dctHScaledSize.toInt ∧ c.dctHScaledSize.toInt ≤ 16 := by
      dsimp [c]; rw [hci_pos]; exact ⟨hd1, hd16⟩
    have hsw_b := int_mul_bounds (A := 4) (B := 16) (by omega) hc_h.2 (by omega) hc_d.2
    have hsh_b := int_mul_bounds (A := 4) (B := 16) (by omega) hc_v.2 (by omega) hc_d.2
    have hsw_ok := i32Mul_eq c.hSampFactor c.dctHScaledSize (by omega) (by omega)
    have hsh_ok := i32Mul_eq c.vSampFactor c.dctHScaledSize (by omega) (by omega)
    let sw := Int32.ofInt (c.hSampFactor.toInt * c.dctHScaledSize.toInt)
    let sh := Int32.ofInt (c.vSampFactor.toInt * c.dctHScaledSize.toInt)
    have hsw_v : sw.toInt = c.hSampFactor.toInt * c.dctHScaledSize.toInt :=
      toInt_ofInt32 (by omega) (by omega)
    have hsh_v : sh.toInt = c.vSampFactor.toInt * c.dctHScaledSize.toInt :=
      toInt_ofInt32 (by omega) (by omega)
    have hsw_rng : 0 ≤ sw.toInt ∧ sw.toInt ≤ 64 := by rw [hsw_v]; omega
    have hsh_rng : 0 ≤ sh.toInt ∧ sh.toInt ≤ 64 := by rw [hsh_v]; omega
    have hw_nat_ok := int_mul_bounds (Int.natCast_nonneg _) (Int.ofNat_le.mpr hdim.1) hsw_rng.1 hsw_rng.2
    have hh_nat_ok := int_mul_bounds (Int.natCast_nonneg _) (Int.ofNat_le.mpr hdim.2) hsh_rng.1 hsh_rng.2
    have h8 : (8 : Int64).toInt = 8 := rfl
    have hiw64 : (Int64.ofNat imgW.toNat).toInt = (imgW.toNat : Int) := int64_toInt_ofNat (by omega)
    have hih64 : (Int64.ofNat imgH.toNat).toInt = (imgH.toNat : Int) := int64_toInt_ofNat (by omega)
    have hsw64 : (Int64.ofInt sw.toInt).toInt = sw.toInt := toInt_ofInt64 (by omega) (by omega)
    have hsh64 : (Int64.ofInt sh.toInt).toInt = sh.toInt := toInt_ofInt64 (by omega) (by omega)
    have hmh64 : (Int64.ofInt maxH.toInt).toInt = maxH.toInt := toInt_ofInt64 (by omega) (by omega)
    have hmv64 : (Int64.ofInt maxV.toInt).toInt = maxV.toInt := toInt_ofInt64 (by omega) (by omega)
    have hdwN_ok := i64Mul_eq (Int64.ofNat imgW.toNat) (Int64.ofInt sw.toInt)
      (by rw [hiw64, hsw64]; omega) (by rw [hiw64, hsw64]; omega)
    have hdwD_ok := i64Mul_eq (Int64.ofInt maxH.toInt) 8
      (by simp only [hmh64, h8]; omega) (by simp only [hmh64, h8]; omega)
    have hdhN_ok := i64Mul_eq (Int64.ofNat imgH.toNat) (Int64.ofInt sh.toInt)
      (by rw [hih64, hsh64]; omega) (by rw [hih64, hsh64]; omega)
    have hdhD_ok := i64Mul_eq (Int64.ofInt maxV.toInt) 8
      (by simp only [hmv64, h8]; omega) (by simp only [hmv64, h8]; omega)
    let dwNum := Int64.ofInt ((Int64.ofNat imgW.toNat).toInt * (Int64.ofInt sw.toInt).toInt)
    let dwDen := Int64.ofInt ((Int64.ofInt maxH.toInt).toInt * (8 : Int64).toInt)
    let dhNum := Int64.ofInt ((Int64.ofNat imgH.toNat).toInt * (Int64.ofInt sh.toInt).toInt)
    let dhDen := Int64.ofInt ((Int64.ofInt maxV.toInt).toInt * (8 : Int64).toInt)
    have hdwN_v : 0 ≤ dwNum.toInt ∧ dwNum.toInt ≤ 65500 * 64 := by
      dsimp [dwNum]; simp only [hiw64, hsw64]; rw [toInt_ofInt64 (by omega) (by omega)]; exact hw_nat_ok
    have hdwD_v : 8 ≤ dwDen.toInt ∧ dwDen.toInt ≤ 32 := by
      dsimp [dwDen]; simp only [hmh64]; rw [toInt_ofInt64 (by omega) (by omega)]; omega
    have hdhN_v : 0 ≤ dhNum.toInt ∧ dhNum.toInt ≤ 65500 * 64 := by
      dsimp [dhNum]; simp only [hih64, hsh64]; rw [toInt_ofInt64 (by omega) (by omega)]; exact hh_nat_ok
    have hdhD_v : 8 ≤ dhDen.toInt ∧ dhDen.toInt ≤ 32 := by
      dsimp [dhDen]; simp only [hmv64]; rw [toInt_ofInt64 (by omega) (by omega)]; omega
    obtain ⟨dw, hdw⟩ := MozjpegF.Proof.Jutils.jdiv_round_up_safety h dwNum dwDen
      hdwN_v.1 (by omega) (by omega)
    obtain ⟨dh, hdh⟩ := MozjpegF.Proof.Jutils.jdiv_round_up_safety h dhNum dhDen
      hdhN_v.1 (by omega) (by omega)
    let comp1 := { c with downsampledWidth := dw.toInt.toNat.toUInt32, downsampledHeight := dh.toInt.toNat.toUInt32 }
    let comps1 := comps.set! ci comp1
    let h1 := C.Space.put h (C.CompRef.comp bc) comps1
    have hsz1 : comps1.size = comps.size := by simp [comps1, Array.set!_eq_setIfInBounds]
    have hget1 : h1.comps bc = some comps1 := by simp [h1, C.Space.put]
    have hsamp1 : ∀ i, i < n →
        1 ≤ (comps1[i]!).hSampFactor.toInt ∧ (comps1[i]!).hSampFactor.toInt ≤ 4 ∧
        1 ≤ (comps1[i]!).vSampFactor.toInt ∧ (comps1[i]!).vSampFactor.toInt ≤ 4 ∧
        1 ≤ (comps1[i]!).dctHScaledSize.toInt ∧ (comps1[i]!).dctHScaledSize.toInt ≤ 16 := by
      intro i hi
      by_cases hic : i = ci
      · subst hic
        have heq : comps1[i]! = comp1 := by
          rw [getElem!_pos comps1 i (by omega)]
          dsimp only [comps1]; simp only [Array.set!_eq_setIfInBounds]
          rw [Array.getElem_setIfInBounds hci_sz]; simp
        rw [heq]; simp only [comp1, c]; rw [← getElem!_pos comps i hci_sz]; exact ⟨hh1, hh4, hv1, hv4, hd1, hd16⟩
      · have heq : comps1[i]! = comps[i]! := by
          have hi_sz : i < comps.size := by omega
          rw [getElem!_pos comps1 i (by omega), getElem!_pos comps i hi_sz]
          dsimp only [comps1]; simp only [Array.set!_eq_setIfInBounds]
          rw [Array.getElem_setIfInBounds hi_sz]
          have hne : ci ≠ i := Ne.symm hic
          simp [hne]
        rw [heq]; exact hsamp i hi
    obtain ⟨comps', hsz', hsamp', hrun'⟩ :=
      ih h1 comps1 hget1 (by omega) hsamp1 (ci + 1) (by omega) (by omega)
    refine ⟨comps', by omega, hsamp', ?_⟩
    unfold downsampleCompLoop
    simp only [hlt, ↓reduceDIte, Int.ofNat_eq_natCast]
    rw [Ptr.add_bind h _ 0 _ comps _ hget_ci hb_add, hci_eq]
    rw [Ptr.load_bind h _ ci comps _ hget_ci hci_sz]
    rw [hsw_ok, pure_bind_m, hsh_ok, pure_bind_m, hdwN_ok, pure_bind_m, hdwD_ok, pure_bind_m]
    have hdw_bind : ∀ (f : Int64 → M Unit),
        C.run (jdiv_round_up dwNum dwDen >>= f) h = C.run (f dw) h := by
      intro f; simp only [C.run, bind] at hdw ⊢; rw [hdw]
    rw [hdw_bind, hdhN_ok, pure_bind_m, hdhD_ok, pure_bind_m]
    have hdh_bind : ∀ (f : Int64 → M Unit),
        C.run (jdiv_round_up dhNum dhDen >>= f) h = C.run (f dh) h := by
      intro f; simp only [C.run, bind] at hdh ⊢; rw [hdh]
    rw [hdh_bind]
    rw [Ptr.store_bind h _ ci comp1 comps _ hget_ci hro hci_sz]
    simpa only [h1, comps1, put_comp_put] using hrun'

theorem jpeg_core_output_dimensions_safety : Goal.jpeg_core_output_dimensions_safety := by
  intro h cinfo ⟨_hvalid, rc, dcs, dc, rmas, masters, mst,
    hc, hgetdc, hszdc, hdc, hmas, hgetmas, hszmas, hmst, _,
    hnc, hdim, _hmaxh, _hmaxv, hcomp⟩
  subst hc
  obtain ⟨rcomp, comps, hci, hgetcomp, hszcomp, _⟩ := hcomp
  cases rc with | decomp bdc =>
  cases rmas with | master bmas =>
  cases rcomp with | comp bcomp =>
  have hdc0 : dcs[0] = dc := by rw [← getElem!_pos dcs 0 hszdc]; exact hdc.symm
  have hmst0 : masters[0] = mst := by rw [← getElem!_pos masters 0 hszmas]; exact hmst.symm
  unfold jpeg_core_output_dimensions
  rw [Ptr.load_bind h _ 0 dcs _ hgetdc hszdc, hdc0, hmas]
  rw [Ptr.load_bind h _ 0 masters _ hgetmas hszmas, hmst0]
  have hro_dc : C.Space.ro h (C.DecompRef.decomp bdc) = false := rfl
  by_cases hll : (mst.lossless == 0) = true
  · simp only [hll, ↓reduceIte]
    obtain ⟨hk1, hk16⟩ := selectIdctScale_bounds dc.scaleNum dc.scaleDenom
    let k := selectIdctScale dc.scaleNum dc.scaleDenom
    have hk_bd : 1 ≤ k.toNat ∧ k.toNat ≤ 16 := ⟨hk1, hk16⟩
    have hwk := int_mul_bounds (Int.natCast_nonneg _) (Int.ofNat_le.mpr hdim.1)
      (Int.natCast_nonneg _) (Int.ofNat_le.mpr hk_bd.2)
    have hhk := int_mul_bounds (Int.natCast_nonneg _) (Int.ofNat_le.mpr hdim.2)
      (Int.natCast_nonneg _) (Int.ofNat_le.mpr hk_bd.2)
    have hiw64 : (Int64.ofNat dc.imageWidth.toNat).toInt = (dc.imageWidth.toNat : Int) := int64_toInt_ofNat (by omega)
    have hih64 : (Int64.ofNat dc.imageHeight.toNat).toInt = (dc.imageHeight.toNat : Int) := int64_toInt_ofNat (by omega)
    have hk64 : (Int64.ofNat k.toNat).toInt = (k.toNat : Int) := int64_toInt_ofNat (by omega)
    have hkw_ok := i64Mul_eq (Int64.ofNat dc.imageWidth.toNat) (Int64.ofNat k.toNat)
      (by rw [hiw64, hk64]; omega)
      (by rw [hiw64, hk64]; omega)
    have hkh_ok := i64Mul_eq (Int64.ofNat dc.imageHeight.toNat) (Int64.ofNat k.toNat)
      (by rw [hih64, hk64]; omega)
      (by rw [hih64, hk64]; omega)
    let w64 := Int64.ofInt ((Int64.ofNat dc.imageWidth.toNat).toInt * (Int64.ofNat k.toNat).toInt)
    let h64 := Int64.ofInt ((Int64.ofNat dc.imageHeight.toNat).toInt * (Int64.ofNat k.toNat).toInt)
    have hw64_v : 0 ≤ w64.toInt ∧ w64.toInt ≤ 65500 * 16 := by
      dsimp [w64]; simp only [hiw64, hk64]; rw [toInt_ofInt64 (by omega) (by omega)]; exact hwk
    have hh64_v : 0 ≤ h64.toInt ∧ h64.toInt ≤ 65500 * 16 := by
      dsimp [h64]; simp only [hih64, hk64]; rw [toInt_ofInt64 (by omega) (by omega)]; exact hhk
    have h8 : (8 : Int64).toInt = 8 := rfl
    obtain ⟨outW, houtW⟩ := MozjpegF.Proof.Jutils.jdiv_round_up_safety h w64 8
      hw64_v.1 (by decide) (by simp only [h8]; omega)
    obtain ⟨outH, houtH⟩ := MozjpegF.Proof.Jutils.jdiv_round_up_safety h h64 8
      hh64_v.1 (by decide) (by simp only [h8]; omega)
    rw [hkw_ok, pure_bind_m]
    have houtW_bind : ∀ (f : Int64 → M Unit),
        C.run (jdiv_round_up w64 8 >>= f) h = C.run (f outW) h := by
      intro f; simp only [C.run, bind] at houtW ⊢; rw [houtW]
    rw [houtW_bind, hkh_ok, pure_bind_m]
    have houtH_bind : ∀ (f : Int64 → M Unit),
        C.run (jdiv_round_up h64 8 >>= f) h = C.run (f outH) h := by
      intro f; simp only [C.run, bind] at houtH ⊢; rw [houtH]
    rw [houtH_bind]
    let k32 := Int32.ofNat k.toNat
    let dc1 := {
      dc with
      outputWidth := outW.toInt.toNat.toUInt32
      outputHeight := outH.toInt.toNat.toUInt32
      minDctHScaledSize := k32
      minDctVScaledSize := k32
    }
    rw [← hmas]
    rw [Ptr.store_bind h _ 0 dc1 dcs _ hgetdc hro_dc hszdc]
    let h1 := C.Space.put h (C.DecompRef.decomp bdc) (dcs.set! 0 dc1)
    have hgetdc1 : C.Space.get h1 (C.DecompRef.decomp bdc) = some (dcs.set! 0 dc1) := by
      simp [h1, C.Space.get, C.Space.put]
    have hszdc1 : 0 < (dcs.set! 0 dc1).size := by rw [Array.size_set!]; exact hszdc
    change ∃ h', C.run _ h1 = .ok ((), h')
    rw [Ptr.load_bind h1 _ 0 (dcs.set! 0 dc1) _ hgetdc1 hszdc1]
    have hdc1_eq : (dcs.set! 0 dc1)[0] = dc1 := by simp [Array.set!_eq_setIfInBounds]
    rw [hdc1_eq]
    have hnc_neg : ¬ (dc1.numComponents < 0) := by
      intro hlt
      have hlt' := Int32.lt_iff_toInt_lt.mp hlt
      have h0 : (0 : Int32).toInt = 0 := rfl
      have : dc1.numComponents = dc.numComponents := rfl
      rw [this, h0] at hlt'; omega
    simp only [hnc_neg, ↓reduceIte]
    dsimp only [dc1]
    rw [hci]
    have hgetcomp1 : h1.comps bcomp = some comps := hgetcomp
    obtain ⟨comps', _, _, hset_run⟩ := setCompScaledSizes_ok h1 bcomp comps
      dc.numComponents.toInt.toNat k32 hgetcomp1 hszcomp 0 (Nat.zero_le _)
    exact ⟨_, hset_run⟩
  · have hllF : (mst.lossless == 0) = false := Bool.eq_false_iff.mpr hll
    simp only [hllF, Bool.false_eq_true, ↓reduceIte]
    simp [C.run, Ptr.store, hgetdc, hro_dc, hszdc]

private theorem use_merged_upsample_ok (h : C.Heap) (cinfo : C.DecompPtr)
    (hvalid : ValidDecompDimsInput h cinfo false) :
    ∃ res, C.run (use_merged_upsample cinfo) h = .ok (res, h) := by
  obtain ⟨_hcore, rc, dcs, dc, rmas, masters, mst,
    hc, hgetdc, hszdc, hdc, hmas, hgetmas, hszmas, hmst, _,
    _hnc, _, _, _, hcomp⟩ := hvalid
  subst hc
  obtain ⟨rcomp, comps, hci, hgetcomp, hszcomp, _⟩ := hcomp
  cases rc with | decomp bdc =>
  cases rmas with | master bmas =>
  cases rcomp with | comp bcomp =>
  have hdc0 : dcs[0] = dc := by rw [← getElem!_pos dcs 0 hszdc]; exact hdc.symm
  have hmst0 : masters[0] = mst := by rw [← getElem!_pos masters 0 hszmas]; exact hmst.symm
  unfold use_merged_upsample
  rw [Ptr.load_bind h _ 0 dcs _ hgetdc hszdc, hdc0, hmas]
  rw [Ptr.load_bind h _ 0 masters _ hgetmas hszmas, hmst0]
  by_cases hll : (mst.lossless != 0) = true
  · simp only [hll, ↓reduceIte]; exact ⟨_, rfl⟩
  · have hllF := Bool.eq_false_iff.mpr hll
    simp only [hllF, Bool.false_eq_true, ↓reduceIte]
    by_cases hfu : (dc.doFancyUpsampling != 0 || dc.ccir601Sampling != 0) = true
    · simp only [hfu, ↓reduceIte]; exact ⟨_, rfl⟩
    · have hfuF := Bool.eq_false_iff.mpr hfu
      simp only [hfuF, Bool.false_eq_true, ↓reduceIte]
      by_cases hsupp : (dc.jpegColorSpace != JCS_YCbCr || dc.numComponents != 3 ||
        !(dc.outColorSpace == JCS_RGB || dc.outColorSpace == JCS_RGB565 ||
          (dc.outColorSpace ≥ JCS_EXT_RGB && dc.outColorSpace ≤ JCS_EXT_ARGB))) = true
      · simp only [hsupp, ↓reduceIte]; exact ⟨_, rfl⟩
      · have hsuppF := Bool.eq_false_iff.mpr hsupp
        simp only [hsuppF, Bool.false_eq_true, ↓reduceIte]
        have hnc3 : dc.numComponents = 3 := by
          exact Classical.byContradiction fun hne => by
            apply hsupp
            have : (dc.numComponents != 3) = true := bne_iff_ne.mpr hne
            simp [this]
        have hcs : dc.outColorSpace = JCS_RGB565 ∨
            (0 ≤ dc.outColorSpace.toInt ∧ dc.outColorSpace.toInt < 17) := by
          by_cases h565 : dc.outColorSpace == JCS_RGB565
          · left; exact beq_iff_eq.mp h565
          · right
            have : (dc.outColorSpace == JCS_RGB || dc.outColorSpace == JCS_RGB565 ||
              (dc.outColorSpace ≥ JCS_EXT_RGB && dc.outColorSpace ≤ JCS_EXT_ARGB)) = true := by
              exact Classical.byContradiction fun hn => by
                apply hsupp; simp [hn]
            simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
            have hr1 : JCS_RGB.toInt = 2 := rfl
            have hr2 : JCS_RGB565.toInt = 16 := rfl
            have hr3 : JCS_EXT_RGB.toInt = 6 := rfl
            have hr4 : JCS_EXT_ARGB.toInt = 15 := rfl
            rcases this with (h1 | h2) | ⟨h3, h4⟩
            · rw [h1, hr1]; omega
            · exfalso; exact h565 (beq_iff_eq.mpr h2)
            · have ha : JCS_EXT_RGB.toInt ≤ dc.outColorSpace.toInt := Int32.le_iff_toInt_le.mp h3
              have hb : dc.outColorSpace.toInt ≤ JCS_EXT_ARGB.toInt := Int32.le_iff_toInt_le.mp h4
              omega
        have hcomp_sz3 : 3 ≤ comps.size := by
          have : dc.numComponents.toInt.toNat = 3 := by rw [hnc3]; rfl
          omega
        have htail : ∀ ps : Int32, ∃ res, C.run (do
            if dc.outColorComponents != ps then return FALSE
            let c0 ← Ptr.index dc.compInfo 0
            let c1 ← Ptr.index dc.compInfo 1
            let c2 ← Ptr.index dc.compInfo 2
            if c0.hSampFactor != 2 || c1.hSampFactor != 1 || c2.hSampFactor != 1 ||
               c0.vSampFactor > 2 || c1.vSampFactor != 1 || c2.vSampFactor != 1 then return FALSE
            if c0.dctHScaledSize != dc.minDctHScaledSize ||
               c1.dctHScaledSize != dc.minDctHScaledSize ||
               c2.dctHScaledSize != dc.minDctHScaledSize then return FALSE
            return TRUE) h = .ok (res, h) := by
          intro ps
          by_cases hcc : (dc.outColorComponents != ps) = true
          · simp only [hcc, ↓reduceIte]; exact ⟨_, rfl⟩
          · have hccF := Bool.eq_false_iff.mpr hcc
            simp only [hccF, Bool.false_eq_true, ↓reduceIte, hci]
            have hget_c : C.Space.get h (C.CompRef.comp bcomp) = some comps := hgetcomp
            have ha0 : 0 ≤ comps.size ∧ 0 ≤ ((0 : Nat) : Int) + 0 ∧ ((0 : Nat) : Int) + 0 ≤ (comps.size : Int) := by omega
            have ha1 : 0 ≤ comps.size ∧ 0 ≤ ((0 : Nat) : Int) + 1 ∧ ((0 : Nat) : Int) + 1 ≤ (comps.size : Int) := by omega
            have ha2 : 0 ≤ comps.size ∧ 0 ≤ ((0 : Nat) : Int) + 2 ∧ ((0 : Nat) : Int) + 2 ≤ (comps.size : Int) := by omega
            simp only [Ptr.index, bind_assoc_m]
            rw [Ptr.add_bind h _ 0 0 comps _ hget_c ha0]
            simp only [Int.natCast_zero, Int.add_zero, Int.toNat_zero]
            rw [Ptr.load_bind h _ 0 comps _ hget_c (by omega)]
            rw [Ptr.add_bind h _ 0 1 comps _ hget_c ha1]
            simp only [Int.natCast_zero, Int.zero_add]
            have ha1_nat : (1 : Int).toNat = 1 := rfl
            rw [ha1_nat, Ptr.load_bind h _ 1 comps _ hget_c (by omega)]
            rw [Ptr.add_bind h _ 0 2 comps _ hget_c ha2]
            simp only [Int.natCast_zero, Int.zero_add]
            have ha2_nat : (2 : Int).toNat = 2 := rfl
            rw [ha2_nat, Ptr.load_bind h _ 2 comps _ hget_c (by omega)]
            by_cases h1 : (comps[0].hSampFactor != 2 || comps[1].hSampFactor != 1 || comps[2].hSampFactor != 1 ||
                comps[0].vSampFactor > 2 || comps[1].vSampFactor != 1 || comps[2].vSampFactor != 1) = true
            · simp only [h1, ↓reduceIte]; exact ⟨_, rfl⟩
            · have h1F := Bool.eq_false_iff.mpr h1
              simp only [h1F, Bool.false_eq_true, ↓reduceIte]
              by_cases h2 : (comps[0].dctHScaledSize != dc.minDctHScaledSize ||
                  comps[1].dctHScaledSize != dc.minDctHScaledSize ||
                  comps[2].dctHScaledSize != dc.minDctHScaledSize) = true
              · simp only [h2, ↓reduceIte]; exact ⟨_, rfl⟩
              · have h2F := Bool.eq_false_iff.mpr h2
                simp only [h2F, Bool.false_eq_true, ↓reduceIte]; exact ⟨_, rfl⟩
        by_cases h565 : (dc.outColorSpace == JCS_RGB565) = true
        · simp only [h565, ↓reduceIte, pure_bind_m]
          exact htail 3
        · have h565F := Bool.eq_false_iff.mpr h565
          have hrng : 0 ≤ dc.outColorSpace.toInt ∧ dc.outColorSpace.toInt < 17 := by
            rcases hcs with heq | hr
            · exfalso; exact h565 (beq_iff_eq.mpr heq)
            · exact hr
          obtain ⟨ps, hps⟩ := rgbPixelSize_ok dc.outColorSpace hrng
          simp only [h565F, Bool.false_eq_true, ↓reduceIte, hps, pure_bind_m]
          exact htail ps

private theorem finish_calc_dims_safety (h2 : C.Heap) (bdc bmas : Nat)
    (dcs2 : Array C.JpegDecompressStruct) (dc1 : C.JpegDecompressStruct)
    (masters : Array C.JpegDecompMaster) (mst : C.JpegDecompMaster)
    (hvalid2 : ValidDecompDimsInput h2 (.ref (C.DecompRef.decomp bdc) 0) false)
    (hgetdc2 : h2.decomps bdc = some dcs2) (hszdc2 : 0 < dcs2.size) (hdc2_bang : dc1 = dcs2[0]!)
    (hmas1 : dc1.master = .ref (.master bmas) 0)
    (hgetmas1 : h2.masters bmas = some masters) (hszmas : 0 < masters.size) (hmst : mst = masters[0]!)
    (hnc : 0 ≤ dc1.numComponents.toInt ∧ dc1.numComponents.toInt ≤ 10)
    (hdim : dc1.imageWidth.toNat ≤ 65500 ∧ dc1.imageHeight.toNat ≤ 65500)
    (hmaxh : 1 ≤ dc1.maxHSampFactor.toInt ∧ dc1.maxHSampFactor.toInt ≤ 4)
    (hmaxv : 1 ≤ dc1.maxVSampFactor.toInt ∧ dc1.maxVSampFactor.toInt ≤ 4) :
    ∃ h' dcs', C.run ((do
      let dc ← Ptr.load (Ptr.ref (C.DecompRef.decomp bdc) 0)
      let outCC ←
        if dc.outColorSpace == JCS_GRAYSCALE then pure (1 : Int32)
        else if dc.outColorSpace == JCS_RGB ||
                (dc.outColorSpace ≥ JCS_EXT_RGB && dc.outColorSpace ≤ JCS_EXT_ARGB) then
          rgbPixelSize dc.outColorSpace
        else if dc.outColorSpace == JCS_YCbCr || dc.outColorSpace == JCS_RGB565 then pure (3 : Int32)
        else if dc.outColorSpace == JCS_CMYK || dc.outColorSpace == JCS_YCCK then pure (4 : Int32)
        else pure dc.numComponents
      let outComps : Int32 := if dc.quantizeColors != 0 then 1 else outCC
      Ptr.store (Ptr.ref (C.DecompRef.decomp bdc) 0) { dc with outColorComponents := outCC, outputComponents := outComps }
      let merged ← use_merged_upsample (Ptr.ref (C.DecompRef.decomp bdc) 0)
      let dc ← Ptr.load (Ptr.ref (C.DecompRef.decomp bdc) 0)
      let recH : Int32 := if merged != 0 then dc.maxVSampFactor else 1
      Ptr.store (Ptr.ref (C.DecompRef.decomp bdc) 0) { dc with recOutbufHeight := recH }
      return .ok ()) : M (JpegRes Unit)) h2 = .ok (.ok (), h') ∧
      h'.decomps bdc = some dcs' ∧ 0 < dcs'.size ∧
      dcs'[0]!.outputWidth = dc1.outputWidth ∧ dcs'[0]!.outputHeight = dc1.outputHeight := by
  have hdc2_pos : dcs2[0] = dc1 := by rw [← getElem!_pos dcs2 0 hszdc2]; exact hdc2_bang.symm
  have hgetdc2' : C.Space.get h2 (C.DecompRef.decomp bdc) = some dcs2 := hgetdc2
  rw [Ptr.load_bind h2 _ 0 dcs2 _ hgetdc2' hszdc2, hdc2_pos]
  have htail_outcc : ∀ outCC : Int32,
      ∃ h' dcs', C.run (do
        let outComps : Int32 := if dc1.quantizeColors != 0 then 1 else outCC
        Ptr.store (Ptr.ref (C.DecompRef.decomp bdc) 0) { dc1 with outColorComponents := outCC, outputComponents := outComps }
        let merged ← use_merged_upsample (Ptr.ref (C.DecompRef.decomp bdc) 0)
        let dc ← Ptr.load (Ptr.ref (C.DecompRef.decomp bdc) 0)
        let recH : Int32 := if merged != 0 then dc.maxVSampFactor else 1
        Ptr.store (Ptr.ref (C.DecompRef.decomp bdc) 0) { dc with recOutbufHeight := recH }
        return (.ok () : JpegRes Unit)) h2 = .ok (.ok (), h') ∧
        h'.decomps bdc = some dcs' ∧ 0 < dcs'.size ∧
        dcs'[0]!.outputWidth = dc1.outputWidth ∧ dcs'[0]!.outputHeight = dc1.outputHeight := by
    intro outCC
    let outComps := if dc1.quantizeColors != 0 then 1 else outCC
    let dc3 := { dc1 with outColorComponents := outCC, outputComponents := outComps }
    have hro_dc2 : C.Space.ro h2 (C.DecompRef.decomp bdc) = false := rfl
    rw [Ptr.store_bind h2 _ 0 dc3 dcs2 _ hgetdc2' hro_dc2 hszdc2]
    let h3 := C.Space.put h2 (C.DecompRef.decomp bdc) (dcs2.set! 0 dc3)
    have hgetdc3 : C.Space.get h3 (C.DecompRef.decomp bdc) = some (dcs2.set! 0 dc3) := by
      simp [h3, C.Space.get, C.Space.put]
    have hszdc3 : 0 < (dcs2.set! 0 dc3).size := by rw [Array.size_set!]; exact hszdc2
    have hdc3_bang : (dcs2.set! 0 dc3)[0]! = dc3 := by
      rw [getElem!_pos _ 0 hszdc3]; simp [Array.set!_eq_setIfInBounds]
    have hvalid3 : ValidDecompDimsInput h3 (.ref (C.DecompRef.decomp bdc) 0) false := by
      obtain ⟨⟨_rc2, _dcs2, _dc2, _rm2, _mems2, _rmas2, _masters2, _ric2, _ics2, _rmrk2, _mrks2,
        _hc2', _hgdc2, _hszdc2, _hdc2, _herr2, _hm2, _hgm2, _hzm2, _hmas2, _hgmas2, _hzmas2,
        _hin2, _hgin2, _hzin2, _hmrk2, _hgmrk2, _hzmrk2, _hpsz2, _hpd2⟩,
        _rc2', _dcs2', _dc2', _, _, _, _hc2'', _hgdc2', _, _hdc2',
        _, _, _, _, _, _, _, _, _, hcomp3⟩ := hvalid2
      have hdc2_same : _dc2 = dc1 := by
        have hrc_eq : _rc2 = .decomp bdc := C.Ptr.ref.inj _hc2'.symm |>.1
        rw [hrc_eq] at _hgdc2
        have hdcs_eq : _dcs2 = dcs2 := Option.some.inj (_hgdc2.symm.trans hgetdc2)
        rw [_hdc2, hdcs_eq, ← hdc2_bang]
      have hdc2'_same : _dc2' = dc1 := by
        have hrc_eq : _rc2' = .decomp bdc := C.Ptr.ref.inj _hc2''.symm |>.1
        rw [hrc_eq] at _hgdc2'
        have hdcs_eq : _dcs2' = dcs2 := Option.some.inj (_hgdc2'.symm.trans hgetdc2)
        rw [_hdc2', hdcs_eq, ← hdc2_bang]
      rw [hdc2_same] at _herr2 _hm2 _hmas2 _hin2 _hmrk2
      rw [hdc2'_same] at hcomp3
      have hrmas2_eq : _rmas2 = .master bmas := C.Ptr.ref.inj (_hmas2.symm.trans hmas1) |>.1
      subst hrmas2_eq
      exact ⟨⟨.decomp bdc, dcs2.set! 0 dc3, dc3, _rm2, _mems2, .master bmas, masters, _ric2, _ics2, _rmrk2, _mrks2,
        rfl, hgetdc3, hszdc3, hdc3_bang.symm, _herr2, _hm2, _hgm2, _hzm2, hmas1, hgetmas1, hszmas,
        _hin2, _hgin2, _hzin2, _hmrk2, _hgmrk2, _hzmrk2, _hpsz2, _hpd2⟩,
        .decomp bdc, dcs2.set! 0 dc3, dc3, .master bmas, masters, mst,
        rfl, hgetdc3, hszdc3, hdc3_bang.symm, hmas1, hgetmas1, hszmas, hmst, rfl,
        hnc, hdim, hmaxh, hmaxv, hcomp3⟩
    obtain ⟨merged, hmerged⟩ := use_merged_upsample_ok h3 (.ref (C.DecompRef.decomp bdc) 0) hvalid3
    rw [run_bind _ _ h3 h3 merged hmerged]
    have hdc3_pos : (dcs2.set! 0 dc3)[0] = dc3 := by rw [← getElem!_pos _ 0 hszdc3]; exact hdc3_bang
    rw [Ptr.load_bind h3 _ 0 (dcs2.set! 0 dc3) _ hgetdc3 hszdc3, hdc3_pos]
    let recH := if merged != 0 then dc3.maxVSampFactor else 1
    let dc4 := { dc3 with recOutbufHeight := recH }
    have hro_dc3 : C.Space.ro h3 (C.DecompRef.decomp bdc) = false := rfl
    rw [Ptr.store_bind h3 _ 0 dc4 (dcs2.set! 0 dc3) _ hgetdc3 hro_dc3 hszdc3]
    let dcs4 := (dcs2.set! 0 dc3).set! 0 dc4
    let h4 := C.Space.put h3 (C.DecompRef.decomp bdc) dcs4
    have hsz4 : 0 < dcs4.size := by simp [dcs4]; exact hszdc2
    refine ⟨h4, dcs4, rfl, ?_, hsz4, ?_, ?_⟩
    · simp [h4, C.Space.put]
    · rw [getElem!_pos dcs4 0 hsz4]; simp [dcs4, Array.set!_eq_setIfInBounds]; rfl
    · rw [getElem!_pos dcs4 0 hsz4]; simp [dcs4, Array.set!_eq_setIfInBounds]; rfl
  by_cases hg : (dc1.outColorSpace == JCS_GRAYSCALE) = true
  · simp only [hg, ↓reduceIte, pure_bind_m]; exact htail_outcc 1
  · have hgF := Bool.eq_false_iff.mpr hg
    simp only [hgF, Bool.false_eq_true, ↓reduceIte]
    by_cases hrgb : (dc1.outColorSpace == JCS_RGB ||
        (dc1.outColorSpace ≥ JCS_EXT_RGB && dc1.outColorSpace ≤ JCS_EXT_ARGB)) = true
    · have hrng : 0 ≤ dc1.outColorSpace.toInt ∧ dc1.outColorSpace.toInt < 17 := by
        have hrgb' := hrgb
        simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hrgb'
        have hr1 : JCS_RGB.toInt = 2 := rfl
        have hr2 : JCS_EXT_RGB.toInt = 6 := rfl
        have hr3 : JCS_EXT_ARGB.toInt = 15 := rfl
        rcases hrgb' with h1 | ⟨h2, h3⟩
        · rw [h1, hr1]; omega
        · have ha : JCS_EXT_RGB.toInt ≤ dc1.outColorSpace.toInt := Int32.le_iff_toInt_le.mp h2
          have hb : dc1.outColorSpace.toInt ≤ JCS_EXT_ARGB.toInt := Int32.le_iff_toInt_le.mp h3
          omega
      obtain ⟨ps, hps⟩ := rgbPixelSize_ok dc1.outColorSpace hrng
      simp only [hrgb, ↓reduceIte, hps, pure_bind_m]; exact htail_outcc ps
    · have hrgbF := Bool.eq_false_iff.mpr hrgb
      simp only [hrgbF, Bool.false_eq_true, ↓reduceIte]
      by_cases hycc : (dc1.outColorSpace == JCS_YCbCr || dc1.outColorSpace == JCS_RGB565) = true
      · simp only [hycc, ↓reduceIte, pure_bind_m]; exact htail_outcc 3
      · have hyccF := Bool.eq_false_iff.mpr hycc
        simp only [hyccF, Bool.false_eq_true, ↓reduceIte]
        by_cases hcmyk : (dc1.outColorSpace == JCS_CMYK || dc1.outColorSpace == JCS_YCCK) = true
        · simp only [hcmyk, ↓reduceIte, pure_bind_m]; exact htail_outcc 4
        · have hcmykF := Bool.eq_false_iff.mpr hcmyk
          simp only [hcmykF, Bool.false_eq_true, ↓reduceIte, pure_bind_m]; exact htail_outcc dc1.numComponents

theorem jpeg_calc_output_dimensions_safety : Goal.jpeg_calc_output_dimensions_safety := by
  intro h cinfo hvalid
  obtain ⟨⟨_rc0, _dcs0, _dc0, rm, mems, _rmas0, _masters0, ric, ics, rmrk, mrks,
    hc', hgetdc', hszdc', hdc', herrValid, hmem, hgetmem, hszmem, hmas0, _, _,
    hin, hgetin, hszin, hmrk, hgetmrk, hszmrk, hpsz, hpd⟩,
    rc, dcs, dc, rmas, masters, mst,
    hc, hgetdc, hszdc, hdc, hmas, hgetmas, hszmas, hmst, _,
    hnc, hdim, hmaxh, hmaxv, hcomp⟩ := hvalid
  have hdc_same : _dc0 = dc := by
    have hrc_eq : _rc0 = rc := C.Ptr.ref.inj (hc'.symm.trans hc) |>.1
    rw [hrc_eq] at hgetdc'
    have hdcs_eq : _dcs0 = dcs := Option.some.inj (hgetdc'.symm.trans hgetdc)
    rw [hdc', hdcs_eq, ← hdc]
  rw [hdc_same] at herrValid hmem hmas0 hin hmrk
  obtain ⟨rerr, errs, herr, hgeterr, hszerr⟩ := herrValid
  obtain ⟨rcomp, comps, hci, hgetcomp, hszcomp, hsamp⟩ := hcomp
  subst hc
  cases rc with | decomp bdc =>
  cases rerr with | err berr =>
  cases rmas with | master bmas =>
  cases rcomp with | comp bcomp =>
  have hrmas0_eq : _rmas0 = .master bmas := C.Ptr.ref.inj (hmas0.symm.trans hmas) |>.1
  subst hrmas0_eq
  have hdc0 : dcs[0] = dc := by rw [← getElem!_pos dcs 0 hszdc]; exact hdc.symm
  have hmst0 : masters[0] = mst := by rw [← getElem!_pos masters 0 hszmas]; exact hmst.symm
  unfold jpeg_calc_output_dimensions Mozjpeg.JerrorH.errexit1
  rw [Ptr.load_bind h _ 0 dcs _ hgetdc hszdc, hdc0]
  by_cases hnotready : (dc.globalState != DSTATE_READY) = true
  · simp only [hnotready, ↓reduceIte, bind_assoc_m, pure_bind_m]
    rw [herr]
    rw [Ptr.load_bind h _ 0 errs _ hgeterr hszerr]
    have hro_err : C.Space.ro h (C.ErrRef.err berr) = false := rfl
    rw [Ptr.store_bind h _ 0 _ errs _ hgeterr hro_err hszerr]
    exact ⟨_, _, rfl⟩
  · have hreadyF := Bool.eq_false_iff.mpr hnotready
    simp only [hreadyF, Bool.false_eq_true, ↓reduceIte]
    have hcore_ok : ∃ h1 dcs1 dc1 comps1,
        C.run (jpeg_core_output_dimensions (.ref (C.DecompRef.decomp bdc) 0)) h = .ok ((), h1) ∧
        ValidDecompDimsInput h1 (.ref (C.DecompRef.decomp bdc) 0) false ∧
        h1.decomps bdc = some dcs1 ∧ 0 < dcs1.size ∧ dc1 = dcs1[0]! ∧
        dc1.master = .ref (C.MasterRef.master bmas) 0 ∧ h1.masters bmas = some masters ∧
        dc1.compInfo = .ref (C.CompRef.comp bcomp) 0 ∧ h1.comps bcomp = some comps1 ∧
        comps1.size = comps.size ∧
        dc1.numComponents = dc.numComponents ∧ dc1.imageWidth = dc.imageWidth ∧
        dc1.imageHeight = dc.imageHeight ∧ dc1.maxHSampFactor = dc.maxHSampFactor ∧
        dc1.maxVSampFactor = dc.maxVSampFactor ∧
        (mst.lossless = 0 → 1 ≤ dc1.minDctHScaledSize.toInt ∧ dc1.minDctHScaledSize.toInt ≤ 16) ∧
        (∀ i, i < dc.numComponents.toInt.toNat →
          1 ≤ (comps1[i]!).hSampFactor.toInt ∧ (comps1[i]!).hSampFactor.toInt ≤ 4 ∧
          1 ≤ (comps1[i]!).vSampFactor.toInt ∧ (comps1[i]!).vSampFactor.toInt ≤ 4) := by
      unfold jpeg_core_output_dimensions
      rw [Ptr.load_bind h _ 0 dcs _ hgetdc hszdc, hdc0, hmas]
      rw [Ptr.load_bind h _ 0 masters _ hgetmas hszmas, hmst0]
      have hro_dc : C.Space.ro h (C.DecompRef.decomp bdc) = false := rfl
      by_cases hll : (mst.lossless == 0) = true
      · simp only [hll, ↓reduceIte]
        obtain ⟨hk1, hk16⟩ := selectIdctScale_bounds dc.scaleNum dc.scaleDenom
        let k := selectIdctScale dc.scaleNum dc.scaleDenom
        have hk_bd : 1 ≤ k.toNat ∧ k.toNat ≤ 16 := ⟨hk1, hk16⟩
        have hwk := int_mul_bounds (Int.natCast_nonneg _) (Int.ofNat_le.mpr hdim.1)
          (Int.natCast_nonneg _) (Int.ofNat_le.mpr hk_bd.2)
        have hhk := int_mul_bounds (Int.natCast_nonneg _) (Int.ofNat_le.mpr hdim.2)
          (Int.natCast_nonneg _) (Int.ofNat_le.mpr hk_bd.2)
        have hiw64 : (Int64.ofNat dc.imageWidth.toNat).toInt = (dc.imageWidth.toNat : Int) := int64_toInt_ofNat (by omega)
        have hih64 : (Int64.ofNat dc.imageHeight.toNat).toInt = (dc.imageHeight.toNat : Int) := int64_toInt_ofNat (by omega)
        have hk64 : (Int64.ofNat k.toNat).toInt = (k.toNat : Int) := int64_toInt_ofNat (by omega)
        have hkw_ok := i64Mul_eq (Int64.ofNat dc.imageWidth.toNat) (Int64.ofNat k.toNat)
          (by rw [hiw64, hk64]; omega)
          (by rw [hiw64, hk64]; omega)
        have hkh_ok := i64Mul_eq (Int64.ofNat dc.imageHeight.toNat) (Int64.ofNat k.toNat)
          (by rw [hih64, hk64]; omega)
          (by rw [hih64, hk64]; omega)
        let w64 := Int64.ofInt ((Int64.ofNat dc.imageWidth.toNat).toInt * (Int64.ofNat k.toNat).toInt)
        let h64 := Int64.ofInt ((Int64.ofNat dc.imageHeight.toNat).toInt * (Int64.ofNat k.toNat).toInt)
        have hw64_v : 0 ≤ w64.toInt ∧ w64.toInt ≤ 65500 * 16 := by
          dsimp [w64]; simp only [hiw64, hk64]; rw [toInt_ofInt64 (by omega) (by omega)]; exact hwk
        have hh64_v : 0 ≤ h64.toInt ∧ h64.toInt ≤ 65500 * 16 := by
          dsimp [h64]; simp only [hih64, hk64]; rw [toInt_ofInt64 (by omega) (by omega)]; exact hhk
        have h8 : (8 : Int64).toInt = 8 := rfl
        obtain ⟨outW, houtW⟩ := MozjpegF.Proof.Jutils.jdiv_round_up_safety h w64 8 hw64_v.1 (by decide) (by simp only [h8]; omega)
        obtain ⟨outH, houtH⟩ := MozjpegF.Proof.Jutils.jdiv_round_up_safety h h64 8 hh64_v.1 (by decide) (by simp only [h8]; omega)
        rw [hkw_ok, pure_bind_m]
        have houtW_bind : ∀ (f : Int64 → M Unit), C.run (jdiv_round_up w64 8 >>= f) h = C.run (f outW) h := by
          intro f; simp only [C.run, bind] at houtW ⊢; rw [houtW]
        rw [houtW_bind, hkh_ok, pure_bind_m]
        have houtH_bind : ∀ (f : Int64 → M Unit), C.run (jdiv_round_up h64 8 >>= f) h = C.run (f outH) h := by
          intro f; simp only [C.run, bind] at houtH ⊢; rw [houtH]
        rw [houtH_bind]
        let k32 := Int32.ofNat k.toNat
        let dc1 := { dc with outputWidth := outW.toInt.toNat.toUInt32, outputHeight := outH.toInt.toNat.toUInt32,
                             minDctHScaledSize := k32, minDctVScaledSize := k32 }
        rw [← hmas]
        rw [Ptr.store_bind h _ 0 dc1 dcs _ hgetdc hro_dc hszdc]
        let h1a := C.Space.put h (C.DecompRef.decomp bdc) (dcs.set! 0 dc1)
        have hgetdc1a : C.Space.get h1a (C.DecompRef.decomp bdc) = some (dcs.set! 0 dc1) := by
          simp [h1a, C.Space.get, C.Space.put]
        have hszdc1a : 0 < (dcs.set! 0 dc1).size := by rw [Array.size_set!]; exact hszdc
        rw [Ptr.load_bind h1a _ 0 (dcs.set! 0 dc1) _ hgetdc1a hszdc1a]
        have hdc1a_eq : (dcs.set! 0 dc1)[0] = dc1 := by simp [Array.set!_eq_setIfInBounds]
        rw [hdc1a_eq]
        have hnc_neg : ¬ (dc1.numComponents < 0) := by
          intro hlt
          have hlt' := Int32.lt_iff_toInt_lt.mp hlt
          have h0 : (0 : Int32).toInt = 0 := rfl
          have : dc1.numComponents = dc.numComponents := rfl
          rw [this, h0] at hlt'; omega
        simp only [hnc_neg, ↓reduceIte]
        have hci1 : dc1.compInfo = .ref (C.CompRef.comp bcomp) 0 := hci
        have hdc1_nc : dc1.numComponents = dc.numComponents := rfl
        dsimp only [dc1]
        rw [hci]
        have hgetcomp1a : h1a.comps bcomp = some comps := hgetcomp
        obtain ⟨comps1, hsz1, hsamp1, hset_run⟩ := setCompScaledSizes_ok h1a bcomp comps
          dc1.numComponents.toInt.toNat k32 hgetcomp1a hszcomp 0 (Nat.zero_le _)
        let h1 := C.Space.put h1a (C.CompRef.comp bcomp) comps1
        have hgetdc1 : h1.decomps bdc = some (dcs.set! 0 dc1) := by simp [h1, h1a, C.Space.put]
        have hdc1_bang : (dcs.set! 0 dc1)[0]! = dc1 := by rw [getElem!_pos _ 0 hszdc1a]; exact hdc1a_eq
        have hgetcomp1 : h1.comps bcomp = some comps1 := by simp [h1, C.Space.put]
        have hsamp1' : ∀ i, i < dc1.numComponents.toInt.toNat →
            1 ≤ (comps1[i]!).hSampFactor.toInt ∧ (comps1[i]!).hSampFactor.toInt ≤ 4 ∧
            1 ≤ (comps1[i]!).vSampFactor.toInt ∧ (comps1[i]!).vSampFactor.toInt ≤ 4 := by
          intro i hi
          have hi' : i < dc.numComponents.toInt.toNat := by rw [← hdc1_nc]; exact hi
          have hhi := hsamp1 i (by omega)
          obtain ⟨hsa, hsb, hsc, hsd⟩ := hsamp i hi'
          rw [hhi.1, hhi.2]; exact ⟨hsa, hsb, hsc, hsd⟩
        refine ⟨h1, dcs.set! 0 dc1, dc1, comps1, hset_run, ?_, hgetdc1, hszdc1a, hdc1_bang.symm, rfl, hgetmas,
          hci1, hgetcomp1, hsz1, rfl, rfl, rfl, rfl, rfl, fun _ => ?_, hsamp1'⟩
        · refine ⟨⟨.decomp bdc, dcs.set! 0 dc1, dc1, rm, mems, .master bmas, masters, ric, ics, rmrk, mrks,
            rfl, hgetdc1, hszdc1a, hdc1_bang.symm, ⟨.err berr, errs, herr, hgeterr, hszerr⟩, hmem, hgetmem, hszmem, hmas, hgetmas, hszmas,
            hin, hgetin, hszin, hmrk, hgetmrk, hszmrk, hpsz, hpd⟩,
            .decomp bdc, dcs.set! 0 dc1, dc1, .master bmas, masters, mst,
            rfl, hgetdc1, hszdc1a, hdc1_bang.symm, hmas, hgetmas, hszmas, hmst, rfl,
            by rw [hdc1_nc]; exact hnc, hdim, hmaxh, hmaxv,
            .comp bcomp, comps1, hci1, hgetcomp1, by rw [hdc1_nc]; omega, hsamp1'⟩
        · have : k32.toInt = (k.toNat : Int) := int32_toInt_ofNat (by dsimp [k]; omega)
          have hk32' : dc1.minDctHScaledSize = k32 := rfl
          rw [hk32', this]; exact ⟨by dsimp [k]; omega, by dsimp [k]; omega⟩
      · have hllF := Bool.eq_false_iff.mpr hll
        simp only [hllF, Bool.false_eq_true, ↓reduceIte]
        let dc1 := { dc with outputWidth := dc.imageWidth, outputHeight := dc.imageHeight,
                             master := .ref (.master bmas) 0 }
        let h1 := C.Space.put h (C.DecompRef.decomp bdc) (dcs.set! 0 dc1)
        have hrun_ll : C.run (Ptr.store (.ref (C.DecompRef.decomp bdc) 0) dc1) h = .ok ((), h1) := by
          exact (run_bind_pure _ h).symm.trans (Ptr.store_bind h (C.DecompRef.decomp bdc) 0 dc1 dcs pure hgetdc hro_dc hszdc)
        have hszdc1 : 0 < (dcs.set! 0 dc1).size := by rw [Array.size_set!]; exact hszdc
        have hgetdc1 : h1.decomps bdc = some (dcs.set! 0 dc1) := by simp [h1, C.Space.put]
        have hdc1_bang : (dcs.set! 0 dc1)[0]! = dc1 := by
          rw [getElem!_pos _ 0 hszdc1]; simp [Array.set!_eq_setIfInBounds]
        refine ⟨h1, dcs.set! 0 dc1, dc1, comps, hrun_ll, ?_, hgetdc1, hszdc1, hdc1_bang.symm, rfl, hgetmas,
          hci, hgetcomp, rfl, rfl, rfl, rfl, rfl, rfl, fun h0 => False.elim (hll (beq_iff_eq.mpr h0)), hsamp⟩
        exact ⟨⟨.decomp bdc, dcs.set! 0 dc1, dc1, rm, mems, .master bmas, masters, ric, ics, rmrk, mrks,
          rfl, hgetdc1, hszdc1, hdc1_bang.symm, ⟨.err berr, errs, herr, hgeterr, hszerr⟩, hmem, hgetmem, hszmem, rfl, hgetmas, hszmas,
          hin, hgetin, hszin, hmrk, hgetmrk, hszmrk, hpsz, hpd⟩,
          .decomp bdc, dcs.set! 0 dc1, dc1, .master bmas, masters, mst,
          rfl, hgetdc1, hszdc1, hdc1_bang.symm, rfl, hgetmas, hszmas, hmst, rfl,
          hnc, hdim, hmaxh, hmaxv, .comp bcomp, comps, hci, hgetcomp, hszcomp, hsamp⟩
    obtain ⟨h1, dcs1, dc1, comps1, hcore_run, hvalid1, hgetdc1, hszdc1, hdc1, hmas1, hgetmas1,
      hci1, hgetcomp1, hszcomp1, hnc1, hw1, hh1, hmh1, hmv1, hmind1, hsamp1⟩ := hcore_ok
    have hcore_bind : ∀ (f : Unit → M (JpegRes Unit)),
        C.run (jpeg_core_output_dimensions (.ref (C.DecompRef.decomp bdc) 0) >>= f) h = C.run (f ()) h1 := by
      intro f; simp only [C.run, bind] at hcore_run ⊢; rw [hcore_run]
    rw [hcore_bind]
    change ∃ res h', C.run _ h1 = .ok (res, h')
    have hdc1_pos : dcs1[0] = dc1 := by rw [← getElem!_pos dcs1 0 hszdc1]; exact hdc1.symm
    have hgetdc1' : C.Space.get h1 (C.DecompRef.decomp bdc) = some dcs1 := hgetdc1
    have hgetmas1' : C.Space.get h1 (C.MasterRef.master bmas) = some masters := hgetmas1
    rw [Ptr.load_bind h1 _ 0 dcs1 _ hgetdc1' hszdc1, hdc1_pos, hmas1]
    rw [Ptr.load_bind h1 _ 0 masters _ hgetmas1' hszmas, hmst0]
    by_cases hll : (mst.lossless == 0) = true
    · simp only [hll, ↓reduceIte]
      have hnc_neg : ¬ (dc1.numComponents < 0) := by
        intro hlt
        have hlt' := Int32.lt_iff_toInt_lt.mp hlt
        have h0 : (0 : Int32).toInt = 0 := rfl
        rw [hnc1, h0] at hlt'; omega
      simp only [hnc_neg, ↓reduceIte, pure_bind_m]
      rw [hci1]
      have hmind' := hmind1 (beq_iff_eq.mp hll)
      have hnc1_le : dc1.numComponents.toInt.toNat ≤ comps1.size := by rw [hnc1, hszcomp1]; exact hszcomp
      obtain ⟨comps2, hsz2, _, hsamp2, hdct2, hadapt_run⟩ := adaptCompLoop_ok h1 bcomp comps1
        dc1.numComponents.toInt.toNat dc1.maxHSampFactor dc1.maxVSampFactor dc1.minDctHScaledSize
        hgetcomp1 hnc1_le (by rw [hmh1]; exact hmaxh) (by rw [hmv1]; exact hmaxv) hmind'
        (by intro i hi; rw [hnc1] at hi; exact hsamp1 i hi) 0 (Nat.zero_le _)
      let h1b := C.Space.put h1 (C.CompRef.comp bcomp) comps2
      have hgetcomp1b : h1b.comps bcomp = some comps2 := by simp [h1b, C.Space.put]
      obtain ⟨comps3, hsz3, hsamp3, hds_run⟩ := downsampleCompLoop_ok h1b bcomp comps2
        dc1.numComponents.toInt.toNat dc1.imageWidth dc1.imageHeight dc1.maxHSampFactor dc1.maxVSampFactor
        hgetcomp1b (by rw [hsz2]; exact hnc1_le) (by rw [hw1, hh1]; exact hdim)
        (by rw [hmh1]; exact hmaxh) (by rw [hmv1]; exact hmaxv)
        (by intro i hi
            obtain ⟨a, b, c, d⟩ := hsamp2 i hi
            obtain ⟨e, f⟩ := hdct2 i hi (Nat.zero_le _)
            exact ⟨a, b, c, d, e, f⟩) 0 (Nat.zero_le _)
      let h2 := C.Space.put h1b (C.CompRef.comp bcomp) comps3
      have hvalid2 : ValidDecompDimsInput h2 (.ref (C.DecompRef.decomp bdc) 0) false := by
        obtain ⟨⟨_rc1, _dcs1, _dc1, _rm1, _mems1, _rmas1, _masters1, _ric1, _ics1, _rmrk1, _mrks1,
          _hc1', _hgdc1, _hszdc1, _hdc1, _herr1, _hm1, _hgm1, _hzm1, _hmas1, _hgmas1, _hzmas1,
          _hin1, _hgin1, _hzin1, _hmrk1, _hgmrk1, _hzmrk1, _hpsz1, _hpd1⟩,
          _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := hvalid1
        have hdc1_same : _dc1 = dc1 := by
          have hrc_eq : _rc1 = .decomp bdc := C.Ptr.ref.inj _hc1'.symm |>.1
          rw [hrc_eq] at _hgdc1
          have hdcs_eq : _dcs1 = dcs1 := Option.some.inj (_hgdc1.symm.trans hgetdc1)
          rw [_hdc1, hdcs_eq, ← hdc1]
        rw [hdc1_same] at _herr1 _hm1 _hmas1 _hin1 _hmrk1
        have hrmas1_eq : _rmas1 = .master bmas := C.Ptr.ref.inj (_hmas1.symm.trans hmas1) |>.1
        subst hrmas1_eq
        exact ⟨⟨.decomp bdc, dcs1, dc1, _rm1, _mems1, .master bmas, masters, _ric1, _ics1, _rmrk1, _mrks1,
          rfl, hgetdc1, hszdc1, hdc1, _herr1, _hm1, _hgm1, _hzm1, hmas1, hgetmas1, hszmas,
          _hin1, _hgin1, _hzin1, _hmrk1, _hgmrk1, _hzmrk1, _hpsz1, _hpd1⟩,
          .decomp bdc, dcs1, dc1, .master bmas, masters, mst,
          rfl, hgetdc1, hszdc1, hdc1, hmas1, hgetmas1, hszmas, hmst, rfl,
          by rw [hnc1]; exact hnc, by rw [hw1, hh1]; exact hdim,
          by rw [hmh1]; exact hmaxh, by rw [hmv1]; exact hmaxv,
          .comp bcomp, comps3, hci1, by simp [h2, C.Space.get, C.Space.put], by rw [hsz3, hsz2]; exact hnc1_le, hsamp3⟩
      rw [run_bind _ _ h1 h1b () hadapt_run]
      rw [run_bind _ _ h1b h2 () hds_run]
      obtain ⟨h', _, hfin, _⟩ := finish_calc_dims_safety h2 bdc bmas dcs1 dc1 masters mst hvalid2 hgetdc1 hszdc1 hdc1
        hmas1 hgetmas1 hszmas hmst (by rw [hnc1]; exact hnc) (by rw [hw1, hh1]; exact hdim)
        (by rw [hmh1]; exact hmaxh) (by rw [hmv1]; exact hmaxv)
      exact ⟨.ok (), h', hfin⟩
    · have hllF := Bool.eq_false_iff.mpr hll
      simp only [hllF, Bool.false_eq_true, ↓reduceIte, pure_bind_m]
      obtain ⟨h', _, hfin, _⟩ := finish_calc_dims_safety h1 bdc bmas dcs1 dc1 masters mst hvalid1 hgetdc1 hszdc1 hdc1
        hmas1 hgetmas1 hszmas hmst (by rw [hnc1]; exact hnc) (by rw [hw1, hh1]; exact hdim)
        (by rw [hmh1]; exact hmaxh) (by rw [hmv1]; exact hmaxv)
      exact ⟨.ok (), h', hfin⟩

theorem jpeg_core_output_dimensions_shrink_functional :
    Goal.jpeg_core_output_dimensions_shrink_functional := by
  intro h cinfo denom hdenom hvalid hscale
  obtain ⟨_hcore, rc, dcs, dc, rmas, masters, mst,
    hc, hgetdc, hszdc, hdc, hmas, hgetmas, hszmas, hmst, _,
    hnc, hdim, _hmaxh, _hmaxv, hcomp⟩ := hvalid
  obtain ⟨rcomp, comps, hci, hgetcomp, hszcomp, _⟩ := hcomp
  obtain ⟨hsN, hsD, hll0⟩ := hscale rc dcs dc rmas masters hc hgetdc hszdc hdc hmas hgetmas hszmas
  subst hc
  cases rc with | decomp bdc =>
  cases rmas with | master bmas =>
  cases rcomp with | comp bcomp =>
  have hdc0 : dcs[0] = dc := by rw [← getElem!_pos dcs 0 hszdc]; exact hdc.symm
  have hmst0 : masters[0] = mst := by rw [← getElem!_pos masters 0 hszmas]; exact hmst.symm
  unfold jpeg_core_output_dimensions
  rw [Ptr.load_bind h _ 0 dcs _ hgetdc hszdc, hdc0, hmas]
  rw [Ptr.load_bind h _ 0 masters _ hgetmas hszmas, hmst0]
  have hro_dc : C.Space.ro h (C.DecompRef.decomp bdc) = false := rfl
  have hmst_ll : mst.lossless = 0 := by rw [hmst]; exact hll0
  have hllT : (mst.lossless == 0) = true := beq_iff_eq.mpr hmst_ll
  simp only [hllT, ↓reduceIte]
  have hk_val : selectIdctScale dc.scaleNum dc.scaleDenom = 8 / denom := by
    rw [hsN, hsD]
    rcases hdenom with rfl | rfl | rfl | rfl <;> rfl
  have hk_nat : (selectIdctScale dc.scaleNum dc.scaleDenom).toNat = 8 / denom.toNat := by
    rw [hk_val]
    rcases hdenom with rfl | rfl | rfl | rfl <;> rfl
  have hk16 : (selectIdctScale dc.scaleNum dc.scaleDenom).toNat ≤ 8 := by
    rw [hk_nat]; rcases hdenom with rfl | rfl | rfl | rfl <;> decide
  rw [hk_val]
  have hk8_nat : (8 / denom).toNat = 8 / denom.toNat := by
    rcases hdenom with rfl | rfl | rfl | rfl <;> rfl
  have hk8_le : (8 / denom).toNat ≤ 8 := by rw [hk8_nat, ← hk_nat]; exact hk16
  have hwk := int_mul_bounds (Int.natCast_nonneg _) (Int.ofNat_le.mpr hdim.1)
    (Int.natCast_nonneg _) (Int.ofNat_le.mpr hk8_le)
  have hhk := int_mul_bounds (Int.natCast_nonneg _) (Int.ofNat_le.mpr hdim.2)
    (Int.natCast_nonneg _) (Int.ofNat_le.mpr hk8_le)
  have hiw64 : (Int64.ofNat dc.imageWidth.toNat).toInt = (dc.imageWidth.toNat : Int) := int64_toInt_ofNat (by omega)
  have hih64 : (Int64.ofNat dc.imageHeight.toNat).toInt = (dc.imageHeight.toNat : Int) := int64_toInt_ofNat (by omega)
  have hk64 : (Int64.ofNat (8 / denom).toNat).toInt = ((8 / denom).toNat : Int) := int64_toInt_ofNat (by omega)
  have hkw_ok := i64Mul_eq (Int64.ofNat dc.imageWidth.toNat) (Int64.ofNat (8 / denom).toNat)
    (by rw [hiw64, hk64]; omega)
    (by rw [hiw64, hk64]; omega)
  have hkh_ok := i64Mul_eq (Int64.ofNat dc.imageHeight.toNat) (Int64.ofNat (8 / denom).toNat)
    (by rw [hih64, hk64]; omega)
    (by rw [hih64, hk64]; omega)
  let w64 := Int64.ofInt ((Int64.ofNat dc.imageWidth.toNat).toInt * (Int64.ofNat (8 / denom).toNat).toInt)
  let h64 := Int64.ofInt ((Int64.ofNat dc.imageHeight.toNat).toInt * (Int64.ofNat (8 / denom).toNat).toInt)
  have hw64_v : w64.toInt = (dc.imageWidth.toNat * (8 / denom).toNat : Nat) := by
    dsimp [w64]; simp only [hiw64, hk64]; exact toInt_ofInt64 (by omega) (by omega)
  have hh64_v : h64.toInt = (dc.imageHeight.toNat * (8 / denom).toNat : Nat) := by
    dsimp [h64]; simp only [hih64, hk64]; exact toInt_ofInt64 (by omega) (by omega)
  have h8 : (8 : Int64).toInt = 8 := rfl
  obtain ⟨outW, houtW, houtW_eq⟩ := MozjpegF.Proof.Jutils.jdiv_round_up_functional h w64 8
    (by rw [hw64_v]; omega) (by decide) (by rw [hw64_v, h8]; omega)
  obtain ⟨outH, houtH, houtH_eq⟩ := MozjpegF.Proof.Jutils.jdiv_round_up_functional h h64 8
    (by rw [hh64_v]; omega) (by decide) (by rw [hh64_v, h8]; omega)
  rw [hkw_ok, pure_bind_m]
  have houtW_bind : ∀ (f : Int64 → M Unit), C.run (jdiv_round_up w64 8 >>= f) h = C.run (f outW) h := by
    intro f; simp only [C.run, bind] at houtW ⊢; rw [houtW]
  rw [houtW_bind, hkh_ok, pure_bind_m]
  have houtH_bind : ∀ (f : Int64 → M Unit), C.run (jdiv_round_up h64 8 >>= f) h = C.run (f outH) h := by
    intro f; simp only [C.run, bind] at houtH ⊢; rw [houtH]
  rw [houtH_bind]
  let k32 := Int32.ofNat (8 / denom).toNat
  let dc1 := { dc with outputWidth := outW.toInt.toNat.toUInt32, outputHeight := outH.toInt.toNat.toUInt32,
                       minDctHScaledSize := k32, minDctVScaledSize := k32 }
  rw [← hmas]
  rw [Ptr.store_bind h _ 0 dc1 dcs _ hgetdc hro_dc hszdc]
  let h1 := C.Space.put h (C.DecompRef.decomp bdc) (dcs.set! 0 dc1)
  have hgetdc1 : C.Space.get h1 (C.DecompRef.decomp bdc) = some (dcs.set! 0 dc1) := by
    simp [h1, C.Space.get, C.Space.put]
  have hszdc1 : 0 < (dcs.set! 0 dc1).size := by rw [Array.size_set!]; exact hszdc
  have hdc1_eq : (dcs.set! 0 dc1)[0] = dc1 := by simp [Array.set!_eq_setIfInBounds]
  have hnc_neg : ¬ (dc1.numComponents < 0) := by
    intro hlt
    have hlt' := Int32.lt_iff_toInt_lt.mp hlt
    have h0 : (0 : Int32).toInt = 0 := rfl
    have : dc1.numComponents = dc.numComponents := rfl
    rw [this, h0] at hlt'; omega
  have hgetcomp1 : h1.comps bcomp = some comps := hgetcomp
  obtain ⟨comps', _, _, hset_run⟩ := setCompScaledSizes_ok h1 bcomp comps
    dc.numComponents.toInt.toNat k32 hgetcomp1 hszcomp 0 (Nat.zero_le _)
  let h' := C.Space.put h1 (C.CompRef.comp bcomp) comps'
  have hfull_run :
      C.run (do
        let dc ← Ptr.load (Ptr.ref (C.DecompRef.decomp bdc) 0)
        if dc.numComponents < 0 then ub "negative num_components"
        setCompScaledSizes dc.compInfo 0 dc.numComponents.toInt.toNat k32) h1 = .ok ((), h') := by
    rw [Ptr.load_bind h1 _ 0 (dcs.set! 0 dc1) _ hgetdc1 hszdc1, hdc1_eq]
    simp only [hnc_neg, ↓reduceIte, dc1, hci]
    exact hset_run
  refine ⟨h', C.DecompRef.decomp bdc, dcs.set! 0 dc1, rfl, hfull_run, ?_, hszdc1, ?_, ?_⟩
  · simp [h', h1, C.Space.get, C.Space.put]
  · rw [getElem!_pos _ 0 hszdc1, hdc1_eq]
    have hk32 : k32.toInt = ((8 / denom).toNat : Int) := by
      dsimp [k32]; exact int32_toInt_ofNat (by omega)
    rw [hk32, hk8_nat, ← hk_nat, hk_nat]; rfl
  · intro d0 hd0 _hd0sz
    have hd0_eq : d0 = dcs := Option.some.inj (hd0.symm.trans hgetdc)
    rw [getElem!_pos (dcs.set! 0 dc1) 0 hszdc1, hdc1_eq, hd0_eq, ← hdc]
    simp only [dc1]
    have hw_nat : outW.toInt = ((dc.imageWidth.toNat * (8 / denom).toNat + 7) / 8 : Nat) := by
      rw [houtW_eq, hw64_v, h8]; omega
    have hh_nat : outH.toInt = ((dc.imageHeight.toNat * (8 / denom).toNat + 7) / 8 : Nat) := by
      rw [houtH_eq, hh64_v, h8]; omega
    have hw_lt : outW.toInt.toNat < 2 ^ 32 := by omega
    have hh_lt : outH.toInt.toNat < 2 ^ 32 := by omega
    have huw : outW.toInt.toNat.toUInt32.toNat = outW.toInt.toNat := by
      rw [UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt hw_lt
    have huh : outH.toInt.toNat.toUInt32.toNat = outH.toInt.toNat := by
      rw [UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt hh_lt
    rw [huw, huh]
    have hk_v : (8 / denom).toNat = 8 / denom.toNat := hk8_nat
    rw [hk_v] at hw_nat hh_nat
    have hdenom_nat : denom.toNat = 1 ∨ denom.toNat = 2 ∨ denom.toNat = 4 ∨ denom.toNat = 8 := by
      rcases hdenom with rfl | rfl | rfl | rfl <;> decide
    rcases hdenom_nat with hd | hd | hd | hd <;> (
      rw [hd] at hw_nat hh_nat ⊢
      constructor <;> omega)

theorem jpeg_calc_output_dimensions_shrink_nonvacuous :
    Goal.jpeg_calc_output_dimensions_shrink_nonvacuous := by
  dsimp only [Goal.jpeg_calc_output_dimensions_shrink_nonvacuous]
  let comp0 : C.JpegCompInfo := { componentId := 1, componentIndex := 0, hSampFactor := 2, vSampFactor := 2 }
  let comp1 : C.JpegCompInfo := { componentId := 2, componentIndex := 1, hSampFactor := 1, vSampFactor := 1 }
  let comp2 : C.JpegCompInfo := { componentId := 3, componentIndex := 2, hSampFactor := 1, vSampFactor := 1 }
  let comps : Array C.JpegCompInfo := #[comp0, comp1, comp2]
  let dc : C.JpegDecompressStruct := {
    err := .ref (.err 0) 0
    mem := .ref (.mem 0) 0
    globalState := DSTATE_READY
    imageWidth := 1001
    imageHeight := 753
    numComponents := 3
    jpegColorSpace := JCS_YCbCr
    outColorSpace := JCS_RGB
    scaleNum := 1
    scaleDenom := 4
    maxHSampFactor := 2
    maxVSampFactor := 2
    compInfo := .ref (.comp 0) 0
    master := .ref (.master 0) 0
    inputctl := .ref (.inputctl 0) 0
    marker := .ref (.marker 0) 0
  }
  let mst : C.JpegDecompMaster := {}
  let masters : Array C.JpegDecompMaster := #[mst]
  let dcs : Array C.JpegDecompressStruct := #[dc]
  let h : C.Heap := {
    errMgrs := C.upd C.Tbl.empty 0 (some #[{}])
    mems := C.upd C.Tbl.empty 0 (some #[{}])
    masters := C.upd C.Tbl.empty 0 (some masters)
    inputctls := C.upd C.Tbl.empty 0 (some #[{}])
    markers := C.upd C.Tbl.empty 0 (some #[{}])
    comps := C.upd C.Tbl.empty 0 (some comps)
    decomps := C.upd C.Tbl.empty 0 (some dcs)
  }
  have hgetdc : C.Space.get h (C.DecompRef.decomp 0) = some dcs := rfl
  have hszdc : 0 < dcs.size := by decide
  have hdc : dc = dcs[0]! := rfl
  have hgetmas : C.Space.get h (C.MasterRef.master 0) = some masters := rfl
  have hszmas : 0 < masters.size := by decide
  have hmst : mst = masters[0]! := rfl
  have hro_dc : C.Space.ro h (C.DecompRef.decomp 0) = false := rfl
  have hgetcomp : h.comps 0 = some comps := rfl
  have hvalid : ValidDecompDimsInput h (.ref (.decomp 0) 0) false := by
    refine ⟨⟨.decomp 0, dcs, dc, .mem 0, #[{}], .master 0, masters, .inputctl 0, #[{}], .marker 0, #[{}],
      rfl, rfl, (by decide), rfl, ⟨.err 0, #[{}], rfl, rfl, (by decide)⟩,
      rfl, rfl, (by decide), rfl, rfl, (by decide), rfl, rfl, (by decide), rfl, rfl, (by decide),
      (by decide), (fun _ _ => by simp)⟩,
      .decomp 0, dcs, dc, .master 0, masters, mst,
      rfl, rfl, (by decide), rfl, rfl, rfl, (by decide), rfl, rfl,
      (by decide), (by decide), (by decide), (by decide),
      .comp 0, comps, rfl, rfl, (by decide), fun i hi => ?_⟩
    have hi3 : i < 3 := hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> decide
  have hk_val : selectIdctScale dc.scaleNum dc.scaleDenom = 2 := rfl
  have hkw : i64Mul (Int64.ofNat dc.imageWidth.toNat) (Int64.ofNat 2) = pure 2002 := by
    refine i64Mul_eq _ _ (by decide) (by decide) |>.trans ?_; rfl
  have hkh : i64Mul (Int64.ofNat dc.imageHeight.toNat) (Int64.ofNat 2) = pure 1506 := by
    refine i64Mul_eq _ _ (by decide) (by decide) |>.trans ?_; rfl
  obtain ⟨outW, houtW, houtW_eq⟩ := MozjpegF.Proof.Jutils.jdiv_round_up_functional h 2002 8
    (by decide) (by decide) (by decide)
  obtain ⟨outH, houtH, houtH_eq⟩ := MozjpegF.Proof.Jutils.jdiv_round_up_functional h 1506 8
    (by decide) (by decide) (by decide)
  have houtW251 : outW = 251 := by
    have h8 : (8 : Int64).toInt = 8 := rfl
    have h2002 : (2002 : Int64).toInt = 2002 := rfl
    rw [h2002, h8] at houtW_eq
    have : outW.toInt = 251 := by omega
    exact Int64.toInt_inj.mp this
  have houtH189 : outH = 189 := by
    have h8 : (8 : Int64).toInt = 8 := rfl
    have h1506 : (1506 : Int64).toInt = 1506 := rfl
    rw [h1506, h8] at houtH_eq
    have : outH.toInt = 189 := by omega
    exact Int64.toInt_inj.mp this
  subst houtW251; subst houtH189
  let dc1 : C.JpegDecompressStruct := {
    dc with outputWidth := 251, outputHeight := 189, minDctHScaledSize := 2, minDctVScaledSize := 2
  }
  have hdc1_w : ((251 : Int64).toInt.toNat.toUInt32) = 251 := rfl
  have hdc1_h : ((189 : Int64).toInt.toNat.toUInt32) = 189 := rfl
  let h1a := C.Space.put h (C.DecompRef.decomp 0) (dcs.set! 0 dc1)
  have hgetdc1a : C.Space.get h1a (C.DecompRef.decomp 0) = some (dcs.set! 0 dc1) := by simp [h1a, C.Space.get, C.Space.put]
  have hszdc1a : 0 < (dcs.set! 0 dc1).size := by rw [Array.size_set!]; exact hszdc
  have hgetcomp1a : h1a.comps 0 = some comps := hgetcomp
  obtain ⟨comps1, hsz1, hsamp1, hset_run⟩ := setCompScaledSizes_ok h1a 0 comps 3 2 hgetcomp1a (by decide) 0 (by decide)
  let h1 := C.Space.put h1a (C.CompRef.comp 0) comps1
  have hcore_run : C.run (jpeg_core_output_dimensions (.ref (.decomp 0) 0)) h = .ok ((), h1) := by
    unfold jpeg_core_output_dimensions
    rw [Ptr.load_bind h _ 0 dcs _ hgetdc hszdc]
    have hdc0 : dcs[0]'hszdc = dc := rfl
    rw [hdc0]
    have hmas0 : dc.master = .ref (.master 0) 0 := rfl
    rw [hmas0, Ptr.load_bind h _ 0 masters _ hgetmas hszmas]
    have hmst0 : masters[0]'hszmas = mst := rfl
    rw [hmst0]
    have hll : (mst.lossless == 0) = true := rfl
    have h2nat : (2 : UInt32).toNat = 2 := rfl
    simp only [hll, ↓reduceIte, hk_val, h2nat]
    rw [hkw, pure_bind_m]
    rw [run_bind _ _ h h 251 houtW]
    rw [hkh, pure_bind_m]
    rw [run_bind _ _ h h 189 houtH]
    have hk32_eq' : Int32.ofNat 2 = (2 : Int32) := rfl
    simp only [hk32_eq', hdc1_w, hdc1_h]
    have hdc1_eq' :
        { dc with outputWidth := 251, outputHeight := 189, minDctHScaledSize := 2, minDctVScaledSize := 2,
                  master := Ptr.ref (MasterRef.master 0) 0 } = dc1 := rfl
    rw [hdc1_eq', Ptr.store_bind h _ 0 dc1 dcs _ hgetdc hro_dc hszdc]
    rw [Ptr.load_bind h1a _ 0 (dcs.set! 0 dc1) _ hgetdc1a hszdc1a]
    have hdc1a_pos : (dcs.set! 0 dc1)[0]'hszdc1a = dc1 := rfl
    rw [hdc1a_pos]
    have hnc_neg : ¬ (dc1.numComponents < 0) := by decide
    simp only [hnc_neg, ↓reduceIte]
    exact hset_run
  have hgetdc1 : h1.decomps 0 = some (dcs.set! 0 dc1) := by simp only [h1, h1a, C.Space.put]; rfl
  have hgetmas1 : h1.masters 0 = some masters := by simp only [h1, h1a, C.Space.put]; exact hgetmas
  have hgetcomp1 : h1.comps 0 = some comps1 := by simp only [h1, C.Space.put]; rfl
  have hsamp1' : ∀ i, i < 3 → 1 ≤ (comps1[i]!).hSampFactor.toInt ∧ (comps1[i]!).hSampFactor.toInt ≤ 4 ∧
      1 ≤ (comps1[i]!).vSampFactor.toInt ∧ (comps1[i]!).vSampFactor.toInt ≤ 4 := by
    intro i hi
    have hhi := hsamp1 i (by omega)
    have hs_orig : 1 ≤ (comps[i]!).hSampFactor.toInt ∧ (comps[i]!).hSampFactor.toInt ≤ 4 ∧
        1 ≤ (comps[i]!).vSampFactor.toInt ∧ (comps[i]!).vSampFactor.toInt ≤ 4 := by
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> decide
    rw [hhi.1, hhi.2]; exact hs_orig
  obtain ⟨comps2, hsz2, _, hsamp2, hdct2, hadapt_run⟩ := adaptCompLoop_ok h1 0 comps1
    3 2 2 2 hgetcomp1 (by rw [hsz1]; decide) (by decide) (by decide) (by decide) hsamp1' 0 (by decide)
  let h1b := C.Space.put h1 (C.CompRef.comp 0) comps2
  have hgetcomp1b : h1b.comps 0 = some comps2 := by simp [h1b, C.Space.put]
  obtain ⟨comps3, hsz3, hsamp3, hds_run⟩ := downsampleCompLoop_ok h1b 0 comps2
    3 1001 753 2 2 hgetcomp1b (by rw [hsz2, hsz1]; decide) (by decide) (by decide) (by decide)
    (fun i hi => by
      obtain ⟨a, b, c, d⟩ := hsamp2 i hi
      obtain ⟨e, f⟩ := hdct2 i hi (Nat.zero_le _)
      exact ⟨a, b, c, d, e, f⟩) 0 (by decide)
  let h2 := C.Space.put h1b (C.CompRef.comp 0) comps3
  have hgetdc2 : h2.decomps 0 = some (dcs.set! 0 dc1) := by simp only [h2, h1b, h1, h1a, C.Space.put]; rfl
  have hgetmas2 : h2.masters 0 = some masters := by simp only [h2, h1b, h1, h1a, C.Space.put]; exact hgetmas
  have hgetcomp2 : h2.comps 0 = some comps3 := by simp only [h2, C.Space.put]; rfl
  have hdc1_bang : dc1 = (dcs.set! 0 dc1)[0]! := rfl
  have hvalid2 : ValidDecompDimsInput h2 (.ref (.decomp 0) 0) false := by
    refine ⟨⟨.decomp 0, dcs.set! 0 dc1, dc1, .mem 0, #[{}], .master 0, masters, .inputctl 0, #[{}], .marker 0, #[{}],
      rfl, hgetdc2, hszdc1a, hdc1_bang, ⟨.err 0, #[{}], rfl, rfl, (by decide)⟩,
      rfl, rfl, (by decide), rfl, hgetmas2, (by decide), rfl, rfl, (by decide), rfl, rfl, (by decide),
      (by decide), (fun _ _ => by simp)⟩,
      .decomp 0, dcs.set! 0 dc1, dc1, .master 0, masters, mst,
      rfl, hgetdc2, hszdc1a, hdc1_bang, rfl, hgetmas2, (by decide), rfl, rfl,
      (by decide), (by decide), (by decide), (by decide),
      .comp 0, comps3, rfl, hgetcomp2, (by rw [hsz3, hsz2, hsz1]; decide), hsamp3⟩
  obtain ⟨h', dcs', hfin, hdcs', hsz', hw', hh'⟩ := finish_calc_dims_safety h2 0 0 (dcs.set! 0 dc1) dc1 masters mst
    hvalid2 hgetdc2 hszdc1a hdc1_bang rfl hgetmas2 (by decide) hmst (by decide) (by decide) (by decide) (by decide)
  refine ⟨h', dcs', ?_, hdcs', hw', hh'⟩
  unfold jpeg_calc_output_dimensions
  rw [Ptr.load_bind h _ 0 dcs _ hgetdc hszdc]
  have hdc0 : dcs[0]'hszdc = dc := rfl
  rw [hdc0]
  have hready : (dc.globalState != DSTATE_READY) = false := rfl
  simp only [hready, Bool.false_eq_true, ↓reduceIte]
  rw [run_bind _ _ h h1 () hcore_run]
  have hgetdc1' : C.Space.get h1 (C.DecompRef.decomp 0) = some (dcs.set! 0 dc1) := hgetdc1
  rw [Ptr.load_bind h1 _ 0 (dcs.set! 0 dc1) _ hgetdc1' hszdc1a]
  have hdc1_pos : (dcs.set! 0 dc1)[0]'hszdc1a = dc1 := rfl
  rw [hdc1_pos]
  have hmas1 : dc1.master = .ref (.master 0) 0 := rfl
  have hgetmas1' : C.Space.get h1 (C.MasterRef.master 0) = some masters := hgetmas1
  rw [hmas1, Ptr.load_bind h1 _ 0 masters _ hgetmas1' hszmas]
  have hmst0 : masters[0]'hszmas = mst := rfl
  rw [hmst0]
  have hll : (mst.lossless == 0) = true := rfl
  simp only [hll, ↓reduceIte]
  have hnc_neg : ¬ (dc1.numComponents < 0) := by decide
  simp only [hnc_neg, ↓reduceIte, pure_bind_m]
  have hci1 : dc1.compInfo = .ref (.comp 0) 0 := rfl
  have hnc1 : dc1.numComponents.toInt.toNat = 3 := by decide
  simp only [hci1, hnc1]
  rw [run_bind _ _ h1 h1b () hadapt_run]
  rw [run_bind _ _ h1b h2 () hds_run]
  exact hfin

end MozjpegF.Proof.Jdmaster
