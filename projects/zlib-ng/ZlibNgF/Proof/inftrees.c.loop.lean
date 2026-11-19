import ZlibNgF.Proof.«inftrees.c.cont»

/-!
# `zng_inflate_table`: the table-filling loop (`ZlibNgF`)

`tblBody_wp`: one trip of the loop makes the entry `here` of the current symbol (a literal, a length or distance
base with its extra bits from the static tables, the end-of-block marker, or for `CODES` the code-length symbol) and
continues with `tblCont_wp`. `tbl_loop_wp`: the loop ends without fault, after the last code (`ret = 0`) or when
the room check fails (`ret = 1`).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.Inftrees
open C ZlibNg.Inftrees ZlibNg.InflateP ZlibNgF.Math.BitReverse ZlibNgF.Math.InftreesCount

theorem bind_have {α β γ : Type} {h : Heap} {Q : γ → Heap → Prop} {m : M α} {v : α → β}
    {f : α → β → M γ} (hm : Wp m h (fun a h' => Wp (f a (v a)) h' Q)) :
    Wp (m >>= fun a => have x := v a; f a x) h Q := Wp.bind hm

/-- The `base` / `extra` tables and `match` of each code type. -/
def Kind (S : Setup) (base extra : U16Src) (match_ : UInt32) : Prop :=
  (S.type = CODES ∧ base = .ptr (.ref (.work S.b) 0) ∧ extra = .ptr (.ref (.work S.b) 0) ∧ match_ = 20) ∨
  (S.type = LENS ∧ base = .st lbase ∧ extra = .st lext ∧ match_ = 257) ∨
  (S.type = DISTS ∧ base = .st dbase ∧ extra = .st dext ∧ match_ = 0)

theorem st_at_ok {a : Array UInt16} {i : Nat} (hi : i < a.size) : (U16Src.st a).at i = pure a[i] := by
  simp [U16Src.at, aget_ok hi]

/-- One trip of the table-filling loop. -/
theorem tblBody_wp {S : Setup} (hS : S.OK) {t : TL} {C : Array Code} {K : Nat} (hst : St S t C K true)
    {maxv rootv mask : UInt32} (hmax : maxv.toNat = S.mx) (hroot : rootv.toNat = S.root)
    (hmask : mask.toNat = 2 ^ S.root - 1) {base extra : U16Src} {match_ : UInt32} (hk : Kind S base extra match_) :
    Wp (tblBody S.type (.ref (.lens S.b) S.lo) (.ref (.work S.b) 0) (.ref (.codes S.b) S.off) base extra match_
      maxv rootv mask t) (setCW S.h0 S.b S.s C S.W) (fun t' h' => Trip S t t' h') := by
  have hl := hS.live
  have hsym := hst.sym
  have hc1 := hst.cur_pos
  have hlen1 := hst.len_lo
  have hlen2 := hst.len_hi
  have hmx := hS.mx15
  have hn := nsum_mono S.c0 (show t.len.toNat ≤ 15 by omega)
  have hnle := hS.n_le
  have hcl := hst.cur_le
  have hlo : nsum S.c0 (t.len.toNat - 1) ≤ t.sym.toNat := by
    have := nsum_succ S.c0 (t.len.toNat - 1)
    rw [show t.len.toNat - 1 + 1 = t.len.toNat by omega] at this
    omega
  obtain ⟨hWc, -⟩ := hS.sorted t.len.toNat hlen1 (by omega) t.sym.toNat hlo (by omega)
  have hncodes := hS.n_codes
  unfold tblBody
  refine Wp.have_ ?_
  refine Wp.have_ ?_
  refine bind_have ?_
  refine Wp.of_eq (index_nat (get_work hl C S.W) (off := 0) (by omega)) ?_
  rw [Nat.zero_add]
  have hW := hWc
  have hcont := fun here => tblCont_wp hS hst hmax hroot hmask here
  rcases hk with ⟨hty, rfl, rfl, rfl⟩ | ⟨hty, rfl, rfl, rfl⟩ | ⟨hty, rfl, rfl, rfl⟩
  · -- CODES: every symbol is below 19, a literal-style entry
    have hc19 : S.codes ≤ 19 := by rcases hS.kind with ⟨-, -, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> simp_all [CODES, LENS, DISTS]
    have hlt : ¬ (S.W[t.sym.toNat]!).toUInt32 ≥ 20 := by
      rw [ge_iff_le, UInt32.le_iff_toNat_le, UInt16.toNat_toUInt32]; show ¬ 20 ≤ _; omega
    rw [ite_eq_right hlt]
    have hlt2 : (S.W[t.sym.toNat]!).toUInt32 + 1 < 20 := by
      rw [UInt32.lt_iff_toNat_lt, u32_add (by rw [UInt16.toNat_toUInt32]; show _ + 1 < _; omega),
        UInt16.toNat_toUInt32]
      show _ + 1 < 20; omega
    rw [ite_eq_left hlt2]
    exact hcont _
  · -- LENS
    have hc : S.codes ≤ 288 := by rcases hS.kind with ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨h, -⟩ <;> simp_all [CODES, LENS, DISTS]
    by_cases hge : (S.W[t.sym.toNat]!).toUInt32 ≥ 257
    · rw [ite_eq_left hge]
      have hidx : ((S.W[t.sym.toNat]!).toUInt32 - 257).toNat < 31 := by
        rw [u32_sub (by rw [ge_iff_le, UInt32.le_iff_toNat_le] at hge; exact hge), UInt16.toNat_toUInt32]
        show _ - 257 < 31; omega
      rw [Wp.bind_iff, st_at_ok (by simp [lext]; exact hidx), Wp.pure_iff]
      refine Wp.have_ ?_
      refine Wp.have_ ?_
      refine Wp.have_ ?_
      rw [Wp.bind_iff, st_at_ok (by simp [lbase]; exact hidx), Wp.pure_iff]
      refine Wp.have_ ?_
      exact hcont _
    · rw [ite_eq_right hge]
      split
      · exact hcont _
      · exact hcont _
  · -- DISTS
    have hc : S.codes ≤ 32 := by rcases hS.kind with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, h⟩ <;> simp_all [CODES, LENS, DISTS]
    have hge : (S.W[t.sym.toNat]!).toUInt32 ≥ 0 := by
      rw [ge_iff_le, UInt32.le_iff_toNat_le]; exact Nat.zero_le _
    rw [ite_eq_left hge]
    rw [Wp.bind_iff, st_at_ok (by simp [dext]; omega), Wp.pure_iff]
    refine Wp.have_ ?_
    refine Wp.have_ ?_
    refine Wp.have_ ?_
    rw [Wp.bind_iff, st_at_ok (by simp [dbase]; omega), Wp.pure_iff]
    refine Wp.have_ ?_
    exact hcont _

/-- The table-filling loop ends without fault, after the last code or on a failed room check. -/
theorem tbl_loop_wp {S : Setup} (hS : S.OK) {t0 : TL} {h : Heap} (hI : MI S t0 h)
    {maxv rootv mask : UInt32} (hmax : maxv.toNat = S.mx) (hroot : rootv.toNat = S.root)
    (hmask : mask.toNat = 2 ^ S.root - 1) {base extra : U16Src} {match_ : UInt32} (hk : Kind S base extra match_) :
    Wp (cwhile (fun (t : TL) => pure (t.ret.isNone, t))
      (tblBody S.type (.ref (.lens S.b) S.lo) (.ref (.work S.b) 0) (.ref (.codes S.b) S.off) base extra match_
        maxv rootv mask) t0) h
      (fun t h' => (∃ C, h' = setCW S.h0 S.b S.s C S.W ∧ Fin0 S t C) ∨
        (∃ C, h' = setCW S.h0 S.b S.s C S.W ∧ Fin1 S t C)) := by
  obtain ⟨C0, K0, rfl, hst0⟩ := hI
  have hs0 : t0.sym.toNat ≤ nsum S.c0 15 := by
    have := hst0.sym
    have := nsum_mono S.c0 (show t0.len.toNat ≤ 15 by have := hst0.len_hi; have := hS.mx15; omega)
    omega
  refine Wp.cwhile_pure (c := fun t => t.ret.isNone)
    (fun n t h' => (MI S t h' ∧ t.sym.toNat ≤ nsum S.c0 15 ∧ n = nsum S.c0 15 - t.sym.toNat + 1) ∨
      (n = 0 ∧ ((∃ C, h' = setCW S.h0 S.b S.s C S.W ∧ Fin0 S t C) ∨
        (∃ C, h' = setCW S.h0 S.b S.s C S.W ∧ Fin1 S t C)))) _ ?_
    (Or.inl ⟨⟨C0, K0, rfl, hst0⟩, hs0, rfl⟩) (by unfold fuel; have := hS.n_codes; have := hS.kind; omega)
  rintro n t h' (⟨⟨C, K, rfl, hst⟩, hsn, rfl⟩ | ⟨rfl, hfin⟩)
  · refine ⟨fun _ => ?_, fun hc => ?_⟩
    · refine Wp.mono (tblBody_wp hS hst hmax hroot hmask hk) ?_
      rintro t' h'' (⟨hmi, hlt, hle⟩ | hf0 | hf1)
      · exact ⟨_, by omega, Or.inl ⟨hmi, hle, rfl⟩⟩
      · exact ⟨0, by omega, Or.inr ⟨rfl, Or.inl hf0⟩⟩
      · exact ⟨0, by omega, Or.inr ⟨rfl, Or.inr hf1⟩⟩
    · simp [hst.ret] at hc
  · refine ⟨fun hc => ?_, fun _ => hfin⟩
    exfalso
    rcases hfin with ⟨C, -, hf⟩ | ⟨C, -, hf⟩ <;> simp [hf.ret] at hc

end ZlibNgF.Proof.Inftrees
