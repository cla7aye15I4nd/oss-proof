import ZlibNgF.Proof.«inftrees.c.safety»
import Lean

/-!
# `zng_inflate_table` terminates without fault (`ZlibNgF`)

`zng_inflate_table_wp`: under `TblPre` (the lengths are readable and at most 15; for `CODES` at most `bits`, with
`1 <= bits <= 15`; the room `bndOf type bits` from `off` fits in `codes`; `work` has 288 entries) the function ends
without fault, changes only `codes[off .. off + bndOf type bits)` and `work`, and returns `TablePost`.

The table-filling loop is the translation's own loop: its body is walked here (`wp_have_intro` names the entry
`here` at the join point), and the part after `here` is `tblCont`, whose pattern-matching function is the one of the
translation once `zng_inflate_table.match_7` is rewritten to it.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.Inftrees
open C ZlibNg.Inftrees ZlibNg.InflateP ZlibNgF.Math.BitReverse ZlibNgF.Math.InftreesCount

/-- What `zng_inflate_table` needs from its caller: `lens = state->lens + lo` with `codes` readable lengths at most
15, `work = state->work` (288 entries), `*table = state->codes + off` with room `bndOf type bits`. For `CODES`
every length is at most `bits` and `1 <= bits <= 15` (as `inflate` guarantees: 19 lengths of at most 7 bits,
`bits = 7`); `LENS` has at most 288 lengths, `DISTS` at most 32. -/
structure TblPre (h : Heap) (b : Nat) (s : InflateState) (type : UInt32) (lo : Nat) (codes : UInt32) (off : Nat)
    (bits : UInt32) : Prop where
  live : LiveSt h b s
  lens_size : lo + codes.toNat ≤ s.lens.size
  lens15 : ∀ j, j < codes.toNat → lensf s lo j ≤ 15
  work_size : s.work.size = 288
  room : off + bndOf type bits ≤ s.codes.size
  codes_lt : s.codes.size < 2 ^ 63
  kind : (type = CODES ∧ codes.toNat ≤ 19 ∧ 1 ≤ bits.toNat ∧ bits.toNat ≤ 15 ∧
      ∀ j, j < codes.toNat → lensf s lo j ≤ bits.toNat) ∨
    (type = LENS ∧ codes.toNat ≤ 288) ∨ (type = DISTS ∧ codes.toNat ≤ 32)

theorem Wp.have_all {α β : Type} {h : Heap} {Q : β → Heap → Prop} {v : α} {f : α → M β}
    (hf : ∀ x, Wp (f x) h Q) : Wp (have x := v; f x) h Q := hf v

open Lean Elab Tactic Meta in
/-- On a goal `Wp (have x := v; b) h Q`, continue with `∀ x, Wp b h Q` (`Wp.have_all` with `b` taken as is, without
unification, which would reduce the join point applied to `x`). -/
elab "wp_have_intro" : tactic => do
  let g ← getMainGoal
  g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  let args := tgt.getAppArgs
  unless tgt.isAppOfArity ``Wp 4 do throwError "wp_have_intro: goal is not Wp"
  match args[1]! with
  | .letE n ty v b _ =>
    let newTy := Expr.forallE n ty (mkAppN (mkConst ``Wp) #[args[0]!, b, args[2]!, args[3]!]) .default
    let ng ← mkFreshExprSyntheticOpaqueMVar newTy
    g.assign (mkAppN (mkConst ``Wp.have_all) #[ty, args[0]!, args[2]!, args[3]!, v, .lam n ty b .default, ng])
    replaceMainGoal [ng.mvarId!]
  | _ => throwError "wp_have_intro: program is not a let"

theorem post_err {h : Heap} {b : Nat} {s : InflateState} {type bits : UInt32} {off : Nat} {C : Array Code}
    {W : Array UInt16} (hC : C.size = s.codes.size) (hW : W.size = s.work.size)
    (hfr : ∀ i, ¬ (off ≤ i ∧ i < off + bndOf type bits) → C[i]? = s.codes[i]?) {r : Int32} (hr : r = -1 ∨ r = 1) :
    TablePost h b s type bits off (r, .ref (.codes b) off, bits) (setCW h b s C W) :=
  ⟨C, W, rfl, hC, hW, hfr, Or.inr hr, fun _ => rfl, fun e => by rcases hr with rfl | rfl <;> cases e⟩

set_option hygiene false in
/-- Name the setup `S` of the loop of code type `ty` and rewrite the fixed pointers of the goal in its terms. -/
macro "tbl_to_S" ty:term:max : tactic => `(tactic| (
  generalize hSd : (⟨h, b, s, W, lo, codes.toNat, off, $ty, cnt cnt0, mx.toNat, root.toNat, bndOf $ty bits⟩ :
    Setup) = S at hS hst ⊢
  have hmax : mx.toNat = S.mx := by rw [← hSd]
  have hroot : root.toNat = S.root := by rw [← hSd]
  replace hmask : ((1 : UInt32) <<< root - 1).toNat = 2 ^ S.root - 1 := by rw [← hSd]; exact hmask
  rw [show b = S.b by rw [← hSd], show lo = S.lo by rw [← hSd], show off = S.off by rw [← hSd],
    show ($ty == LENS) = (S.type == LENS) by rw [← hSd], show ($ty == DISTS) = (S.type == DISTS) by rw [← hSd]]))

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
/-- `zng_inflate_table` on the `lens` / `work` / `codes` arrays of a live `inflate_state`: no fault, only
`codes[off ..]` and `work` change, and the result is `TablePost`. -/
theorem zng_inflate_table_wp {h : Heap} {b : Nat} {s : InflateState} {type codes bits : UInt32} {lo off : Nat}
    (hP : TblPre h b s type lo codes off bits) :
    Wp (zng_inflate_table type (.ref (.lens b) lo) codes (.ref (.codes b) off) bits (.ref (.work b) 0)) h
      (TablePost h b s type bits off) := by
  have hl := hP.live
  have hc288 : codes.toNat ≤ 288 := by
    rcases hP.kind with ⟨-, h1, -⟩ | ⟨-, h1⟩ | ⟨-, h1⟩ <;> omega
  have hbnd2 : 2 ≤ bndOf type bits := by
    unfold bndOf
    rcases hP.kind with ⟨h1, -, h2, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> subst h1 <;> simp [CODES, LENS, DISTS]
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ bits.toNat := Nat.pow_le_pow_right (by omega) h2
  have hroom := hP.room
  have hcl := hP.codes_lt
  suffices H : Wp (zng_inflate_table type (.ref (.lens b) lo) codes (.ref (.codes b) off) bits (.ref (.work b) 0))
      (setCW h b s s.codes s.work) (TablePost h b s type bits off) by rwa [setCW_self hl] at H
  unfold zng_inflate_table
  refine Wp.bind (Wp.mono (count_lengths_wp (get_lens hl s.codes s.work) hP.lens_size hc288
    (fun j hj => by have := hP.lens15 j hj; unfold lensf at this; omega)) ?_)
  rintro cnt0 h1 ⟨hcnt0, rfl⟩
  have hcs : cnt0.size = 16 := by rw [hcnt0]; exact cntArr_size _ _
  have hcv : ∀ L, L < 16 → cnt cnt0 L = lcount (lensf s lo) codes.toNat L := by
    intro L hL; rw [← cnt_eq (by omega)]; subst hcnt0; exact cntArr_get _ _ hc288 L hL
  refine Wp.have_ ?_
  refine Wp.bind (Wp.mono (max_loop_wp hcs) ?_)
  rintro ⟨mx, dn⟩ h1 ⟨rfl, hmx15, habove, hmxc⟩
  dsimp only at hmx15 habove hmxc
  refine Wp.have_ ?_
  refine Wp.ite (fun hm0 => ?_) (fun hm0 => ?_)
  · refine Wp.have_ ?_
    refine Wp.bind (Wp.of_eq (stCode_ok hl (p := off) (i := 0) (by omega) _) ?_)
    refine Wp.bind (Wp.of_eq (add_ok (get_codes hl _ _) (by simp; omega) (by omega) (by simp; omega)) ?_)
    refine Wp.have_ ?_
    rw [show ((off : Int) + 1).toNat = off + 1 by omega]
    refine Wp.bind (Wp.of_eq (stCode_ok hl (p := off + 1) (i := 0) (by simp; omega) _) ?_)
    refine Wp.bind (Wp.of_eq (add_ok (get_codes hl _ _) (by simp; omega) (by omega) (by simp; omega)) ?_)
    refine Wp.have_ ?_
    rw [Wp.pure_iff]
    refine ⟨_, _, rfl, by simp, rfl, ?_, Or.inl rfl, fun e => absurd rfl e, fun _ => ⟨2, by simp, hbnd2, ?_, by simp, by simp, ?_⟩⟩
    · intro i hi
      rw [set_ne _ (by omega), set_ne _ (by omega)]
    · show Ptr.ref _ (((off + 1 + 0 : Nat) : Int) + 1).toNat = _
      congr 1
    · intro i hi
      rw [set_ne _ (by omega), set_ne _ (by omega)]
  have hmx1 : 1 ≤ mx.toNat := by
    have : mx ≠ 0 := fun e => hm0 (by rw [e]; rfl)
    have : mx.toNat ≠ 0 := fun e => this (UInt32.toNat_inj.mp (by rw [e]; rfl))
    omega
  refine Wp.bind (Wp.mono (min_loop_wp hcs mx hmx15 hmx1 (hmxc hmx1)) ?_)
  rintro ⟨mn, dn2⟩ h1 ⟨rfl, hmn1, hmnmx, hbelow, hmnc⟩
  dsimp only at hmn1 hmnmx hbelow hmnc
  refine Wp.have_ ?_
  refine Wp.bind (Wp.mono (left_loop_wp hcs) ?_)
  rintro ⟨lf, len0, ov⟩ h1 ⟨rfl, hlf⟩
  dsimp only at hlf
  refine Wp.ite (fun hov => ?_) (fun hov => ?_)
  · rw [Wp.pure_iff]
    exact post_err rfl rfl (fun _ _ => rfl) (Or.inl rfl)
  obtain ⟨hlf0, hlfk⟩ := hlf (by simpa using hov)
  refine Wp.ite (fun hov => ?_) (fun hcomp => ?_)
  · rw [Wp.pure_iff]
    exact post_err rfl rfl (fun _ _ => rfl) (Or.inl rfl)
  refine Wp.have_ ?_
  refine Wp.bind ?_
  rw [aset_ok (by simp), Wp.pure_iff]
  refine Wp.have_ ?_
  have hc0 : ∀ L, 1 ≤ L → L ≤ 15 → cnt cnt0 L = lcount (lensf s lo) codes.toNat L := fun L _ h2 => hcv L (by omega)
  have hn15 : nsum (cnt cnt0) 15 ≤ codes.toNat := by
    rw [nsum_congr hc0]; exact nsum_lcount_le _ _ _
  refine Wp.bind (Wp.mono (offs_loop_wp hcs (by omega) _ (by simp) (by simp [cnt])) ?_)
  rintro offs h1 ⟨rfl, hos, hov⟩
  refine Wp.have_ ?_
  refine Wp.bind (Wp.mono (sort_loop_wp hl hP.lens_size hc288 hP.lens15 (by rw [hP.work_size]; exact hc288) hc0 offs hos hov) ?_)
  rintro ⟨offs2, sy⟩ h1 ⟨W, rfl, hWs, hsorted⟩
  refine Wp.have_ ?_
  have hrootv := root_toNat bits mx mn hmnmx
  generalize (if (if bits > mx then mx else bits) > mn then (if bits > mx then mx else bits) else mn) = root at hrootv ⊢
  have hr15 : root.toNat ≤ 15 := by omega
  have hroot1 : 1 ≤ root.toNat := by omega
  have hrootmx : root.toNat ≤ mx.toNat := by omega
  have hsh : ((1 : UInt32) <<< root).toNat = 2 ^ root.toNat := u32_shl_one (by omega)
  have hp15 : 2 ^ root.toNat ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) hr15
  have hmask : ((1 : UInt32) <<< root - 1).toNat = 2 ^ root.toNat - 1 := by
    rw [u32_sub (by rw [hsh]; have := Nat.two_pow_pos root.toNat; simp; omega), hsh]; rfl
  refine Wp.bind ?_
  rw [shl32_ok (by rw [UInt32.lt_iff_toNat_lt]; show _ < 32; omega), Wp.pure_iff]
  refine Wp.have_ ?_
  refine Wp.ite (fun hbig => ?_) (fun hbig => ?_)
  · rw [Wp.pure_iff]
    exact post_err rfl hWs (fun _ _ => rfl) (Or.inr rfl)
  have hkind : (type = CODES ∧ mx.toNat ≤ root.toNat ∧ codes.toNat ≤ 19 ∧ 2 ^ root.toNat ≤ bndOf type bits ∧
        bndOf type bits < 2 ^ 16) ∨
      (type = LENS ∧ bndOf type bits = 1332 ∧ codes.toNat ≤ 288 ∧ 2 ^ root.toNat ≤ bndOf type bits) ∨
      (type = DISTS ∧ bndOf type bits = 592 ∧ codes.toNat ≤ 32 ∧ 2 ^ root.toNat ≤ bndOf type bits) := by
    rcases hP.kind with ⟨rfl, hk1, hk2, hk3, hk4⟩ | ⟨rfl, hk1⟩ | ⟨rfl, hk1⟩
    · have hmxb : mx.toNat ≤ bits.toNat := by
        have := hmxc hmx1
        rw [hcv _ (by omega)] at this
        obtain ⟨j, hj, hfj⟩ := lcount_pos this
        rw [← hfj]; exact hk4 j hj
      have hb : bndOf CODES bits = 2 ^ bits.toNat := by
        unfold bndOf; rw [ite_eq_right (by decide), ite_eq_right (by decide)]
      refine Or.inl ⟨rfl, by omega, hk1, ?_, ?_⟩
      · rw [hb]; exact Nat.pow_le_pow_right (by omega) (by omega)
      · rw [hb]; exact Nat.pow_lt_pow_right (by omega) (by omega)
    · have hb : bndOf LENS bits = 1332 := by unfold bndOf; rw [ite_eq_left rfl]
      refine Or.inr (Or.inl ⟨rfl, hb, hk1, ?_⟩)
      rw [hb]
      simp only [show (LENS == LENS) = true from rfl, show (LENS == DISTS) = false from rfl, Bool.true_and,
        Bool.false_and, Bool.or_false, decide_eq_true_eq, gt_iff_lt, UInt32.lt_iff_toNat_lt, hsh] at hbig
      exact Nat.le_of_not_lt hbig
    · have hb : bndOf DISTS bits = 592 := by unfold bndOf; rw [ite_eq_right (by decide), ite_eq_left rfl]
      refine Or.inr (Or.inr ⟨rfl, hb, hk1, ?_⟩)
      rw [hb]
      simp only [show (DISTS == LENS) = false from rfl, show (DISTS == DISTS) = true from rfl, Bool.true_and,
        Bool.false_and, Bool.false_or, decide_eq_true_eq, gt_iff_lt, UInt32.lt_iff_toNat_lt, hsh] at hbig
      exact Nat.le_of_not_lt hbig
  have hbroot : 2 ^ root.toNat ≤ bndOf type bits := by
    rcases hkind with ⟨-, -, -, h1, -⟩ | ⟨-, -, -, h1⟩ | ⟨-, -, -, h1⟩ <;> exact h1
  have hblt : bndOf type bits < 2 ^ 16 := by
    rcases hkind with ⟨-, -, -, -, h1⟩ | ⟨-, h1, -⟩ | ⟨-, h1, -⟩ <;> omega
  have hS : Setup.OK ⟨h, b, s, W, lo, codes.toNat, off, type, cnt cnt0, mx.toNat, root.toNat, bndOf type bits⟩ := by
    refine { live := hl, lens_size := hP.lens_size, W_size := hWs, n_le := by rw [hWs, hP.work_size]; exact Nat.le_trans hn15 hc288,
             n_codes := hn15, sorted := hsorted, mx1 := hmx1, mx15 := hmx15,
             c0mx := by have := hmxc hmx1; dsimp only; omega, above := habove, root1 := hroot1,
             rootmx := hrootmx, kraft := by dsimp only; omega, complete := ?_, bnd_root := hbroot,
             bnd_size := hroom, bnd_lt := hblt, codes_lt := hcl, kind := ?_ }
    · dsimp only
      by_cases hl0 : lf.toInt = 0
      · left; omega
      · right
        have hpos : (decide (lf > 0)) = true := by
          simp only [decide_eq_true_eq, gt_iff_lt, Int32.lt_iff_toInt_lt]
          show (0 : Int) < _
          omega
        rw [hpos, Bool.true_and] at hcomp
        have hm1 : mx = 1 := by
          simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Classical.not_not] at hcomp
          exact hcomp.2
        have hm1' : mx.toNat = 1 := by rw [hm1]; rfl
        refine ⟨hm1', ?_⟩
        have := wsum_one (c := cnt cnt0) (fun L h1 h2 => habove L (by omega) h2)
        have := hmxc hmx1
        rw [hm1'] at this
        omega
    · rcases hkind with ⟨h1, h2, h3, -⟩ | ⟨h1, h2, h3, -⟩ | ⟨h1, h2, h3, -⟩
      · exact Or.inl ⟨h1, h2, h3⟩
      · exact Or.inr (Or.inl ⟨h1, h2, h3⟩)
      · exact Or.inr (Or.inr ⟨h1, h2, h3⟩)
  refine Wp.bind ?_
  refine Wp.of_eq rfl ?_
  refine Wp.have_ ?_
  refine Wp.bind (Wp.mono (tbl_loop_gen hS ?_ _ ?_) ?_)
  · refine ⟨s.codes, 0, rfl, ?_⟩
    have hns : nsum (cnt cnt0) mn.toNat = cnt cnt0 mn.toNat := by
      have := nsum_succ (cnt cnt0) (mn.toNat - 1)
      rw [show mn.toNat - 1 + 1 = mn.toNat by omega, nsum_eq_zero (fun L h1 (h2 : L ≤ mn.toNat - 1) => hbelow L h1 (by omega))] at this
      omega
    exact { ret := rfl, csize := rfl, frame := fun _ _ => rfl, used_bnd := by dsimp only; rw [hsh]; exact hbroot,
            count_size := hcs, len_lo := hmn1, len_hi := hmnmx, below := hbelow, above := fun _ _ _ => rfl,
            cur_pos := by dsimp only; omega, cur_le := Nat.le_refl _, sym := by dsimp only; rw [hns]; simp,
            rhuff := rfl, kraft := by simp, dvd := Nat.dvd_zero _, huff := by simp,
            geo := Or.inl ⟨rfl, rfl, rfl, by dsimp only; rw [hsh], rfl, fun _ => by dsimp only; omega⟩ }
  · intro t h1 hmi
    obtain ⟨C, K, rfl, hst⟩ := hmi
    rw [show @zng_inflate_table.match_7.{1} = @tblCont.match_1.{1} from rfl]
    have hsym := hst.sym
    have hlen1 := hst.len_lo
    have hlen2 := hst.len_hi
    have hn := nsum_mono (cnt cnt0) (show t.len.toNat ≤ 15 by dsimp only at hlen2; omega)
    have hc1 := hst.cur_pos
    have hcl := hst.cur_le
    dsimp only at hsym hlen1 hlen2 hc1 hcl
    have hlo : nsum (cnt cnt0) (t.len.toNat - 1) ≤ t.sym.toNat := by
      have := nsum_succ (cnt cnt0) (t.len.toNat - 1)
      rw [show t.len.toNat - 1 + 1 = t.len.toNat by omega] at this
      omega
    obtain ⟨hWc, -⟩ := hsorted t.len.toNat hlen1 (by omega) t.sym.toNat hlo (by omega)
    have hWsz : t.sym.toNat < W.size := by rw [hWs, hP.work_size]; omega
    refine Wp.have_ ?_
    refine Wp.have_ ?_
    refine bind_have ?_
    refine Wp.of_eq (index_nat (get_work hl C W) (off := 0) (by omega)) ?_
    rw [Nat.zero_add]
    rcases hkind with ⟨rfl, -, hc19, -⟩ | ⟨rfl, -, hc, -⟩ | ⟨rfl, -, hc, -⟩
    · refine Wp.ite (fun hge => absurd hge ?_) (fun _ => ?_)
      · rw [ge_iff_le, UInt32.le_iff_toNat_le, UInt16.toNat_toUInt32]
        show ¬ 20 ≤ _
        omega
      refine Wp.ite (fun _ => ?_) (fun _ => ?_)
      · wp_have_intro
        intro here
        tbl_to_S CODES; tblCont_steps mx root ((1 : UInt32) <<< root - 1)
      · wp_have_intro
        intro here
        tbl_to_S CODES; tblCont_steps mx root ((1 : UInt32) <<< root - 1)
    · refine Wp.ite (fun hge => ?_) (fun _ => ?_)
      · have hge' : 257 ≤ (W[t.sym.toNat]!).toNat := by
          rw [ge_iff_le, UInt32.le_iff_toNat_le, UInt16.toNat_toUInt32] at hge
          exact hge
        have hidx : ((W[t.sym.toNat]!).toUInt32 - 257).toNat < 31 := by
          rw [u32_sub (by rw [UInt16.toNat_toUInt32]; exact hge'), UInt16.toNat_toUInt32]
          show _ - 257 < 31; omega
        refine Wp.bind ?_
        show Wp ((U16Src.st lext).at ((W[t.sym.toNat]!).toUInt32 - 257).toNat) _ _
        rw [st_at_ok (by simp [lext]; exact hidx), Wp.pure_iff]
        refine Wp.have_ ?_
        refine Wp.have_ ?_
        refine Wp.have_ ?_
        refine Wp.bind ?_
        show Wp ((U16Src.st lbase).at ((W[t.sym.toNat]!).toUInt32 - 257).toNat) _ _
        rw [st_at_ok (by simp [lbase]; exact hidx), Wp.pure_iff]
        wp_have_intro; intro here
        tbl_to_S LENS; tblCont_steps mx root ((1 : UInt32) <<< root - 1)
      refine Wp.ite (fun _ => ?_) (fun _ => ?_) <;>
        (wp_have_intro; intro here
         tbl_to_S LENS; tblCont_steps mx root ((1 : UInt32) <<< root - 1))
    · refine Wp.ite (fun hge => ?_) (fun hge => absurd (show (W[t.sym.toNat]!).toUInt32 ≥ (0 : UInt32) from
        UInt32.zero_le) hge)
      have hidx : ((W[t.sym.toNat]!).toUInt32 - 0).toNat < 32 := by
        rw [UInt32.sub_zero, UInt16.toNat_toUInt32]; omega
      refine Wp.bind ?_
      show Wp ((U16Src.st dext).at ((W[t.sym.toNat]!).toUInt32 - 0).toNat) _ _
      rw [st_at_ok (by simp [dext]; omega), Wp.pure_iff]
      refine Wp.have_ ?_
      refine Wp.have_ ?_
      refine Wp.have_ ?_
      refine Wp.bind ?_
      show Wp ((U16Src.st dbase).at ((W[t.sym.toNat]!).toUInt32 - 0).toNat) _ _
      rw [st_at_ok (by simp [dbase]; omega), Wp.pure_iff]
      wp_have_intro; intro here
      tbl_to_S DISTS; tblCont_steps mx root ((1 : UInt32) <<< root - 1)
  · rintro t h1 (⟨C, rfl, hf⟩ | ⟨C, rfl, hf⟩)
    · have hfu := hf.used_bnd
      have hfr := hf.root_le
      have hfc := hf.csize
      have hff := hf.frame
      dsimp only at hfu hfr hfc hff
      rw [hf.ret]
      refine Wp.ite (fun e => absurd e (by decide)) (fun _ => ?_)
      refine Wp.have_ ?_
      have hjp : ∀ C', C'.size = s.codes.size → (∀ i, ¬ (off ≤ i ∧ i < off + t.used.toNat) → C'[i]? = s.codes[i]?) →
          Wp ((Ptr.ref (CodeRef.codes b) off).add (Int.ofNat t.used.toNat) >>= fun x => pure (0, x, root))
            (setCW h b s C' W) (TablePost h b s type bits off) := by
        intro C' hC' hfr'
        refine Wp.bind (Wp.of_eq (add_ok (get_codes hl C' W) (by omega) (by simp only [Int.ofNat_eq_natCast]; omega) (by simp only [Int.ofNat_eq_natCast]; omega)) ?_)
        rw [Wp.pure_iff]
        refine ⟨C', W, rfl, hC', hWs, fun i hi => hfr' i (fun x => hi ⟨x.1, by omega⟩), Or.inl rfl,
          fun e => absurd rfl e, fun _ => ⟨t.used.toNat, hfr, hfu, ?_, hroot1, hr15, hfr'⟩⟩
        show Ptr.ref _ _ = _
        congr 1
      rcases hf.huff with ⟨-, hz⟩ | ⟨-, hd, hh1, hr1, hnx, hu2⟩
      · rw [hz]
        refine Wp.ite (fun e => absurd e (by decide)) (fun _ => ?_)
        exact hjp C hfc hff
      · have hne : (t.huff != 0) = true := by
          have : t.huff ≠ 0 := fun e => by rw [e] at hh1; simp at hh1
          simpa using this
        rw [ite_eq_left hne]
        refine Wp.have_ ?_
        dsimp only at hnx hu2 hr1
        rw [hnx]
        refine Wp.bind (Wp.of_eq (stCode_ok hl (p := off) (i := t.huff.toNat) (by omega) _) ?_)
        refine hjp _ (by simp [hfc]) (fun i hi => ?_)
        rw [set_ne _ (by omega)]
        exact hff i hi
    · rw [hf.ret]
      refine Wp.ite (fun _ => ?_) (fun e => absurd rfl e)
      rw [Wp.pure_iff]
      exact post_err hf.csize hWs hf.frame (Or.inr rfl)

end ZlibNgF.Proof.Inftrees
