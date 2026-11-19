import ZlibNgF.Proof.«inftrees.c.sub»

/-!
# `zng_inflate_table`: replicating an entry and stepping to the next code (`ZlibNgF`)

`tblCont_wp`: from a loop state satisfying the invariant, the part of the body after `here` is made stores `here`
in every slot of the current table that the code selects, steps `rhuff` / `huff` to the next canonical code,
decrements the count of the current length, moves `len` to the next length when that count reaches zero, and either
finishes (`ret = 0` after the last code) or continues in `tblSub`.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.Inftrees
open C ZlibNg.Inftrees ZlibNg.InflateP ZlibNgF.Math.BitReverse ZlibNgF.Math.InftreesCount

theorem cnt_set {a : Array UInt16} {k : Nat} (hk : k < a.size) (v : UInt16) (L : Nat) :
    cnt (a.set! k v) L = if L = k then v.toNat else cnt a L := by
  unfold cnt
  by_cases e : L = k
  · subst e
    rw [getElem!_pos _ L (by simp [hk])]
    simp
  · rw [ite_eq_right e]
    by_cases hL : L < a.size
    · rw [getElem!_pos _ L (by simp [hL]), getElem!_pos _ L hL]
      simp only [Array.set!_eq_setIfInBounds]
      rw [Array.getElem_setIfInBounds_ne hL (Ne.symm e)]
    · rw [getElem!_neg _ L (by simp [hL]), getElem!_neg _ L hL]

theorem rev16_pow15 : rev 16 (2 ^ 15) = 1 := by
  have := rev_mul_pow 15 1 1
  rw [show rev 1 1 = 1 from rfl] at this
  simpa using this

theorem rhuff_step {r : UInt16} {x : UInt32} (hx : x.toNat < 2 ^ 31) :
    ((r.toUInt32 + x).toUInt16).toNat = (r.toNat + x.toNat) % 2 ^ 16 := by
  have hr := r.toNat_lt
  rw [UInt32.toNat_toUInt16, u32_add (by rw [UInt16.toNat_toUInt32]; omega), UInt16.toNat_toUInt32]

theorem wsum_one {c : Nat → Nat} (h : ∀ L, 1 < L → L ≤ 15 → c L = 0) : wsum c 15 = c 1 * 2 ^ 15 := by
  have : ∀ m, 1 ≤ m → m ≤ 15 → wsum c m = c 1 * 2 ^ 15 := by
    intro m h1 h2
    induction m with
    | zero => omega
    | succ m ih =>
      rw [wsum_succ]
      by_cases e : m = 0
      · subst e; simp
      · rw [ih (by omega) (by omega), h (m + 1) (by omega) (by omega)]; simp
  exact this 15 (by omega) (by omega)

theorem fill_bound {q d m j : Nat} (hq : q < d) (hj : j < m) : q + j * d < m * d := by
  have : (j + 1) * d ≤ m * d := Nat.mul_le_mul_right _ hj
  rw [Nat.add_mul, Nat.one_mul] at this
  omega

/-- The invariant for the state after one code: `len` is the length of the next code (`inb = false`: the next
code may start a new block). -/
theorem st_next {S : Setup} (hS : S.OK) {t : TL} {C C' : Array Code} {K : Nat} (hst : St S t C K true)
    (hsize : C'.size = C.size)
    (hfr : ∀ i, ¬ (S.off ≤ i ∧ i < S.off + t.used.toNat) → C'[i]? = C[i]?)
    {count : Array UInt16} (hcount : count = t.count.set! t.len.toNat (t.count[t.len.toNat]! - 1))
    {r : UInt16} (hr : r.toNat = (K + 2 ^ (16 - t.len.toNat)) % 2 ^ 16)
    {hf : UInt32} (hhf : hf.toNat = rev 16 (K + 2 ^ (16 - t.len.toNat)))
    {len : UInt32} {min : UInt32} (here : Code)
    (hcov : CovPre S → Cv S t C' (K + 2 ^ (16 - t.len.toNat)))
    (hlen : (2 ≤ cnt t.count t.len.toNat ∧ len = t.len) ∨
      (cnt t.count t.len.toNat = 1 ∧ 1 ≤ len.toNat ∧ len.toNat ≤ 15 ∧
        nsum S.c0 (len.toNat - 1) ≤ t.sym.toNat + 1 ∧ t.sym.toNat + 1 < nsum S.c0 len.toNat)) :
    St S { t with len, sym := t.sym + 1, min, rhuff := r, huff := hf, here, count } C'
      (K + 2 ^ (16 - t.len.toNat)) false := by
  have hlen1 := hst.len_lo
  have hlen2 := hst.len_hi
  have hmx := hS.mx15
  have hcs := hst.count_size
  have hcl : t.len.toNat < t.count.size := by omega
  have hc1 := hst.cur_pos
  have hcv : cnt count = fun L => if L = t.len.toNat then cnt t.count t.len.toNat - 1 else cnt t.count L := by
    funext L
    rw [hcount, cnt_set hcl]
    split
    · unfold cnt
      have : (t.count[t.len.toNat]! - 1).toNat = (t.count[t.len.toNat]!).toNat - 1 := by
        rw [UInt16.toNat_sub_of_le]
        · rfl
        · rw [UInt16.le_iff_toNat_le]; unfold cnt at hc1; exact hc1
      rw [this]
    · rfl
  have hsym := hst.sym
  have hn := nsum_mono S.c0 (show t.len.toNat ≤ 15 by omega)
  have hnle := hS.n_le
  have hncodes := hS.n_codes
  have hcodes : S.codes ≤ 288 := by rcases hS.kind with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> omega
  have one : (1 : UInt32).toNat = 1 := rfl
  have hsym1 : (t.sym + 1).toNat = t.sym.toNat + 1 := by
    rw [u32_add (by rw [one]; omega), one]
  have hkr : K + 2 ^ (16 - t.len.toNat) + wsum (cnt count) 15 = wsum S.c0 15 := by
    have := wsum_dec (c := cnt t.count) (d := cnt count) (k := t.len.toNat) (m := 15) (by omega) (by omega)
      (by rw [hcv]; simp; omega) (fun L hL => by rw [hcv]; simp [hL])
    have := hst.kraft
    omega
  have hw1 : 1 ≤ 2 ^ (16 - t.len.toNat) := Nat.two_pow_pos _
  have hT := hS.kraft
  have hdvd0 := hst.dvd
  -- the tables carry over; the weight of the codes of the current sub-table drops by this code's
  have hgeo : ∀ (L : Nat), t.len.toNat ≤ L →
      Geo S { t with len, sym := t.sym + 1, min, rhuff := r, huff := hf, here, count } (cnt count)
        (K + 2 ^ (16 - t.len.toNat)) L false := by
    intro L hL
    rcases hst.geo with ⟨h1, h2, h3, h4, h5, -⟩ | ⟨h1, h2, h3, h4, nx, P, h5, h6, h7, h8, h9, h10, h11⟩
    · exact Or.inl ⟨h1, h2, h3, h4, h5, fun e => by simp at e⟩
    · refine Or.inr ⟨h1, by omega, h3, h4, nx, P, h5, h6, h7, h8, h9, fun _ => ?_, fun e => by simp at e⟩
      have hll := hst.len_le
      rw [h1] at hll
      rcases h10 (h11 rfl) with h | h
      · exact Or.inl h
      · refine Or.inr ?_
        have := wsum_dec (c := cnt t.count) (d := cnt count) (k := t.len.toNat) (m := S.root + t.curr.toNat)
          (by omega) (by omega) (by rw [hcv]; simp; omega) (fun L hL => by rw [hcv]; simp [hL])
        dsimp only
        omega
  rcases hlen with ⟨h2, rfl⟩ | ⟨h1c, hL1, hL15, hcl1, hcl2⟩
  · have hcnt : cnt count t.len.toNat = cnt t.count t.len.toNat - 1 := by rw [hcv]; simp
    have hpos : 1 ≤ wsum (cnt count) 15 := by
      have := wsum_le_of (cnt count) (k := t.len.toNat) (m := 15) (by omega) (by omega)
      have : 2 ^ (16 - t.len.toNat) ≤ cnt count t.len.toNat * 2 ^ (16 - t.len.toNat) :=
        Nat.le_mul_of_pos_left _ (by omega)
      omega
    exact {
           ret := hst.ret
           csize := (by rw [hsize]; exact hst.csize)
           frame := fun i hi => (by rw [hfr i hi]; exact hst.frame i hi)
           used_bnd := hst.used_bnd
           count_size := (by rw [hcount]; simp [hcs])
           len_lo := hlen1
           len_hi := hlen2
           below := fun L h1 h2 => (by dsimp only at h1 h2 ⊢; rw [hcv]; simp [show L ≠ t.len.toNat by omega]; exact hst.below L h1 h2)
           above := fun L h1 h2 => (by dsimp only at h1 h2 ⊢; rw [hcv]; simp [show L ≠ t.len.toNat by omega]; exact hst.above L h1 h2)
           cur_pos := (by dsimp only; omega)
           cur_le := (by dsimp only; have := hst.cur_le; omega)
           sym := (by dsimp only; rw [hsym1]; omega)
           rhuff := (by dsimp only; rw [hr]; exact Nat.mod_eq_of_lt (by omega))
           kraft := hkr
           dvd := Nat.dvd_add hdvd0 (Nat.dvd_refl _)
           huff := hhf
           geo := hgeo _ (Nat.le_refl _)
           cov := hcov }
  · have hsl : t.sym.toNat + 1 = nsum S.c0 t.len.toNat := by omega
    have hgt : t.len.toNat < len.toNat := by
      apply Classical.byContradiction
      intro hle
      have := nsum_mono S.c0 (show len.toNat ≤ t.len.toNat by omega)
      omega
    have hzero : ∀ L, t.len.toNat < L → L < len.toNat → S.c0 L = 0 := by
      intro L h1 h2
      have e2 : nsum S.c0 t.len.toNat + S.c0 L ≤ nsum S.c0 (len.toNat - 1) := by
        have := ssum_sub_le (fun i => S.c0 (i + 1)) (m := t.len.toNat) (n := len.toNat - 1) (by omega) (L - 1)
          (by omega) (by omega)
        simp only [show L - 1 + 1 = L by omega] at this
        exact this
      omega
    have hc0 : 1 ≤ S.c0 len.toNat := by
      have := nsum_succ S.c0 (len.toNat - 1)
      rw [show len.toNat - 1 + 1 = len.toNat by omega] at this
      omega
    have hlmx : len.toNat ≤ S.mx := by
      apply Classical.byContradiction
      intro h
      have := hS.above len.toNat (by omega) hL15
      omega
    have hcnt' : cnt count len.toNat = S.c0 len.toNat := by
      rw [hcv]; simp [show len.toNat ≠ t.len.toNat by omega]; exact hst.above _ hgt hL15
    have hpos : 1 ≤ wsum (cnt count) 15 := by
      have := wsum_le_of (cnt count) (k := len.toNat) (m := 15) (by omega) (by omega)
      have : 2 ^ (16 - len.toNat) ≤ cnt count len.toNat * 2 ^ (16 - len.toNat) :=
        Nat.le_mul_of_pos_left _ (by omega)
      have := Nat.two_pow_pos (16 - len.toNat)
      omega
    exact {
           ret := hst.ret
           csize := (by rw [hsize]; exact hst.csize)
           frame := fun i hi => (by rw [hfr i hi]; exact hst.frame i hi)
           used_bnd := hst.used_bnd
           count_size := (by rw [hcount]; simp [hcs])
           len_lo := hL1
           len_hi := hlmx
           below := fun L h1 h2 => (by
             dsimp only at h1 h2 ⊢
             rw [hcv]
             by_cases e : L = t.len.toNat
             · simp [e]; omega
             · simp only [e, ite_false]
               by_cases hlt : L < t.len.toNat
               · exact hst.below L h1 hlt
               · rw [hst.above L (by omega) (by omega)]; exact hzero L (by omega) h2)
           above := fun L h1 h2 => (by
             dsimp only at h1 h2 ⊢
             rw [hcv]; simp [show L ≠ t.len.toNat by omega]; exact hst.above L (by omega) h2)
           cur_pos := (by dsimp only; omega)
           cur_le := (by dsimp only; omega)
           sym := (by
             dsimp only
             rw [hsym1, hcnt']
             have := nsum_mono S.c0 (show t.len.toNat ≤ len.toNat - 1 by omega)
             have := nsum_succ S.c0 (len.toNat - 1)
             rw [show len.toNat - 1 + 1 = len.toNat by omega] at this
             omega)
           rhuff := (by dsimp only; rw [hr]; exact Nat.mod_eq_of_lt (by omega))
           kraft := hkr
           dvd := (by
             dsimp only
             exact Nat.dvd_add (Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) hdvd0)
               (Nat.pow_dvd_pow 2 (by omega)))
           huff := hhf
           geo := hgeo _ (by dsimp only; omega)
           cov := hcov }

set_option hygiene false in
/-- The steps of `tblCont_wp` after the program is unfolded, on a goal
`Wp P (setCW S.h0 S.b S.s C S.W) (fun t' h' => Trip S t t' h')` where `P` is the part of the loop body after `here`
(`tblCont` unfolded, or the translation's own join point applied to `here`), with `hS`, `hst`, `hmax`, `hroot`,
`hmask` and `here` as in `tblCont_wp`; the arguments are `max`, `root` and `mask` of the program. -/
macro "tblCont_steps" maxv:term:max rootv:term:max mask:term:max : tactic => `(tactic| (
    have hl := hS.live
    have hK := hst.K_lt hS
    have hlen1 := hst.len_lo
    have hlen2 := hst.len_hi
    have hmx := hS.mx15
    have hr1 := hS.root1
    have hrmx := hS.rootmx
    have hcs := hst.count_size
    have hll := hst.len_le
    obtain ⟨nx, hnext, hnx, hur, hdr, hcu15⟩ := hst.geo.next_used hS
    have hdl : t.drop.toNat ≤ t.len.toNat := by
      rcases hst.geo with ⟨h1, -⟩ | ⟨h1, h2, -⟩
      · rw [h1]; exact Nat.zero_le _
      · omega
    have hdrop32 : t.drop.toNat < 32 := by omega
    have hld : (t.len - t.drop).toNat = t.len.toNat - t.drop.toNat := u32_sub hdl
    rw [Wp.bind_iff, shl32_ok (by rw [UInt32.lt_iff_toNat_lt, hld]; show _ < 32; omega), Wp.pure_iff,
      Wp.bind_iff, shl32_ok (by rw [UInt32.lt_iff_toNat_lt]; show _ < 32; omega), Wp.pure_iff]
    refine Wp.have_ ?_
    refine Wp.have_ ?_
    rw [Wp.bind_iff, shr32_ok (by rw [UInt32.lt_iff_toNat_lt]; show _ < 32; omega), Wp.pure_iff]
    have hhuffl : t.huff.toNat < 2 ^ t.len.toNat := by rw [hst.huff]; exact rev16_lt (by omega) hst.dvd
    have hsh : (t.huff >>> t.drop).toNat = t.huff.toNat / 2 ^ t.drop.toNat := u32_shr hdrop32
    have hq : t.huff.toNat / 2 ^ t.drop.toNat < 2 ^ (t.len.toNat - t.drop.toNat) := by
      apply Nat.div_lt_of_lt_mul
      rw [← Nat.pow_add, show t.drop.toNat + (t.len.toNat - t.drop.toNat) = t.len.toNat by omega]
      exact hhuffl
    have hio : Int.ofNat (t.huff >>> t.drop).toNat = ((t.huff.toNat / 2 ^ t.drop.toNat : Nat) : Int) := by
      rw [hsh]; rfl
    have hma : 2 ^ (t.curr.toNat - (t.len.toNat - t.drop.toNat)) * 2 ^ (t.len.toNat - t.drop.toNat) =
        2 ^ t.curr.toNat := by
      rw [← Nat.pow_add]; congr 1; omega
    have hpa : 2 ^ (t.len.toNat - t.drop.toNat) ≤ 2 ^ t.curr.toNat := Nat.pow_le_pow_right (by omega) (by omega)
    have hpc : 2 ^ t.curr.toNat ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) (by omega)
    have hcsz := hst.csize
    have hbs := hS.bnd_size
    have hub := hst.used_bnd
    rw [Wp.bind_iff, hio]
    refine Wp.of_eq (by rw [hnext]; exact add_ok (get_codes hl C S.W) (by omega) (by omega) (by omega)) ?_
    rw [show ((↑(S.off + nx) : Int) + ((t.huff.toNat / 2 ^ t.drop.toNat : Nat) : Int)).toNat =
      S.off + nx + t.huff.toNat / 2 ^ t.drop.toNat by omega]
    refine Wp.have_ ?_
    have hp : ∀ j, j < 2 ^ (t.curr.toNat - (t.len.toNat - t.drop.toNat)) →
        S.off + nx + t.huff.toNat / 2 ^ t.drop.toNat + j * 2 ^ (t.len.toNat - t.drop.toNat) < C.size := by
      intro j hj
      have := fill_bound hq hj
      omega
    have hincr : ((1 : UInt32) <<< (t.len - t.drop)).toNat = 2 ^ (t.len.toNat - t.drop.toNat) := by
      rw [u32_shl_one (by rw [hld]; omega), hld]
    have hf0 : ((1 : UInt32) <<< t.curr).toNat =
        2 ^ (t.curr.toNat - (t.len.toNat - t.drop.toNat)) * 2 ^ (t.len.toNat - t.drop.toNat) := by
      rw [u32_shl_one (by omega), hma]
    rw [Wp.bind_iff]
    refine Wp.mono (fill4_wp hl (Nat.two_pow_pos _) (by omega) hp _ hincr (packCode here) _ hf0) ?_
    rintro f h1 ⟨q4, C1, hf, hq4, hq4m, rfl, hF1⟩
    rw [Wp.bind_iff]
    refine Wp.mono (fill1_wp hl (by omega) hp _ hincr _ f hf hq4m hF1) ?_
    rintro _ h2 ⟨C2, rfl, hF2⟩
    have hcov2 : CovPre S → Cv S t C2 (K + 2 ^ (16 - t.len.toNat)) := fun hp => cov_fill hS hst hp (hhere hp) hnx hF2
    -- the stores stay in the current table
    have hsize2 : C2.size = C.size := hF2.size
    have hfr2 : ∀ i, ¬ (S.off ≤ i ∧ i < S.off + t.used.toNat) → C2[i]? = C[i]? := by
      intro i hi
      apply hF2.keep
      intro j _ hj e
      have := fill_bound hq hj
      omega
    have hl1 : (t.len - 1).toNat = t.len.toNat - 1 := u32_sub (by simp; omega)
    rw [Wp.bind_iff, shr32_ok (by rw [UInt32.lt_iff_toNat_lt, hl1]; show _ < 32; omega), Wp.pure_iff]
    have hw : ((32768 : UInt32) >>> (t.len - 1)).toNat = 2 ^ (16 - t.len.toNat) := by
      rw [u32_shr (by rw [hl1]; omega), hl1]
      show 2 ^ 15 / 2 ^ (t.len.toNat - 1) = _
      rw [Nat.pow_div (by omega) (by omega)]
      congr 1; omega
    refine Wp.have_ ?_
    refine Wp.have_ ?_
    refine Wp.have_ ?_
    have hcl : t.len.toNat < t.count.size := by omega
    rw [Wp.bind_iff, aget_ok hcl, Wp.pure_iff, Wp.bind_iff, aset_ok hcl, Wp.pure_iff]
    refine Wp.have_ ?_
    refine Wp.have_ ?_
    have hc1 := hst.cur_pos
    have hcget : t.count[t.len.toNat] = t.count[t.len.toNat]! := (getElem!_pos t.count _ hcl).symm
    have hcnat : (t.count[t.len.toNat]).toNat = cnt t.count t.len.toNat := by rw [hcget]; rfl
    have hr : (((t.rhuff.toUInt32 + (32768 : UInt32) >>> (t.len - 1)).toUInt16)).toNat =
        (K + 2 ^ (16 - t.len.toNat)) % 2 ^ 16 := by
      rw [rhuff_step (by rw [hw]; have : 2 ^ (16 - t.len.toNat) ≤ 2 ^ 16 := Nat.pow_le_pow_right (by omega) (by omega); omega),
        hw, hst.rhuff]
    have hhf : ((zng_bitreverse16 (t.rhuff.toUInt32 + (32768 : UInt32) >>> (t.len - 1)).toUInt16).toUInt32).toNat =
        rev 16 (K + 2 ^ (16 - t.len.toNat)) := by
      rw [UInt16.toNat_toUInt32, bitreverse16_toNat, hr, rev_mod]
    have hsym := hst.sym
    have hnle := hS.n_le
    have hncodes := hS.n_codes
    have hcodes : S.codes ≤ 288 := by rcases hS.kind with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> omega
    have one : (1 : UInt32).toNat = 1 := rfl
    have hn := nsum_mono S.c0 (show t.len.toNat ≤ 15 by omega)
    have hsym1 : (t.sym + 1).toNat = t.sym.toNat + 1 := by rw [u32_add (by rw [one]; omega), one]
    have hsub_trip : ∀ (len' : UInt32) (h' : Heap),
        (2 ≤ cnt t.count t.len.toNat ∧ len' = t.len) ∨
          (cnt t.count t.len.toNat = 1 ∧ 1 ≤ len'.toNat ∧ len'.toNat ≤ 15 ∧
            nsum S.c0 (len'.toNat - 1) ≤ t.sym.toNat + 1 ∧ t.sym.toNat + 1 < nsum S.c0 len'.toNat) →
        h' = setCW S.h0 S.b S.s C2 S.W →
        Wp (tblSub S.type (.ref (.codes S.b) S.off) $maxv $rootv $mask t here ((1 : UInt32) <<< t.curr)
          ((t.rhuff.toUInt32 + (32768 : UInt32) >>> (t.len - 1)).toUInt16)
          (zng_bitreverse16 (t.rhuff.toUInt32 + (32768 : UInt32) >>> (t.len - 1)).toUInt16).toUInt32
          (t.sym + 1) (t.count.set! t.len.toNat (t.count[t.len.toNat] - 1)) len') h'
          (fun t' h' => Trip S t t' h') := by
      intro len' h' hlen' rfl
      have hst' := st_next hS hst hsize2 hfr2 (count := t.count.set! t.len.toNat (t.count[t.len.toNat] - 1))
        (by rw [hcget]) hr hhf (len := len') (min := (1 : UInt32) <<< t.curr) here hcov2 hlen'
      refine Wp.mono (tblSub_wp hS hmax hroot hmask hst' (by rw [u32_shl_one (by omega)])) ?_
      rintro t' h'' (⟨hmi, hs'⟩ | h1)
      · refine Or.inl ⟨hmi, by rw [hs', hsym1]; omega, by rw [hs', hsym1]; omega⟩
      · exact Or.inr (Or.inr h1)
    by_cases hz : (t.count[t.len.toNat] - 1 == 0) = true
    · have hc1' : cnt t.count t.len.toNat = 1 := by
        have h0 : (t.count[t.len.toNat] - 1).toNat = 0 := by rw [beq_iff_eq.mp hz]; rfl
        rw [UInt16.toNat_sub_of_le _ _ (by rw [UInt16.le_iff_toNat_le, hcnat]; exact hc1), hcnat] at h0
        have : (1 : UInt16).toNat = 1 := rfl
        omega
      rw [ite_eq_left hz]
      by_cases hm : (t.len == $maxv) = true
      · rw [ite_eq_left hm, Wp.pure_iff]
        have hlm : t.len.toNat = S.mx := by rw [← hmax]; exact congrArg UInt32.toNat (beq_iff_eq.mp hm)
        refine Or.inr (Or.inl ⟨C2, rfl, ?_⟩)
        have hcv0 : ∀ L, 1 ≤ L → L ≤ 15 → cnt (t.count.set! t.len.toNat (t.count[t.len.toNat] - 1)) L = 0 := by
          intro L h1 h2
          rw [cnt_set hcl]
          split
          · rw [UInt16.toNat_sub_of_le _ _ (by rw [UInt16.le_iff_toNat_le, hcnat]; exact hc1), hcnat]
            have : (1 : UInt16).toNat = 1 := rfl
            omega
          · by_cases hlt : L < t.len.toNat
            · exact hst.below L h1 hlt
            · rw [hst.above L (by omega) h2]; exact hS.above L (by omega) h2
        have hKT : K + 2 ^ (16 - t.len.toNat) = wsum S.c0 15 := by
          have e1 := wsum_dec (c := cnt t.count) (d := cnt (t.count.set! t.len.toNat (t.count[t.len.toNat] - 1)))
            (k := t.len.toNat) (m := 15) (by omega) (by omega) (by rw [hcv0 _ (by omega) (by omega)]; omega)
            (fun L hL => by rw [cnt_set hcl]; simp [hL])
          rw [wsum_eq_zero hcv0] at e1
          have := hst.kraft
          omega
        refine { ret := rfl, csize := by rw [hsize2]; exact hst.csize,
                 frame := fun i hi => by rw [hfr2 i hi]; exact hst.frame i hi,
                 used_bnd := hst.used_bnd, root_le := hur, geo := ?_, huff := ?_, cov := ?_,
                 lenb := by
                   show 1 ≤ (t.len - t.drop).toNat ∧ (t.len - t.drop).toNat ≤ 15
                   have := hst.cbf hS
                   rw [hld]; omega }
        · rcases hst.geo with ⟨h1, -, h3, h4, -⟩ | ⟨h1, -, -, -, nx', P, h5, -, h7, -⟩
          · exact Or.inl ⟨h1, h3, h4⟩
          · exact Or.inr ⟨h1, nx', h5, h7⟩
        · dsimp only
          rcases hS.complete with hT | ⟨hm1, hc01⟩
          · refine Or.inl ⟨hT, ?_⟩
            apply UInt32.toNat_inj.mp
            rw [hhf, hKT, hT, ← rev_mod, Nat.mod_self]
            simp
          · have hT : wsum S.c0 15 = 2 ^ 15 := by
              rw [wsum_one (fun L h1 h2 => hS.above L (by omega) h2), hc01]
            have hr1 : S.root = 1 := by omega
            rcases hst.geo with ⟨h1, -, h3, h4, -⟩ | ⟨h1, h2, -⟩
            · refine Or.inr ⟨hm1, h1, ?_, hr1, h3, by rw [h4, hr1]⟩
              rw [hhf, hKT, hT, rev16_pow15]
            · omega
        · intro hp i hi hh
          refine (hcov2 hp).ok i hi ?_
          rcases hS.complete with hT | ⟨hm1, hc01⟩
          · rw [hKT, hT]; exact wr_all hS hst i hi
          · have hT : wsum S.c0 15 = 2 ^ 15 := by
              rw [wsum_one (fun L h1 h2 => hS.above L (by omega) h2), hc01]
            have hr1 : S.root = 1 := by omega
            have hh1 : (zng_bitreverse16 (t.rhuff.toUInt32 + (32768 : UInt32) >>> (t.len - 1)).toUInt16).toUInt32.toNat
                = 1 := by rw [hhf, hKT, hT, rev16_pow15]
            have hi0 : i = 0 := by
              rcases hst.geo with ⟨-, -, -, h4, -⟩ | ⟨-, h2, -⟩
              · rw [h4, hr1] at hi
                rcases hh with hh | hh
                · simp only at hh; rw [hh] at hh1; simp at hh1
                · simp only at hh; omega
              · omega
            subst hi0
            refine Or.inl ⟨Nat.two_pow_pos _, Or.inl ?_⟩
            rw [rev_of_zero, Nat.zero_mul, hKT, hT]
            exact Nat.two_pow_pos _
      · rw [ite_eq_right hm]
        have hlm : t.len.toNat ≠ S.mx := fun e => hm (beq_iff_eq.mpr (UInt32.toNat_inj.mp (by rw [e, hmax])))
        have hsl : t.sym.toNat + 1 = nsum S.c0 t.len.toNat := by omega
        have hnmx : nsum S.c0 t.len.toNat + S.c0 S.mx ≤ nsum S.c0 15 := by
          have := ssum_sub_le (fun i => S.c0 (i + 1)) (m := t.len.toNat) (n := 15) (by omega) (S.mx - 1)
            (by omega) (by omega)
          simp only [show S.mx - 1 + 1 = S.mx by omega] at this
          exact this
        have hc0mx := hS.c0mx
        obtain ⟨L', hL1, hL15, hL2, hL3⟩ := class_exists S.c0 15 (t.sym.toNat + 1) (by omega)
        obtain ⟨hWc, hWl⟩ := hS.sorted L' hL1 hL15 _ hL2 hL3
        have hWs := hS.W_size
        have hls := hS.lens_size
        rw [Wp.bind_iff, show (Int.ofNat (t.sym + 1).toNat) = Int.ofNat (t.sym.toNat + 1) by rw [hsym1]]
        refine Wp.of_eq (index_nat (get_work hl C2 S.W) (off := 0) (by omega)) ?_
        rw [Nat.zero_add, Wp.bind_iff]
        refine Wp.of_eq (index_nat (get_lens hl C2 S.W) (by omega)) ?_
        refine Wp.have_ ?_
        refine hsub_trip _ _ (Or.inr ⟨hc1', ?_, ?_, ?_, ?_⟩) rfl
        all_goals
          have e : (S.s.lens[S.lo + (S.W[t.sym.toNat + 1]!).toNat]!).toUInt32.toNat = L' := by
            rw [UInt16.toNat_toUInt32]; exact hWl
          rw [e]
        all_goals omega
    · rw [ite_eq_right hz]
      refine hsub_trip t.len _ (Or.inl ⟨?_, rfl⟩) rfl
      apply Classical.byContradiction
      intro h
      apply hz
      apply beq_iff_eq.mpr
      apply UInt16.toNat_inj.mp
      rw [UInt16.toNat_sub_of_le _ _ (by rw [UInt16.le_iff_toNat_le, hcnat]; exact hc1), hcnat]
      show _ = 0
      have : (1 : UInt16).toNat = 1 := rfl
      omega))

/-- The part of the body after `here` is made. -/
theorem tblCont_wp {S : Setup} (hS : S.OK) {t : TL} {C : Array Code} {K : Nat} (hst : St S t C K true)
    {maxv rootv mask : UInt32} (hmax : maxv.toNat = S.mx) (hroot : rootv.toNat = S.root)
    (hmask : mask.toNat = 2 ^ S.root - 1) (here : Code) (hhere : CovPre S → SubOK S.type t.drop.toNat here) :
    Wp (tblCont S.type (.ref (.lens S.b) S.lo) (.ref (.work S.b) 0) (.ref (.codes S.b) S.off) maxv rootv mask t
      here) (setCW S.h0 S.b S.s C S.W) (fun t' h' => Trip S t t' h') := by
  unfold tblCont
  tblCont_steps maxv rootv mask

end ZlibNgF.Proof.Inftrees
