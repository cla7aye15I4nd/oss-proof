import ZlibNgF.Proof.«inftrees.c.geom»

/-!
# `zng_inflate_table`: opening a sub-table (`ZlibNgF`)

`tblSub_wp`: after the counts and `len` are updated, the body either keeps the current table or opens a new
sub-table whose size `curr` makes every code of its block fit (`curr_loop_wp`), checks the room, and links the root
entry to it.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.Inftrees
open C ZlibNg.Inftrees ZlibNg.InflateP ZlibNgF.Math.BitReverse ZlibNgF.Math.InftreesCount

theorem Wp.have_ {α β : Type} {h : Heap} {Q : β → Heap → Prop} {v : α} {f : α → M β}
    (hf : Wp (f v) h Q) : Wp (have x := v; f x) h Q := hf

theorem St.K_lt {S : Setup} {t : TL} {C : Array Code} {K : Nat} {inb : Bool} (hS : S.OK)
    (hs : St S t C K inb) : K + 2 ^ (16 - t.len.toNat) ≤ 2 ^ 16 := by
  have h1 := wsum_le_of (cnt t.count) (k := t.len.toNat) (m := 15) hs.len_lo (by have := hs.len_hi; have := hS.mx15; omega)
  have h2 := hs.kraft
  have h3 := hS.kraft
  have h4 : 2 ^ (16 - t.len.toNat) ≤ cnt t.count t.len.toNat * 2 ^ (16 - t.len.toNat) :=
    Nat.le_mul_of_pos_left _ hs.cur_pos
  omega

/-- The block number of a code. -/
theorem blk_lt {K r : Nat} (hK : K < 2 ^ 16) (hr : r ≤ 16) : K / 2 ^ (16 - r) < 2 ^ r := by
  apply Nat.div_lt_of_lt_mul
  rw [← Nat.pow_add, show 16 - r + r = 16 by omega]
  exact hK

/-- No new sub-table: the state keeps its tables and `K` is in their block. -/
theorem St.keep {S : Setup} {t : TL} {C : Array Code} {K : Nat} (hS : S.OK) (hs : St S t C K false)
    (mask : UInt32) (hmask : mask.toNat = 2 ^ S.root - 1)
    (hc : ¬ (S.root < t.len.toNat ∧ (t.huff &&& mask) ≠ t.low)) : St S t C K true := by
  have hK := hs.K_lt hS
  have := Nat.two_pow_pos (16 - t.len.toNat)
  have hr16 : S.root ≤ 16 := by have := hS.rootmx; have := hS.mx15; omega
  have hhm : (t.huff &&& mask).toNat = rev S.root (K / 2 ^ (16 - S.root)) := by
    rw [u32_and_mask hmask, hs.huff, rev16_mod hr16]
  refine { hs with geo := ?_ }
  rcases hs.geo with ⟨h1, h2, h3, h4, h5, -⟩ | ⟨h1, h2, h3, h4, nx, P, h5, h6, h7, h8, h9, h10, -⟩
  · refine Or.inl ⟨h1, h2, h3, h4, h5, fun _ => ?_⟩
    apply Classical.byContradiction
    intro hlt
    apply hc ⟨by omega, ?_⟩
    rw [h5]
    intro e
    have := congrArg UInt32.toNat e
    rw [hhm] at this
    have hl := rev_lt S.root (K / 2 ^ (16 - S.root))
    have : 2 ^ S.root ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) (by have := hS.rootmx; have := hS.mx15; omega)
    have e2 : (0xFFFFFFFF : UInt32).toNat = 4294967295 := rfl
    omega
  · refine Or.inr ⟨h1, h2, h3, h4, nx, P, h5, h6, h7, h8, h9, h10, fun _ => ?_⟩
    have heq : t.huff &&& mask = t.low := by
      apply Classical.byContradiction
      intro hne
      exact hc ⟨h2, hne⟩
    have := congrArg UInt32.toNat heq
    rw [hhm, h9] at this
    exact rev_inj (blk_lt (by omega) hr16) h8 this

theorem i32_ok {v : Int} (h1 : -2147483648 ≤ v) (h2 : v < 2147483648) : (Int32.ofInt v).toInt = v :=
  Int32.toInt_ofInt_of_le (by omega) (by omega)

theorem cnt_eq {a : Array UInt16} {L : Nat} (h : L < a.size) : (a[L]'h).toNat = cnt a L := by
  unfold cnt; rw [getElem!_pos a L h]

/-- The look-ahead loop that sizes a new sub-table. -/
theorem curr_loop_wp {S : Setup} (hS : S.OK) {count : Array UInt16} (hcs : count.size = 16)
    {len : Nat} (hlen1 : S.root < len) (hlen2 : len ≤ S.mx)
    (hbelow : ∀ L, 1 ≤ L → L < len → cnt count L = 0)
    (drop maxv : UInt32) (hdrop : drop.toNat = S.root) (hmax : maxv.toNat = S.mx)
    (curr : UInt32) (hcurr : curr.toNat = len - S.root) (left : Int32)
    (hleft : left.toInt = ((2 ^ (len - S.root) : Nat) : Int)) (h : Heap) :
    Wp (cwhile
        (fun ((curr, left, done) : UInt32 × Int32 × Bool) => pure (!done && curr + drop < maxv, (curr, left, done)))
        (fun ((curr, left, _) : UInt32 × Int32 × Bool) => do
          let left ← chkI32 (left.toInt - ((← aget count (curr + drop).toNat).toNat : Int))
          if left <= 0 then pure (curr, left, true)
          else pure (curr + 1, ← chkI32 (left.toInt * 2), false))
        (curr, left, false)) h
      (fun r h' => h' = h ∧ len - S.root ≤ r.1.toNat ∧ S.root + r.1.toNat ≤ S.mx ∧
        (S.mx ≤ S.root + r.1.toNat ∨ 2 ^ (16 - S.root) ≤ wsum (cnt count) (S.root + r.1.toNat))) := by
  have hmx := hS.mx15
  refine Wp.cwhile (fun n (st : UInt32 × Int32 × Bool) h' => h' = h ∧ len - S.root ≤ st.1.toNat ∧
      S.root + st.1.toNat ≤ S.mx ∧
      (st.2.2 = false → st.2.1.toInt * ((2 ^ (16 - S.root - st.1.toNat) : Nat) : Int) +
          (wsum (cnt count) (S.root + st.1.toNat - 1) : Int) = ((2 ^ (16 - S.root) : Nat) : Int) ∧
        1 ≤ st.2.1.toInt ∧ n = 2 * (S.mx - S.root - st.1.toNat) + 1) ∧
      (st.2.2 = true → 2 ^ (16 - S.root) ≤ wsum (cnt count) (S.root + st.1.toNat) ∧ n = 0))
    _ ?_ (n := 2 * (S.mx - S.root - curr.toNat) + 1) ⟨rfl, by dsimp only; omega, by dsimp only; omega,
      fun _ => ⟨?_, ?_, rfl⟩, fun e => by simp at e⟩
    (by unfold fuel; omega)
  · rintro n ⟨cu, lf, done⟩ h' ⟨rfl, hc1, hc2, hnd, hd⟩
    dsimp only at hc1 hc2 hnd hd
    simp only [Wp.pure_iff]
    refine ⟨fun hc => ?_, fun hc => ?_⟩
    · -- a trip: done = false and root + cu < mx
      have hdn : done = false := by cases done <;> simp_all
      subst hdn
      have hlt : (cu + drop).toNat < S.mx := by
        simp only [Bool.not_false, Bool.true_and, decide_eq_true_eq, UInt32.lt_iff_toNat_lt, hmax] at hc
        exact hc
      have hcd : (cu + drop).toNat = S.root + cu.toNat := by
        rw [u32_add (by omega), hdrop]; omega
      obtain ⟨hinv, hl1, rfl⟩ := hnd rfl
      rw [Wp.bind_iff, aget_ok (by rw [hcs]; omega), Wp.pure_iff, Wp.bind_iff]
      have hcv := cnt_eq (a := count) (L := (cu + drop).toNat) (by rw [hcs]; omega)
      rw [hcv, hcd]
      -- the weights
      set_option linter.unusedVariables false in
      have hB : 2 ^ (16 - S.root - cu.toNat) = 2 * 2 ^ (16 - S.root - (cu.toNat + 1)) := by
        rw [← Nat.pow_succ']; congr 1; omega
      have hw : wsum (cnt count) (S.root + cu.toNat) = wsum (cnt count) (S.root + cu.toNat - 1) +
          cnt count (S.root + cu.toNat) * 2 ^ (16 - S.root - cu.toNat) := by
        have := wsum_succ (cnt count) (S.root + cu.toNat - 1)
        rw [show S.root + cu.toNat - 1 + 1 = S.root + cu.toNat by omega,
          show 15 - (S.root + cu.toNat - 1) = 16 - S.root - cu.toNat by omega] at this
        exact this
      have hpos := Nat.two_pow_pos (16 - S.root - (cu.toNat + 1))
      have hle : lf.toInt ≤ 65536 := by
        have h65 : ((2 ^ (16 - S.root) : Nat) : Int) ≤ 65536 := by
          have : 2 ^ (16 - S.root) ≤ 2 ^ 16 := Nat.pow_le_pow_right (by omega) (by omega)
          omega
        have : lf.toInt * 1 ≤ lf.toInt * ((2 ^ (16 - S.root - cu.toNat) : Nat) : Int) :=
          Int.mul_le_mul_of_nonneg_left (by rw [hB]; omega) (by omega)
        omega
      have hcb : cnt count (S.root + cu.toNat) ≤ 65535 := by
        unfold cnt; have := (count[S.root + cu.toNat]!).toNat_lt; omega
      rw [chkI32_ok (by omega) (by omega), Wp.pure_iff]
      have e1 := i32_ok (v := lf.toInt - (cnt count (S.root + cu.toNat) : Int)) (by omega) (by omega)
      by_cases hz : Int32.ofInt (lf.toInt - (cnt count (S.root + cu.toNat) : Int)) ≤ 0
      · rw [ite_eq_left hz, Wp.pure_iff]
        refine ⟨0, by omega, rfl, hc1, hc2, fun e => by simp at e, fun _ => ⟨?_, rfl⟩⟩
        rw [Int32.le_iff_toInt_le, e1] at hz
        have : (0 : Int32).toInt = 0 := rfl
        rw [this] at hz
        -- lf * B + w = 2^(16-root), lf ≤ c, so 2^(16-root) ≤ w + c * B
        have hm : lf.toInt * ((2 ^ (16 - S.root - cu.toNat) : Nat) : Int) ≤
            (cnt count (S.root + cu.toNat) : Int) * ((2 ^ (16 - S.root - cu.toNat) : Nat) : Int) :=
          Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
        rw [hw]
        have : ((cnt count (S.root + cu.toNat) * 2 ^ (16 - S.root - cu.toNat) : Nat) : Int) =
            (cnt count (S.root + cu.toNat) : Int) * ((2 ^ (16 - S.root - cu.toNat) : Nat) : Int) := by
          push_cast; rfl
        omega
      · rw [ite_eq_right hz, Wp.bind_iff]
        rw [Int32.le_iff_toInt_le, e1] at hz
        have : (0 : Int32).toInt = 0 := rfl
        rw [this] at hz
        rw [e1, chkI32_ok (by omega) (by omega), Wp.pure_iff, Wp.pure_iff]
        have one : (1 : UInt32).toNat = 1 := rfl
        have hcu1 : (cu + 1).toNat = cu.toNat + 1 := by rw [u32_add (by omega), one]
        refine ⟨2 * (S.mx - S.root - (cu.toNat + 1)) + 1, by omega, rfl, by rw [hcu1]; omega,
          by rw [hcu1]; omega, fun _ => ⟨?_, ?_, by rw [hcu1]⟩, fun e => by simp at e⟩
        · rw [hcu1, i32_ok (by omega) (by omega)]
          rw [show S.root + (cu.toNat + 1) - 1 = S.root + cu.toNat by omega, hw, hB]
          rw [hB] at hinv
          push_cast at hinv ⊢
          have : (lf.toInt - (cnt count (S.root + cu.toNat) : Int)) * 2 * (2 : Int) ^ (16 - S.root - (cu.toNat + 1)) =
              lf.toInt * (2 * (2 : Int) ^ (16 - S.root - (cu.toNat + 1))) -
              (cnt count (S.root + cu.toNat) : Int) * (2 * (2 : Int) ^ (16 - S.root - (cu.toNat + 1))) := by
            rw [Int.sub_mul, Int.sub_mul, Int.mul_assoc, Int.mul_assoc]
          rw [this]
          omega
        · rw [i32_ok (by omega) (by omega)]; omega
    · -- exit
      refine ⟨trivial, hc1, hc2, ?_⟩
      cases done with
      | true => exact Or.inr (hd rfl).1
      | false =>
        left
        simp only [Bool.not_false, Bool.true_and, decide_eq_false_iff_not, UInt32.lt_iff_toNat_lt, hmax,
          Nat.not_lt] at hc
        rw [u32_add (by omega), hdrop] at hc
        omega
  · dsimp only
    rw [hleft, hcurr]
    have hz : wsum (cnt count) (S.root + (len - S.root) - 1) = 0 :=
      wsum_eq_zero (fun L h1 h2 => hbelow L h1 (by omega))
    rw [hz, Int.natCast_zero, Int.add_zero, ← Int.natCast_mul, ← Nat.pow_add]
    congr 2
    omega
  · dsimp only
    rw [hleft]
    have := Nat.two_pow_pos (len - S.root)
    omega

theorem diff_codes {h : Heap} {b : Nat} {s : InflateState} (hl : LiveSt h b s) {C : Array Code}
    {W : Array UInt16} {o1 o2 : Nat} (h1 : o1 ≤ C.size) (h2 : o2 ≤ C.size) (h3 : o1 < 2 ^ 63) (h4 : o2 < 2 ^ 63) :
    Ptr.diff (.ref (CodeRef.codes b) o1) (.ref (CodeRef.codes b) o2) (setCW h b s C W) =
      .ok (Int64.ofInt ((o1 : Int) - (o2 : Int)), setCW h b s C W) := by
  have h5 : -(2 ^ 63 : Int) ≤ (o1 : Int) - (o2 : Int) ∧ (o1 : Int) - (o2 : Int) < 2 ^ 63 := by omega
  have h6 : o1 ≤ C.size ∧ o2 ≤ C.size := ⟨h1, h2⟩
  have hg := get_codes hl C W
  unfold Ptr.diff
  simp only [eq_self, ite_true]
  rw [hg]
  simp only [h6, h5, and_self, ite_true]

theorem Geo.next_used {S : Setup} {t : TL} {c : Nat → Nat} {K len : Nat} {inb : Bool} (hS : S.OK)
    (hg : Geo S t c K len inb) :
    ∃ nx, t.next = .ref (.codes S.b) (S.off + nx) ∧ nx + 2 ^ t.curr.toNat = t.used.toNat ∧
      2 ^ S.root ≤ t.used.toNat ∧ (t.drop = 0 ∨ t.drop.toNat = S.root) ∧ t.curr.toNat ≤ 15 := by
  rcases hg with ⟨h1, h2, h3, h4, -, -⟩ | ⟨h1, -, -, h4, nx, P, h5, h6, h7, -⟩
  · refine ⟨0, by simpa using h3, by rw [h2, h4]; omega, by rw [h4]; exact Nat.le_refl _, Or.inl h1,
      by have := hS.rootmx; have := hS.mx15; omega⟩
  · exact ⟨nx, h5, h7, Nat.le_trans h6 (by rw [← h7]; exact Nat.le_add_right _ _), Or.inr h1, by omega⟩

/-- After the counts and `len` are updated: keep the table, or open a sub-table. -/
theorem tblSub_wp {S : Setup} (hS : S.OK) {t : TL} {here : Code} {min : UInt32} {rhuff : UInt16}
    {huff sym : UInt32} {count : Array UInt16} {len : UInt32} {C : Array Code} {K : Nat}
    {maxv rootv mask : UInt32} (hmax : maxv.toNat = S.mx) (hroot : rootv.toNat = S.root)
    (hmask : mask.toNat = 2 ^ S.root - 1)
    (hst : St S { t with len, sym, min, rhuff, huff, here, count } C K false)
    (hmin : min.toNat = 2 ^ t.curr.toNat) :
    Wp (tblSub S.type (.ref (.codes S.b) S.off) maxv rootv mask t here min rhuff huff sym count len)
      (setCW S.h0 S.b S.s C S.W)
      (fun t' h' => (MI S t' h' ∧ t'.sym = sym) ∨ (∃ C', h' = setCW S.h0 S.b S.s C' S.W ∧ Fin1 S t' C')) := by
  have hl := hS.live
  have hK := hst.K_lt hS
  have hlen1 := hst.len_lo
  have hlen2 := hst.len_hi
  dsimp only at hK hlen1 hlen2
  have hmx := hS.mx15
  have hr1 := hS.root1
  have hrmx := hS.rootmx
  have hcs := hst.count_size
  have hbelow := hst.below
  dsimp only at hcs hbelow
  unfold tblSub
  by_cases hc : S.root < len.toNat ∧ (huff &&& mask) ≠ t.low
  · have hc' : (decide (len > rootv) && huff &&& mask != t.low) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, UInt32.lt_iff_toNat_lt, hroot]
      exact hc
    rw [ite_eq_left hc']
    refine Wp.have_ ?_
    obtain ⟨nxo, hnext, hnxo, hur, hdr, hcu15⟩ := hst.geo.next_used hS
    dsimp only at hnext hnxo hur hdr hcu15
    have hdrop' : (if (t.drop == 0) = true then rootv else t.drop).toNat = S.root := by
      rcases hdr with e | e
      · rw [e]; simp [hroot]
      · by_cases e0 : t.drop = 0
        · rw [e0]; simp [hroot]
        · have : (t.drop == 0) = false := by simpa using e0
          rw [this]; simp [e]
    have hub := hst.used_bnd
    have hcsize := hst.csize
    dsimp only at hub hcsize
    have hbs := hS.bnd_size
    have hmi : Int.ofNat min.toNat = ((2 ^ t.curr.toNat : Nat) : Int) := by rw [hmin]; rfl
    rw [Wp.bind_iff, hnext, hmi]
    refine Wp.of_eq (add_ok (get_codes hl C S.W) (by omega) (by omega) (by omega)) ?_
    refine Wp.have_ ?_
    have hcur0 : (len - if (t.drop == 0) = true then rootv else t.drop).toNat = len.toNat - S.root := by
      rw [u32_sub (by omega), hdrop']
    rw [Wp.bind_iff, shl32_ok (by rw [UInt32.lt_iff_toNat_lt, hcur0]; show _ < 32; omega), Wp.pure_iff,
      Wp.bind_iff]
    have hsh := u32_shl_one (k := len - if (t.drop == 0) = true then rootv else t.drop) (by rw [hcur0]; omega)
    rw [hcur0] at hsh
    have hp15 : 2 ^ (len.toNat - S.root) ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) (by omega)
    rw [hsh, chkI32_ok (by omega) (by omega), Wp.pure_iff, Wp.bind_iff]
    refine Wp.mono (curr_loop_wp hS hcs (len := len.toNat) hc.1 hlen2 (fun L h1 h2 => hbelow L h1 h2) _ maxv
      hdrop' hmax _ hcur0 _ (i32_ok (by omega) (by omega)) _) ?_
    rintro ⟨cu, lf, dn⟩ h1 ⟨rfl, hcu1, hcu2, hsub⟩
    dsimp only at hcu1 hcu2 hsub ⊢
    have hcu15 : cu.toNat < 32 := by omega
    rw [Wp.bind_iff, shl32_ok (by rw [UInt32.lt_iff_toNat_lt]; exact hcu15), Wp.pure_iff]
    have hsh2 := u32_shl_one hcu15
    have hp2 : 2 ^ cu.toNat ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) (by omega)
    have hbl := hS.bnd_lt
    have hused : (t.used + (1 : UInt32) <<< cu).toNat = t.used.toNat + 2 ^ cu.toNat := by
      rw [u32_add (by omega), hsh2]
    have hchk : ((S.type == LENS && decide (t.used + (1 : UInt32) <<< cu > ENOUGH_LENS) ||
        S.type == DISTS && decide (t.used + (1 : UInt32) <<< cu > ENOUGH_DISTS)) = true) ↔
        S.bnd < t.used.toNat + 2 ^ cu.toNat := by
      rcases hS.kind with ⟨-, hmr, -⟩ | ⟨hty, hb, -⟩ | ⟨hty, hb, -⟩
      · omega
      · rw [hty, hb]
        simp only [show (LENS == LENS) = true from rfl, show (LENS == DISTS) = false from rfl, Bool.true_and,
          Bool.false_and, Bool.or_false, decide_eq_true_eq, gt_iff_lt, UInt32.lt_iff_toNat_lt, hused]
        rfl
      · rw [hty, hb]
        simp only [show (DISTS == LENS) = false from rfl, show (DISTS == DISTS) = true from rfl, Bool.true_and,
          Bool.false_and, Bool.false_or, decide_eq_true_eq, gt_iff_lt, UInt32.lt_iff_toNat_lt, hused]
        rfl
    have hframe := hst.frame
    dsimp only at hframe
    by_cases hov : S.bnd < t.used.toNat + 2 ^ cu.toNat
    · rw [ite_eq_left (hchk.2 hov), Wp.pure_iff]
      refine Or.inr ⟨C, rfl, rfl, hcsize, fun i hi => hframe i (fun x => hi ⟨x.1, by omega⟩)⟩
    · rw [ite_eq_right (fun x => hov (hchk.1 x))]
      have hhuff := hst.huff
      dsimp only at hhuff
      have hr16 : S.root ≤ 16 := by omega
      have hKl : K < 2 ^ 16 := by have := Nat.two_pow_pos (16 - len.toNat); omega
      have hlow : (huff &&& mask).toNat = rev S.root (K / 2 ^ (16 - S.root)) := by
        rw [u32_and_mask hmask, hhuff, rev16_mod hr16]
      have hlowlt : (huff &&& mask).toNat < 2 ^ S.root := by rw [hlow]; exact rev_lt _ _
      have hcl := hS.codes_lt
      have hi : S.off + (huff &&& mask).toNat < C.size := by omega
      have hio : Int.ofNat (huff &&& mask).toNat = ((huff &&& mask).toNat : Int) := rfl
      rw [Wp.bind_iff, hio]
      refine Wp.of_eq (add_ok (get_codes hl C S.W) (by omega) (by omega) (by omega)) ?_
      rw [show ((S.off : Int) + ((huff &&& mask).toNat : Int)).toNat = S.off + (huff &&& mask).toNat by omega]
      rw [Wp.bind_iff]
      refine Wp.of_eq (load_ok (get_codes hl C S.W) hi) ?_
      rw [Wp.bind_iff]
      refine Wp.of_eq (store_codes hl hi _) ?_
      rw [Wp.bind_iff]
      refine Wp.of_eq (load_ok (get_codes hl _ S.W) (by simpa using hi)) ?_
      rw [Wp.bind_iff]
      refine Wp.of_eq (store_codes hl (by simpa using hi) _) ?_
      have hno : (((S.off + nxo : Nat) : Int) + ((2 ^ t.curr.toNat : Nat) : Int)).toNat = S.off + t.used.toNat := by
        omega
      rw [Wp.bind_iff, hno]
      refine Wp.of_eq (diff_codes hl (by simp; omega) (by simp; omega) (by omega) (by omega)) ?_
      rw [Wp.bind_iff]
      refine Wp.of_eq (load_ok (get_codes hl _ S.W) (by simpa using hi)) ?_
      rw [Wp.bind_iff]
      refine Wp.of_eq (store_codes hl (by simpa using hi) _) ?_
      rw [Wp.pure_iff]
      left
      refine ⟨⟨_, K, rfl, ?_⟩, rfl⟩
      have hus : (t.used + (1 : UInt32) <<< cu).toNat = t.used.toNat + 2 ^ cu.toNat := hused
      refine { hst with
        csize := by simp [hcsize]
        frame := fun j hj => ?_
        used_bnd := by dsimp only; rw [hus]; omega
        geo := Or.inr ⟨hdrop', hc.1, by dsimp only; omega, by dsimp only; omega, t.used.toNat, K / 2 ^ (16 - S.root), rfl, hur,
          by dsimp only; rw [hus], blk_lt hKl hr16, hlow, fun _ => ?_, fun _ => rfl⟩ }
      · dsimp only at hj
        rw [hus] at hj
        have hne : S.off + (huff &&& mask).toNat ≠ j := fun e => hj ⟨by omega, by omega⟩
        simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, hne, ite_false]
        exact hframe j (fun x => hj ⟨x.1, by omega⟩)
      · rcases hsub with h | h
        · exact Or.inl h
        · refine Or.inr ?_
          dsimp only
          have := Nat.div_mul_le_self K (2 ^ (16 - S.root))
          rw [Nat.add_mul, Nat.one_mul]
          omega
  · have hc' : ¬ (decide (len > rootv) && huff &&& mask != t.low) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, UInt32.lt_iff_toNat_lt, hroot]
      exact hc
    rw [ite_eq_right hc', Wp.pure_iff]
    exact Or.inl ⟨⟨C, K, rfl, St.keep hS hst mask hmask hc⟩, rfl⟩

end ZlibNgF.Proof.Inftrees
