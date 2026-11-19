import ZlibNgF.Proof.«infback.c.steps»

/-!
# `inflateBack()`: the mode `TYPE` (`ZlibNgF`)

`TYPE` ends the call after the last block (`DONE`), or reads the three header bits of the next block and selects
`STORED`, the fixed tables with `LEN`, `TABLE`, or `BAD`. The prefix property of the fixed tables (`Rep`) is checked by
evaluation.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InfbackLoop
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Infback ZlibNg.InflateP
open ZlibNgF.Proof.InflateX
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.mono Sat.of_eq)
open ZlibNgF.Proof.InfbackPull
open ZlibNgF.Proof.InflateLoop (withS bits_ok dropbits_ok bytebits_ok bytebits_le strIdx fixF fixedtables_eq
  lenfix_table distfix_table)
open ZlibNgF.Proof.InflateTab (CodeTable linkTest)

/-! ## The prefix property by evaluation -/

/-- The live code bits (`1000` for an entry that is not live) and the code bits of the entries. -/
def cbl (a : List Code) : List (Nat × Nat) :=
  a.map fun e => (if decide (Live e) then (CODE_BITS e).toNat else 1000, (CODE_BITS e).toNat)

/-- `Lvl a 0 k` by evaluation on `cbl a`: for every live index `x'` with `L` code bits, the indices with the same low
`L` bits. -/
def chk (c : List (Nat × Nat)) (k : Nat) : Bool :=
  (List.range (2 ^ k)).all fun x' =>
    (c[x']!).1 == 1000 || decide ((c[x']!).1 ≤ k) &&
      (List.range (2 ^ (k - (c[x']!).1))).all fun y => (c[x' % 2 ^ (c[x']!).1 + y * 2 ^ (c[x']!).1]!).2 == (c[x']!).1

theorem cbl_get (a : Array Code) (j : Nat) (hj : j < a.size) :
    (cbl a.toList)[j]! = (if decide (Live a[j]!) then (CODE_BITS a[j]!).toNat else 1000, (CODE_BITS a[j]!).toNat) := by
  simp [cbl, hj]

theorem cb_lt (e : Code) : (CODE_BITS e).toNat < 256 := by
  unfold CODE_BITS
  split
  · rw [UInt8.toNat_toUInt32]; exact UInt8.toNat_lt _
  · rw [UInt8.toNat_toUInt32]; exact UInt8.toNat_lt _

theorem chk_ok {a : Array Code} {k : Nat} (h : chk (cbl a.toList) k = true) (hs : 2 ^ k ≤ a.size) : Lvl a 0 k := by
  intro x x' hx hx' hv
  simp only [Nat.zero_add] at hv ⊢
  have h1 := List.all_eq_true.mp h x' (List.mem_range.mpr hx')
  rw [cbl_get a x' (by omega)] at h1
  simp only [hv, decide_true, ↓reduceIte, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.mem_range] at h1
  have h256 := cb_lt a[x']!
  obtain ⟨hL, hy⟩ := h1.resolve_left (by omega)
  refine ⟨hL, fun hm => ?_⟩
  generalize hLd : (CODE_BITS a[x']!).toNat = L at hL hy hm h256
  have hp : 0 < 2 ^ L := Nat.two_pow_pos L
  have hdec : x = x % 2 ^ L + x / 2 ^ L * 2 ^ L := by
    have := Nat.mod_add_div x (2 ^ L); rw [Nat.mul_comm] at this; omega
  have hlt : x / 2 ^ L < 2 ^ (k - L) := by
    rw [Nat.div_lt_iff_lt_mul hp, ← Nat.pow_add, Nat.sub_add_cancel hL]; exact hx
  have := hy (x / 2 ^ L) hlt
  rw [← hm, ← hdec, cbl_get a x (by omega)] at this
  apply UInt32.toNat_inj.mp
  rw [hLd]
  exact this

open ZlibNgF.Proof.InflateLoop (tabB) in
theorem noLink_of_tabB {a : Array Code} {m : Nat} {dist : Bool} (h : tabB a m dist = true) (j : Nat)
    (hj : j < a.size) : linkTest dist a[j]! = false := by
  have := List.all_eq_true.mp h j (List.mem_range.mpr hj)
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
  exact this.2

theorem lenfix_chk : chk (cbl lenfix.toList) 9 = true := by decide +kernel
theorem distfix_chk : chk (cbl distfix.toList) 5 = true := by decide +kernel

theorem lenfix_rep : Rep lenfix 0 9 false := by
  refine ⟨chk_ok lenfix_chk (by rw [ZlibNgF.Proof.InflateLoop.lenfix_size]; decide), fun j hj hl => ?_⟩
  rw [Nat.zero_add, noLink_of_tabB ZlibNgF.Proof.InflateLoop.lenfix_tabB j
    (by rw [ZlibNgF.Proof.InflateLoop.lenfix_size]; exact hj)] at hl
  cases hl

theorem distfix_rep : Rep distfix 0 5 true := by
  refine ⟨chk_ok distfix_chk (by rw [ZlibNgF.Proof.InflateLoop.distfix_size]; decide), fun j hj hl => ?_⟩
  rw [Nat.zero_add, noLink_of_tabB ZlibNgF.Proof.InflateLoop.distfix_tabB j
    (by rw [ZlibNgF.Proof.InflateLoop.distfix_size]; exact hj)] at hl
  cases hl

theorem lenfix_rtab (b : Nat) (codes : Array Code) :
    RTab b codes (.val (.ref .lenfix 0)) 9 28 false :=
  Or.inr (Or.inl ⟨rfl, ⟨512, lenfix_table⟩, lenfix_rep⟩)

theorem distfix_rtab (b : Nat) (codes : Array Code) :
    RTab b codes (.val (.ref .distfix 0)) 5 28 true :=
  Or.inr (Or.inr ⟨rfl, ⟨32, distfix_table⟩, distfix_rep⟩)

/-! ## Small facts -/

theorem u8_sub {a : UInt8} {k : Nat} (h : k ≤ a.toNat) (hk : k < 256) :
    (a - UInt8.ofNat k).toNat = a.toNat - k := by
  have hk' : (UInt8.ofNat k).toNat = k := by simp; omega
  rw [UInt8.toNat_sub_of_le _ _ (by rw [UInt8.le_iff_toNat_le, hk']; exact h), hk']

theorem rank_TYPE : rank TYPE = 3 := by decide
theorem rank_DONE : rank DONE = 0 := by decide

theorem rank_le (m : UInt32) : rank m ≤ 5 := by
  unfold rank; repeat' (first | decide | split)

/-- The mode clauses of a mode outside `LEN` and `MATCH`. -/
theorem BModeOK.quiet (b : Nat) (S : InflateState) (h1 : S.mode ≠ LEN) (h2 : S.mode ≠ MATCH) : BModeOK b S :=
  ⟨fun h => by rcases h with h | h <;> contradiction, fun h => absurd h h2⟩

/-- The leave outcome of a `NEEDBITS` / `PULLBYTE` that ran out of input. -/
theorem leave_of_pull {E : BEnv} {l l' : IL} {H H' : Heap} {t t' : Nat} {z : ZStream} {S : InflateState}
    (bm : BM E l H t z S) {q : BPtr} (hk : BackKeep H H' E.i E.b E.w) (hI : E.I H' q 0 t') (hp : Pb l l')
    (h0 : l'.have_ = 0) : BLv E l' H' := by
  refine ⟨t', z, S, bm.sh.keep hk, ⟨q, 0, hI, by rw [h0]; exact Nat.le_refl _, fun h => absurd h0 h⟩, ?_, ?_⟩
  · rw [hp]; exact bm.put
  · rw [hp]; exact bm.left

/-! ## `TYPE` -/

theorem run_TYPE (E : BEnv) : ModeRun E back_TYPE (fun S => S.mode = TYPE) := by
  intro cb l H t z S bl hm m hμ
  have hb8 : l.bits.toNat < 8 := by
    rcases bl.bits with e | e
    · rw [hm] at e; exact absurd e (by decide)
    · exact e
  have hμ' : 32 * (8 * (l.have_.toNat + t) + l.bits.toNat) + 3 ≤ m := by
    unfold μ at hμ; rw [hm, rank_TYPE] at hμ; exact hμ
  unfold back_TYPE
  refine SatX.bind (liftEq (bl.sh.rdS (·.last)) ?_)
  dsimp (config := { zeta := false }) only
  split
  · refine SatX.bind (bytebits_ok ?_)
    have hbb := bytebits_le l.bits
    obtain ⟨e1, bm1⟩ := (bl.toBM.locals (l' := { l with
      hold := l.hold >>> (l.bits &&& 7).toUInt32.toUInt64
      bits := l.bits - (l.bits &&& 7) }) rfl rfl rfl rfl).setMode cb DONE
    refine SatX.bind (SatX.lift (Sat.of_eq e1 ?_))
    refine SatX.pure ⟨t, z, _, ⟨bm1, Or.inr (by dsimp only; omega),
      BModeOK.quiet _ { S with mode := DONE } (by show DONE ≠ LEN; decide)
        (by show DONE ≠ MATCH; decide)⟩, ?_⟩
    unfold μ; dsimp only; rw [rank_DONE]
    omega
  · refine SatX.bind (needbits_ok cb E.c rfl rfl bl.inB 3 (by decide) ?_ ?_)
    · intro l' H' t' q hk hI hp h0 _ _
      exact leave_of_pull bl.toBM hk hI hp h0
    intro l1 H1 t1 hk hin1 hmeas h3 hb1 hp1 _
    have h3' : 3 ≤ l1.bits.toNat := h3
    have hb1' : l1.bits.toNat ≤ 10 := by
      have : max l.bits.toNat ((3 : UInt32).toNat + 7) ≤ 10 := Nat.max_le.mpr ⟨by omega, by decide⟩
      omega
    have bm1 : BM E l1 H1 t1 z S := by
      refine ⟨bl.sh.keep hk, hin1, ?_, by rw [hp1]; exact bl.put, by rw [hp1]; exact bl.left, bl.whave⟩
      have := bl.tot
      omega
    refine SatX.bind (bits_ok 1 (by decide) ?_)
    dsimp (config := { zeta := false }) only
    refine SatX.bind (SatX.lift (Sat.of_eq (bm1.sh.wrS _) ?_))
    have bm2 := bm1.wS cb (S' := { S with last := (l1.hold &&& ((1 : UInt32) <<< 1 - 1).toUInt64).toUInt32.toInt32 })
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    refine SatX.bind (dropbits_ok 1 (by decide) ?_)
    have e1 : (l1.bits - (1 : UInt32).toUInt8).toNat = l1.bits.toNat - 1 := u8_sub (k := 1) (by omega) (by decide)
    have bm3 := bm2.locals (l' := { l1 with
      hold := l1.hold >>> (1 : UInt32).toUInt64
      bits := l1.bits - (1 : UInt32).toUInt8 }) rfl rfl rfl rfl
    generalize hl2 : ({ l1 with
      hold := l1.hold >>> (1 : UInt32).toUInt64
      bits := l1.bits - (1 : UInt32).toUInt8 } : IL) = l2 at bm3 ⊢
    have hb2 : l2.bits.toNat = l1.bits.toNat - 1 := by rw [← hl2]; exact e1
    have hh2 : l2.have_ = l1.have_ := by rw [← hl2]
    generalize (withS H1 E.b _) = H2 at bm3
    generalize ({ S with last := _ } : InflateState) = S2 at bm3
    refine SatX.bind (bits_ok 2 (by decide) ?_)
    dsimp (config := { zeta := false }) only
    have fin : ∀ H' z' S', BM E l2 H' t1 z' S' → BModeOK E.b S' → SatX H' l2 (DROPBITS 2) (Post E m) := by
      intro H' z' S' bm' mo'
      have e2 : (l2.bits - (2 : UInt32).toUInt8).toNat = l2.bits.toNat - 2 := u8_sub (k := 2) (by omega) (by decide)
      refine dropbits_ok 2 (by decide) ⟨t1, z', S', ⟨bm'.locals rfl rfl rfl rfl, Or.inr (by dsimp only; omega), mo'⟩,
        ?_⟩
      have := rank_le S'.mode
      unfold μ; dsimp only; rw [e2, hh2]; omega
    split
    · obtain ⟨e3, bm4⟩ := bm3.setMode cb STORED
      refine SatX.bind (SatX.lift (Sat.of_eq e3 ?_))
      exact fin _ _ _ bm4 (BModeOK.quiet _ { S2 with mode := STORED } (by show STORED ≠ LEN; decide)
        (by show STORED ≠ MATCH; decide))
    split
    · refine SatX.bind (SatX.lift (Sat.of_eq ((fixedtables_eq bm3.sh.istate).trans (bm3.sh.wrS fixF)) ?_))
      have bm4 := bm3.wS cb (S' := fixF S2) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      obtain ⟨e4, bm5⟩ := bm4.setMode cb LEN
      refine SatX.bind (SatX.lift (Sat.of_eq e4 ?_))
      exact fin _ _ _ bm5 ⟨fun _ => ⟨lenfix_rtab _ _, distfix_rtab _ _⟩,
        fun e => absurd (show LEN = MATCH from e) (by decide)⟩
    split
    · obtain ⟨e3, bm4⟩ := bm3.setMode cb TABLE
      refine SatX.bind (SatX.lift (Sat.of_eq e3 ?_))
      exact fin _ _ _ bm4 (BModeOK.quiet _ { S2 with mode := TABLE } (by show TABLE ≠ LEN; decide)
        (by show TABLE ≠ MATCH; decide))
    · obtain ⟨H4, z4, e3, bm4⟩ := bm3.setBad cb "invalid block type" (strIdx 16 (by decide) (by decide) (by decide))
      refine SatX.bind (SatX.lift (Sat.of_eq e3 ?_))
      exact fin _ _ _ bm4 (BModeOK.quiet _ { S2 with mode := BAD } (by show BAD ≠ LEN; decide)
        (by show BAD ≠ MATCH; decide))

end ZlibNgF.Proof.InfbackLoop
