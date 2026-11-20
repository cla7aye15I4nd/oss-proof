import ZlibNgF.Proof.«inflate.c.type-modes»

/-!
# The modes `STORED`, `COPY_`, `COPY`, `LIT` of `inflate` (`ZlibNgF`)

These modes write the output buffer (`outW` of `EnvOK`: writable bytes of a block other than the state's, a write
range of the call, disjoint from the input) at `put`, which `OutAt` places inside it with `left` bytes of room.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InflateLoop
open C ZlibNgF.Spec ZlibNg.Inflate
open ZlibNgF.Proof.InflateInv (Inv Core view)
open ZlibNgF.Proof.InflateX
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.mono Sat.of_eq St Touch)
open ZlibNgF.Proof.InflateDict (copyFold copyFold_size add_heap)

theorem rank_COPY : rank COPY = 12 := by decide
theorem rank_COPY_ : rank COPY_ = 13 := by decide
theorem rank_STORED : rank STORED = 14 := by decide
theorem rank_LIT : rank LIT = 5 := by decide
theorem rank_LEN : rank LEN = 3 := by decide

/-! ## The output buffer -/

theorem LI.outBytes {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (eo : EnvOK E)
    (li : LI E l H z S) : ∃ data, H.bytes E.bo = some data ∧ E.oo + E.O0.toNat ≤ data.size := by
  obtain ⟨d0, hd0, hs0, hne, -, -⟩ := eo.outW
  obtain ⟨d, hd, hs⟩ := li.sz.1 E.bo hne d0 hd0
  exact ⟨d, hd, by omega⟩

/-- `put` in the output buffer with `left` bytes of room. -/
theorem LI.outPos {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (li : LI E l H z S) :
    ∃ p, l.put = .ref (.heap E.bo) p ∧ E.oo ≤ p ∧ p + l.left.toNat = E.oo + E.O0.toNat := by
  obtain ⟨hle, ob, h1, h2, hput⟩ := li.outAt
  have hle' : l.left.toNat ≤ l.out.toNat := hle
  refine ⟨_, hput, by omega, ?_⟩
  rw [UInt32.toNat_sub_of_le _ _ hle]; omega

/-- `put += c; left -= c` for `c ≤ left`. -/
theorem LI.produce {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (li : LI E l H z S)
    {p : Nat} (hp : l.put = .ref (.heap E.bo) p) (c : UInt32) (hc : c ≤ l.left) (l' : IL)
    (e1 : l'.next = l.next) (e2 : l'.have_ = l.have_) (e3 : l'.put = .ref (.heap E.bo) (p + c.toNat))
    (e4 : l'.out = l.out) (e5 : l'.left = l.left - c) (e6 : l'.bits = l.bits) (e7 : l'.in_ = l.in_ := by rfl)
    (e8 : l'.ret = l.ret := by rfl) :
    LI E l' H z S := by
  obtain ⟨hle, ob, h1, h2, hput⟩ := li.outAt
  have hle' : l.left.toNat ≤ l.out.toNat := hle
  have hc' : c.toNat ≤ l.left.toNat := hc
  have hs : (l.left - c).toNat = l.left.toNat - c.toNat := UInt32.toNat_sub_of_le _ _ hc
  refine ⟨li.inv, li.frame, li.sz, li.hz, li.hb, li.hs, li.head, li.hdr, by rw [e1, e2]; exact li.inAt, ?_,
    by rw [e6]; exact li.bits, by rw [e7]; exact li.inn, by rw [e4]; exact li.outO, by rw [e8]; exact li.retB, li.sacc, li.msgK,
    li.fr.mono e2 fun ⟨a, b, c, d⟩ => ⟨e6 ▸ a, b, c, e8 ▸ d⟩⟩
  rw [e3, e4, e5]
  refine ⟨by rw [UInt32.le_iff_toNat_le, hs]; omega, ob, h1, h2, ?_⟩
  rw [hp] at hput
  injection hput with _ hput
  rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, hs]; omega), hs]
  rw [UInt32.toNat_sub_of_le _ _ hle] at hput
  congr 1; omega

/-! ## `COPY` -/

theorem run_COPY (E : Env) (eo : EnvOK E) : ModeRun E inflate_COPY (·.mode = COPY) := by
  intro l H z S li hm m hμ
  have hμ' : 32 * (8 * l.have_.toNat + l.bits.toNat + l.left.toNat) + 12 ≤ m := by
    unfold μ at hμ; rwa [hm, rank_COPY] at hμ
  unfold inflate_COPY
  refine SatX.bind (SatX.lift_eq (li.rdS (·.length)) ?_)
  dsimp (config := { zeta := false }) only
  split
  · rename_i hlen
    refine SatX.bind (SatX.get ?_)
    dsimp (config := { zeta := false }) only
    extract_lets c1 c2 jp
    have hc2 : c2 ≤ l.have_ ∧ c2 ≤ l.left := by
      simp only [c2, c1]
      constructor <;> split <;> rename_i h1 <;> (try split) <;> (try rename_i h2) <;>
        first
        | exact UInt32.le_refl _
        | exact UInt32.le_of_lt (by assumption)
        | exact UInt32.not_lt.mp (by assumption)
        | (exact UInt32.le_trans (UInt32.not_lt.mp ‹_›) (UInt32.le_of_lt ‹_›))
        | (exact UInt32.le_trans (UInt32.le_of_lt ‹_›) (UInt32.le_of_lt ‹_›))
        | (exact UInt32.le_trans (UInt32.not_lt.mp ‹_›) (UInt32.not_lt.mp ‹_›))
        | (exact UInt32.le_trans (UInt32.le_of_lt ‹_›) (UInt32.not_lt.mp ‹_›))
        | skip
    obtain ⟨hch, hcl⟩ := hc2
    have hc3 : c2 = S.length ∨ c2 = l.have_ ∨ c2 = l.left := by
      simp only [c2, c1]
      by_cases h1 : S.length > l.have_
      · simp only [h1, ↓reduceIte]; by_cases h2 : l.have_ > l.left <;> simp [h2]
      · simp only [h1, ↓reduceIte]; by_cases h2 : S.length > l.left <;> simp [h2]
    clear_value c2 c1
    refine SatX.bind (SatX.modify ?_)
    dsimp (config := { zeta := false }) only
    have li1 : LI E { l with copy := c2 } H z S := li.locals rfl rfl rfl rfl rfl rfl
    split
    · rename_i hz0
      have hc0 : c2 = 0 := by simpa using hz0
      refine SatX.bind (SatX.throw ⟨⟨z, S, li1⟩, ?_⟩)
      rcases hc3 with e | e | e
      · exact absurd (e.symm.trans hc0) (by simpa using hlen)
      · exact Why.have0 (show l.have_ = 0 by rw [← e, hc0])
      · exact Why.full (show l.left = 0 by rw [← e, hc0]) (li.outEq (by rw [hm]; decide))
    rename_i hc0'
    have hc0 : c2 ≠ 0 := by simpa using hc0'
    simp only [jp]
    have hcl' : c2.toNat ≤ l.left.toNat := hcl
    have hch' : c2.toNat ≤ l.have_.toNat := hch
    have hc0n : 0 < c2.toNat := by
      rcases Nat.eq_zero_or_pos c2.toNat with e | e
      · exact absurd (UInt32.toNat_inj.mp (by rw [e]; rfl)) hc0
      · exact e
    have hh : l.have_ ≠ 0 := fun e => by
      rw [e] at hch'; have e0 : (0 : UInt32).toNat = 0 := rfl; omega
    obtain ⟨r, o, d, hnx, hg, hsz⟩ := li.inBytes eo hh
    obtain ⟨p, hput, hp1, hp2⟩ := li.outPos
    obtain ⟨data, hd, hds⟩ := li.outBytes eo
    obtain ⟨-, -, -, hbne, hw, hdj⟩ := eo.outW
    have hov : r = .heap E.bo → p + c2.toNat ≤ o ∨ o + c2.toNat ≤ p := by
      intro er
      obtain ⟨hle, hat⟩ := li.inAt
      have hle' : l.have_.toNat ≤ E.A0.toNat := hle
      rcases hinp : E.inp with _ | ⟨r0, o0⟩
      · rw [hinp, hnx] at hat; cases hat.1
      · rw [hinp] at hat hdj
        rw [hnx] at hat
        injection hat with f1 f2
        subst f1 er
        rw [UInt32.toNat_sub_of_le _ _ hle] at f2
        rcases hdj with hne | hdj | hdj
        · exact absurd rfl hne
        · right; omega
        · left; omega
    rw [hput, hnx]
    refine SatX.bind (SatX.lift (Sat.of_eq (memcpy_heap' hd hg hov (by omega) (by omega)) ?_))
    have li2 := li1.wrBytes (od := p) (n := c2.toNat) (o0 := E.oo) (n0 := E.O0.toNat)
      (a' := copyFold d p o (List.range' 0 c2.toNat) data) hd hbne
      (copyFold_size _ _ _ _ _) (copyFold_out _ _ _ _ _) hw hp1 (by omega)
    obtain ⟨r', o', d', hnx', hg', hsz'⟩ := li2.inBytes eo hh
    rw [show l.next = _ from hnx] at hnx'
    obtain ⟨rfl, rfl⟩ : r = r' ∧ o = o' := by cases hnx'; exact ⟨rfl, rfl⟩
    have hsz'' : o + l.have_.toNat ≤ d'.size := hsz'
    refine SatX.bind (SatX.lift_eq (add_in hg' (by omega)) ?_)
    refine SatX.bind (SatX.lift_eq (add_heap (upd_same _ _ _) (by rw [copyFold_size]; omega)) ?_)
    refine SatX.bind (SatX.modify ?_)
    have li3 := li2.consume hnx c2 hch { l with copy := c2, have_ := l.have_ - c2, next := .ref r (o + c2.toNat) }
      rfl rfl rfl rfl rfl rfl
    have li4 := li3.produce (p := p) hput c2 hcl { l with
      copy := c2
      have_ := l.have_ - c2
      next := .ref r (o + c2.toNat)
      left := l.left - c2
      put := .ref (.heap E.bo) (p + c2.toNat) } rfl rfl rfl rfl rfl rfl
    refine SatX.bind (SatX.lift (Sat.mono (li4.wrS (fun s => { s with length := s.length - c2 })
      (fun _ _ c => { c with }) rfl) ?_))
    intro _ H5 li5
    refine SatX.pure (post_ok li5 ?_)
    unfold μ; dsimp only
    rw [hm, rank_COPY, UInt32.toNat_sub_of_le _ _ hch, UInt32.toNat_sub_of_le _ _ hcl]
    omega
  · refine SatX.bind (SatX.modify ?_)
    have li1 : LI E { l with copy := S.length } H z S := li.locals rfl rfl rfl rfl rfl rfl
    refine SatX.lift (Sat.mono (li1.setQuiet TYPE (by decide) (by decide) (Or.inl (by decide))
      (Or.inl (li.outEq (by rw [hm]; decide)))) ?_)
    intro _ H1 li2
    refine post_ok li2 ?_
    unfold μ; dsimp only; rw [rank_TYPE]; omega

theorem run_COPY_ (E : Env) (hX : ModeRun E inflate_COPY (·.mode = COPY)) :
    ModeRun E inflate_COPY_ (·.mode = COPY_) := by
  intro l H z S li hm m hμ
  have hμ' : 32 * (8 * l.have_.toNat + l.bits.toNat + l.left.toNat) + 13 ≤ m := by
    unfold μ at hμ; rwa [hm, rank_COPY_] at hμ
  unfold inflate_COPY_
  exact fall_ok hX (by decide) (by decide) (Or.inl (by decide)) li (by rw [rank_COPY]; omega)
    (Or.inl (li.outEq (by rw [hm]; decide)))

/-! ## `STORED` -/

theorem run_STORED (E : Env) (eo : EnvOK E) (hX : ModeRun E inflate_COPY_ (·.mode = COPY_)) :
    ModeRun E inflate_STORED (·.mode = STORED) := by
  intro l H z S li hm m hμ
  have hμ' : 32 * (8 * l.have_.toNat + l.bits.toNat + l.left.toNat) + 14 ≤ m := by
    unfold μ at hμ; rwa [hm, rank_STORED] at hμ
  have hb39 : l.bits.toNat ≤ 39 := li.bits
  unfold inflate_STORED
  refine SatX.bind (bytebits_ok ?_)
  have hbb := bytebits_le l.bits
  have li1 := li.setBits (l' := { l with
    hold := l.hold >>> (l.bits &&& 7).toUInt32.toUInt64
    bits := l.bits - (l.bits &&& 7) }) rfl rfl rfl rfl rfl
    (by show l.bits - (l.bits &&& 7) ≤ 39; rw [UInt8.le_iff_toNat_le]; show _ ≤ 39; omega)
  refine needbits_then eo li1 32 (by decide) ?_
  intro l2 li2 h32 hleft hT
  have h32' : 32 ≤ l2.bits.toNat := h32
  have hT' : 8 * l2.have_.toNat + l2.bits.toNat ≤ 8 * l.have_.toNat + l.bits.toNat := by
    have : 8 * l2.have_.toNat + l2.bits.toNat =
      8 * l.have_.toNat + (l.bits - (l.bits &&& 7)).toNat := hT
    omega
  have hleft' : l2.left = l.left := hleft
  refine SatX.bind (SatX.get ?_)
  dsimp only
  split
  · exact bad_ok li2 (by rw [hleft']; omega) "invalid stored block lengths"
      (strIdx 24 (by decide) (by decide) (by decide))
  refine SatX.bind (SatX.lift (Sat.mono (li2.wrS (fun s => { s with length := l2.hold.toUInt16.toUInt32 })
    (fun _ _ c => { c with }) rfl) ?_))
  intro _ H3 li3
  refine SatX.bind (initbits_ok ?_)
  have li4 := li3.setBits (l' := { l2 with hold := 0, bits := 0 }) rfl rfl rfl rfl rfl
    (by show (0 : UInt8) ≤ 39; decide)
  refine SatX.bind (SatX.lift (Sat.mono (li4.setQuiet COPY_ (by decide) (by decide) (Or.inl (by decide))
    (Or.inl (li2.outEq (by rw [hm]; decide)))) ?_))
  intro _ H5 li5
  dsimp only
  split
  · rename_i h
    exact SatX.bind (SatX.throw ⟨⟨_, _, li5⟩, Why.trees (by simpa [Env.c] using h)⟩)
  · refine hX _ _ _ _ li5 rfl m ?_
    have e0 : (0 : UInt8).toNat = 0 := rfl
    unfold μ; dsimp only; rw [rank_COPY_, e0, hleft']; omega

/-! ## `LIT` -/

open ZlibNgF.Proof.InflateInv (ModeOK DecodeMode) in
/-- `state->mode = LEN` from a decoding mode keeps the mode clauses (the tables stay). -/
theorem modeOK_len (b : Nat) (S : InflateState) (hm : ModeOK b (view S).m) (hd : DecodeMode S.mode) :
    ModeOK b (view { S with mode := LEN }).m where
  lenlens := fun e => absurd (show LEN = LENLENS from e) (by decide)
  codelens := fun e => absurd (show LEN = CODELENS from e) (by decide)
  decode := fun _ => hm.decode hd
  extra := fun e => by
    rcases e with e | e
    · exact absurd (show LEN = LENEXT from e) (by decide)
    · exact absurd (show LEN = DISTEXT from e) (by decide)
  offset := fun e => by
    rcases e with e | e
    · exact absurd (show LEN = DISTEXT from e) (by decide)
    · exact absurd (show LEN = MATCH from e) (by decide)

open ZlibNgF.Proof.InflateInv (DecodeMode) in
/-- The decoding modes come before `CHECK`. -/
theorem decodeMode_rank {M : UInt32} (h : DecodeMode M) : 2 < rank M := by
  rcases h with h | h | h | h | h | h | h <;> rw [h] <;> decide

open ZlibNgF.Proof.InflateInv (DecodeMode) in
theorem LI.setLen {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (li : LI E l H z S)
    (hd : DecodeMode S.mode) (hfr : Fr E l S → Fr E l { S with mode := LEN } := by frt) :
    Sat H (setMode (some E.b) LEN) (fun _ H' => LI E l H' z { S with mode := LEN }) :=
  li.wrS (fun s => { s with mode := LEN }) (fun _ _ c => { c with
    mode_lo := by show HEAD ≤ LEN; decide
    mode_hi := by show LEN ≤ SYNC; decide
    modes := modeOK_len _ S c.modes hd }) rfl (Or.inl (li.outEq (decodeMode_rank hd))) hfr

theorem run_LIT (E : Env) (eo : EnvOK E) : ModeRun E inflate_LIT (·.mode = LIT) := by
  intro l H z S li hm m hμ
  have hμ' : 32 * (8 * l.have_.toNat + l.bits.toNat + l.left.toNat) + 5 ≤ m := by
    unfold μ at hμ; rwa [hm, rank_LIT] at hμ
  unfold inflate_LIT
  refine SatX.bind (SatX.get ?_)
  dsimp (config := { zeta := false }) only
  split
  · rename_i h
    exact SatX.bind (SatX.throw ⟨⟨z, S, li⟩, Why.full (by simpa using h) (li.outEq (by rw [hm]; decide))⟩)
  rename_i hl0
  have hl : l.left ≠ 0 := by simpa using hl0
  have hl1 : 1 ≤ l.left.toNat := by
    rcases Nat.eq_zero_or_pos l.left.toNat with e | e
    · exact absurd (UInt32.toNat_inj.mp (by rw [e]; rfl)) hl
    · exact e
  refine SatX.bind (SatX.lift_eq (li.rdS (·.length)) ?_)
  obtain ⟨p, hput, hp1, hp2⟩ := li.outPos
  obtain ⟨data, hd, hds⟩ := li.outBytes eo
  obtain ⟨-, -, -, hbne, hw, -⟩ := eo.outW
  rw [hput]
  refine SatX.bind (SatX.lift (Sat.of_eq (store_heap hd (by omega) S.length.toUInt8) ?_))
  have li2 := li.wrBytes (od := p) (n := 1) (o0 := E.oo) (n0 := E.O0.toNat)
    (a' := data.set! p S.length.toUInt8) hd hbne (by simp)
    (fun j hj => set_get _ _ _ _ (by omega)) hw hp1 (by omega)
  refine SatX.bind (SatX.lift_eq (add_heap (upd_same _ _ _) (by simp; omega)) ?_)
  refine SatX.bind (SatX.modify ?_)
  have hc : (1 : UInt32) ≤ l.left := by rw [UInt32.le_iff_toNat_le]; exact hl1
  have li3 := li2.produce (p := p) hput 1 hc { l with put := .ref (.heap E.bo) (p + 1), left := l.left - 1 }
    rfl rfl rfl rfl rfl rfl
  refine SatX.lift (Sat.mono (li3.setLen (by rw [hm]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))) ?_)
  intro _ H4 li4
  refine post_ok li4 ?_
  unfold μ; dsimp only
  rw [rank_LEN, UInt32.toNat_sub_of_le _ _ hc]
  have : (1 : UInt32).toNat = 1 := rfl
  omega

end ZlibNgF.Proof.InflateLoop
