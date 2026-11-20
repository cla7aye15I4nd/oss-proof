import ZlibNgF.Proof.«match_tpl.h.top»
import ZlibNgF.ZlibNg.«deflate_medium_tpl.h»

/-!
# `find_best_match` of `deflate_medium` (`deflate_medium_tpl.h:43-82`, `ZlibNgF`)

`find_best_match` calls `longest_match_c` only for `0 < strstart - hash_head <= max_dist` (`max_dist = MAX_DIST(s)`), so
the candidate is at or above `limit_base`, and it keeps a match only when `match_start < strstart` and the length is at
least `WANT_MIN_MATCH`. With the `B = 65536` theorem of `longest_match_c` (nothing assumed of the hash chains) a kept
match has `match_start < strstart <= match_start + MAX_DIST`, length `4..258` and at most `lookahead`.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.MediumFind
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNg.Compare256 ZlibNg.DeflateMedium ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.LongestMatch
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)

/-- The match that `find_best_match` returns at `strstart = ss` (`lookahead = la`, distance bound `md`): no match
(`match_length = 1`), or a match of length `4..258`, at most `la`, starting before `ss` and at most `md` back. -/
def FindOk (ss la md : Nat) (m : Match) : Prop :=
  m.strstart.toNat = ss ∧ ss ≤ m.orgstart.toNat ∧ m.orgstart.toNat + 1 ≤ ss + m.match_length.toNat ∧
    (m.match_length = 1 ∨
      (4 ≤ m.match_length.toNat ∧ m.match_length.toNat ≤ 258 ∧ m.match_length.toNat ≤ la ∧
        m.match_start.toNat < ss ∧ ss ≤ m.match_start.toNat + md))

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8}

theorem find_best_match_ok {wo po ho : Nat} {hh : UInt32} {md : Int32}
    (hw : st.window = .val (.ref (.heap b) wo)) (hpv : st.prev = .val (.ref (.heap b) po))
    (N : LN d wo po ho st) (hh6 : hh.toNat < 65536) (hmd : md.toInt = (MAX_DIST st).toNat) :
    Sat (SH H i z b st d) (find_best_match (some b) hh md)
      (fun m H' => ∃ ms, H' = LH H i z b st d ms ∧ FindOk st.strstart.toNat st.lookahead.toNat (MAX_DIST st).toNat m) := by
  have hst := N.look
  have hw5 := N.w_hi
  have hw1 := N.w_lo
  have hmx : (MAX_DIST st).toNat = st.w_size.toNat - 262 := by
    unfold MAX_DIST MIN_LOOKAHEAD STD_MAX_MATCH STD_MIN_MATCH
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)]; rfl
  unfold find_best_match
  dsimp only
  have hss := ZlibNgF.Proof.DeflateAlloc.u32_toInt32_toInt st.strstart (by omega)
  have hhi := ZlibNgF.Proof.DeflateAlloc.u32_toInt32_toInt hh (by omega)
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  have hck : chkI32 (st.strstart.toInt32.toInt - hh.toInt32.toInt) (SH H i z b st d) =
      .ok (Int32.ofInt ((st.strstart.toNat : Int) - hh.toNat), SH H i z b st d) := by
    unfold chkI32; rw [hss, hhi]; rw [ite_eq_left_iff.mpr (fun h => absurd (by omega) h)]; rfl
  refine Sat.bind (Sat.of_eq hck ?_)
  have hdv : (Int32.ofInt ((st.strstart.toNat : Int) - hh.toNat)).toInt = (st.strstart.toNat : Int) - hh.toNat :=
    Int32.toInt_ofInt_of_le (by omega) (by omega)
  have hok0 : FindOk st.strstart.toNat st.lookahead.toNat (MAX_DIST st).toNat
      { match_start := 0, match_length := 1, strstart := st.strstart, orgstart := st.strstart } :=
    ⟨rfl, Nat.le_refl _, by simp, Or.inl rfl⟩
  split
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hc
    obtain ⟨⟨hc1, hc2⟩, hc3⟩ := hc
    have hc1' := Int32.le_iff_toInt_le.mp hc1
    have hc2' := Int32.lt_iff_toInt_lt.mp hc2
    rw [hdv, hmd] at hc1'
    rw [hdv] at hc2'
    simp only [Int32.toInt_zero] at hc2'
    have hlb : (limitBase st).toNat ≤ hh.toNat := by
      unfold limitBase
      split
      · rename_i hg
        have hg' := UInt32.lt_iff_toNat_lt.mp hg
        rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega))]; omega
      · simp
    refine Sat.bind (Sat.mono (longest_match_c_safe hw hpv N hh6 hlb) ?_)
    rintro len _ ⟨ms, rfl, hpr⟩
    refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
    dsimp only
    have hk1 : FindOk st.strstart.toNat st.lookahead.toNat (MAX_DIST st).toNat
        { match_start := ms, match_length := 1, strstart := st.strstart, orgstart := st.strstart } :=
      ⟨rfl, Nat.le_refl _, by simp, Or.inl rfl⟩
    split
    · exact Sat.pure ⟨ms, rfl, hk1⟩
    rename_i hl4
    have hl4' : 4 ≤ len.toNat := by
      have := UInt32.not_lt.mp hl4; exact UInt32.le_iff_toNat_le.mp this
    split
    · exact Sat.pure ⟨ms, rfl, hk1⟩
    rename_i hms
    have hms' : ms.toNat < st.strstart.toNat := UInt32.lt_iff_toNat_lt.mp (UInt32.not_le.mp hms)
    rcases hpr with hp | ⟨hp1, hp2, ⟨hm1, -⟩⟩
    · omega
    obtain ⟨hlb2, hlb3⟩ := limitBase_le st hw1
    have hsub : (st.strstart - ms).toNat = st.strstart.toNat - ms.toNat :=
      UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega))
    have hk : ∀ o : UInt32, st.strstart.toNat ≤ o.toNat → o.toNat + 1 ≤ st.strstart.toNat + len.toNat →
        FindOk st.strstart.toNat st.lookahead.toNat (MAX_DIST st).toNat
          { match_start := ms, match_length := len, strstart := st.strstart, orgstart := o } :=
      fun o h1 h2 => ⟨rfl, h1, h2, Or.inr ⟨hl4', hp2, hp1, hms', show st.strstart.toNat ≤ ms.toNat + (MAX_DIST st).toNat by omega⟩⟩
    split
    · rename_i hlt
      have hlt' := UInt32.lt_iff_toNat_lt.mp hlt
      rw [hsub] at hlt'
      have e : (st.strstart + (len - (st.strstart - ms))).toNat = st.strstart.toNat + (len.toNat - (st.strstart.toNat - ms.toNat)) := by
        rw [UInt32.toNat_add, UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by rw [hsub]; omega)), hsub]
        exact Nat.mod_eq_of_lt (by omega)
      exact Sat.pure ⟨ms, rfl, hk _ (by rw [e]; omega) (by rw [e]; omega)⟩
    · exact Sat.pure ⟨ms, rfl, hk _ (Nat.le_refl _) (by omega)⟩
  · exact Sat.pure ⟨st.match_start, LH_self.symm, hok0⟩

end

end ZlibNgF.Proof.MediumFind
