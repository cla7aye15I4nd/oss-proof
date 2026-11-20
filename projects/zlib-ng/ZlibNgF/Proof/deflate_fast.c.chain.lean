import ZlibNgF.Proof.«insert_string_p.h.sli»
import ZlibNgF.Proof.«match_tpl.h.top»

/-!
# The hash chains at the match search of `deflate_fast` (`ZlibNgF`)

`deflate_fast` inserts `strstart` (`insert_knuth_val`) and searches from the old head `hash_head`
(`longest_match_c`) when `0 < strstart - hash_head <= MAX_DIST`. At level 2 the chain clauses hold with the limit
`strstart` (`chainLim`): every position of the set `I` is below `strstart`. The insertion of `strstart` writes
`head[h]` and `prev[strstart & w_mask]` only (`insert_knuth_val_V`); a candidate of `I` at or above `limit_base`
(`> strstart - w_size`) and below `strstart` uses another `prev` slot, so `I` is still closed under the chain step on
the new bytes (`prevCh_after_insert`), and the returned head is 0 or in `I` (C2). `longest_match_c_chain` then puts an
accepted `match_start` in `I`: `0 < strstart - match_start <= MAX_DIST`.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.DeflateFastChain
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInit
open ZlibNg.InsertStringP ZlibNgF.Proof.InsertSafe ZlibNgF.Proof.InsertChain ZlibNgF.Proof.InsertGrow
open ZlibNgF.Proof.LongestMatch (PrevCh rd2 limitBase limitBase_le)
open ZlibNgF.Proof.DeflateFacts (posAt)
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNgF.Proof.WinBase (knuth_lt)

/-- The `Pos` read by `posLoad` is `posAt`. -/
theorem rd2_posAt (d : Array UInt8) (o k : Nat) : (rd2 d (o + 2 * k)).toNat = posAt d o k := by
  rw [← pv_toNat]; rfl

/-- `MAX_DIST` in numbers. -/
theorem maxDist_toNat (st : DeflateState) (hw : 512 ≤ st.w_size.toNat) :
    (MAX_DIST st).toNat = st.w_size.toNat - 262 := by
  unfold MAX_DIST MIN_LOOKAHEAD STD_MAX_MATCH STD_MIN_MATCH
  rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)]; rfl

/-- A candidate at or above `limit_base` is inside the window: `strstart < c + w_size`. -/
theorem lb_window {st : DeflateState} (hw : 512 ≤ st.w_size.toNat) {c : Nat} (hc : (limitBase st).toNat ≤ c) :
    st.strstart.toNat < c + st.w_size.toNat := by
  have := (limitBase_le st hw).2
  have := maxDist_toNat st hw
  omega

/-- The chain clauses with `strstart` of `st` give the chain closure of `I` (clause (C3)). -/
theorem prevCh_of_chain {d : Array UInt8} {ho po lim : Nat} {st : DeflateState} {I : Nat → Prop}
    (C : ChainSet d ho po st.w_size.toNat st.strstart.toNat lim I) (hp : ∃ k, st.w_size.toNat = 2 ^ k)
    (hw : 512 ≤ st.w_size.toNat) : PrevCh d po st I := by
  intro c hc hlb
  have hm := wmask_mod hp c
  unfold W_MASK at hm
  rw [hm, rd2_posAt]
  exact C.c3 _ hc (lb_window hw hlb)

/-- Two positions less than `w` apart, the first below the second, have different slots `p % w`. -/
theorem mod_ne {c s w : Nat} (h1 : c < s) (h2 : s < c + w) : c % w ≠ s % w := by
  intro e
  have h0 := Nat.sub_mod_eq_zero_of_mod_eq e.symm
  rw [Nat.mod_eq_of_lt (by omega)] at h0
  omega

/-- After an insertion of `strstart` that changes `prev` only at `strstart & w_mask`, the positions `I` of the chain
clauses with the limit `strstart` are still closed under the chain step. -/
theorem prevCh_after_insert {d d' : Array UInt8} {ho po : Nat} {st : DeflateState} {I : Nat → Prop}
    (C : ChainSet d ho po st.w_size.toNat st.strstart.toNat st.strstart.toNat I)
    (hp : ∃ k, st.w_size.toNat = 2 ^ k) (hw : 512 ≤ st.w_size.toNat)
    (hk : ∀ k, k < st.w_size.toNat → k ≠ st.strstart.toNat % st.w_size.toNat → posAt d' po k = posAt d po k) :
    PrevCh d' po st I := by
  intro c hc hlb
  have hm := wmask_mod hp c
  unfold W_MASK at hm
  rw [hm, rd2_posAt]
  have h1 := (C.c1 _ hc).2
  have h2 := lb_window hw hlb
  rw [hk _ (Nat.mod_lt _ (by omega)) (mod_ne h1 h2)]
  exact C.c3 _ hc h2

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8}

/-- `insert_knuth_val(s, str, val)`, exactly: it returns a `head` entry of the old bytes, and changes no `prev` entry
but `prev[str & w_mask]`. -/
theorem insert_knuth_val_V {wo po ho : Nat} (L : HLay b d.size st wo po ho) (hp : ∃ k, st.w_size.toNat = 2 ^ k)
    (str val : UInt32) :
    Sat (SH H i z b st d) (insert_knuth_val (some b) str val)
      (fun r H' => ∃ d', H' = SH H i z b st d' ∧ d'.size = d.size ∧ (∃ h, h < 65536 ∧ r.toNat = posAt d ho h) ∧
        ∀ k, k < st.w_size.toNat → k ≠ str.toNat % st.w_size.toNat → posAt d' po k = posAt d po k) := by
  have hw := L.w1
  have hph := L.ph
  have hho := L.hd
  have hr : ∃ h, h < 65536 ∧ (pv d ho (UPDATE_HASH_KNUTH val).toNat).toUInt32.toNat =
      posAt d ho h := ⟨_, knuth_lt val, by rw [UInt16.toNat_toUInt32, pv_toNat]⟩
  unfold insert_knuth_val
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  simp only [L.head]
  refine Sat.bind (Sat.pure ?_)
  refine Sat.bind (Sat.of_eq (posLoad_eq _ (by have := knuth_lt val; omega)) ?_)
  split
  · have hmw := Nat.mod_lt str.toNat (show 0 < st.w_size.toNat by omega)
    have hm := wmask_mod hp str
    refine Sat.bind (Sat.of_eq ldDState_SH ?_)
    simp only [L.prev]
    refine Sat.bind (Sat.pure ?_)
    refine Sat.bind (Sat.of_eq (posStore_eq (str &&& W_MASK st).toNat _ (by omega)) ?_)
    refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
    simp only [L.head]
    refine Sat.bind (Sat.pure ?_)
    refine Sat.bind (Sat.of_eq (posStore_eq _ _ (by rw [wr2_size]; have := knuth_lt val; omega)) ?_)
    refine Sat.pure ⟨_, rfl, by rw [wr2_size, wr2_size], hr, fun k hk hne => ?_⟩
    have hs1 : po + 2 * (str &&& W_MASK st).toNat + 1 < d.size := by omega
    have hs2 : ho + 2 * (UPDATE_HASH_KNUTH val).toNat + 1 <
        (wr2 d (po + 2 * (str &&& W_MASK st).toNat) (pv d ho (UPDATE_HASH_KNUTH val).toNat).toUInt32.toUInt16).size := by
      rw [wr2_size]; have := knuth_lt val; omega
    rw [posAt_wr2_other _ hs2 (by omega), posAt_wr2_other _ hs1 (by omega)]
  · exact Sat.pure ⟨d, rfl, rfl, hr, fun _ _ _ => rfl⟩

end

/-- A candidate within `MAX_DIST` of `strstart` is at or above `limit_base`. -/
theorem lb_of_dist {st : DeflateState} (hw : 512 ≤ st.w_size.toNat) {c : Nat}
    (hd : st.strstart.toNat ≤ c + (MAX_DIST st).toNat) : (limitBase st).toNat ≤ c := by
  have hm := maxDist_toNat st hw
  unfold limitBase
  split
  · rename_i hg
    have hg' : (MAX_DIST st).toNat < st.strstart.toNat := UInt32.lt_iff_toNat_lt.mp hg
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; omega)]; omega
  · simp

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState}

/-- The match search of `deflate_fast` (`deflate_fast.c:46-61`) after the insertion of `strstart`: with the chain
clauses of the bytes `d` before the insertion (limit `strstart`), the bytes `d'` after it (only
`prev[strstart & w_mask]` changed), and the returned head `r` with `0 < strstart - r <= MAX_DIST`, `longest_match_c`
returns at most 2, or a match of at most `lookahead` and 258 bytes at a distance `strstart - match_start` in
`1 .. MAX_DIST`. -/
theorem fast_search {wo po ho : Nat} {d d' : Array UInt8} {I : Nat → Prop}
    (C : ChainSet d ho po st.w_size.toNat st.strstart.toNat st.strstart.toNat I)
    (hp : ∃ k, st.w_size.toNat = 2 ^ k) (hw5 : 512 ≤ st.w_size.toNat)
    (hw : st.window = .val (.ref (.heap b) wo)) (hpv : st.prev = .val (.ref (.heap b) po))
    (N : ZlibNgF.Proof.LongestMatch.LN d' wo po ho st)
    (hk : ∀ k, k < st.w_size.toNat → k ≠ st.strstart.toNat % st.w_size.toNat → posAt d' po k = posAt d po k)
    {r : UInt32} (hr : ∃ h, h < 65536 ∧ r.toNat = posAt d ho h) (hr0 : r.toNat ≠ 0)
    (hd : st.strstart.toNat ≤ r.toNat + (MAX_DIST st).toNat) :
    Sat (SH H i z b st d') (ZlibNg.Compare256.longest_match_c (some b) r)
      (fun m H' => ∃ ms, H' = ZlibNgF.Proof.LongestMatch.LH H i z b st d' ms ∧ (m.toNat ≤ 2 ∨
        (m.toNat ≤ st.lookahead.toNat ∧ m.toNat ≤ 258 ∧ ms.toNat < st.strstart.toNat ∧
          st.strstart.toNat ≤ ms.toNat + (MAX_DIST st).toNat))) := by
  obtain ⟨h, hh, hrh⟩ := hr
  have hrI : I r.toNat := by rw [hrh] at hr0 ⊢; exact C.c2 h hh hr0
  have hr65 : r.toNat < 65536 := by rw [hrh]; exact posAt_lt _ _ _
  refine Sat.mono (ZlibNgF.Proof.LongestMatch.longest_match_c_chain hw hpv N (prevCh_after_insert C hp hw5 hk)
    hr65 (lb_of_dist hw5 hd) hrI) ?_
  rintro m _ ⟨ms, rfl, hm⟩
  refine ⟨ms, rfl, ?_⟩
  rcases hm with hm | ⟨a1, a2, a3, a4⟩
  · exact Or.inl hm
  · have := (limitBase_le st hw5).2
    exact Or.inr ⟨a1, a2, (C.c1 _ a4).2, by omega⟩

end

end ZlibNgF.Proof.DeflateFastChain
