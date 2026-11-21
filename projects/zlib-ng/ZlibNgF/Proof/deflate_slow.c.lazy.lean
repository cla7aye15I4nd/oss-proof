import ZlibNgF.Proof.«deflate.c.facts»
import ZlibNgF.Proof.«match_tpl.h.safety»

/-!
# `deflate_slow`: the lazy-match fields (`ZlibNgF`)

Heap-free facts about one trip of `deflate_slow` (`deflate_slow.c:31-152`):

* `ml_cases`: the match length that the trip keeps (`match_len`, after the `match_discard` test and the test of patch
  0016 that `match_start` lies before `strstart`), when it is `STD_MIN_MATCH` or more, is either at most a pending
  `prev_length` (the trip tallies the pending match) or a fresh match of at most `STD_MAX_MATCH` bytes within the
  lookahead, starting at `match_start` with `limit_base <= match_start < strstart`;
* `lazy_step`: `LazyOk` after the two branches that advance `strstart` by one with `prev_length = match_len`.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.SlowLazy
open C ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateFacts

/-- The match length `ml` that a trip keeps, from the pending `prev_length` `pl`, `match_floor` `mf`,
`match_discard` `md`, the `prev_length` `bl = MAX(pl, mf)` that `longest_match` sees (its initial best length
`bl0`), its result `r` with `match_start = ms` (`PR`: at most `bl0`, or within the lookahead `la`, at most 258, from
`lb = limit_base`), and `strstart = ss`. -/
theorem ml_cases (pl mf md bl bl0 r ms ss la lb ml : Nat) (hmf : mf ≤ md)
    (hbl : (pl < mf → bl = mf) ∧ (¬ pl < mf → bl = pl)) (hbl0 : (bl ≠ 0 → bl0 = bl) ∧ (bl = 0 → bl0 = 2))
    (hpr : r ≤ bl0 ∨ (r ≤ la ∧ r ≤ 258 ∧ lb ≤ ms))
    (hml : (r ≤ md → ml = 2) ∧ (¬ r ≤ md → ss ≤ ms → ml = 2) ∧ (¬ r ≤ md → ¬ ss ≤ ms → ml = r)) (h3 : 3 ≤ ml) :
    (3 ≤ pl ∧ ml ≤ pl) ∨ (ml ≤ 258 ∧ ml ≤ la ∧ lb ≤ ms ∧ ms < ss) := by
  obtain ⟨b1, b2⟩ := hbl
  obtain ⟨c1, c2⟩ := hbl0
  obtain ⟨m1, m2, m3⟩ := hml
  by_cases a : r ≤ md
  · have := m1 a; omega
  by_cases c : ss ≤ ms
  · have := m2 a c; omega
  have e1 := m3 a c
  by_cases p : pl < mf
  · have := b1 p
    by_cases z : bl = 0
    · have := c2 z; omega
    · have := c1 z; omega
  · have := b2 p
    by_cases z : bl = 0
    · have := c2 z; omega
    · have := c1 z; omega

/-- `limit_base <= match_start` bounds the distance `strstart - match_start` by `MAX_DIST`. -/
theorem dist_le (st : DeflateState) (ms : Nat) (h : (ZlibNgF.Proof.LongestMatch.limitBase st).toNat ≤ ms)
    (hw : 262 ≤ st.w_size.toNat) : st.strstart.toNat - ms ≤ (MAX_DIST st).toNat := by
  have hML : MIN_LOOKAHEAD.toNat = 262 := by decide
  have hmd : (MAX_DIST st).toNat = st.w_size.toNat - 262 := by
    unfold MAX_DIST
    rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by rw [hML]; exact hw)), hML]
  unfold ZlibNgF.Proof.LongestMatch.limitBase at h
  split at h
  · rename_i hg
    have hg' := UInt32.lt_iff_toNat_lt.mp hg
    rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_of_lt hg)] at h
    omega
  · rename_i hg
    have hg' := UInt32.le_iff_toNat_le.mp (UInt32.not_lt.mp hg)
    simp at h
    omega

/-- `LazyOk` after a trip that leaves `prev_length = match_len` and advances `strstart` (`ss` before) by one and
lowers `lookahead` (`la` before) by one: at the levels of `deflate_slow`, after a `deflate` dispatch
(`last_flush != -2`), with `block_start <= ss`, and a kept match (3 or more) within the lookahead before, at most
258 long, starting at `match_start < ss` within `MAX_DIST`. -/
theorem lazy_step {st : DeflateState} (ss la : Nat) (e_ss : st.strstart.toNat = ss + 1)
    (e_la : st.lookahead.toNat + 1 = la) (hT : TableAt 7 9 st) (hlf : st.last_flush ≠ -2)
    (hbs : st.block_start.toInt ≤ ss)
    (hml : 3 ≤ st.prev_length → st.prev_length.toNat ≤ 258 ∧ st.prev_length.toNat ≤ la ∧
      st.match_start.toNat < ss ∧ ss - st.match_start.toNat ≤ (MAX_DIST st).toNat) :
    LazyOk st := by
  refine ⟨fun h3 => ?_, fun _ => ⟨by omega, by omega⟩, fun hn => absurd hT hn, fun e => absurd e hlf⟩
  obtain ⟨a1, a2, a3, a4⟩ := hml h3
  exact ⟨a1, by omega, by omega, by omega⟩

end ZlibNgF.Proof.SlowLazy
