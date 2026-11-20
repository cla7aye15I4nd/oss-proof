import ZlibNgF.Proof.«match_tpl.h.safety»

/-!
# `short_match_accept` and the offset search of `LONGEST_MATCH` (`match_tpl.h:201-293`, `ZlibNgF`)

An accepted candidate (`len > best_len`, `len <= 258`) writes `match_start = cur_match - match_offset`, which lies in
`[limit_base, B)` (`CurOk`). Then `LONGEST_MATCH` returns, or goes on with `best_len = len`: through
`GOTO_NEXT_CHAIN`, or, in the slow variants, through the offset search, which keeps `chain_length` and raises
`best_len`. Either way the outer loop's measure `lmMu` falls.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.LongestMatch
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNg.Compare256 ZlibNg.InsertStringP ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono sat_cwhile)
open ZlibNgF.Proof.ChunkMem (sat_add sat_memread8 sat_memread4 sat_index8)
open ZlibNgF.Proof.WinBase (knuth_lt roll_lt)

variable {B : Nat}

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8}

theorem wr_ms (ms ms' : UInt32) :
    wrD (some b) (fun s => { s with match_start := ms' }) (LH H i z b st d ms) = .ok ((), LH H i z b st d ms') :=
  wrD_SH _

/-- `offset = best_len >= 8 ? best_len - 7 : 0`. -/
theorem off_le (x : UInt32) : (if x >= 8 then x - 7 else 0 : UInt32).toNat ≤ x.toNat := by
  split
  · rename_i h
    have := UInt32.le_iff_toNat_le.mp h
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp at this ⊢; omega)]; exact Nat.sub_le _ _
  · simp

theorem lmMu_lt {v v' : LMVars} (hc : chainLeft v'.chain_length ≤ chainLeft v.chain_length)
    (hb : v.best_len.toNat < v'.best_len.toNat) (hb' : v'.best_len.toNat ≤ 131072) :
    lmMu (.cont, v') < lmMu (.cont, v) := by
  simp only [lmMu, LMExit.isCont, ↓reduceIte]
  have := Nat.mul_le_mul_right 131072 hc
  omega

/-- The end of the offset search after the head lookup: `pos` is the head entry, `k` the offset it would take, `np`
and `mo` the candidate and offset of the `prev` walk. -/
theorem osb_tail {e : LMEnv} {v : LMVars} {wo po ho bl0 : Nat} (E : LE b wo po ho st e) (N : LN d wo po ho st)
    (V : VI b wo st { v with mbase_end := .ref (.heap b) (wo + v.offset.toNat) }) {ms : UInt32} (hb : BL st B bl0 v.best_len ms) (pos : UInt16) (k np mo : UInt32)
    (hk : k.toNat ≤ 256) (hnp : np.toNat < 65536) (hmo : mo.toNat ≤ 255) (hle : (limitBase st).toNat + mo.toNat ≤ np.toNat) :
    Sat (LH H i z b st d ms)
      (if pos.toUInt32 < np then
        (if pos.toUInt32 ≤ e.limit_base + k then
          (pure (LMExit.ret v.best_len, { v with cur_match := np, match_offset := k }) : M (LMExit × LMVars))
        else do
          let m ← Ptr.add v.mbase_start ↑v.offset.toNat
          pure (LMExit.cont,
            { v with cur_match := pos.toUInt32, match_offset := k, mbase_end := m, limit := e.limit_base + k }))
      else do
        let m ← Ptr.add v.mbase_start ↑v.offset.toNat
        pure (LMExit.cont,
          { v with cur_match := np, match_offset := mo, mbase_end := m, limit := e.limit_base + mo }))
      (fun s H' => LI H i z b st B d wo bl0 s H' ∧
        (s.1.isCont = true → chainLeft s.2.chain_length = chainLeft v.chain_length ∧ s.2.best_len = v.best_len)) := by
  have Vms : v.mbase_start = .ref (.heap b) wo := V.ms
  have Voff : v.offset.toNat ≤ v.best_len.toNat := V.off
  have Vbl : v.best_len.toNat ≤ 65536 := V.bl
  have Vcur : v.cur_match.toNat < 65536 := V.cur
  have Vmo : v.match_offset.toNat ≤ 65536 := V.mo
  have Vlim : v.limit.toNat = (limitBase st).toNat + v.match_offset.toNat := V.lim
  have Vle : v.limit.toNat ≤ v.cur_match.toNat := V.le
  have hst := N.look
  have hbig := N.big
  have hlb := (limitBase_le st N.w_lo).1
  have hlbv : e.limit_base = limitBase st := E.lb
  have hpos := UInt16.toNat_lt pos
  have hoff := Voff
  have hbl := Vbl
  split
  · rename_i hlt
    split
    · exact Sat.pure ⟨⟨ms, rfl, hb.pr⟩, fun h => by simp [LMExit.isCont] at h⟩
    · rename_i hgt
      simp only [UInt32.not_le] at hgt
      have hgt' := UInt32.lt_iff_toNat_lt.mp hgt
      rw [UInt16.toNat_toUInt32, UInt32.toNat_add, hlbv] at hgt'
      have e1 : ((limitBase st).toNat + k.toNat) % 2 ^ 32 = (limitBase st).toNat + k.toNat :=
        Nat.mod_eq_of_lt (by omega)
      rw [e1] at hgt'
      refine Sat.bind (Sat.mono (sat_add' Vms (LH_get ms) (by omega) _ (wo + v.offset.toNat) (by simp)
        (by omega)) ?_)
      rintro _ _ ⟨rfl, rfl⟩
      refine Sat.pure ⟨⟨ms, rfl, ⟨Vms, rfl, hoff, hbl, by simp only [UInt16.toNat_toUInt32]; omega,
        by simp only []; omega, ?_, ?_⟩, hb⟩, fun _ => ⟨rfl, rfl⟩⟩
      · simp only [hlbv, UInt32.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
      · simp only [hlbv, UInt32.toNat_add, UInt16.toNat_toUInt32]; rw [Nat.mod_eq_of_lt (by omega)]; omega
  · refine Sat.bind (Sat.mono (sat_add' Vms (LH_get ms) (by omega) _ (wo + v.offset.toNat) (by simp)
      (by omega)) ?_)
    rintro _ _ ⟨rfl, rfl⟩
    refine Sat.pure ⟨⟨ms, rfl, ⟨Vms, rfl, hoff, hbl, hnp, by simp only []; omega, ?_, ?_⟩, hb⟩,
      fun _ => ⟨rfl, rfl⟩⟩
    · simp only [hlbv, UInt32.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    · simp only [hlbv, UInt32.toNat_add]; rw [Nat.mod_eq_of_lt (by omega)]; omega

/-- The offset search (`match_tpl.h:222-290`), entered with `best_len = len` already stored and the accepted
candidate `cm = cur_match - match_offset` in `[limit_base, B)`. -/
theorem osb_ok {e : LMEnv} {v : LMVars} {wo po ho bl0 : Nat} (E : LE b wo po ho st e) (N : LN d wo po ho st)
    (V : VI b wo st { v with mbase_end := .ref (.heap b) (wo + v.offset.toNat) }) {ms : UInt32} (hb : BL st B bl0 v.best_len ms) (hs : e.slow = true)
    (hlen : 3 < v.best_len.toNat) (h258 : v.best_len.toNat ≤ 258)
    (hcm : (limitBase st).toNat ≤ (v.cur_match - v.match_offset).toNat) :
    Sat (LH H i z b st d ms) (LM.offset_search_block e v v.best_len) (fun s H' => LI H i z b st B d wo bl0 s H' ∧
      (s.1.isCont = true → chainLeft s.2.chain_length = chainLeft v.chain_length ∧ s.2.best_len = v.best_len)) := by
  have Vms : v.mbase_start = .ref (.heap b) wo := V.ms
  have Voff : v.offset.toNat ≤ v.best_len.toNat := V.off
  have Vbl : v.best_len.toNat ≤ 65536 := V.bl
  have Vcur : v.cur_match.toNat < 65536 := V.cur
  have Vmo : v.match_offset.toNat ≤ 65536 := V.mo
  have Vlim : v.limit.toNat = (limitBase st).toNat + v.match_offset.toNat := V.lim
  have Vle : v.limit.toNat ≤ v.cur_match.toNat := V.le
  have hst := N.look
  have hbig := N.big
  have hlb := (limitBase_le st N.w_lo).1
  have hcm65 : (v.cur_match - v.match_offset).toNat < 65536 := by
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; omega)]; omega
  unfold LM.offset_search_block
  dsimp only
  have h3 : STD_MIN_MATCH.toNat = 3 := rfl
  have h4 : WANT_MIN_MATCH.toNat = 4 := rfl
  have hbound : (if e.roll then v.best_len - STD_MIN_MATCH else v.best_len - WANT_MIN_MATCH).toNat ≤ 255 := by
    split
    · rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; omega)]; omega
    · rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; omega)]; omega
  refine Sat.bind (Sat.mono (os_walk_ok E N (v.cur_match - v.match_offset) _ v.best_len hcm65 hbound hcm ms) ?_)
  rintro ⟨i1, np, mo, r⟩ _ ⟨rfl, hnp, hmo, hle, hr⟩
  dsimp only at hnp hmo hle hr ⊢
  cases r with
  | some x =>
    obtain rfl := hr x rfl
    exact Sat.pure ⟨⟨ms, rfl, hb.pr⟩, fun h => by simp [LMExit.isCont] at h⟩
  | none =>
  dsimp only
  have hbl := Vbl
  have hhd := E.head hs
  have hho := N.hd
  have hS := E.scan
  have hk2 : (v.best_len - (STD_MIN_MATCH - 1)).toNat = v.best_len.toNat - 2 := by
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; show 2 ≤ _; omega)]; rfl
  have hk4 : (v.best_len - WANT_MIN_MATCH).toNat = v.best_len.toNat - 4 := by
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; omega)]; rfl
  split
  · refine Sat.bind (Sat.mono (sat_add' hS (LH_get ms) (by omega) _ (wo + st.strstart.toNat + v.best_len.toNat)
      (by simp) (by omega)) ?_)
    rintro _ _ ⟨rfl, rfl⟩
    refine Sat.bind (Sat.mono (sat_add (LH_get ms) (by omega) _ (wo + st.strstart.toNat + v.best_len.toNat - 2)
      (by rw [show (STD_MIN_MATCH - 1).toNat = 2 from rfl]; omega) (by omega)) ?_)
    rintro _ _ ⟨rfl, rfl⟩
    refine Sat.bind (Sat.mono (sat_index8 (LH_get ms) 0 (by omega)) ?_)
    rintro x0 _ rfl
    refine Sat.bind (Sat.mono (sat_index8 (LH_get ms) 1 (by omega)) ?_)
    rintro x1 _ rfl
    refine Sat.bind (Sat.mono (sat_index8 (LH_get ms) 2 (by omega)) ?_)
    rintro x2 _ rfl
    rw [hhd]
    refine Sat.bind (Sat.mono (posLoad_v (LH_get ms) _ (by
      have := roll_lt (update_hash_roll (update_hash_roll 0 x0.toUInt32) x1.toUInt32) x2.toUInt32
      simp only [update_hash_roll] at this ⊢; omega)) ?_)
    rintro pos _ ⟨rfl, -⟩
    exact osb_tail E N V hb pos _ np mo (by rw [hk2]; omega) hnp hmo hle
  · refine Sat.bind (Sat.mono (sat_add' hS (LH_get ms) (by omega) _ (wo + st.strstart.toNat + v.best_len.toNat)
      (by simp) (by omega)) ?_)
    rintro _ _ ⟨rfl, rfl⟩
    refine Sat.bind (Sat.mono (sat_add (LH_get ms) (by omega) _ (wo + st.strstart.toNat + v.best_len.toNat - 4)
      (by rw [h4]; omega) (by omega)) ?_)
    rintro _ _ ⟨rfl, rfl⟩
    refine Sat.bind (Sat.mono (sat_memread4 (LH_get ms) (by omega)) ?_)
    rintro val _ rfl
    rw [hhd]
    refine Sat.bind (Sat.mono (posLoad_v (LH_get ms) _ (by have := knuth_lt val; omega)) ?_)
    rintro pos _ ⟨rfl, -⟩
    exact osb_tail E N V hb pos _ np mo (by rw [hk4]; omega) hnp hmo hle

/-- The block at `short_match_accept` (`match_tpl.h:201-293`) for an accepted candidate with `len > best_len`,
`len <= 258` and `cur_match < B`: it writes `match_start` in `[limit_base, B)`, and returns, or goes on with
`best_len = len` and a smaller measure. -/
theorem accept_ok {e : LMEnv} {v : LMVars} {wo po ho bl0 : Nat} (E : LE b wo po ho st e) (N : LN d wo po ho st)
    (hp : PrevBelow d po st B) (V : VI b wo st v) {ms : UInt32} (hb : BL st B bl0 v.best_len ms) {len : UInt32}
    (hlen : v.best_len < len) (h258 : len.toNat ≤ 258) (hc : v.cur_match.toNat < B) :
    Sat (LH H i z b st d ms) (LM.short_match_accept e v len) (fun s H' => LI H i z b st B d wo bl0 s H' ∧
      (s.1.isCont = true → lmMu s < lmMu (.cont, v))) := by
  have hst := N.look
  have hbig := N.big
  have hlen' := UInt32.lt_iff_toNat_lt.mp hlen
  have hsub := sub_mo V.lim V.le
  have hlim := V.lim
  have hle := V.le
  have hcm : MSOk st B (v.cur_match - v.match_offset) := ⟨by rw [hsub]; omega, by rw [hsub]; omega⟩
  have hbl0 : bl0 ≤ v.best_len.toNat := by rcases hb with h | h <;> omega
  unfold LM.short_match_accept
  dsimp only
  rw [E.hst]
  refine Sat.bind (Sat.of_eq (wr_ms ms (v.cur_match - v.match_offset)) ?_)
  rw [E.lookahead]
  split
  · rename_i hge
    have := UInt32.le_iff_toNat_le.mp hge
    exact Sat.pure ⟨⟨_, rfl, Or.inr ⟨Nat.le_refl _, by omega, hcm⟩⟩, fun h => by simp [LMExit.isCont] at h⟩
  rename_i hlt
  have hlt' : len.toNat < st.lookahead.toNat := by
    have := UInt32.not_le.mp hlt; exact UInt32.lt_iff_toNat_lt.mp this
  split
  · exact Sat.pure ⟨⟨_, rfl, Or.inr ⟨by omega, h258, hcm⟩⟩, fun h => by simp [LMExit.isCont] at h⟩
  have hoff := off_le len
  refine Sat.bind (Sat.mono (sat_add' E.scan (LH_get _) (by omega) _
    (wo + st.strstart.toNat + (if len >= 8 then len - 7 else 0 : UInt32).toNat) (by simp) (by omega)) ?_)
  rintro _ _ ⟨rfl, rfl⟩
  refine Sat.bind (Sat.mono (sat_memread8 (LH_get _) (by omega)) ?_)
  rintro se _ rfl
  have hb2 : BL st B bl0 len (v.cur_match - v.match_offset) := Or.inr ⟨by omega, hlt', h258, hcm⟩
  let v2 : LMVars := { v with best_len := len, offset := if len >= 8 then len - 7 else 0, scan_end := se }
  have V2 : VI b wo st { v2 with mbase_end := .ref (.heap b) (wo + v2.offset.toNat) } :=
    ⟨V.ms, rfl, hoff, by show len.toNat ≤ 65536; omega, V.cur, V.mo, hlim, hle⟩
  have tail : Sat (LH H i z b st d (v.cur_match - v.match_offset)) (do
      let m ← v2.mbase_start.add v2.offset.toNat
      LM.goto_next_chain_outer e { v2 with mbase_end := m }) (fun s H' => LI H i z b st B d wo bl0 s H' ∧
        (s.1.isCont = true → lmMu s < lmMu (.cont, v))) := by
    refine Sat.bind (Sat.mono (sat_add' V.ms (LH_get _) (by omega) _ (wo + v2.offset.toNat) (by simp)
      (by simp only [v2]; omega)) ?_)
    rintro _ _ ⟨rfl, rfl⟩
    refine Sat.mono (goto_outer_ok E N hp V2 hb2) ?_
    rintro s _ ⟨hL, hm⟩
    refine ⟨hL, fun hc' => ?_⟩
    obtain ⟨h1, h2⟩ := hm hc'
    obtain ⟨x, s2⟩ := s
    cases x with
    | cont =>
      have hx : v.best_len.toNat < s2.best_len.toNat := by rw [h2]; show v.best_len.toNat < len.toNat; exact hlen'
      have hy : s2.best_len.toNat ≤ 131072 := by rw [h2]; show len.toNat ≤ 131072; omega
      exact lmMu_lt (v := v) (v' := s2) (Nat.le_of_lt h1) hx hy
    | brk => simp [LMExit.isCont] at hc'
    | ret r => simp [LMExit.isCont] at hc'
  split
  · rename_i hsl
    split
    · rename_i hcond
      refine Sat.mono (osb_ok (v := v2) E N V2 hb2 hsl ?_ h258 ?_) ?_
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
        exact UInt32.lt_iff_toNat_lt.mp hcond.1.2
      · show (limitBase st).toNat ≤ (v.cur_match - v.match_offset).toNat; rw [hsub]; omega
      · rintro s _ ⟨hL, hm⟩
        refine ⟨hL, fun hc' => ?_⟩
        obtain ⟨h1, h2⟩ := hm hc'
        obtain ⟨x, s2⟩ := s
        cases x with
        | cont =>
          have hw : chainLeft s2.chain_length ≤ chainLeft v.chain_length := by rw [h1]; exact Nat.le_refl _
          have hx : v.best_len.toNat < s2.best_len.toNat := by rw [h2]; show v.best_len.toNat < len.toNat; exact hlen'
          have hy : s2.best_len.toNat ≤ 131072 := by rw [h2]; show len.toNat ≤ 131072; omega
          exact lmMu_lt (v := v) (v' := s2) hw hx hy
        | brk => simp [LMExit.isCont] at hc'
        | ret r => simp [LMExit.isCont] at hc'
    · exact tail
  · exact tail

theorem lmMu_le {v v' : LMVars} (hc : chainLeft v'.chain_length ≤ chainLeft v.chain_length)
    (hb : v'.best_len = v.best_len) : lmMu (.cont, v') ≤ lmMu (.cont, v) := by
  simp only [lmMu, LMExit.isCont, ↓reduceIte, hb]
  have := Nat.mul_le_mul_right 131072 hc
  omega

theorem lmMu_lt_chain {v v' : LMVars} (hc : chainLeft v'.chain_length < chainLeft v.chain_length)
    (hb : v'.best_len = v.best_len) : lmMu (.cont, v') < lmMu (.cont, v) := by
  simp only [lmMu, LMExit.isCont, ↓reduceIte, hb]
  have := Nat.mul_le_mul_right 131072 (Nat.succ_le_of_lt hc)
  rw [Nat.succ_mul] at this
  omega

/-- One trip of the outer loop (`match_tpl.h:139-294`) with `strstart <= B`: `LI` holds after it, and a running loop
has a smaller measure. -/
theorem loop_body_ok {e : LMEnv} {v : LMVars} {wo po ho bl0 : Nat} (E : LE b wo po ho st e) (N : LN d wo po ho st)
    (hp : PrevBelow d po st B) (hBs : st.strstart.toNat ≤ B) (V : VI b wo st v) {ms : UInt32}
    (hb : BL st B bl0 v.best_len ms) :
    Sat (LH H i z b st d ms) (LM.loop_body e v) (fun s H' => LI H i z b st B d wo bl0 s H' ∧
      (s.1.isCont = true → lmMu s < lmMu (.cont, v))) := by
  have hst := N.look
  have hbig := N.big
  have hB := hp.1
  unfold LM.loop_body
  rw [E.strstart]
  split
  · exact Sat.pure ⟨⟨ms, rfl, hb⟩, fun h => by simp [LMExit.isCont] at h⟩
  rename_i hlt
  have hlt' : v.cur_match.toNat < st.strstart.toNat := UInt32.lt_iff_toNat_lt.mp (UInt32.not_le.mp hlt)
  have hcur : CurOk B v v := ⟨by omega, V.le⟩
  dsimp only
  split
  refine Sat.bind (Sat.mono (short_filter_ok E N hp V (UInt32.lt_iff_toNat_lt.mp ‹v.best_len < 8›) hcur ms) ?_)
  rotate_left
  refine Sat.bind (Sat.mono (long_filter_ok E N hp V hcur ms) ?_)
  all_goals
    rintro ⟨sel, v'⟩ _ ⟨rfl, hv', htl⟩
    dsimp only at hv' htl ⊢
    have hbest : v'.best_len = v.best_len := by rw [hv']
    have hlim : v'.limit = v.limit := by rw [hv']
    have hmo : v'.match_offset = v.match_offset := by rw [hv']
    cases sel with
    | ret x =>
      simp only [SelTail] at htl
      exact Sat.pure ⟨⟨ms, rfl, by rw [htl]; exact hb.pr⟩, fun h => by simp [LMExit.isCont] at h⟩
    | accept len =>
      obtain ⟨hl, h8, ⟨hc1, hc2⟩, hcl⟩ := htl
      have V' : VI b wo st v' := by
        have := V.upd v'.chain_length v'.cur_match (by omega) hc2
        rw [← hv'] at this; exact this
      refine Sat.mono (accept_ok E N hp V' (by rw [hbest]; exact hb) (by rw [hbest]; exact hl) (by omega) hc1) ?_
      rintro s _ ⟨hL, hm⟩
      exact ⟨hL, fun h => Nat.lt_of_lt_of_le (hm h) (lmMu_le hcl hbest)⟩
    | compare =>
      obtain ⟨⟨hc1, hc2⟩, hcl⟩ := htl
      have V' : VI b wo st v' := by
        have := V.upd v'.chain_length v'.cur_match (by omega) hc2
        rw [← hv'] at this; exact this
      have hsub := sub_mo V'.lim V'.le
      have hb' : BL st B bl0 v'.best_len ms := by rw [hbest]; exact hb
      refine Sat.bind (Sat.mono (sat_add' E.scan (LH_get ms) (by omega) _ (wo + st.strstart.toNat + 2) (by simp)
        (by omega)) ?_)
      rintro _ _ ⟨rfl, rfl⟩
      refine Sat.bind (Sat.mono (sat_add' V'.ms (LH_get ms) (by omega) _ (wo + (v'.cur_match - v'.match_offset).toNat)
        (by simp) (by omega)) ?_)
      rintro _ _ ⟨rfl, rfl⟩
      refine Sat.bind (Sat.mono (sat_add (LH_get ms) (by omega) 2 (wo + (v'.cur_match - v'.match_offset).toNat + 2)
        (by simp) (by omega)) ?_)
      rintro _ _ ⟨rfl, rfl⟩
      refine Sat.bind (Sat.mono (ZlibNgF.Proof.Compare256.compare256_ok (LH_get ms) (by omega) (by omega)) ?_)
      rintro c _ ⟨rfl, hc⟩
      have hc2' : (c + 2).toNat = c.toNat + 2 := by rw [UInt32.toNat_add]; simp; omega
      split
      · rename_i hgt
        refine Sat.mono (accept_ok E N hp V' hb' hgt (by omega) hc1) ?_
        rintro s _ ⟨hL, hm⟩
        exact ⟨hL, fun h => Nat.lt_of_lt_of_le (hm h) (lmMu_le hcl hbest)⟩
      · refine Sat.mono (goto_outer_ok E N hp V' hb') ?_
        rintro ⟨x, s2⟩ _ ⟨hL, hm⟩
        refine ⟨hL, fun h => ?_⟩
        obtain ⟨h1, h2⟩ := hm h
        cases x with
        | cont =>
          exact lmMu_lt_chain (Nat.lt_of_lt_of_le h1 hcl) (by rw [h2, hbest])
        | brk => simp [LMExit.isCont] at h
        | ret r => simp [LMExit.isCont] at h

theorem lmMu_lt_fuel (s : LMExit × LMVars) : lmMu s < fuel := by
  have := chainLeft_lt s.2.chain_length
  have h2 := Nat.mul_le_mul_right 131072 (Nat.le_of_lt this)
  unfold lmMu fuel; split <;> omega

/-- The outer `for (;;)` of `LONGEST_MATCH` (`match_tpl.h:139-294`) with `strstart <= B`: it ends with `break` or
`return`, keeping `LI`. -/
theorem main_loop_ok {e : LMEnv} {v : LMVars} {wo po ho bl0 : Nat} (E : LE b wo po ho st e) (N : LN d wo po ho st)
    (hp : PrevBelow d po st B) (hBs : st.strstart.toNat ≤ B) (V : VI b wo st v) {ms : UInt32}
    (hb : BL st B bl0 v.best_len ms) :
    Sat (LH H i z b st d ms) (cwhile
      (fun ((x, v) : LMExit × LMVars) => pure (x.isCont, (x, v)))
      (fun ((_, v) : LMExit × LMVars) => LM.loop_body e v)
      (LMExit.cont, v))
      (fun s H' => LI H i z b st B d wo bl0 s H' ∧ s.1.isCont = false) := by
  refine sat_cwhile (fun s H' => LI H i z b st B d wo bl0 s H') lmMu _ ?_ ⟨ms, rfl, V, hb⟩ (lmMu_lt_fuel _)
  rintro ⟨x, v1⟩ _ hI
  refine Sat.pure ⟨fun hc => ?_, fun hc => ⟨hI, hc⟩⟩
  cases x with
  | cont =>
    obtain ⟨ms1, rfl, V1, hb1⟩ := hI
    refine Sat.mono (loop_body_ok E N hp hBs V1 hb1) ?_
    rintro ⟨x2, v2⟩ _ ⟨hL, hm⟩
    refine ⟨hL, ?_⟩
    cases x2 with
    | cont => exact hm rfl
    | brk => simp [lmMu, LMExit.isCont]; omega
    | ret r => simp [lmMu, LMExit.isCont]; omega
  | brk => simp [LMExit.isCont] at hc
  | ret r => simp [LMExit.isCont] at hc

end

end ZlibNgF.Proof.LongestMatch
