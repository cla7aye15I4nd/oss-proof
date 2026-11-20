import ZlibNgF.Proof.«deflate.c.facts»
import ZlibNgF.Proof.«public-deflate-control»
import ZlibNgF.Proof.«public-deflate-bound»
import ZlibNgF.Proof.«deflate.c.setdict»
import ZlibNgF.Proof.«deflate.c.copy»
import ZlibNgF.Proof.«deflate.c.dict»
import ZlibNgF.Proof.«deflate.c.fill_window.facts»

/-!
# Between-call facts of a deflate stream beside the invariant (`ZlibNgF`)

`DSide h s`: facts about the state of stream `s` that hold between public calls but not inside a strategy, so they
are not clauses of `DCore` (which the working state `DWork` of the strategies and the window state `DInvW` contain):

* `SymsOk` (room for one more symbol, `strstart - block_start` bounded by the symbols, the level-0 and level-1
  `Z_FIXED` states without symbols, no symbols at `block_start == strstart`), which a strategy needs on entry;
* after a call with a flush that completed (`last_flush > 0`), no symbols; in `FINISH_STATE`, no symbols and no
  lookahead (`deflateParams` and the strategy dispatch of `deflate` read these);
* the gzip header (`HdrOk`): in `GZIP_STATE` and the header states `wrap` is 2; in the header states
  (`EXTRA_STATE` .. `HCRC_STATE`) a header is registered, and the saved index `gzindex` is within the extra field
  (`extra_len & 0xffff`) or the string being copied, which lies outside the library's block (so that the library's
  own stores between calls, such as `deflatePrime`'s, keep its length). The header is the caller's: the caller step
  keeps its fields and string lengths while the header is being written (`DCallerStep`), and the other calls do not
  write it. (That the header's buffers lie outside the library's block during a `deflate` call is part of
  `DStreamIO`.)

The preservation lemmas at the end cover every public step except `deflateResetKeep` (open: it keeps `strstart` and
`block_start` and drops the symbols, so the gap clause of `SymsOk` does not follow), `deflate` and `deflateParams`.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.DeflateSide
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateFacts

/-- The states in which `deflate` resumes the gzip header. -/
def HdrState (st : DeflateState) : Prop :=
  st.status = EXTRA_STATE ∨ st.status = NAME_STATE ∨ st.status = COMMENT_STATE ∨ st.status = HCRC_STATE

/-- The gzip-header facts of state `st` of block `b` in `h`. -/
def HdrOk (h : Heap) (b : Nat) (st : DeflateState) : Prop :=
  ((st.status = GZIP_STATE ∨ HdrState st) → st.wrap = 2) ∧
  (HdrState st → ∃ k g, st.gzhead = .val (some k) ∧ h.gzheaders k = some g ∧
    (st.status = EXTRA_STATE → g.extra ≠ .null → st.gzindex.toNat ≤ (g.extra_len &&& 0xffff).toNat) ∧
    (st.status = NAME_STATE → g.name ≠ .null →
      NotInBlock b g.name ∧ ∃ n, CStringLen h g.name n ∧ st.gzindex.toNat ≤ n) ∧
    (st.status = COMMENT_STATE → g.comment ≠ .null →
      NotInBlock b g.comment ∧ ∃ n, CStringLen h g.comment n ∧ st.gzindex.toNat ≤ n))

/-- The between-call facts of state `st` of block `b` in `h`. -/
def SideAt (h : Heap) (b : Nat) (st : DeflateState) : Prop :=
  SymsOk st ∧ (0 < st.last_flush → st.sym_next = 0) ∧
    (st.status = FINISH_STATE → st.sym_next = 0 ∧ st.lookahead = 0) ∧ HdrOk h b st

/-- The between-call facts of stream `s` in `h`. -/
def DSide (h : Heap) (s : StreamPtr) : Prop := ∀ b st, DStateIs h s b st → SideAt h b st

/-! ## Interface lemmas -/

/-- `HdrOk` reads the state only through `status`, `wrap`, `gzhead`, `gzindex`. -/
theorem HdrOk.of_state {h : Heap} {b : Nat} {st st' : DeflateState} (H : HdrOk h b st)
    (e1 : st'.status = st.status) (e2 : st'.wrap = st.wrap) (e3 : st'.gzhead = st.gzhead)
    (e4 : st'.gzindex = st.gzindex) : HdrOk h b st' := by
  unfold HdrOk HdrState at *
  rw [e1, e2, e3, e4]; exact H

/-- `SideAt` reads the state through the fields of `SymsOk`, `last_flush`, `status`, `wrap`, `gzhead`,
`gzindex`. -/
theorem SideAt.of_state {h : Heap} {b : Nat} {st st' : DeflateState} (S : SideAt h b st)
    (e1 : st'.status = st.status) (e2 : st'.wrap = st.wrap) (e3 : st'.gzhead = st.gzhead)
    (e4 : st'.gzindex = st.gzindex) (e5 : st'.sym_next = st.sym_next) (e6 : st'.sym_end = st.sym_end)
    (e7 : st'.strstart = st.strstart) (e8 : st'.block_start = st.block_start) (e9 : st'.level = st.level)
    (e10 : st'.lookahead = st.lookahead) (e11 : st'.strategy = st.strategy)
    (e12 : st'.last_flush = st.last_flush) : SideAt h b st' := by
  obtain ⟨S1, S2, S3, S4⟩ := S
  refine ⟨?_, ?_, ?_, S4.of_state e1 e2 e3 e4⟩
  · unfold SymsOk at *; rw [e5, e6, e7, e8, e9, e10, e11]; exact S1
  · rw [e12, e5]; exact S2
  · rw [e1, e5, e10]; exact S3

/-- How the header facts move from heap `h` (library block `b`) to heap `h'` (library block `b'`), for state `st`:
in a header state, the registered header record keeps its fields, and a string outside block `b` keeps its length
and lies outside block `b'`. -/
def HdrMove (h h' : Heap) (b b' : Nat) (st : DeflateState) : Prop :=
  HdrState st → ∀ k g, st.gzhead = .val (some k) → h.gzheaders k = some g → ∃ g', h'.gzheaders k = some g' ∧
    g'.extra = g.extra ∧ g'.extra_len = g.extra_len ∧ g'.name = g.name ∧ g'.comment = g.comment ∧
    ∀ p n, (p = g.name ∨ p = g.comment) → NotInBlock b p → CStringLen h p n → CStringLen h' p n ∧ NotInBlock b' p

theorem HdrOk.move {h h' : Heap} {b b' : Nat} {st : DeflateState} (H : HdrOk h b st) (m : HdrMove h h' b b' st) :
    HdrOk h' b' st := by
  obtain ⟨H1, H2⟩ := H
  refine ⟨H1, fun hs => ?_⟩
  obtain ⟨k, g, hk, hgk, x1, x2, x3⟩ := H2 hs
  obtain ⟨g', hg', e1, e2, e3, e4, c⟩ := m hs k g hk hgk
  refine ⟨k, g', hk, hg', fun a q => ?_, fun a q => ?_, fun a q => ?_⟩
  · rw [e2]; exact x1 a (by rw [← e1]; exact q)
  · obtain ⟨nb, n, hn, hi⟩ := x2 a (by rw [← e3]; exact q)
    obtain ⟨c1, c2⟩ := c g.name n (Or.inl rfl) nb hn
    exact ⟨by rw [e3]; exact c2, n, by rw [e3]; exact c1, hi⟩
  · obtain ⟨nb, n, hn, hi⟩ := x3 a (by rw [← e4]; exact q)
    obtain ⟨c1, c2⟩ := c g.comment n (Or.inr rfl) nb hn
    exact ⟨by rw [e4]; exact c2, n, by rw [e4]; exact c1, hi⟩

/-- `SideAt` moves along `HdrMove` to a state that agrees on the fields of `SideEq`. -/
theorem SideAt.move {h h' : Heap} {b b' : Nat} {st st' : DeflateState} (S : SideAt h b st)
    (m : HdrMove h h' b b' st) (e : SideEq st st') : SideAt h' b' st' := by
  have S' := S.of_state e.status e.wrap e.gzhead e.gzindex e.sym_next e.sym_end e.strstart e.block_start e.level
    e.lookahead e.strategy e.last_flush
  have m' : HdrMove h h' b b' st' := fun hs k g hk hg =>
    m (by unfold HdrState at hs ⊢; rwa [e.status] at hs) k g (by rw [← e.gzhead]; exact hk) hg
  exact ⟨S'.1, S'.2.1, S'.2.2.1, S'.2.2.2.move m'⟩

/-- A C string keeps its length on a heap with the same bytes at its object. -/
theorem cstr_get {h h' : Heap} {p : BPtr} {n : Nat} (c : CStringLen h p n)
    (e : ∀ r off, p = .ref r off → Space.get h' r = Space.get h r) : CStringLen h' p n := by
  obtain ⟨r, off, data, rfl, hg, h1, h2, h3⟩ := c
  exact ⟨r, off, data, rfl, by rw [e r off rfl]; exact hg, h1, h2, h3⟩

/-- `HdrMove` with the same header records and the same bytes outside block `b`. -/
theorem hdrMove_out {h h' : Heap} {b : Nat} {st : DeflateState} (hg : h'.gzheaders = h.gzheaders)
    (e : ∀ r : BRef, r ≠ .heap b → Space.get h' r = Space.get h r) : HdrMove h h' b b st := by
  intro _ k g _ hk
  refine ⟨g, by rw [hg]; exact hk, rfl, rfl, rfl, rfl, fun p n _ nb c => ⟨cstr_get c fun r off hp => e r ?_, nb⟩⟩
  intro hr; subst hr; exact nb off hp

/-! ## Preservation by calls and by the caller -/

/-- A store into the state record of stream `i` (block `b`) that keeps the fields that `SideAt` reads keeps
`DSide`. -/
theorem side_setD {h : Heap} {i : Nat} {z : ZStream} {b : Nat} {st st' : DeflateState}
    (hz : h.streams i = some z) (hb : z.state = some b) (hst : h.dstate b = some st) (hs : DSide h (some i))
    (k : SideAt h b st → SideAt h b st') :
    DSide { h with dstates := upd h.dstates b (some st') } (some i) := by
  intro b' st2 ⟨i', z', e, hz', hb', hst2⟩
  obtain rfl := Option.some.inj e
  obtain rfl : z = z' := Option.some.inj (hz.symm.trans hz')
  obtain rfl : b = b' := Option.some.inj (hb.symm.trans hb')
  have hd : ∃ d, h.bytes b = some d := by
    unfold Heap.dstate at hst; split at hst <;> simp_all
  obtain ⟨d, hd⟩ := hd
  have e2 : st2 = st' := by simpa [Heap.dstate, hd] using hst2.symm
  subst e2
  have S := k (hs b st ⟨i, z, rfl, hz, hb, hst⟩)
  exact S.move (hdrMove_out rfl fun _ _ => rfl) (SideEq.refl _)

/-- `deflateTune` keeps `DSide`: it writes `good_match`, `max_lazy_match`, `nice_match`, `max_chain_length`. -/
theorem tune_side {h : Heap} {s : StreamPtr} (hv : DInv h s) (hs : DSide h s) (g l n c : Int32) :
    ∃ h', C.run (deflateTune s g l n c) h = .ok (Z_OK, h') ∧ DSide h' s := by
  obtain ⟨i, z, b, st, rfl, hz, hb, hst, e, -⟩ := DeflateControl.deflateTune_inv hv g l n c
  exact ⟨_, e, side_setD hz hb hst hs fun S => S.of_state rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩

/-- `deflateSetHeader` keeps `DSide` when called before the first `deflate` call (`GZIP_STATE`, not a header
state; `wrap` is kept). -/
theorem setHeader_side {h h' : Heap} {s : StreamPtr} {hp : HeaderPtr} {r : Int32} (hv : DInv h s) (hs : DSide h s)
    (hbf : BeforeFirstDeflate h s) (e : C.run (deflateSetHeader s hp) h = .ok (r, h')) : DSide h' s := by
  rcases DeflateControl.deflateSetHeader_inv hv hp with e0 | ⟨i, z, b, st, rfl, hz, hb, hst, e0, -⟩
  · rw [e0] at e; cases e; exact hs
  · rw [e0] at e; cases e
    obtain ⟨b1, st1, ⟨⟨z1, ⟨i1, e1, hz1⟩, hb1⟩, hst1⟩, hgz⟩ := hbf
    obtain rfl := Option.some.inj e1
    obtain rfl : z = z1 := Option.some.inj (hz.symm.trans hz1)
    obtain rfl : b = b1 := Option.some.inj (hb.symm.trans hb1)
    obtain rfl : st = st1 := Option.some.inj (hst.symm.trans hst1)
    refine side_setD hz hb hst hs fun S => ⟨S.1, S.2.1, S.2.2.1, ?_⟩
    have hn : ¬ HdrState st := by
      unfold HdrState; rw [hgz]; decide
    exact ⟨fun _ => S.2.2.2.1 (Or.inl hgz), fun hh => absurd hh hn⟩

/-- The caller step keeps `DSide`: the state record is the same, and while the header is being written its fields
and string lengths stay. -/
theorem caller_side {h h' : Heap} {s : StreamPtr} (hs : DSide h s) (hc : DCallerStep h h' s) : DSide h' s := by
  obtain ⟨i, z, z', b, st, rfl, hz, hz', hb, hst, ez, hbytes, hdstates, -, hhd, -, -⟩ := hc
  intro b' st2 ⟨i', z2, e, hz2, hb2, hst2⟩
  obtain rfl := Option.some.inj e
  obtain rfl : z' = z2 := Option.some.inj (hz'.symm.trans hz2)
  have hs' : z'.state = z.state := by rw [ez]
  obtain rfl : b = b' := Option.some.inj (hb.symm.trans (hs'.symm.trans hb2))
  have hst' : h'.dstate b = some st := by simp only [Heap.dstate, hbytes, hdstates]; exact hst
  obtain rfl : st = st2 := Option.some.inj (hst'.symm.trans hst2)
  refine (hs b st ⟨i, z, rfl, hz, hb, hst⟩).move (fun hh k g hk hg => ?_) (SideEq.refl _)
  obtain ⟨g', hg', hf⟩ := hhd k g hk hg
  obtain ⟨e1, e2, e3, e4, c1, c2⟩ := hf hh
  refine ⟨g', hg', e1, e2, e3, e4, fun p n hp nb c => ⟨?_, nb⟩⟩
  rcases hp with rfl | rfl
  · exact c1 n c
  · exact c2 n c

/-! ## The other steps -/

open ZlibNgF.Proof.DeflateInit (SH FreshSt DFreshOf)

/-- The state record of an invariant stream satisfies the invariant's clauses. -/
theorem core_of {h : Heap} {s : StreamPtr} {b : Nat} {st : DeflateState} (hv : DInv h s) (hs : DStateIs h s b st) :
    ∃ z al, DCore h s z b (dview st) al := by
  obtain ⟨i, z, b0, st0, al, rfl, hz, hb, hst, -, c⟩ := hv
  obtain ⟨i', z', e, hz', hb', hst'⟩ := hs
  obtain rfl := Option.some.inj e
  obtain rfl := Option.some.inj (hz.symm.trans hz')
  obtain rfl := Option.some.inj (hb.symm.trans hb')
  obtain rfl := Option.some.inj (hst.symm.trans hst')
  exact ⟨z, al, c⟩

theorem symEnd_pos {h : Heap} {s : StreamPtr} {z : ZStream} {b : Nat} {st : DeflateState} {al : DeflateAllocs}
    (c : DCore h s z b (dview st) al) : 0 < st.sym_end := by
  obtain ⟨-, -, -, l1, -, -, se⟩ := c.sizes
  simp only [dview] at l1 se
  rw [UInt32.lt_iff_toNat_lt, se]; simp; omega

/-- A state with no symbols, `block_start` at `strstart`, no lookahead satisfies `SymsOk`. -/
theorem symsOk_clean {st : DeflateState} (h0 : 0 < st.sym_end) (hs : st.sym_next = 0)
    (hb : st.block_start.toInt = st.strstart.toNat) (hl : st.lookahead = 0) : SymsOk st := by
  refine ⟨by rw [hs]; exact h0, fun _ => by rw [hb]; omega, fun _ => ⟨?_, hs, hl⟩, fun _ _ => hs, fun _ => hs⟩
  rw [Int32.le_iff_toInt_le, hb]; simp

/-- `SideAt` of a state with no symbols, `block_start` at `strstart`, no lookahead, outside the header states, with
`wrap = 2` in `GZIP_STATE`. -/
theorem sideAt_clean {h : Heap} {b : Nat} {st : DeflateState} (h0 : 0 < st.sym_end) (hs : st.sym_next = 0)
    (hb : st.block_start.toInt = st.strstart.toNat) (hl : st.lookahead = 0) (hn : ¬ HdrState st)
    (hg : st.status = GZIP_STATE → st.wrap = 2) : SideAt h b st :=
  ⟨symsOk_clean h0 hs hb hl, fun _ => hs, fun _ => ⟨hs, hl⟩,
    ⟨fun e => e.elim hg (fun e2 => absurd e2 hn), fun e => absurd e hn⟩⟩

/-- `deflateInit*` and `deflateReset` leave `DSide` (`FreshSt`). -/
theorem side_fresh {h : Heap} {s : StreamPtr} (hv : DInv h s) (hf : DFreshOf h s) : DSide h s := by
  intro b st hs
  obtain ⟨z, al, c⟩ := core_of hv hs
  obtain ⟨i, z0, b0, st0, rfl, hz0, hb0, hst0, f⟩ := hf
  obtain ⟨i', z', e, hz', hb', hst'⟩ := hs
  obtain rfl := Option.some.inj e
  obtain rfl := Option.some.inj (hz0.symm.trans hz')
  obtain rfl := Option.some.inj (hb0.symm.trans hb')
  obtain rfl := Option.some.inj (hst0.symm.trans hst')
  obtain ⟨f1, f2, f3, f4, -, f6, f7⟩ := f
  refine sideAt_clean (symEnd_pos c) f1 (by rw [f2, f3]; rfl) f4 ?_ f7
  unfold HdrState
  rcases f6 with e | e <;> rw [e] <;> decide

/-- A step that changes only the stream record, the state record (keeping the fields of `SideEq`) and the bytes of
the stream's block keeps `DSide`. -/
theorem side_SH {h : Heap} {i : Nat} {z z' : ZStream} {b : Nat} {st st' : DeflateState} {d : Array UInt8}
    (hs : DSide h (some i)) (hz : h.streams i = some z) (hb : z.state = some b) (hst : h.dstate b = some st)
    (hb' : z'.state = some b) (e : SideEq st st') : DSide (SH h i z' b st' d) (some i) := by
  intro b2 st2 ⟨i2, z2, e2, hz2, hzb2, hst2⟩
  obtain rfl := Option.some.inj e2
  rw [ZlibNgF.Proof.DeflateInit.SH_streams] at hz2
  obtain rfl := Option.some.inj hz2
  obtain rfl := Option.some.inj (hb'.symm.trans hzb2)
  rw [ZlibNgF.Proof.DeflateInit.SH_dstate] at hst2
  obtain rfl := Option.some.inj hst2
  exact (hs b st ⟨i, z, rfl, hz, hb, hst⟩).move
    (hdrMove_out rfl fun r hr => ZlibNgF.Proof.DeflateSetDict.space_SH_ne hr) e

/-- A step that leaves the heap unchanged keeps `DSide`. -/
theorem side_same {h : Heap} {s : StreamPtr} (hs : DSide h s) : DSide h s := hs

/-- `deflatePrime` keeps `DSide`. -/
theorem prime_side {h h' : Heap} {s : StreamPtr} {bits value r : Int32} (hv : DInv h s) (hs : DSide h s)
    (e : C.run (deflatePrime s bits value) h = .ok (r, h')) : DSide h' s := by
  obtain ⟨i, z, b, rfl, hz, hb, r0, h0, e0, -, hk, -⟩ := ZlibNgF.Proof.DeflatePrime.prime_inv hv bits value
  rw [e] at e0; cases e0
  obtain ⟨i1, z1, b1, st1, al, e1, hz1, hb1, hst1, -, -⟩ := hv
  obtain rfl := Option.some.inj e1
  obtain rfl := Option.some.inj (hz.symm.trans hz1)
  obtain rfl := Option.some.inj (hb.symm.trans hb1)
  obtain ⟨st', d', rfl, eq⟩ := hk st1 hst1
  exact side_SH hs hz hb hst1 hb eq

/-- `deflateGetDictionary` keeps `DSide`: it writes only the caller's buffer, which is outside the library's block
and does not overlap the registered header's buffers. -/
theorem getDict_side {h h' : Heap} {s : StreamPtr} {d : BPtr} {hasLen : Bool} {r : Int32 × Option UInt32}
    (hv : DInv h s) (hs : DSide h s) (hd : NullOrWrite h d 32768) (hnb : ∀ b, StateBlock h s b → NotInBlock b d)
    (hdis : ∀ k, DRegisteredHeader h s (some k) → ∀ r, DHeaderRange h k r → Disjoint d 32768 r.1 r.2)
    (e : C.run (deflateGetDictionary s d hasLen) h = .ok (r, h')) : DSide h' s := by
  obtain ⟨r0, h0, e0, -, -, ho⟩ := ZlibNgF.Proof.DeflateDict.getDict_inv hasLen hv hd hnb
  rw [e] at e0; cases e0
  rcases ho with rfl | ⟨bd, off, ad, a1, rfl, had, rfl, hsz, hpt⟩
  · exact hs
  intro b st ⟨i, z, e1, hz, hzb, hst⟩
  subst e1
  have hbd : bd ≠ b := fun e2 => hnb b ⟨z, ⟨i, rfl, hz⟩, hzb⟩ off (by rw [e2])
  have hst0 : h.dstate b = some st := by
    simpa [Heap.dstate, upd_ne _ _ _ _ (Ne.symm hbd)] using hst
  refine (hs b st ⟨i, z, rfl, hz, hzb, hst0⟩).move (fun hh k g hk hg => ⟨g, hg, rfl, rfl, rfl, rfl,
    fun p n hp nb c => ⟨?_, nb⟩⟩) (SideEq.refl _)
  have hreg : DRegisteredHeader h (some i) (some k) := ⟨b, st, ⟨⟨z, ⟨i, rfl, hz⟩, hzb⟩, hst0⟩, hk⟩
  have hdj : Disjoint (.ref (.heap bd) off) 32768 p (n + 1) := by
    refine hdis k hreg (p, n + 1) ⟨g, hg, Or.inr ?_⟩
    rcases hp with rfl | rfl
    · exact Or.inl ⟨n, c, rfl⟩
    · exact Or.inr ⟨n, c, rfl⟩
  obtain ⟨r, o, data, rfl, hgd, h1, h2, h3⟩ := c
  by_cases hr : r = .heap bd
  · subst hr
    have hda : data = ad := Option.some.inj (hgd.symm.trans had)
    subst hda
    have hdj' : off + 32768 ≤ o ∨ o + (n + 1) ≤ off := by
      rcases hdj with x | x
      · exact absurd rfl x
      · exact x
    refine ⟨.heap bd, o, a1, rfl, by show (upd h.bytes bd (some a1)) bd = _; exact upd_same _ _ _, by omega,
      ?_, fun j hj => ?_⟩
    · rw [hpt _ (by omega)]; exact h2
    · rw [hpt _ (by omega)]; exact h3 j hj
  · refine ⟨r, o, data, rfl, ?_, h1, h2, h3⟩
    cases r with
    | heap c0 =>
      show (upd h.bytes bd (some a1)) c0 = _
      rw [upd_ne _ _ _ _ (fun e3 => hr (by rw [e3]))]; exact hgd
    | const c0 => exact hgd
    | str c0 => exact hgd


/-- `deflateSetDictionary` keeps `DSide` when called with no tallied symbols (`DictReady`). -/
theorem setDict_side {h h' : Heap} {s : StreamPtr} {d : BPtr} {n : UInt32} {r : Int32} (hv : DInv h s)
    (hs : DSide h s) (hdr : DictReady h s) (hd : NullOrRead h d n.toNat) (hnb : ∀ b, StateBlock h s b → NotInBlock b d)
    (e : C.run (deflateSetDictionary s d n) h = .ok (r, h')) : DSide h' s := by
  obtain ⟨r0, h0, e0, hv', -, ho⟩ := ZlibNgF.Proof.DeflateSetDict.setDict_inv ZlibNgF.Proof.FillFacts.windowFacts hv hd hnb
  rw [e] at e0; cases e0
  rcases ho with rfl | ⟨i, z, b, st, rfl, hz, hzb, hst, hw2, hout⟩
  · exact hs
  intro b' st' hs'
  obtain ⟨z', al', c'⟩ := core_of hv' hs'
  obtain ⟨i', z2, e1, hz2, hzb2, hst2⟩ := hs'
  obtain rfl := Option.some.inj e1
  obtain ⟨⟨k1, k2, -, -, -, -, -⟩, -, kb, kl⟩ := hout z2 b' st' hz2 hzb2 hst2
  obtain ⟨b3, st3, ⟨⟨z3, ⟨i3, e3, hz3⟩, hzb3⟩, hst3⟩, h0⟩ := hdr
  obtain rfl := Option.some.inj e3
  obtain rfl := Option.some.inj (hz.symm.trans hz3)
  obtain rfl := Option.some.inj (hzb.symm.trans hzb3)
  obtain rfl := Option.some.inj (hst.symm.trans hst3)
  have H1 := (hs b st ⟨i, z, rfl, hz, hzb, hst⟩).2.2.2.1
  have hnh : ¬ (st.status = GZIP_STATE ∨ HdrState st) := fun hh => hw2 (H1 hh)
  refine sideAt_clean (symEnd_pos c') (k1.trans h0) kb kl ?_ ?_
  · intro hh; unfold HdrState at hh; rw [k2] at hh; exact hnh (Or.inr hh)
  · intro hh; rw [k2] at hh; exact absurd (Or.inl hh) hnh

/-- On a heap with fresh blocks, a C string keeps its length across a step that changes no existing block, and lies
outside every block not yet allocated. -/
theorem cstr_frame {h h' : Heap} {S : List Nat} {p : BPtr} {n : Nat} (hfr : DFreshBlocks h)
    (f : DFrame h h' S [] [] []) (c : CStringLen h p n) :
    CStringLen h' p n ∧ ∀ b', h.nextBlk ≤ b' → NotInBlock b' p := by
  obtain ⟨⟨-, -, -, fb, -, fc, -⟩, -⟩ := f
  obtain ⟨r, o, data, rfl, hgd, h1, h2, h3⟩ := c
  cases r with
  | heap k0 =>
    have hk0 : k0 < h.nextBlk := by
      refine Nat.lt_of_not_le fun hle => ?_
      have := (hfr.1 k0 hle).2.2
      have hgd' : h.bytes k0 = some data := hgd
      rw [this] at hgd'; cases hgd'
    obtain ⟨data', hd', hsz, hpt⟩ := fb k0 hk0 (by simp) data hgd
    refine ⟨⟨.heap k0, o, data', rfl, hd', by omega, ?_, fun q hq => ?_⟩, fun b' hb' off e3 => ?_⟩
    · rw [hpt _ (by omega) (by simp)]; exact h2
    · rw [hpt _ (by omega) (by simp)]; exact h3 q hq
    · injection e3 with e4; injection e4 with e5; omega
  | const k0 =>
    refine ⟨⟨.const k0, o, data, rfl, ?_, h1, h2, h3⟩, fun _ _ off e3 => by injection e3 with e4; cases e4⟩
    show h'.consts k0 = some data
    rw [fc]; exact hgd
  | str k0 => exact ⟨⟨.str k0, o, data, rfl, hgd, h1, h2, h3⟩, fun _ _ off e3 => by injection e3 with e4; cases e4⟩

/-- The destination of `deflateCopy` (on a heap with fresh blocks) has `DSide`. -/
theorem copy_side {h h' : Heap} {src dst : StreamPtr} (hs : DSide h src) (hfr : DFreshBlocks h)
    (hc : ZlibNgF.Proof.DeflateCopy.CopySide h h' src dst) (hf : DFrame h h' (streamIds dst) [] [] []) :
    DSide h' dst := by
  obtain ⟨i, j, z, b, st, z', nb, st', rfl, rfl, hz, hzb, hst, hz', hzb', hnb, hst', eq⟩ := hc
  intro b2 st2 ⟨j2, z2, e2, hz2, hzb2, hst2⟩
  obtain rfl := Option.some.inj e2
  obtain rfl := Option.some.inj (hz'.symm.trans hz2)
  obtain rfl := Option.some.inj (hzb'.symm.trans hzb2)
  obtain rfl := Option.some.inj (hst'.symm.trans hst2)
  refine (hs b st ⟨i, z, rfl, hz, hzb, hst⟩).move (fun hh k g hk hg => ⟨g, by rw [hf.1.2.1 k (by simp)]; exact hg,
    rfl, rfl, rfl, rfl, fun p n _ _ c => ?_⟩) eq
  obtain ⟨c1, c2⟩ := cstr_frame hfr hf c
  exact ⟨c1, c2 nb hnb⟩

/-- The source of a `deflateCopy` step (on a heap with fresh blocks) keeps `DSide`. -/
theorem copy_src_side {h h' : Heap} {s dst : StreamPtr} {r : Int32} (hv : DInv h s) (hs : DSide h s)
    (hfr : DFreshBlocks h) (hdst : InitReady h dst) (hne : dst ≠ s)
    (e : C.run (deflateCopy dst s) h = .ok (r, h')) : DSide h' s := by
  obtain ⟨r0, h0, e0, f⟩ := ZlibNgF.Proof.DeflateCopy.copy_safe hv hfr hdst hne
  rw [e] at e0; cases e0
  obtain ⟨i, z, b, st, al, rfl, hz, hzb, hst, -, -⟩ := hv
  have hdi : i ∉ streamIds dst := by
    rcases dst with _ | j
    · simp [streamIds]
    · simp only [streamIds, List.mem_singleton]; intro e1; exact hne (by rw [e1])
  obtain ⟨d, hd⟩ : ∃ d, h.bytes b = some d := by
    unfold Heap.dstate at hst; split at hst <;> simp_all
  have hb : b < h.nextBlk := by
    refine Nat.lt_of_not_le fun hle => ?_
    rw [(hfr.1 b hle).2.2] at hd; cases hd
  obtain ⟨⟨fs, fg, -, fb, -⟩, fo⟩ := id f
  have hz' : h'.streams i = some z := by rw [fs i hdi]; exact hz
  obtain ⟨d', hd', -, -⟩ := fb b hb (by simp) d hd
  have hst' : h'.dstate b = some st := by
    have hst0 : h.dstates b = some st := by simpa [Heap.dstate, hd] using hst
    simp [Heap.dstate, hd', (fo b hb (by simp)).1, hst0]
  intro b2 st2 ⟨i2, z2, e2, hz2, hzb2, hst2⟩
  obtain rfl := Option.some.inj e2
  obtain rfl := Option.some.inj (hz'.symm.trans hz2)
  obtain rfl := Option.some.inj (hzb.symm.trans hzb2)
  obtain rfl := Option.some.inj (hst'.symm.trans hst2)
  refine (hs b st ⟨i, z, rfl, hz, hzb, hst⟩).move (fun hh k g hk hg => ⟨g, by rw [fg k (by simp)]; exact hg,
    rfl, rfl, rfl, rfl, fun p n _ nb c => ⟨(cstr_frame hfr f c).1, nb⟩⟩) (SideEq.refl _)

end ZlibNgF.Proof.DeflateSide
