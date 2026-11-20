import ZlibNgF.Proof.«deflate.c.facts»
import ZlibNgF.Proof.«public-deflate-control»
import ZlibNgF.Proof.«public-deflate-bound»

/-!
# Between-call facts of a deflate stream beside the invariant (`ZlibNgF`)

`DSide h s`: facts about the state of stream `s` that hold between public calls but not inside a strategy, so they
are not clauses of `DCore` (which the working state `DWork` of the strategies and the window state `DInvW` contain):

* `SymsOk` (room for one more symbol, `strstart - block_start` bounded by the symbols, the level-0 and level-1
  `Z_FIXED` states without symbols, no symbols at `block_start == strstart`), which a strategy needs on entry;
* after a call with a flush that completed (`last_flush > 0`), no symbols; in `FINISH_STATE`, no symbols and no
  lookahead (`deflateParams` and the strategy dispatch of `deflate` read these);
* the gzip header (`HdrOk`): in `GZIP_STATE` and the header states `wrap` is 2; in the header states
  (`EXTRA_STATE` .. `HCRC_STATE`) a header is registered, its buffers lie outside the library's block, and the saved
  index `gzindex` is within the extra field (`extra_len & 0xffff`) or the string being copied. The header is the
  caller's: the caller step keeps its fields and string lengths while the header is being written
  (`DCallerStep`), and the other calls do not write it.

The preservation lemmas at the end cover the calls that leave the state record unchanged or change only fields that
`DSide` does not read, and the caller step.
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
    NotInBlock b g.extra ∧ NotInBlock b g.name ∧ NotInBlock b g.comment ∧
    (st.status = EXTRA_STATE → g.extra ≠ .null → st.gzindex.toNat ≤ (g.extra_len &&& 0xffff).toNat) ∧
    (st.status = NAME_STATE → g.name ≠ .null → ∃ n, CStringLen h g.name n ∧ st.gzindex.toNat ≤ n) ∧
    (st.status = COMMENT_STATE → g.comment ≠ .null → ∃ n, CStringLen h g.comment n ∧ st.gzindex.toNat ≤ n))

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

/-- `HdrOk` on another heap with the same header records and string lengths (for the pointers outside block
`b`). -/
theorem HdrOk.of_heap {h h' : Heap} {b : Nat} {st : DeflateState} (H : HdrOk h b st)
    (hg : ∀ k g, st.gzhead = .val (some k) → HdrState st → h.gzheaders k = some g → ∃ g', h'.gzheaders k = some g' ∧
      g'.extra = g.extra ∧ g'.extra_len = g.extra_len ∧ g'.name = g.name ∧ g'.comment = g.comment ∧
      (∀ n, CStringLen h g.name n → CStringLen h' g.name n) ∧
      (∀ n, CStringLen h g.comment n → CStringLen h' g.comment n)) : HdrOk h' b st := by
  obtain ⟨H1, H2⟩ := H
  refine ⟨H1, fun hs => ?_⟩
  obtain ⟨k, g, hk, hgk, n1, n2, n3, x1, x2, x3⟩ := H2 hs
  obtain ⟨g', hg', e1, e2, e3, e4, c1, c2⟩ := hg k g hk hs hgk
  refine ⟨k, g', hk, hg', by rw [e1]; exact n1, by rw [e3]; exact n2, by rw [e4]; exact n3,
    fun a c => ?_, fun a c => ?_, fun a c => ?_⟩
  · rw [e2]; exact x1 a (by rw [← e1]; exact c)
  · obtain ⟨n, hn, hi⟩ := x2 a (by rw [← e3]; exact c)
    exact ⟨n, by rw [e3]; exact c1 n hn, hi⟩
  · obtain ⟨n, hn, hi⟩ := x3 a (by rw [← e4]; exact c)
    exact ⟨n, by rw [e4]; exact c2 n hn, hi⟩

/-- `SideAt` on another heap with the same header records and string lengths. -/
theorem SideAt.of_heap {h h' : Heap} {b : Nat} {st : DeflateState} (S : SideAt h b st)
    (hg : ∀ k g, st.gzhead = .val (some k) → HdrState st → h.gzheaders k = some g → ∃ g', h'.gzheaders k = some g' ∧
      g'.extra = g.extra ∧ g'.extra_len = g.extra_len ∧ g'.name = g.name ∧ g'.comment = g.comment ∧
      (∀ n, CStringLen h g.name n → CStringLen h' g.name n) ∧
      (∀ n, CStringLen h g.comment n → CStringLen h' g.comment n)) : SideAt h' b st :=
  ⟨S.1, S.2.1, S.2.2.1, S.2.2.2.of_heap hg⟩

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
  exact S.of_heap fun k g _ _ hg => ⟨g, hg, rfl, rfl, rfl, rfl, fun _ h1 => h1, fun _ h1 => h1⟩

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
  refine (hs b st ⟨i, z, rfl, hz, hb, hst⟩).of_heap fun k g hk hh hg => ?_
  obtain ⟨g', hg', hf⟩ := hhd k g hk hg
  exact ⟨g', hg', hf hh⟩

end ZlibNgF.Proof.DeflateSide
