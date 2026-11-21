import ZlibNgF.Proof.«inflate.c.leave»
import ZlibNgF.Proof.«inflate.c.reach»

/-!
# The safety of `inflate` and of the other inflate entry points (`ZlibNgF`)

`inflate_ok`: on a stream with the structural invariant, valid buffers (`StreamIO`) and the static CRC table in
place, `inflate` does not fault and returns with the invariant and the frame of the call. Its parts: the entry checks,
the `TYPE → TYPEDO` store, `LOAD()`, the loop of the modes (`loop_ok` from `tripOK`), and the `inf_leave` epilogue
(`leave_ok`); `envOK_of` turns `StreamIO` and the entry checks into the facts the modes use about the caller's buffers.
`pending` closes the induction of `InflateReach.reach_inv`, and every inflate goal follows.
-/

set_option autoImplicit false
namespace ZlibNgF.Proof.InflateTop
open C ZlibNgF.Spec ZlibNg.Inflate
open ZlibNgF.Proof.InflateInv (Inv Core view)
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.mono Sat.of_eq Touch)
open ZlibNgF.Proof.InflateLoop
open ZlibNgF.Proof.InflateX

theorem runX_tryCatch {α : Type} (m : X α) (hd : Ex → X α) (l : IL) :
    runX (tryCatch m hd) l = (runX m l >>= fun p => match p.1 with
      | .ok a => pure (.ok a, p.2)
      | .error e => runX (hd e) p.2) := by
  funext h
  simp only [runX, tryCatch, tryCatchThe, MonadExceptOf.tryCatch, ExceptT.tryCatch, ExceptT.run, ExceptT.mk,
    StateT.run, bind, StateT.bind]
  split
  · rename_i a h' _
    rcases a with ⟨r, l'⟩
    cases r <;> rfl
  · rfl

theorem satX_tryCatch {α : Type} {H : Heap} {l : IL} {m : X α} {hd : Ex → X α}
    {Q : Except Ex α → IL → Heap → Prop}
    (hm : SatX H l m (fun r l' H' => match r with
      | .ok a => Q (.ok a) l' H'
      | .error e => SatX H' l' (hd e) Q)) : SatX H l (tryCatch m hd) Q := by
  unfold SatX at hm ⊢
  rw [runX_tryCatch]
  refine Sat.bind (Sat.mono hm ?_)
  rintro ⟨r, l'⟩ H' q
  cases r with
  | ok a => exact Sat.pure q
  | error e => exact q

/-- What a return of `inflate` after its entry checks gives: one of its codes (`Z_STREAM_ERROR` from a mode `SYNC` or
`MEM`) with the exact accounting of the input and output positions (`IoAcc`). -/
def ResAcc (E : Env) (v : Int32) (H : Heap) : Prop :=
  (v = Z_OK ∨ v = Z_STREAM_END ∨ v = Z_NEED_DICT ∨ v = Z_BUF_ERROR ∨ v = Z_DATA_ERROR ∨ v = Z_STREAM_ERROR) ∧
    IoAcc E H

theorem resAcc_of_leave {E : Env} {v : Int32} {H : Heap} (h : InflateLeave.LeaveRes E v H) : ResAcc E v H := by
  obtain ⟨hr, ha⟩ := h
  refine ⟨?_, ha⟩
  rcases hr with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem ret_cases {E : Env} {v : Int32} {H : Heap} (h : IoAcc E H ∧ (v = Z_NEED_DICT ∨ v = Z_STREAM_ERROR)) :
    v ≠ Z_OK ∧ v ≠ Z_BUF_ERROR ∧ ResAcc E v H := by
  rcases h with ⟨ha, rfl | rfl⟩
  · exact ⟨by decide, by decide, Or.inr (Or.inr (Or.inl rfl)), ha⟩
  · exact ⟨by decide, by decide, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))), ha⟩

/-- The loop of `inflate` and its epilogue, from the loop invariant. -/
theorem loopPart_ok (E : Env) (eo : EnvOK E) {l : IL} {H : Heap} {z : ZStream} {S : InflateState}
    (li : LI E l H z S) :
    SatX H l (do
      let r ← tryCatch (do xloopBrk (do dispatch E.c; return false); return none)
        (fun e => match e with
          | .leave => pure none
          | .ret v => pure (some v))
      match r with
      | some v => return v
      | none => infLeave E.c) (fun r _ H' => (∃ v, r = .ok v ∧ (v = Z_OK → InflateLeave.Prog E H') ∧
        (v = Z_BUF_ERROR → E.flush ≠ Z_FINISH → E.flush ≠ Z_BLOCK → E.flush ≠ Z_TREES → InflateLeave.BufOut E H') ∧
        ResAcc E v H' ∧ (v = Z_STREAM_END → InflateLeave.EndIn E H') ∧ (v ≠ Z_STREAM_ERROR → InFr E H')) ∧
        Fin E H') := by
  refine SatX.bind (satX_tryCatch ?_)
  refine SatX.bind (SatX.mono (loop_ok (tripOK E eo) li) ?_)
  rintro r l' H' p
  match r, p with
  | .error .leave, ⟨⟨z', S', li'⟩, hw⟩ =>
    exact SatX.pure (SatX.mono (InflateLeave.leave_ok E eo li' hw)
      (fun r l2 H2 ⟨⟨v, hr, hp, hb, hres, hend⟩, hf, hin⟩ => ⟨⟨v, hr, hp, hb, resAcc_of_leave hres, hend,
        fun _ => hin⟩, hf⟩))
  | .error (.ret v), hf =>
    have hc := ret_cases ⟨hf.2.1, hf.2.2.1⟩
    exact SatX.pure (SatX.pure ⟨⟨v, rfl, fun e => absurd e hc.1, fun e => absurd e hc.2.1, hc.2.2, fun e => by
      rcases hf.2.2.1 with h | h <;> rw [h] at e <;> exact absurd e (by decide),
      fun hne => hf.2.2.2 (hf.2.2.1.resolve_right hne)⟩, hf.1⟩)

theorem space_get_eq {h H1 : Heap} (hB : H1.bytes = h.bytes) (hK : H1.consts = h.consts) (r : BRef) :
    Space.get H1 r = Space.get h r := by
  cases r with
  | heap c => show H1.bytes c = h.bytes c; rw [hB]
  | const c => show H1.consts c = h.consts c; rw [hK]
  | str _ => rfl

theorem headerIds_eq {h : Heap} {i b : Nat} {z : ZStream} {st : InflateState} {hp : HeaderPtr}
    (hz : h.streams i = some z) (hb : z.state = some b) (hst : h.istate b = some st) (hhead : st.head = .val hp) :
    headerIds h (some i) = (match hp with | some k => [k] | none => []) := by
  cases hp <;> simp [headerIds, stateIds, hz, hb, hst, hhead]

theorem outputRanges_eq {h : Heap} {i b : Nat} {z : ZStream} {st : InflateState} {hp : HeaderPtr}
    (hz : h.streams i = some z) (hb : z.state = some b) (hst : h.istate b = some st) (hhead : st.head = .val hp) :
    outputRanges h (some i) = (z.next_out, z.avail_out.toNat) :: headerRanges h hp := by
  have e := headerIds_eq hz hb hst hhead
  cases hp with
  | none => simp only [outputRanges, hz, e, headerRanges]
  | some k => simp only [outputRanges, hz, e]

/-- What the caller's buffers give at entry (`StreamIO` and `inflate`'s own checks). -/
theorem envOK_of {h H1 : Heap} {i b : Nat} {z : ZStream} {st : InflateState} {hp : HeaderPtr} (flush : Int32)
    (hz : h.streams i = some z) (hb : z.state = some b) (hst : h.istate b = some st) (hhead : st.head = .val hp)
    (hok : HeaderOk h hp) (hin : NullOrRead h z.next_in z.avail_in.toNat)
    (hout : NullOrWrite h z.next_out z.avail_out.toNat)
    (hdisj : PairwiseDisjoint ((z.next_in, z.avail_in.toNat) :: (z.next_out, z.avail_out.toNat) :: headerRanges h hp))
    (hnb : ∀ r ∈ (z.next_in, z.avail_in.toNat) :: (z.next_out, z.avail_out.toNat) :: headerRanges h hp,
      NotInBlock b r.1)
    (hno : z.next_out ≠ .null) (hni : z.next_in = .null → z.avail_in = 0) (hc : h.crcTable = ZlibNg.Crc32Tbl.crc_table)
    (hB : H1.bytes = h.bytes) (hG : H1.gzheaders = h.gzheaders) (hC : H1.crcTable = h.crcTable)
    (hK : H1.consts = h.consts) :
    ∃ bo oo, z.next_out = .ref (.heap bo) oo ∧
      EnvOK ⟨H1, i, b, flush, z.next_in, z.avail_in, bo, oo, z.avail_out, hp, headerIds h (some i),
        outputRanges h (some i)⟩ := by
  have hW := outputRanges_eq hz hb hst hhead
  have hGi := headerIds_eq hz hb hst hhead
  rcases hout with h0 | ⟨bo, oo, dout, hpo, hdo, hdos⟩
  · exact absurd h0 hno
  refine ⟨bo, oo, hpo, ⟨hC.trans hc, ?_, ?_, hni, hnb _ (List.mem_cons_self ..), ?_, ?_⟩⟩
  · intro k hk
    have hk' : hp = some k := hk
    subst hk'
    show k ∈ headerIds h (some i)
    simp [hGi]
  · rcases hin with h0 | ⟨r, o, d, e1, e2, e3⟩
    · exact Or.inl h0
    · exact Or.inr ⟨r, o, d, e1, by rw [space_get_eq hB hK]; exact e2, e3⟩
  · intro k g0 hk hg0
    subst hk
    have hg0' : h.gzheaders k = some g0 := by rw [← hG]; exact hg0
    have hHR : headerRanges h (some k) = [(g0.extra, g0.extra_max.toNat), (g0.name, g0.name_max.toNat),
        (g0.comment, g0.comm_max.toNat)] := by simp [headerRanges, hg0']
    rcases hok with h0 | ⟨k', g, e1, e2, w1, w2, w3⟩
    · cases h0
    cases e1
    rw [hg0'] at e2; cases e2
    have mk : ∀ (j : Nat) (p : BPtr) (n : Nat), NullOrWrite h p n →
        ((z.next_in, z.avail_in.toNat) :: (z.next_out, z.avail_out.toNat) :: headerRanges h (some k))[j + 2]? =
          some (p, n) → HBuf ⟨H1, i, b, flush, z.next_in, z.avail_in, bo, oo, z.avail_out, some k,
            headerIds h (some i), outputRanges h (some i)⟩ H1 p n := by
      intro j p n hw hj
      rcases hw with h0 | ⟨bd, off, data, e1, e2, e3⟩
      · exact Or.inl h0
      · refine Or.inr ⟨bd, off, data, e1, by rw [hB]; exact e2, e3, ?_, ?_, ?_⟩
        · intro e
          have e' : bd = b := e
          subst e'
          have hm : (p, n) ∈ (z.next_in, z.avail_in.toNat) :: (z.next_out, z.avail_out.toNat) ::
              headerRanges h (some k) := List.mem_of_getElem? hj
          exact hnb _ hm off e1
        · show (p, n) ∈ outputRanges h (some i)
          rw [hW]
          have hm : (p, n) ∈ headerRanges h (some k) := by
            have hj' : (headerRanges h (some k))[j]? = some (p, n) := by simpa using hj
            exact List.mem_of_getElem? hj'
          exact List.mem_cons_of_mem _ hm
        · exact hdisj 0 (j + 2) _ _ (by omega) rfl hj
    rw [hHR] at mk
    exact ⟨mk 0 _ _ w1 rfl, mk 1 _ _ w2 rfl, mk 2 _ _ w3 rfl⟩
  · refine ⟨dout, by rw [hB]; exact hdo, hdos, ?_, ?_, ?_⟩
    · intro e
      have e' : bo = b := e
      exact hnb _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) oo (by rw [hpo, e'])
    · rw [hW, ← hpo]; exact List.mem_cons_self ..
    · rw [← hpo]; exact hdisj 0 1 _ _ (by decide) rfl rfl

/-- What a call of `inflate` that returns `Z_OK` did to stream `i`: the input advanced by the bytes consumed, the output
position moved inside the output buffer, the state and the registered header kept, and some input consumed or some
output written. -/
def Progress (h h' : Heap) (i : Nat) : Prop :=
  ∀ z b S, h.streams i = some z → z.state = some b → h.istate b = some S →
    ∃ z' S', h'.streams i = some z' ∧ z'.state = some b ∧ h'.istate b = some S' ∧ S'.head = S.head ∧
      InflateLoop.InAt z.next_in z.avail_in z'.next_in z'.avail_in ∧
      (z'.avail_out ≤ z.avail_out ∧ ∃ bo oo p, z.next_out = .ref (.heap bo) oo ∧ oo ≤ p ∧
        p + z'.avail_out.toNat ≤ oo + z.avail_out.toNat ∧ z'.next_out = .ref (.heap bo) p) ∧
      (z'.avail_in < z.avail_in ∨ z'.avail_out < z.avail_out)

/-- What a call of `inflate` that returns `Z_BUF_ERROR` with `flush` other than `Z_FINISH`, `Z_BLOCK`, `Z_TREES` did to
stream `i`: no input consumed, and there was no input, or there was no room for output (and the output count kept). -/
def BufStall (h h' : Heap) (i : Nat) : Prop :=
  ∀ z, h.streams i = some z → ∃ z', h'.streams i = some z' ∧ z'.avail_in = z.avail_in ∧
    (z.avail_in = 0 ∨ (z.avail_out = 0 ∧ z'.avail_out = z.avail_out))

/-- The exact accounting of a call of `inflate` on stream `i`: `next_in` advanced by `avail_in - avail_in'` bytes
(`InAt`), and `next_out` (a position of a heap block) advanced by `avail_out - avail_out'` bytes. -/
def IoRes (h h' : Heap) (i : Nat) : Prop :=
  ∀ z, h.streams i = some z → ∃ z', h'.streams i = some z' ∧ z'.state = z.state ∧
    InflateLoop.InAt z.next_in z.avail_in z'.next_in z'.avail_in ∧ z'.avail_out ≤ z.avail_out ∧
    ∃ bo oo, z.next_out = .ref (.heap bo) oo ∧ z'.next_out = .ref (.heap bo) (oo + (z.avail_out - z'.avail_out).toNat)

/-- What `inflate`'s own entry check asks of stream `i`: `next_out` not `NULL`, and `next_in` not `NULL` unless
`avail_in` is 0. -/
def EntryOK (h : Heap) (i : Nat) : Prop :=
  ∀ z, h.streams i = some z → z.next_out ≠ .null ∧ (z.avail_in = 0 ∨ z.next_in ≠ .null)

/-- `msg` of stream `i` after a call of `inflate`: the one before the call, or a string literal of the program. -/
def MsgRes (h h' : Heap) (i : Nat) : Prop :=
  ∀ z, h.streams i = some z → ∃ z', h'.streams i = some z' ∧
    (z'.msg = z.msg ∨ ∃ k, z'.msg = .ref (.str k) 0 ∧ k < strTable.size)

/-- A call of `inflate` from a just reset state of stream `i` (mode `HEAD`, no bits held, not the last block) consumed
input. -/
def FreshEnd (h h' : Heap) (i : Nat) : Prop :=
  ∀ z sb st, h.streams i = some z → z.state = some sb → h.istate sb = some st → st.mode = HEAD → st.bits = 0 →
    st.last = 0 → ∀ z', h'.streams i = some z' → z'.avail_in < z.avail_in

/-- A call of `inflate` from a just reset state of stream `i` (mode `HEAD`, no bits held, not the last block) with
input consumed input. -/
def FreshIn (h h' : Heap) (i : Nat) : Prop :=
  ∀ z sb st, h.streams i = some z → z.state = some sb → h.istate sb = some st → st.mode = HEAD → st.bits = 0 →
    st.last = 0 → z.avail_in ≠ 0 → ∀ z', h'.streams i = some z' → z'.avail_in < z.avail_in

/-- The codes `inflate` returns. -/
def InfRes (r : Int32) : Prop :=
  r = Z_OK ∨ r = Z_STREAM_END ∨ r = Z_NEED_DICT ∨ r = Z_BUF_ERROR ∨ r = Z_DATA_ERROR ∨ r = Z_STREAM_ERROR

/-- `inflate_ok'` with the result codes (`InfRes`), the exact accounting (`IoRes`) for every code but
`Z_STREAM_ERROR`, and for every code when the entry check passes (`EntryOK`), the message (`MsgRes`), that
`Z_STREAM_END` from a just reset state consumed input (`FreshEnd`), and that every code but `Z_STREAM_ERROR` from a
just reset state with input consumed input (`FreshIn`). -/
theorem inflate_full3 {h : Heap} {i : Nat} (flush : Int32) (hv : Inv h (some i)) (hio : StreamIO h (some i))
    (hc : h.crcTable = ZlibNg.Crc32Tbl.crc_table) :
    Sat h (ZlibNg.Inflate.inflate (some i) flush) (fun r h' => Inv h' (some i) ∧
      Frame h h' [i] (stateIds h (some i)) (headerIds h (some i)) (outputRanges h (some i)) ∧
      (r = Z_OK → Progress h h' i) ∧
      (∀ z, h.streams i = some z → ∃ z', h'.streams i = some z' ∧ z'.state = z.state) ∧
      (∀ hq, RegisteredHeader h' (some i) hq → RegisteredHeader h (some i) hq) ∧
      (r = Z_BUF_ERROR → flush ≠ Z_FINISH → flush ≠ Z_BLOCK → flush ≠ Z_TREES → BufStall h h' i) ∧
      (r ≠ Z_STREAM_ERROR ∨ EntryOK h i → IoRes h h' i) ∧ InfRes r ∧ MsgRes h h' i ∧
      (r = Z_STREAM_END → FreshEnd h h' i) ∧ (r ≠ Z_STREAM_ERROR → FreshIn h h' i)) := by
  have hv' := hv
  obtain ⟨i', z, b, st, al, e, hz, hb, hst, hal, c⟩ := hv'
  cases e
  obtain ⟨z1, b1, hp, ⟨i2, e2, hz1⟩, hb1, ⟨b3, st3, ⟨z3, ⟨i3, e3, hz3⟩, hb3⟩, hst3, hhead⟩, hok, hin, hout, hdisj,
    hnb⟩ := hio
  cases e2; cases e3
  rw [hz] at hz1 hz3; cases hz1; cases hz3
  rw [hb] at hb1 hb3; cases hb1; cases hb3
  rw [hst] at hst3; cases hst3
  have hsid := InflateReach.stateIds_of hz hb
  have hW := outputRanges_eq hz hb hst hhead
  unfold ZlibNg.Inflate.inflate
  refine Sat.bind (Sat.of_eq (InflateInv.stateCheck (h := h) ⟨i, z, b, st, al, rfl, hz, hb, hst, hal, c⟩) ?_)
  dsimp only
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine Sat.bind (Sat.of_eq (InflateInv.ldStream_app hz) ?_)
  have hfr0 : ∀ H1, Touch h H1 i b → Frame h H1 [i] (stateIds h (some i)) (headerIds h (some i))
      (outputRanges h (some i)) := fun H1 t => by rw [hsid]; exact touchFrame t _ _
  split
  · rename_i hchk0
    exact Sat.pure ⟨hv, hfr0 h (Touch.refl h i b), fun e => absurd e (by decide), fun z0 h0 => ⟨z0, h0, rfl⟩,
      fun _ hq => hq, fun e => absurd e (by decide), fun e => by
        rcases e with e | e
        · exact absurd rfl e
        · obtain ⟨h1, h2⟩ := e z hz
          exfalso; revert hchk0
          rcases h2 with h2 | h2 <;> simp [h1, h2],
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))), fun z0 h0 => ⟨z0, h0, Or.inl rfl⟩,
      fun e => absurd e (by decide), fun e => absurd rfl e⟩
  rename_i hchk
  have hno : z.next_out ≠ .null := by
    intro e; simp [e] at hchk
  have hni : z.next_in = .null → z.avail_in = 0 := by
    intro e; simp [e] at hchk; exact hchk.2
  rw [hb]
  refine Sat.bind (Sat.of_eq (show rdS (some b) (·.mode) h = .ok (st.mode, h) by
    simp [rdS, bind_app, InflateInv.ldState_app hst]) ?_)
  have tail : ∀ (H1 : Heap) (S1 : InflateState), Inv H1 (some i) → H1.streams i = some z → H1.istate b = some S1 →
      S1.head = .val hp → H1.bytes = h.bytes → H1.gzheaders = h.gzheaders → H1.crcTable = h.crcTable →
      H1.consts = h.consts → Touch h H1 i b →
      (st.mode = HEAD → st.bits = 0 → st.last = 0 → ∀ S0, H1.istate b = some S0 →
        (S0.mode = HEAD ∨ S0.mode = TYPEDO) ∧ S0.bits = 0 ∧ S0.last = 0) →
      Sat H1 (do
        let g ← uninitLocals 0
        let __x ← (ExceptT.run (do
            LOAD ({ strm := some i, st := some b, flush := flush } : Ctx)
            modify fun l => { l with in_ := l.have_, out := l.left, ret := Z_OK }
            let r ← tryCatch (do
                xloopBrk (do
                  dispatch ({ strm := some i, st := some b, flush := flush } : Ctx)
                  pure false)
                pure none)
              (fun e => match e with
                | Ex.leave => pure none
                | Ex.ret v => pure (some v))
            match r with
            | some v => pure v
            | none => infLeave ({ strm := some i, st := some b, flush := flush } : Ctx))).run (IL.init g)
        match __x.fst with
        | Except.ok v => pure v
        | Except.error (Ex.ret v) => pure v
        | Except.error Ex.leave => ub "unreachable: inf_leave outside inflate")
        (fun r h' => Inv h' (some i) ∧
          Frame h h' [i] (stateIds h (some i)) (headerIds h (some i)) (outputRanges h (some i)) ∧
          (r = Z_OK → Progress h h' i) ∧
          (∀ z0, h.streams i = some z0 → ∃ z', h'.streams i = some z' ∧ z'.state = z0.state) ∧
          (∀ hq, RegisteredHeader h' (some i) hq → RegisteredHeader h (some i) hq) ∧
          (r = Z_BUF_ERROR → flush ≠ Z_FINISH → flush ≠ Z_BLOCK → flush ≠ Z_TREES → BufStall h h' i) ∧
          (r ≠ Z_STREAM_ERROR ∨ EntryOK h i → IoRes h h' i) ∧ InfRes r ∧ MsgRes h h' i ∧
          (r = Z_STREAM_END → FreshEnd h h' i) ∧ (r ≠ Z_STREAM_ERROR → FreshIn h h' i)) := by
    intro H1 S1 hv1 hz1 hs1 hh1 hB hG hC hK ht hF
    obtain ⟨bo, oo, hpo, eo⟩ := envOK_of (H1 := H1) flush hz hb hst hhead hok hin hout hdisj hnb hno hni hc hB hG hC hK
    obtain ⟨al1, -, c1⟩ : ∃ al, H1.iallocsOf b = some al ∧ Core H1 (some i) z b (view S1) al := by
      obtain ⟨i', z', b', st', al', e, hz', hb', hst', hal', c'⟩ := hv1
      cases e; rw [hz1] at hz'; cases hz'; rw [hb] at hb'; cases hb'; rw [hs1] at hst'; cases hst'
      exact ⟨al', hal', c'⟩
    refine Sat.bind (Sat.of_eq (show uninitLocals 0 H1 = .ok (_, H1) from rfl) ?_)
    refine Sat.bind (Sat.mono (P := fun p H' => (∃ v, p.1 = Except.ok v ∧
      (v = Z_OK → InflateLeave.Prog ⟨H1, i, b, flush, z.next_in, z.avail_in, bo, oo, z.avail_out, hp, headerIds h (some i),
        outputRanges h (some i)⟩ H') ∧
      (v = Z_BUF_ERROR → flush ≠ Z_FINISH → flush ≠ Z_BLOCK → flush ≠ Z_TREES →
        InflateLeave.BufOut ⟨H1, i, b, flush, z.next_in, z.avail_in, bo, oo, z.avail_out, hp, headerIds h (some i),
          outputRanges h (some i)⟩ H') ∧
      ResAcc ⟨H1, i, b, flush, z.next_in, z.avail_in, bo, oo, z.avail_out, hp, headerIds h (some i),
          outputRanges h (some i)⟩ v H' ∧
      (v = Z_STREAM_END → InflateLeave.EndIn ⟨H1, i, b, flush, z.next_in, z.avail_in, bo, oo, z.avail_out, hp,
          headerIds h (some i), outputRanges h (some i)⟩ H') ∧
      (v ≠ Z_STREAM_ERROR → InFr ⟨H1, i, b, flush, z.next_in, z.avail_in, bo, oo, z.avail_out, hp,
          headerIds h (some i), outputRanges h (some i)⟩ H')) ∧
      Fin ⟨H1, i, b, flush, z.next_in, z.avail_in, bo, oo, z.avail_out, hp, headerIds h (some i),
        outputRanges h (some i)⟩ H') ?_ ?_)
    · show SatX H1 _ _ (fun r _ H' => (∃ v, r = Except.ok v ∧
        (v = Z_OK → InflateLeave.Prog ⟨H1, i, b, flush, z.next_in, z.avail_in, bo, oo, z.avail_out, hp,
          headerIds h (some i), outputRanges h (some i)⟩ H') ∧
        (v = Z_BUF_ERROR → flush ≠ Z_FINISH → flush ≠ Z_BLOCK → flush ≠ Z_TREES →
          InflateLeave.BufOut ⟨H1, i, b, flush, z.next_in, z.avail_in, bo, oo, z.avail_out, hp,
            headerIds h (some i), outputRanges h (some i)⟩ H') ∧
        ResAcc ⟨H1, i, b, flush, z.next_in, z.avail_in, bo, oo, z.avail_out, hp, headerIds h (some i),
          outputRanges h (some i)⟩ v H' ∧
        (v = Z_STREAM_END → InflateLeave.EndIn ⟨H1, i, b, flush, z.next_in, z.avail_in, bo, oo, z.avail_out, hp,
            headerIds h (some i), outputRanges h (some i)⟩ H') ∧
        (v ≠ Z_STREAM_ERROR → InFr ⟨H1, i, b, flush, z.next_in, z.avail_in, bo, oo, z.avail_out, hp,
            headerIds h (some i), outputRanges h (some i)⟩ H')) ∧
        Fin ⟨H1, i, b, flush, z.next_in, z.avail_in, bo, oo, z.avail_out, hp, headerIds h (some i),
          outputRanges h (some i)⟩ H')
      refine SatX.bind ?_
      unfold LOAD
      refine SatX.bind (SatX.lift_eq (InflateInv.ldStream_app hz1) ?_)
      refine SatX.bind (SatX.lift_eq (InflateInv.ldState_app hs1) ?_)
      refine SatX.modify ?_
      refine SatX.bind (SatX.modify ?_)
      refine loopPart_ok _ eo (z := z) (S := S1) ?_
      refine ⟨hv1, touchFrame (Touch.refl H1 i b) _ _, SizeKeep.refl _ _, hz1, hb, hs1, hh1, ?_, ?_, ?_, ?_, rfl,
        Or.inl rfl, Or.inl rfl, ?_, fun z0 h0 => Or.inl (by rw [hz1] at h0; cases h0; rfl), fun hf _ => by
          obtain ⟨hm0, hb0, hl0⟩ := hf S1 hs1
          exact ⟨by show S1.bits.toUInt8 = 0; rw [hb0]; rfl, hl0, hm0,
            by show Z_OK ≠ Z_STREAM_END; decide⟩⟩
      · show HdrOK H1 H1 hp
        unfold HdrOK
        rcases hok with e | ⟨k, g, e, hg, -⟩
        · subst e; trivial
        · subst e
          have hg1 : H1.gzheaders k = some g := by rw [hG]; exact hg
          exact ⟨g, g, hg1, hg1, Or.inl rfl, rfl, Or.inl rfl, rfl, Or.inl rfl, rfl⟩
      · refine ⟨UInt32.le_refl _, ?_⟩
        show match z.next_in with
          | .null => z.next_in = .null ∧ z.avail_in = 0
          | .ref r o => z.next_in = .ref r (o + (z.avail_in - z.avail_in).toNat)
        rcases hn : z.next_in with _ | ⟨r, o⟩
        · exact ⟨rfl, hni hn⟩
        · simp
      · refine ⟨UInt32.le_refl _, oo, Nat.le_refl _, rfl, ?_⟩
        show z.next_out = _
        rw [hpo]; simp
      · show S1.bits.toUInt8 ≤ 39
        have hb39 : S1.bits ≤ 39 := c1.bits
        have : S1.bits.toNat ≤ 39 := hb39
        rw [UInt8.le_iff_toNat_le, UInt32.toNat_toUInt8, Nat.mod_eq_of_lt (by omega)]; exact this
      · refine ⟨⟨UInt32.le_refl _, ?_⟩, UInt32.le_refl _, ?_⟩
        · show match z.next_in with
            | .null => z.next_in = .null ∧ z.avail_in = 0
            | .ref r o => z.next_in = .ref r (o + (z.avail_in - z.avail_in).toNat)
          rcases hn : z.next_in with _ | ⟨r, o⟩
          · exact ⟨rfl, hni hn⟩
          · simp
        · show z.next_out = _
          rw [hpo]; simp
    · rintro ⟨r, l'⟩ H' ⟨⟨v, hr, hpg, hbg, hra, hend, hinf⟩, hf⟩
      dsimp only at hr
      subst hr
      refine Sat.pure ⟨hf.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hsid]
        have f1 := touchFrame ht (headerIds h (some i)) (outputRanges h (some i))
        exact Frame.trans f1 hf.2.1
      · intro hv0 z0 b0 S0 hz0 hb0 hs0
        rw [hz] at hz0; cases hz0
        rw [hb] at hb0; cases hb0
        rw [hst] at hs0; cases hs0
        obtain ⟨z', S', e1, e2, e3, e4, e5, ⟨e6, p, e7, e8, e9⟩, e10⟩ := hpg hv0
        exact ⟨z', S', e1, e2, e3, e4.trans hhead.symm, e5, ⟨e6, bo, oo, p, hpo, e7, e8, e9⟩, e10⟩
      · intro z0 hz0
        rw [hz] at hz0; cases hz0
        obtain ⟨z', -, e1, e2, -, -⟩ := hf.2.2
        exact ⟨z', e1, e2.trans hb.symm⟩
      · rintro hq ⟨b', st', ⟨z'', ⟨i', ei, hz''⟩, hb''⟩, hst', hh'⟩
        cases ei
        obtain ⟨z', S', e1, e2, e3, e4⟩ := hf.2.2
        rw [e1] at hz''; cases hz''
        rw [e2] at hb''; cases hb''
        rw [e3] at hst'; cases hst'
        rw [e4] at hh'; cases hh'
        exact ⟨b, st, ⟨z, ⟨i, rfl, hz⟩, hb⟩, hst, hhead⟩
      · intro hv0 hf1 hf2 hf3 z0 hz0
        rw [hz] at hz0; cases hz0
        exact hbg hv0 hf1 hf2 hf3
      · intro _ z0 hz0
        rw [hz] at hz0; cases hz0
        obtain ⟨-, z', e1, ⟨e2, e3, e4⟩, -⟩ := hra
        obtain ⟨z'', -, e5, e6, -, -⟩ := hf.2.2
        rw [e1] at e5; cases e5
        exact ⟨z', e1, e6.trans hb.symm, e2, e3, bo, oo, hpo, e4⟩
      · exact hra.1
      · intro z0 hz0
        rw [hz] at hz0; cases hz0
        obtain ⟨-, z', e1, -, e5⟩ := hra
        exact ⟨z', e1, e5 z hz1⟩
      · intro hv0 z0 sb st0 hz0 hsb hst0 hm0 hb0 hl0 z' hz'
        rw [hz] at hz0; cases hz0
        rw [hb] at hsb; cases hsb
        rw [hst] at hst0; cases hst0
        obtain ⟨z'', e1, e2⟩ := hend hv0 (hF hm0 hb0 hl0)
        rw [e1] at hz'; cases hz'
        exact e2
      · intro hv0 z0 sb st0 hz0 hsb hst0 hm0 hb0 hl0 hA z' hz'
        rw [hz] at hz0; cases hz0
        rw [hb] at hsb; cases hsb
        rw [hst] at hst0; cases hst0
        obtain ⟨z'', e1, e2⟩ := hinf hv0 (hF hm0 hb0 hl0) hA
        rw [e1] at hz'; cases hz'
        exact e2
  split
  · obtain ⟨e, hv1⟩ := InflateInv.wrS (h := h) (s := some i) hv (fun s => { s with mode := TYPEDO }) ⟨z, ⟨i, rfl, hz⟩, hb⟩
      hst (fun _ _ c => { c with
        mode_lo := by show HEAD ≤ TYPEDO; decide
        mode_hi := by show TYPEDO ≤ SYNC; decide
        modes := InflateInv.ModeOK.quiet _ _ (Or.inl (show TYPEDO < LENLENS by decide)) })
    refine Sat.bind (Sat.of_eq e ?_)
    rename_i hT
    refine tail _ { st with mode := TYPEDO } hv1 hz (InflateLoop.istate_withS hst _) hhead rfl rfl rfl rfl
      ⟨rfl, fun _ _ => rfl, fun c hc => upd_ne _ _ _ _ hc, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ fun hm0 => by
        rw [hm0] at hT; exact absurd hT (by decide)
  · exact tail h st hv hz hst hhead rfl rfl rfl rfl (Touch.refl h i b) fun hm0 hb0 hl0 S0 hS0 => by
      rw [hst] at hS0; cases hS0; exact ⟨Or.inl hm0, hb0, hl0⟩

/-- `inflate_full3` without `FreshIn`. -/
theorem inflate_full2 {h : Heap} {i : Nat} (flush : Int32) (hv : Inv h (some i)) (hio : StreamIO h (some i))
    (hc : h.crcTable = ZlibNg.Crc32Tbl.crc_table) :
    Sat h (ZlibNg.Inflate.inflate (some i) flush) (fun r h' => Inv h' (some i) ∧
      Frame h h' [i] (stateIds h (some i)) (headerIds h (some i)) (outputRanges h (some i)) ∧
      (r = Z_OK → Progress h h' i) ∧
      (∀ z, h.streams i = some z → ∃ z', h'.streams i = some z' ∧ z'.state = z.state) ∧
      (∀ hq, RegisteredHeader h' (some i) hq → RegisteredHeader h (some i) hq) ∧
      (r = Z_BUF_ERROR → flush ≠ Z_FINISH → flush ≠ Z_BLOCK → flush ≠ Z_TREES → BufStall h h' i) ∧
      (r ≠ Z_STREAM_ERROR ∨ EntryOK h i → IoRes h h' i) ∧ InfRes r ∧ MsgRes h h' i ∧
      (r = Z_STREAM_END → FreshEnd h h' i)) :=
  Sat.mono (inflate_full3 flush hv hio hc) (fun _ _ q =>
    ⟨q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2.1, q.2.2.2.2.2.1, q.2.2.2.2.2.2.1, q.2.2.2.2.2.2.2.1,
      q.2.2.2.2.2.2.2.2.1, q.2.2.2.2.2.2.2.2.2.1⟩)

/-- `inflate_full2` without `FreshEnd`. -/
theorem inflate_full {h : Heap} {i : Nat} (flush : Int32) (hv : Inv h (some i)) (hio : StreamIO h (some i))
    (hc : h.crcTable = ZlibNg.Crc32Tbl.crc_table) :
    Sat h (ZlibNg.Inflate.inflate (some i) flush) (fun r h' => Inv h' (some i) ∧
      Frame h h' [i] (stateIds h (some i)) (headerIds h (some i)) (outputRanges h (some i)) ∧
      (r = Z_OK → Progress h h' i) ∧
      (∀ z, h.streams i = some z → ∃ z', h'.streams i = some z' ∧ z'.state = z.state) ∧
      (∀ hq, RegisteredHeader h' (some i) hq → RegisteredHeader h (some i) hq) ∧
      (r = Z_BUF_ERROR → flush ≠ Z_FINISH → flush ≠ Z_BLOCK → flush ≠ Z_TREES → BufStall h h' i) ∧
      (r ≠ Z_STREAM_ERROR ∨ EntryOK h i → IoRes h h' i) ∧ InfRes r ∧ MsgRes h h' i) :=
  Sat.mono (inflate_full2 flush hv hio hc) (fun _ _ q =>
    ⟨q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2.1, q.2.2.2.2.2.1, q.2.2.2.2.2.2.1, q.2.2.2.2.2.2.2.1,
      q.2.2.2.2.2.2.2.2.1⟩)

/-- `inflate_ok` with the meaning of `Z_BUF_ERROR` (`BufStall`). -/
theorem inflate_ok' {h : Heap} {i : Nat} (flush : Int32) (hv : Inv h (some i)) (hio : StreamIO h (some i))
    (hc : h.crcTable = ZlibNg.Crc32Tbl.crc_table) :
    Sat h (ZlibNg.Inflate.inflate (some i) flush) (fun r h' => Inv h' (some i) ∧
      Frame h h' [i] (stateIds h (some i)) (headerIds h (some i)) (outputRanges h (some i)) ∧
      (r = Z_OK → Progress h h' i) ∧
      (∀ z, h.streams i = some z → ∃ z', h'.streams i = some z' ∧ z'.state = z.state) ∧
      (∀ hq, RegisteredHeader h' (some i) hq → RegisteredHeader h (some i) hq) ∧
      (r = Z_BUF_ERROR → flush ≠ Z_FINISH → flush ≠ Z_BLOCK → flush ≠ Z_TREES → BufStall h h' i)) :=
  Sat.mono (inflate_full flush hv hio hc)
    (fun _ _ q => ⟨q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2.1, q.2.2.2.2.2.1⟩)

theorem inflate_ok {h : Heap} {i : Nat} (flush : Int32) (hv : Inv h (some i)) (hio : StreamIO h (some i))
    (hc : h.crcTable = ZlibNg.Crc32Tbl.crc_table) :
    Sat h (ZlibNg.Inflate.inflate (some i) flush) (fun r h' => Inv h' (some i) ∧
      Frame h h' [i] (stateIds h (some i)) (headerIds h (some i)) (outputRanges h (some i)) ∧
      (r = Z_OK → Progress h h' i) ∧
      (∀ z, h.streams i = some z → ∃ z', h'.streams i = some z' ∧ z'.state = z.state) ∧
      ∀ hq, RegisteredHeader h' (some i) hq → RegisteredHeader h (some i) hq) :=
  Sat.mono (inflate_ok' flush hv hio hc) (fun _ _ q => ⟨q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2.1⟩)

theorem frame_refl (h : Heap) (S B G : List Nat) (W : List (BPtr × Nat)) : Frame h h S B G W :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => ⟨rfl, rfl⟩, fun _ _ _ d hd => ⟨d, hd, rfl, fun _ _ _ => rfl⟩,
    fun _ _ _ hd => hd, rfl, rfl, rfl, rfl, Nat.le_refl _⟩

/-- **`inflate` keeps the structural invariant** (the field of `Pending`). -/
theorem pending : InflateReach.Pending := by
  refine ⟨fun h h' s flush r hv hcg hio e => ?_⟩
  have hv' := hv
  obtain ⟨i, -, -, -, -, rfl, -⟩ := hv'
  obtain ⟨r2, h2, e2, hi, -⟩ := inflate_ok flush hv hio hcg.1
  rw [InflateReach.det e e2]
  exact hi

/-- A stream that `inflateStateCheck` rejects: `inflate` returns `Z_STREAM_ERROR` and changes nothing. -/
theorem inflate_rejected {h : Heap} {s : StreamPtr} (flush : Int32)
    (hc : C.run (inflateStateCheck s) h = .ok (true, h)) :
    C.run (ZlibNg.Inflate.inflate s flush) h = .ok (Z_STREAM_ERROR, h) := by
  unfold C.run at hc ⊢
  simp only [ZlibNg.Inflate.inflate, bind_app, hc, ↓reduceIte]
  rfl

open ZlibNgF.Spec.Safety in
/-- **`inflate` is safe** on every stream `zlib.h` lets a program pass: no fault, and only the stream record, the
library's block, the registered header and the output and header buffers change. -/
theorem inflate_safety : Goal.inflate_safety := by
  intro h s flush hcg hh hio
  refine InflateKeep.iframe_up (InflateKeep.K.ZlibNg.Inflate.inflate _ _) ?_
  rcases hh with rfl | ⟨z, hz, hs⟩ | hr
  · exact ⟨_, _, inflate_rejected flush (InflateInv.stateCheck_none h), frame_refl ..⟩
  · exact ⟨_, _, inflate_rejected flush (InflateInv.stateCheck_closed h s z hz hs), frame_refl ..⟩
  · have hv := InflateReach.reach_inv pending hr
    obtain ⟨i, -, -, -, -, rfl, -⟩ := id hv
    obtain ⟨r, h', e, -, hf, -⟩ := inflate_ok flush hv (hio hr) hcg.1
    exact ⟨r, h', e, hf⟩

open ZlibNgF.Spec.Safety

theorem inflateMark_safety : Goal.inflateMark_safety := InflateReach.inflateMark_safety_of pending
theorem inflateSyncPoint_safety : Goal.inflateSyncPoint_safety := InflateReach.inflateSyncPoint_safety_of pending
theorem inflateCodesUsed_safety : Goal.inflateCodesUsed_safety := InflateReach.inflateCodesUsed_safety_of pending
theorem inflateValidate_safety : Goal.inflateValidate_safety := InflateReach.inflateValidate_safety_of pending
theorem inflateGetHeader_safety : Goal.inflateGetHeader_safety := InflateReach.inflateGetHeader_safety_of pending
theorem inflateEnd_safety : Goal.inflateEnd_safety := InflateReach.inflateEnd_safety_of pending
theorem inflateResetKeep_safety : Goal.inflateResetKeep_safety := InflateReach.inflateResetKeep_safety_of pending
theorem inflateReset_safety : Goal.inflateReset_safety := InflateReach.inflateReset_safety_of pending
theorem inflateReset2_safety : Goal.inflateReset2_safety := InflateReach.inflateReset2_safety_of pending
theorem inflatePrime_safety : Goal.inflatePrime_safety := InflateReach.inflatePrime_safety_of pending
theorem inflateSetDictionary_safety : Goal.inflateSetDictionary_safety :=
  InflateReach.inflateSetDictionary_safety_of pending
theorem inflateGetDictionary_safety : Goal.inflateGetDictionary_safety :=
  InflateReach.inflateGetDictionary_safety_of pending
theorem inflateSync_safety : Goal.inflateSync_safety := InflateReach.inflateSync_safety_of pending
theorem inflateCopy_safety : Goal.inflateCopy_safety := InflateReach.inflateCopy_safety_of pending

end ZlibNgF.Proof.InflateTop
