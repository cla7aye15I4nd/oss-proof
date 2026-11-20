import ZlibNgF.Proof.«inflate.c.loop»
import ZlibNgF.Proof.«public-crc32»

/-!
# Statements of `inflate`'s modes on a state with the loop invariant (`ZlibNgF`)

Frames compose; a store into the state or the stream record that keeps the invariant keeps `LI`; reads of the state
and the stream; the bit-buffer macros `NEEDBITS`, `BITS`, `DROPBITS`, `INITBITS`, `BYTEBITS` on the locals.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InflateLoop
open C ZlibNgF.Spec ZlibNg.Inflate
open ZlibNgF.Proof.InflateInv (Inv Core view)
open ZlibNgF.Proof.InflateX
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.mono Sat.of_eq St Touch)

/-! ## Frames -/

theorem Frame.trans {h1 h2 h3 : Heap} {S B G : List Nat} {W : List (BPtr × Nat)} (f : Frame h1 h2 S B G W)
    (g : Frame h2 h3 S B G W) : Frame h1 h3 S B G W := by
  obtain ⟨s1, g1, i1, b1, n1, c1, r1, x1, a1, k1⟩ := f
  obtain ⟨s2, g2, i2, b2, n2, c2, r2, x2, a2, k2⟩ := g
  refine ⟨fun j hj => (s2 j hj).trans (s1 j hj), fun j hj => (g2 j hj).trans (g1 j hj),
    fun c hc hn => ⟨((i2 c (by omega) hn).1).trans (i1 c hc hn).1, ((i2 c (by omega) hn).2).trans (i1 c hc hn).2⟩,
    fun c hc hn data hd => ?_, fun c hc hn hd => n2 c (by omega) hn (n1 c hc hn hd), c2.trans c1, r2.trans r1,
    x2.trans x1, a2.trans a1, Nat.le_trans k1 k2⟩
  obtain ⟨d2, e2, s2', q2⟩ := b1 c hc hn data hd
  obtain ⟨d3, e3, s3, q3⟩ := b2 c (by omega) hn d2 e2
  exact ⟨d3, e3, s3.trans s2', fun j hj hw => (q3 j (by omega) hw).trans (q2 j hj hw)⟩

theorem Frame.mono {h h' : Heap} {S B G S' B' G' : List Nat} {W W' : List (BPtr × Nat)} (f : Frame h h' S B G W)
    (hS : ∀ x, x ∈ S → x ∈ S') (hB : ∀ x, x ∈ B → x ∈ B') (hG : ∀ x, x ∈ G → x ∈ G') (hW : ∀ x, x ∈ W → x ∈ W') :
    Frame h h' S' B' G' W' := by
  obtain ⟨s1, g1, i1, b1, n1, c1, r1, x1, a1, k1⟩ := f
  refine ⟨fun j hj => s1 j (fun m => hj (hS j m)), fun j hj => g1 j (fun m => hj (hG j m)),
    fun c hc hn => i1 c hc (fun m => hn (hB c m)), fun c hc hn data hd => ?_,
    fun c hc hn hd => n1 c hc (fun m => hn (hB c m)) hd, c1, r1, x1, a1, k1⟩
  obtain ⟨d2, e2, s2, q2⟩ := b1 c hc (fun m => hn (hB c m)) data hd
  exact ⟨d2, e2, s2, fun j hj hw => q2 j hj (fun w hw' => hw w (hW w hw'))⟩

theorem touchFrame {h h' : Heap} {i b : Nat} (t : Touch h h' i b) (G : List Nat) (W : List (BPtr × Nat)) :
    Frame h h' [i] [b] G W :=
  Frame.mono t.frame (fun _ m => m) (fun _ m => m) (fun _ m => nomatch m) (fun _ m => nomatch m)

/-! ## Stores and reads -/

theorem LI.st {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (li : LI E l H z S) :
    St H H E.i E.b z S := ⟨li.inv, Touch.refl H E.i E.b, li.hz, li.hb, li.hs⟩

theorem LI.of_touch {E : Env} {l : IL} {H H' : Heap} {z z' : ZStream} {S S' : InflateState} (li : LI E l H z S)
    (t : St H H' E.i E.b z' S') (hh : S'.head = S.head) (ho : l.out = E.O0 ∨ (rank S.mode ≤ 2 → rank S'.mode ≤ 2))
    (hsa : SAcc E z') (hmk : MsgK E z') (hfr : Fr E l S → Fr E l S') :
    LI E l H' z' S' :=
  { li with
    sacc := hsa
    msgK := hmk
    fr := hfr li.fr
    outO := ho.elim Or.inl fun h => li.outO.imp_right h
    inv := t.inv
    frame := Frame.trans li.frame (touchFrame t.touch _ _)
    sz := li.sz.trans ⟨fun c _ d hd => ⟨d, by rw [t.touch.bytes]; exact hd, rfl⟩, t.touch.consts⟩
    hz := t.hz
    hb := t.hb
    hs := t.hs
    head := hh.trans li.head
    hdr := by
      have hg := t.touch.gz
      have hd := li.hdr
      unfold HdrOK at hd ⊢
      rw [hg]; exact hd }

/-- A store into the state that keeps every clause of the invariant and the header field keeps `LI`. -/
theorem LI.wrS {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (li : LI E l H z S)
    (f : InflateState → InflateState)
    (keep : ∀ al z, Core H (some E.i) z E.b (view S) al → Core H (some E.i) z E.b (view (f S)) al)
    (hh : (f S).head = S.head) (hm : l.out = E.O0 ∨ (rank S.mode ≤ 2 → rank (f S).mode ≤ 2) := by exact Or.inr id)
    (hfr : Fr E l S → Fr E l (f S) := by frt) :
    Sat H (ZlibNg.Inflate.wrS (some E.b) f) (fun _ H' => LI E l H' z (f S)) :=
  Sat.mono (InflateSync.step_S li.st f keep) (fun _ _ t => li.of_touch t hh hm li.sacc li.msgK hfr)

/-- `LI.wrS` that also records that the bytes and the headers stay. -/
theorem LI.wrST {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (li : LI E l H z S)
    (f : InflateState → InflateState)
    (keep : ∀ al z, Core H (some E.i) z E.b (view S) al → Core H (some E.i) z E.b (view (f S)) al)
    (hh : (f S).head = S.head) (hm : l.out = E.O0 ∨ (rank S.mode ≤ 2 → rank (f S).mode ≤ 2) := by exact Or.inr id)
    (hfr : Fr E l S → Fr E l (f S) := by frt) :
    Sat H (ZlibNg.Inflate.wrS (some E.b) f) (fun _ H' => LI E l H' z (f S) ∧ H'.bytes = H.bytes ∧
      H'.gzheaders = H.gzheaders) :=
  Sat.mono (InflateSync.step_S li.st f keep)
    (fun _ _ t => ⟨li.of_touch t hh hm li.sacc li.msgK hfr, t.touch.bytes, t.touch.gz⟩)

/-- A store into the stream record with the accounting of the call that keeps `state`, `zalloc`, `zfree` keeps
`LI`. -/
theorem LI.wrZio {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (li : LI E l H z S)
    (f : ZStream → ZStream) (e1 : (f z).state = z.state) (e2 : (f z).zalloc = z.zalloc)
    (e3 : (f z).zfree = z.zfree) (hsa : SAcc E (f z)) (hmk : MsgK E (f z)) :
    Sat H (wrZ (some E.i) f) (fun _ H' => LI E l H' (f z) S) :=
  Sat.mono (InflateSync.step_Z li.st f e1 e2 e3) (fun _ _ t => li.of_touch t rfl (Or.inr id) hsa hmk id)

/-- A store into the stream record that keeps `state`, `zalloc`, `zfree` and the buffer fields keeps `LI`. -/
theorem LI.wrZ {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (li : LI E l H z S)
    (f : ZStream → ZStream) (e1 : (f z).state = z.state) (e2 : (f z).zalloc = z.zalloc)
    (e3 : (f z).zfree = z.zfree) (e4 : (f z).next_in = z.next_in := by rfl)
    (e5 : (f z).avail_in = z.avail_in := by rfl) (e6 : (f z).next_out = z.next_out := by rfl)
    (e7 : (f z).avail_out = z.avail_out := by rfl) (e8 : (f z).msg = z.msg := by rfl) :
    Sat H (wrZ (some E.i) f) (fun _ H' => LI E l H' (f z) S) := by
  refine li.wrZio f e1 e2 e3 ?_ (fun z0 h0 => by rw [e8]; exact li.msgK z0 h0)
  have h := li.sacc
  unfold SAcc at h ⊢
  rw [e4, e5, e6, e7]; exact h

theorem LI.rdS {α : Type} {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (li : LI E l H z S)
    (g : InflateState → α) : (ZlibNg.Inflate.rdS (some E.b) g) H = .ok (g S, H) := by
  simp [ZlibNg.Inflate.rdS, bind_app, InflateInv.ldState_app li.hs]

theorem LI.ldState {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (li : LI E l H z S) :
    (C.ldState (some E.b)) H = .ok (S, H) := InflateInv.ldState_app li.hs

theorem LI.ldStream {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (li : LI E l H z S) :
    (C.ldStream (some E.i)) H = .ok (z, H) := InflateInv.ldStream_app li.hz

/-- A lifted computation that returns `a` and leaves the heap unchanged. -/
theorem SatX.lift_eq {α : Type} {H : Heap} {l : IL} {m : M α} {a : α} {Q : Except Ex α → IL → Heap → Prop}
    (e : m H = .ok (a, H)) (q : Q (.ok a) l H) : SatX H l (MonadLiftT.monadLift m : X α) Q :=
  SatX.lift (Sat.of_eq e q)

/-- The mode of a state with the invariant is in `HEAD .. SYNC`. -/
theorem LI.core {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (li : LI E l H z S) :
    ∃ al, H.iallocsOf E.b = some al ∧ Core H (some E.i) z E.b (view S) al :=
  (li.st.live).2

/-- `setMode` to a mode with no mode clauses. -/
theorem LI.setQuiet {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (li : LI E l H z S) (m : UInt32)
    (lo : HEAD ≤ m) (hi : m ≤ SYNC) (q : m < LENLENS ∨ LIT < m)
    (hm : l.out = E.O0 ∨ (rank S.mode ≤ 2 → rank m ≤ 2) := by exact Or.inr fun _ => by decide)
    (hfr : Fr E l S → Fr E l { S with mode := m } := by frt) :
    Sat H (setMode (some E.b) m) (fun _ H' => LI E l H' z { S with mode := m }) :=
  li.wrS (fun s => { s with mode := m }) (fun _ _ c => { c with
    mode_lo := lo
    mode_hi := hi
    modes := InflateInv.ModeOK.quiet _ _ q }) rfl hm hfr


/-! ## Mode statements -/

/-- `LI` for new locals that agree with the old ones on the fields it reads. -/
theorem LI.locals {E : Env} {l l' : IL} {H : Heap} {z : ZStream} {S : InflateState} (li : LI E l H z S)
    (h1 : l'.next = l.next) (h2 : l'.have_ = l.have_) (h3 : l'.put = l.put) (h4 : l'.out = l.out)
    (h5 : l'.left = l.left) (h6 : l'.bits = l.bits) (h7 : l'.in_ = l.in_ := by rfl)
    (h8 : l'.ret = l.ret := by rfl) : LI E l' H z S :=
  ⟨li.inv, li.frame, li.sz, li.hz, li.hb, li.hs, li.head, li.hdr, by rw [h1, h2]; exact li.inAt,
    by rw [h3, h4, h5]; exact li.outAt, by rw [h6]; exact li.bits, by rw [h7]; exact li.inn,
    by rw [h4]; exact li.outO, by rw [h8]; exact li.retB, li.sacc, li.msgK,
    li.fr.mono h2 fun ⟨a, b, c, d⟩ => ⟨h6 ▸ a, b, c, h8 ▸ d⟩⟩

/-- A fresh call in a state without `FrS` has consumed input. -/
theorem LI.frLt {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (li : LI E l H z S)
    (hn : ¬ FrS l S) : Fresh E → l.have_ < E.A0 :=
  li.fr.lt li.inAt.1 hn

/-- `LI` with `ret` set to `Z_OK`, `Z_STREAM_END` or `Z_DATA_ERROR`. -/
theorem LI.setRet {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (li : LI E l H z S) (v : Int32)
    (hv : RetOK v) (hfr : Fr E l S → Fr E { l with ret := v } S := by frt) : LI E { l with ret := v } H z S :=
  { li with retB := hv, fr := hfr li.fr }

/-- In a mode of rank above 2 (every mode before `CHECK`), `out` is the output count at entry. -/
theorem LI.outEq {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (li : LI E l H z S)
    (h : 2 < rank S.mode) : l.out = E.O0 :=
  li.outO.resolve_right (Nat.not_le.mpr h)

/-- A mode statement: from every state with the invariant and `pre`, below the measure bound `m`, the mode runs to
`Post E m`. -/
def ModeRun (E : Env) (f : Ctx → X Unit) (pre : InflateState → Prop) : Prop :=
  ∀ l H z S, LI E l H z S → pre S → ∀ m, μ l S ≤ m → SatX H l (f E.c) (Post E m)

/-- The mode function of `dispatch` for the mode value `m`. -/
def modeFn (m : UInt32) : Ctx → X Unit := fun c =>
  if m == HEAD then inflate_HEAD c
  else if m == FLAGS then inflate_FLAGS c
  else if m == TIME then inflate_TIME c
  else if m == OS then inflate_OS c
  else if m == EXLEN then inflate_EXLEN c
  else if m == EXTRA then inflate_EXTRA c
  else if m == NAME then inflate_NAME c
  else if m == COMMENT then inflate_COMMENT c
  else if m == HCRC then inflate_HCRC c
  else if m == DICTID then inflate_DICTID c
  else if m == DICT then inflate_DICT c
  else if m == TYPE then inflate_TYPE c
  else if m == TYPEDO then inflate_TYPEDO c
  else if m == STORED then inflate_STORED c
  else if m == COPY_ then inflate_COPY_ c
  else if m == COPY then inflate_COPY c
  else if m == TABLE then inflate_TABLE c
  else if m == LENLENS then inflate_LENLENS c
  else if m == CODELENS then inflate_CODELENS c
  else if m == LEN_ then inflate_LEN_ c
  else if m == LEN then inflate_LEN c
  else if m == LENEXT then inflate_LENEXT c
  else if m == DIST then inflate_DIST c
  else if m == DISTEXT then inflate_DISTEXT c
  else if m == MATCH then inflate_MATCH c
  else if m == LIT then inflate_LIT c
  else if m == CHECK then inflate_CHECK c
  else if m == LENGTH then inflate_LENGTH c
  else if m == DONE then inflate_DONE c
  else if m == BAD then inflate_BAD c
  else throw (Ex.ret Z_STREAM_ERROR)

theorem dispatch_eq (c : Ctx) : dispatch c = (do let m ← rdS c.st (·.mode); modeFn m c) := rfl

/-- One trip of the loop from the statements of the modes. -/
theorem trip_of_modes {E : Env} (hm : ∀ M, ModeRun E (modeFn M) (fun S => S.mode = M)) : TripOK E := by
  intro l H z S lh
  rw [dispatch_eq]
  rcases lh with li | ⟨hm0, v, li⟩
  · refine SatX.bind (SatX.lift_eq (li.rdS (·.mode)) ?_)
    exact hm S.mode l H z S li rfl _ (Nat.le_refl _)
  · refine SatX.bind (SatX.lift_eq (li.rdS (·.mode)) ?_)
    rw [hm0]
    show SatX H l (inflate_BAD E.c) (Post E (μ l S))
    unfold inflate_BAD
    refine SatX.bind (SatX.modify ?_)
    have li1 := li.setRet Z_DATA_ERROR (by decide)
    exact SatX.throw ⟨⟨z, S, li1⟩, Why.ret (show Z_DATA_ERROR ≠ Z_OK by decide) (li1.frL (by rw [hm0]; decide))⟩

/-! ## `BAD`, `DONE`, `SYNC` / `MEM` -/

theorem run_BAD (E : Env) : ModeRun E inflate_BAD (·.mode = BAD) := by
  intro l H z S li hm m _
  unfold inflate_BAD
  refine SatX.bind (SatX.modify ?_)
  have li1 := li.setRet Z_DATA_ERROR (by decide)
  exact SatX.throw ⟨⟨z, S, li1⟩, Why.ret (show Z_DATA_ERROR ≠ Z_OK by decide) (li1.frL (by rw [hm]; decide))⟩

theorem run_DONE (E : Env) : ModeRun E inflate_DONE (·.mode = DONE) := by
  intro l H z S li hm m _
  unfold inflate_DONE
  refine SatX.bind (SatX.modify ?_)
  have li1 := li.setRet Z_STREAM_END (by decide) (fun h => h.mono rfl (FrS.no_mode (by rw [hm]; decide)))
  exact SatX.throw ⟨⟨z, S, li1⟩, Why.ret (show Z_STREAM_END ≠ Z_OK by decide) (li1.frLEnd rfl)⟩

/-- A mode value outside the cases of the `switch` (`SYNC`, `MEM`): `return Z_STREAM_ERROR`. -/
theorem run_default (E : Env) (M : UInt32) (hM : M = SYNC ∨ M = 16210) :
    ModeRun E (modeFn M) (fun S => S.mode = M) := by
  intro l H z S li _ m _
  have e : modeFn M E.c = throw (Ex.ret Z_STREAM_ERROR) := by
    rcases hM with rfl | rfl <;> rfl
  rw [e]
  exact SatX.throw ⟨⟨li.inv, li.frame, _, _, li.hz, li.hb, li.hs, li.head⟩, li.ioAcc, Or.inr rfl,
    fun e => absurd e (by decide)⟩

/-! ## The input buffer -/

/-- A header buffer `p` of `n` bytes in heap `H`: `NULL`, or `n` writable bytes of a heap block other than the state's
block, a write range of the call, disjoint from the input. -/
def HBuf (E : Env) (H : Heap) (p : BPtr) (n : Nat) : Prop :=
  p = .null ∨ ∃ bd off data, p = .ref (.heap bd) off ∧ H.bytes bd = some data ∧ off + n ≤ data.size ∧
    bd ≠ E.b ∧ (p, n) ∈ E.W ∧ Disjoint E.inp E.A0.toNat p n

/-- What the caller's buffers give at entry (`StreamIO`, `inflate`'s own checks). -/
structure EnvOK (E : Env) : Prop where
  crc : E.H0.crcTable = ZlibNg.Crc32Tbl.crc_table
  hdrG : ∀ k, E.hp = some k → k ∈ E.G
  inRd : NullOrRead E.H0 E.inp E.A0.toNat
  inNull : E.inp = .null → E.A0 = 0
  inNB : NotInBlock E.b E.inp
  hdrBuf : ∀ k g0, E.hp = some k → E.H0.gzheaders k = some g0 →
    HBuf E E.H0 g0.extra g0.extra_max.toNat ∧ HBuf E E.H0 g0.name g0.name_max.toNat ∧
    HBuf E E.H0 g0.comment g0.comm_max.toNat
  /-- the output buffer `[oo, oo + O0)` of heap block `bo`: writable, outside the state's block, a write range of the
  call, disjoint from the input -/
  outW : ∃ data, E.H0.bytes E.bo = some data ∧ E.oo + E.O0.toNat ≤ data.size ∧ E.bo ≠ E.b ∧
    ((.ref (.heap E.bo) E.oo : BPtr), E.O0.toNat) ∈ E.W ∧ Disjoint E.inp E.A0.toNat (.ref (.heap E.bo) E.oo) E.O0.toNat

/-- `Space.get` of a reference outside block `b` keeps the size of its array. -/
theorem SizeKeep.get {H0 H : Heap} {b : Nat} (sk : SizeKeep H0 H b) {r : BRef} (hr : ∀ off, Ptr.ref r off ≠ (Ptr.ref (BRef.heap b) off : BPtr))
    {d : Array UInt8} (hd : Space.get H0 r = some d) : ∃ d', Space.get H r = some d' ∧ d'.size = d.size := by
  cases r with
  | heap c =>
    have hc : c ≠ b := fun e => hr 0 (by rw [e])
    exact sk.1 c hc d hd
  | const c =>
    refine ⟨d, ?_, rfl⟩
    show H.consts c = some d
    rw [sk.2]; exact hd
  | str k => exact ⟨d, hd, rfl⟩

/-- With `have != 0`, `next` points to `have` readable bytes. -/
theorem LI.inBytes {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (eo : EnvOK E)
    (li : LI E l H z S) (hh : l.have_ ≠ 0) :
    ∃ r o d, l.next = .ref r o ∧ Space.get H r = some d ∧ o + l.have_.toNat ≤ d.size := by
  obtain ⟨hle, hat⟩ := li.inAt
  cases hi : E.inp with
  | null => rw [hi] at hat; exact absurd hat.2 hh
  | ref r o0 =>
    rw [hi] at hat
    rcases eo.inRd with hn | ⟨r', off, data, he, hg, hsz⟩
    · rw [hi] at hn; cases hn
    rw [hi] at he
    obtain ⟨rfl, rfl⟩ : r = r' ∧ o0 = off := by cases he; exact ⟨rfl, rfl⟩
    have hnb : ∀ off', Ptr.ref r off' ≠ (Ptr.ref (BRef.heap E.b) off' : BPtr) := by
      intro off' e; cases r with
      | heap c => cases e; exact eo.inNB o0 hi
      | const _ => cases e
      | str _ => cases e
    obtain ⟨d', hd', hs'⟩ := li.sz.get hnb hg
    have hle' : l.have_.toNat ≤ E.A0.toNat := hle
    refine ⟨r, o0 + (E.A0 - l.have_).toNat, d', hat, hd', ?_⟩
    rw [UInt32.toNat_sub_of_le _ _ hle, hs']
    omega

/-! ## Bit buffer -/

/-- `l'` differs from `l` only in the bit-buffer locals, with the input bits conserved. -/
def Pulled (l l' : IL) : Prop :=
  l' = { l with have_ := l'.have_, next := l'.next, hold := l'.hold, bits := l'.bits } ∧
    8 * l'.have_.toNat + l'.bits.toNat = 8 * l.have_.toNat + l.bits.toNat

theorem Pulled.refl (l : IL) : Pulled l l := ⟨rfl, rfl⟩

theorem Pulled.trans {l1 l2 l3 : IL} (a : Pulled l1 l2) (b : Pulled l2 l3) : Pulled l1 l3 := by
  refine ⟨?_, by rw [b.2, a.2]⟩
  rw [b.1, a.1]

/-- `NEEDBITS(n)` for `n ≤ 32`: no fault, the heap is unchanged; it pulls whole bytes until `n` bits are held, or
leaves with fewer when the input runs out. -/
theorem needbits_ok {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (eo : EnvOK E)
    (li : LI E l H z S) (n : UInt32) (hn : n.toNat ≤ 32) :
    SatX H l (NEEDBITS n) (fun r l' H' => H' = H ∧ LI E l' H z S ∧ Pulled l l' ∧
      l'.bits.toNat ≤ max l.bits.toNat (n.toNat + 7) ∧
      (match r with
       | .ok () => n.toNat ≤ l'.bits.toNat
       | .error e => e = .leave ∧ l'.bits.toNat < n.toNat ∧ l'.have_ = 0)) := by
  have hn8 : (n.toUInt8).toNat = n.toNat := by
    rw [UInt32.toNat_toUInt8]; exact Nat.mod_eq_of_lt (by omega)
  unfold NEEDBITS xwhile
  refine xwhileBrk_rank (fun l' H' => H' = H ∧ LI E l' H z S ∧ Pulled l l' ∧
      l'.bits.toNat ≤ max l.bits.toNat (n.toNat + 7)) (fun l' _ => l'.have_.toNat) _ ?_
    ⟨rfl, li, Pulled.refl l, Nat.le_max_left _ _⟩ (by have := l.have_.toNat_lt; unfold fuel; omega)
  rintro l1 H1 ⟨rfl, li1, p1, hb1⟩
  refine SatX.bind (SatX.get ?_)
  refine SatX.pure ?_
  dsimp only
  by_cases hlt : l1.bits < n.toUInt8
  · have hlt' : l1.bits.toNat < n.toNat := by rw [← hn8]; exact hlt
    simp only [hlt, decide_true]
    unfold PULLBYTE
    refine SatX.bind (SatX.bind (SatX.get ?_))
    dsimp only
    by_cases h0 : l1.have_ = 0
    · simp only [h0, beq_self_eq_true, ↓reduceIte]
      exact SatX.bind (SatX.throw ⟨rfl, li1, p1, hb1, rfl, hlt', h0⟩)
    · have h0' : (l1.have_ == 0) = false := by simpa using h0
      simp only [h0', Bool.false_eq_true, ↓reduceIte]
      obtain ⟨r, o, d, hnx, hg, hsz⟩ := li1.inBytes eo h0
      have hh1 : 1 ≤ l1.have_.toNat := by
        rcases Nat.eq_zero_or_pos l1.have_.toNat with e | e
        · exact absurd (UInt32.toNat_inj.mp (by rw [e]; rfl)) h0
        · exact e
      rw [hnx]
      have hlo : o < d.size := by omega
      refine SatX.bind (SatX.lift_eq (a := d[o]) (by simp [load8, Ptr.load, hg, hlo]) ?_)
      have e1 : (Ptr.ref r o).add 1 H1 = .ok (.ref r (o + 1), H1) := by
        have hc : o ≤ d.size ∧ 0 ≤ (o : Int) + 1 ∧ (o : Int) + 1 ≤ (d.size : Int) := by omega
        simp only [Ptr.add, hg, hc, and_self, ↓reduceIte]
        rfl
      refine SatX.bind (SatX.lift_eq e1 ?_)
      have hb64 : l1.bits.toUInt32 < 64 := by
        rw [UInt32.lt_iff_toNat_lt, UInt8.toNat_toUInt32]; show _ < 64; omega
      refine SatX.bind (SatX.lift_eq (a := (d[o]).toUInt64 <<< l1.bits.toUInt32.toUInt64)
        (by simp [shl64, hb64]) ?_)
      refine SatX.set ?_
      refine SatX.pure ?_
      have hb8 : (l1.bits + 8).toNat = l1.bits.toNat + 8 := by
        rw [UInt8.toNat_add]; show (l1.bits.toNat + 8) % 256 = _; omega
      have hsub : (l1.have_ - 1).toNat = l1.have_.toNat - 1 := by
        rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; show 1 ≤ _; omega)]; rfl
      refine ⟨⟨rfl, ?_, ?_, ?_⟩, ?_⟩
      · refine ⟨li1.inv, li1.frame, li1.sz, li1.hz, li1.hb, li1.hs, li1.head, li1.hdr, ?_, li1.outAt, ?_, li1.inn,
          li1.outO, li1.retB, li1.sacc, li1.msgK, Fr.ofLt ?_⟩
        · obtain ⟨hle, hat⟩ := li1.inAt
          refine ⟨by rw [UInt32.le_iff_toNat_le, hsub]; have : l1.have_.toNat ≤ E.A0.toNat := hle; omega, ?_⟩
          show match E.inp with
            | .null => Ptr.ref r (o + 1) = .null ∧ l1.have_ - 1 = 0
            | .ref r' o' => Ptr.ref r (o + 1) = .ref r' (o' + (E.A0 - (l1.have_ - 1)).toNat)
          revert hat
          cases E.inp with
          | null => intro hat; exact absurd hat.2 h0
          | ref r' o' =>
            intro hat
            rw [hnx] at hat
            cases hat
            have hle' : l1.have_.toNat ≤ E.A0.toNat := hle
            rw [UInt32.toNat_sub_of_le _ _ hle, UInt32.toNat_sub_of_le _ _
              (by rw [UInt32.le_iff_toNat_le, hsub]; omega), hsub]
            congr 1; omega
        · show l1.bits + 8 ≤ 39
          rw [UInt8.le_iff_toNat_le, hb8]; show _ ≤ 39
          have := li.bits; rw [UInt8.le_iff_toNat_le] at this; have : l.bits.toNat ≤ 39 := this; omega
        · show l1.have_ - 1 < E.A0
          have hle : l1.have_.toNat ≤ E.A0.toNat := li1.inAt.1
          rw [UInt32.lt_iff_toNat_lt, hsub]; omega
      · refine p1.trans ⟨rfl, ?_⟩
        show 8 * (l1.have_ - 1).toNat + (l1.bits + 8).toNat = _
        rw [hsub, hb8]; omega
      · show (l1.bits + 8).toNat ≤ _
        rw [hb8]; omega
      · show (l1.have_ - 1).toNat < l1.have_.toNat
        rw [hsub]; omega
  · have hge : n.toNat ≤ l1.bits.toNat := by
      rw [← hn8]; exact Nat.le_of_not_lt (fun h => hlt (UInt8.lt_iff_toNat_lt.mpr h))
    have hd : decide (l1.bits < n.toUInt8) = false := by simpa using hlt
    rw [hd]
    exact ⟨rfl, li1, p1, hb1, hge⟩

/-- `BITS(n)` for `n < 32`. -/
theorem bits_ok {H : Heap} {l : IL} (n : UInt32) (hn : n < 32) {Q : Except Ex UInt64 → IL → Heap → Prop}
    (q : Q (.ok (l.hold &&& ((1 : UInt32) <<< n - 1).toUInt64)) l H) : SatX H l (BITS n) Q := by
  unfold BITS
  refine SatX.bind (SatX.lift_eq (a := (1 : UInt32) <<< n) (by simp [shl32, hn]) ?_)
  exact SatX.bind (SatX.get (SatX.pure q))

/-- `DROPBITS(n)` for `n < 64`. -/
theorem dropbits_ok {H : Heap} {l : IL} (n : UInt32) (hn : n < 64) {Q : Except Ex PUnit → IL → Heap → Prop}
    (q : Q (.ok ⟨⟩) { l with hold := l.hold >>> n.toUInt64, bits := l.bits - n.toUInt8 } H) :
    SatX H l (DROPBITS n) Q := by
  unfold DROPBITS
  refine SatX.bind (SatX.get ?_)
  refine SatX.bind (SatX.lift_eq (a := l.hold >>> n.toUInt64) (by simp [shr64, hn]) ?_)
  exact SatX.set q

/-- `INITBITS()`. -/
theorem initbits_ok {H : Heap} {l : IL} {Q : Except Ex PUnit → IL → Heap → Prop}
    (q : Q (.ok ⟨⟩) { l with hold := 0, bits := 0 } H) : SatX H l INITBITS Q := SatX.modify q

/-- The index of a message in the string table, by evaluation. -/
theorem strIdx {msg : String} (i : Nat) (hi : i < strTable.size) (he : (strTable[i] == msg) = true)
    (hb : ∀ j (hj : j < i), ¬ (strTable[j]'(Nat.lt_trans hj hi) == msg) = true) :
    strTable.findIdx? (· == msg) = some i :=
  Array.findIdx?_eq_some_iff_getElem.mpr ⟨hi, he, hb⟩

/-- `SET_BAD(msg)` for a message of the string table. -/
theorem LI.setBad {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (li : LI E l H z S)
    (msg : String) {i : Nat} (hm : strTable.findIdx? (· == msg) = some i)
    (hfr : Fr E l S → Fr E l { S with mode := BAD } := by frt) :
    Sat H (SET_BAD E.c msg) (fun _ H' => ∃ z', LI E l H' z' { S with mode := BAD }) := by
  unfold SET_BAD
  refine Sat.bind (Sat.mono (li.setQuiet BAD (by decide) (by decide) (Or.inr (by decide)) (hfr := hfr)) ?_)
  intro _ H1 li1
  refine Sat.bind (Sat.of_eq (show strLitRef msg H1 = .ok (.ref (.str i) 0, H1) by simp [strLitRef, hm]) ?_)
  exact Sat.mono (li1.wrZio (fun z => { z with msg := .ref (.str i) 0 }) rfl rfl rfl li1.sacc
    (fun _ _ => Or.inr ⟨i, rfl, by rw [Array.findIdx?_eq_some_iff_findIdx_eq] at hm; exact hm.1⟩)) (fun _ H2 li2 => ⟨_, li2⟩)

/-- `CRC_DO1_B` with the static table in place. -/
theorem crcDo1_ok {H : Heap} (hc : H.crcTable = ZlibNg.Crc32Tbl.crc_table) (c : UInt32) (w : UInt64) :
    ∃ v, CRC_DO1_B c w H = .ok (v, H) := by
  have hi : ((c.toUInt64 ^^^ w) &&& 0xff).toNat < 256 := by
    rw [UInt64.toNat_and]; exact Nat.lt_of_le_of_lt (Nat.and_le_right) (by decide)
  obtain ⟨t, e, -⟩ := ZlibNgF.Proof.Crc32.crcTab_ok hc _ hi
  exact ⟨_, by simp only [CRC_DO1_B, bind_app]; rw [show ZlibNg.Crc32P.crcTab _ H = _ from e]; rfl⟩

/-- `CRC2` / `CRC4` change only the state's check value. -/
theorem LI.crc2 {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (eo : EnvOK E)
    (li : LI E l H z S) :
    SatX H l (CRC2 E.c) (fun r l' H' => r = .ok ⟨⟩ ∧ l' = l ∧ ∃ v, LI E l H' z { S with check := v } ∧
      H'.gzheaders = H.gzheaders) := by
  have hc : H.crcTable = ZlibNg.Crc32Tbl.crc_table := li.frame.2.2.2.2.2.2.1.trans eo.crc
  unfold CRC2
  refine SatX.bind (SatX.get ?_)
  refine SatX.bind (SatX.lift_eq (li.rdS (·.check)) ?_)
  obtain ⟨v1, e1⟩ := crcDo1_ok hc (~~~S.check.toUInt32) l.hold
  refine SatX.bind (SatX.lift_eq e1 ?_)
  obtain ⟨v2, e2⟩ := crcDo1_ok hc v1 (l.hold >>> 8)
  refine SatX.bind (SatX.lift_eq e2 ?_)
  exact SatX.lift (Sat.mono (li.wrST (fun s => { s with check := (~~~v2).toUInt64 }) (fun _ _ c => c) rfl)
    (fun _ H' li' => ⟨rfl, rfl, _, li'.1, li'.2.2⟩))

theorem LI.crc4 {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (eo : EnvOK E)
    (li : LI E l H z S) :
    SatX H l (CRC4 E.c) (fun r l' H' => r = .ok ⟨⟩ ∧ l' = l ∧ ∃ v, LI E l H' z { S with check := v } ∧
      H'.gzheaders = H.gzheaders) := by
  have hc : H.crcTable = ZlibNg.Crc32Tbl.crc_table := li.frame.2.2.2.2.2.2.1.trans eo.crc
  unfold CRC4
  refine SatX.bind (SatX.get ?_)
  refine SatX.bind (SatX.lift_eq (li.rdS (·.check)) ?_)
  obtain ⟨v1, e1⟩ := crcDo1_ok hc (~~~S.check.toUInt32) l.hold
  refine SatX.bind (SatX.lift_eq e1 ?_)
  obtain ⟨v2, e2⟩ := crcDo1_ok hc v1 (l.hold >>> 8)
  refine SatX.bind (SatX.lift_eq e2 ?_)
  obtain ⟨v3, e3⟩ := crcDo1_ok hc v2 (l.hold >>> 16)
  refine SatX.bind (SatX.lift_eq e3 ?_)
  obtain ⟨v4, e4⟩ := crcDo1_ok hc v3 (l.hold >>> 24)
  refine SatX.bind (SatX.lift_eq e4 ?_)
  exact SatX.lift (Sat.mono (li.wrST (fun s => { s with check := (~~~v4).toUInt64 }) (fun _ _ c => c) rfl)
    (fun _ H' li' => ⟨rfl, rfl, _, li'.1, li'.2.2⟩))

/-- `state->head` of a state with the invariant. -/
theorem LI.headOf {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (li : LI E l H z S) :
    headOf (some E.b) H = .ok (E.hp, H) := by
  show (do (← ZlibNg.Inflate.rdS (some E.b) (·.head)).get : M HeaderPtr) H = _
  simp only [bind_app, li.rdS (·.head), li.head, Ival.get, pure_app]

/-- The registered header record. -/
theorem LI.hdrRec {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (li : LI E l H z S) {k : Nat}
    (hk : E.hp = some k) : ∃ g, H.gzheaders k = some g := by
  have hd := li.hdr
  unfold HdrOK at hd
  rw [hk] at hd
  obtain ⟨_, g, _, hg, _⟩ := hd
  exact ⟨g, hg⟩

/-- A store into the registered header that keeps its buffer fields keeps `LI`. -/
theorem LI.stHdr {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (eo : EnvOK E)
    (li : LI E l H z S) {k : Nat} (hk : E.hp = some k) {g : GzHeader} (hg : H.gzheaders k = some g)
    (g' : GzHeader) (h1 : g'.extra = g.extra ∨ g'.extra = .null) (h2 : g'.extra_max = g.extra_max)
    (h3 : g'.name = g.name ∨ g'.name = .null) (h4 : g'.name_max = g.name_max)
    (h5 : g'.comment = g.comment ∨ g'.comment = .null) (h6 : g'.comm_max = g.comm_max)
    :
    Sat H (stHeader (some k) g') (fun _ H' => LI E l H' z S ∧ H'.gzheaders = upd H.gzheaders k (some g')) := by
  refine ⟨(), { H with gzheaders := upd H.gzheaders k (some g') }, by simp [stHeader, hg], ?_, rfl⟩
  have hkG := eo.hdrG k hk
  obtain ⟨i', z', b', st', al, e, hz', hb', hst', hal, c⟩ := li.inv
  have hst : st' = S := by
    obtain rfl : E.i = i' := Option.some.inj e
    rw [li.hz] at hz'; cases hz'
    rw [li.hb] at hb'; cases hb'
    rw [li.hs] at hst'; exact (Option.some.inj hst').symm
  subst hst
  refine { li with
    inv := ⟨i', z', b', st', al, e, hz', hb', hst', hal, { c with
      head := ?_ }⟩
    frame := ?_
    sz := ?_
    hdr := ?_ }
  · rcases c.head with hh | ⟨k', g'', hk', hg''⟩
    · exact Or.inl hh
    · by_cases e' : k' = k
      · subst e'; exact Or.inr ⟨k', g', hk', by simp⟩
      · exact Or.inr ⟨k', g'', hk', by simp only [upd_ne _ _ _ _ e']; exact hg''⟩
  · obtain ⟨s1, g1, i1, b1, n1, c1, r1, x1, a1, k1⟩ := li.frame
    exact ⟨s1, fun j hj => by
      have : j ≠ k := fun e => hj (e ▸ hkG)
      simp only [upd_ne _ _ _ _ this]; exact g1 j hj, i1, b1, n1, c1, r1, x1, a1, k1⟩
  · exact li.sz
  · have hd := li.hdr
    unfold HdrOK at hd ⊢
    rw [hk] at hd ⊢
    obtain ⟨g0, g1, e0, e1, a1, a2, a3, a4, a5, a6⟩ := hd
    rw [hg] at e1; cases e1
    refine ⟨g0, g', e0, by simp, ?_, h2.trans a2, ?_, h4.trans a4, ?_, h6.trans a6⟩
    · rcases h1 with e | e
      · rw [e]; exact a1
      · exact Or.inr e
    · rcases h3 with e | e
      · rw [e]; exact a3
      · exact Or.inr e
    · rcases h5 with e | e
      · rw [e]; exact a5
      · exact Or.inr e

/-- `LI` for new locals with the same buffers and at most 39 bits. -/
theorem LI.setBits {E : Env} {l l' : IL} {H : Heap} {z : ZStream} {S : InflateState} (li : LI E l H z S)
    (h1 : l'.next = l.next) (h2 : l'.have_ = l.have_) (h3 : l'.put = l.put) (h4 : l'.out = l.out)
    (h5 : l'.left = l.left) (h6 : l'.bits ≤ 39) (h7 : l'.in_ = l.in_ := by rfl)
    (h8 : l'.ret = l.ret := by rfl) (hfr : Fr E l S → Fr E l' S := by frt) : LI E l' H z S :=
  ⟨li.inv, li.frame, li.sz, li.hz, li.hb, li.hs, li.head, li.hdr, by rw [h1, h2]; exact li.inAt,
    by rw [h3, h4, h5]; exact li.outAt, h6, by rw [h7]; exact li.inn, by rw [h4]; exact li.outO,
    by rw [h8]; exact li.retB, li.sacc, li.msgK, hfr li.fr⟩

end ZlibNgF.Proof.InflateLoop
