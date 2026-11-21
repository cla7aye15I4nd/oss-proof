import ZlibNgF.Proof.«gzwrite.c.compspec»

/-!
# The loop of `gz_comp` (`ZlibNgF`)

`gz_comp` with its loop split out (`compAll`, `compBody`, `compCond`; the body's join points `cTail` and `cRT`),
`write` on a descriptor as an `FdWrites` step (`writeG_fd`), the change of the output fields and `x.next` of a write
handle in the state `GzWX` (`wx_out`), `gz_error` in that state (`wx_err`), the potential across a `deflate` call
(`pot_call`), one trip of the body (`body_spec`: `tail_spec` for `deflate`, `rt_spec` for the reset of a full output
buffer) and the loop (`loop_spec`, by the potential `pot`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace ZlibNgF.Proof.GzWrite
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Gz ZlibNgF.Proof.GzInv ZlibNgF.Proof.GzSat ZlibNgF.Proof.GzMode
open ZlibNgF.Proof.GzWriteNeeds

open ZlibNg.Inflate ZlibNg.Deflate in
/-- The tail of the body of the loop of `gz_comp`: `deflate` and its check (copied from the translation). -/
def cTail (state : GzPtr) (strm : StreamPtr) (flush : Int32) (s : CompLoop) : G CompLoop := do
  let hv ← lm (rdZ strm (·.avail_out))
  let ret ← lm (deflate strm flush)
  if ret == Z_STREAM_ERROR then
    gz_error state Z_STREAM_ERROR (← (gzLit "internal error: deflate stream corrupt"))
    return { s with ret := ret, ctl := .ret }
  let hv := hv - (← lm (rdZ strm (·.avail_out)))
  return { s with ret := ret, hv := hv }

open ZlibNg.Inflate ZlibNg.Deflate in
/-- The body of the loop of `gz_comp` (copied from the translation). -/
def compBody (state : GzPtr) (strm : StreamPtr) (flush : Int32) (s : CompLoop) : G CompLoop := do
  if (← lm (rdZ strm (·.avail_out))) == 0 ||
      (flush != Z_NO_FLUSH && (flush != Z_FINISH || s.ret == Z_STREAM_END)) then
    let d ← lm (Ptr.diff (← lm (rdZ strm (·.next_out))) (← (← ldGz state).next.get))
    let hv : UInt32 := d.toUInt64.toUInt32
    if hv != 0 then
      let got ← writeG (← rdG state (·.fd)) (← (← ldGz state).next.get) hv.toUInt64
      if got < 0 || got.toUInt64.toUInt32 != hv then
        gz_error state Z_ERRNO (← zstrerror)
        return { s with ctl := .ret }
    if (← lm (rdZ strm (·.avail_out))) == 0 then
      let sz ← rdG state (·.size)
      lm (wrZ strm fun z => { z with avail_out := sz })
      let o ← (← ldGz state).out.get
      lm (wrZ strm fun z => { z with next_out := o })
      let o ← (← ldGz state).out.get
      wrG state fun st => { st with next := .val o }
    let no ← lm (rdZ strm (·.next_out))
    wrG state fun st => { st with next := .val no }
  let hv ← lm (rdZ strm (·.avail_out))
  let ret ← lm (deflate strm flush)
  if ret == Z_STREAM_ERROR then
    gz_error state Z_STREAM_ERROR (← (gzLit "internal error: deflate stream corrupt"))
    return { s with ret := ret, ctl := .ret }
  let hv := hv - (← lm (rdZ strm (·.avail_out)))
  return { s with ret := ret, hv := hv }

/-- The condition of the loop of `gz_comp` (copied from the translation). -/
def compCond (s : CompLoop) : G (Bool × CompLoop) := do
  if s.ctl != .go then return (false, s)
  return (s.hv != 0, s)

open ZlibNg.Inflate ZlibNg.Deflate in
/-- `gz_comp` with its loop named (copied from the translation). -/
def compAll (state : GzPtr) (flush : Int32) : G Int32 := do
  let strm ← strmOf state
  if (← rdG state (·.size)) == 0 then
    if (← gz_write_init state) == -1 then
      return -1
  if (← rdG state (·.direct)) != 0 then
    let got ← writeG (← rdG state (·.fd)) (← lm (rdZ strm (·.next_in))) (← lm (rdZ strm (·.avail_in))).toUInt64
    if got < 0 || got.toUInt64.toUInt32 != (← lm (rdZ strm (·.avail_in))) then
      gz_error state Z_ERRNO (← zstrerror)
      return -1
    lm (wrZ strm fun z => { z with avail_in := 0 })
    return 0
  if (← rdG state (·.reset)) != 0 then
    if (← lm (rdZ strm (·.avail_in))) == 0 && flush == Z_NO_FLUSH then
      return 0
    let _ ← lm (deflateReset strm)
    wrG state fun s => { s with reset := 0 }
  let ret : Int32 := Z_OK
  let lp ← gdoWhile (compBody state strm flush) compCond ⟨ret, 0, .go⟩
  if lp.ctl == .ret then
    return -1
  if flush == Z_FINISH then
    wrG state fun s => { s with reset := 1 }
  return 0

theorem gz_comp_eq (state : GzPtr) (flush : Int32) : gz_comp state flush = compAll state flush := by
  unfold gz_comp compAll compBody compCond; rfl

/-! ## The file system -/

theorem FdWrites.refl (fd : Int32) (fs : Fs) : FdWrites fd fs fs := ⟨[], rfl⟩

theorem FdWrites.trans {fd : Int32} {a b c : Fs} (x : FdWrites fd a b) (y : FdWrites fd b c) : FdWrites fd a c := by
  obtain ⟨l1, rfl⟩ := x
  obtain ⟨l2, rfl⟩ := y
  exact ⟨l1 ++ l2, by rw [List.foldl_append]⟩

theorem FdWrites.one (fd : Int32) (fs : Fs) (bs : Array UInt8) : FdWrites fd fs (fs.writeCall fd bs).2 :=
  ⟨[bs], rfl⟩

/-- `write(fd, p, n)` of `n` readable bytes: no fault, one `write` call on `fd`. -/
theorem writeG_fd (W : World) (H : Heap) (fd : Int32) (p : BPtr) (n : UInt64)
    (hrd : n = 0 ∨ ∃ r off a, p = .ref r off ∧ Space.get H r = some a ∧ off + n.toNat ≤ a.size) :
    ∃ r bs, writeG fd p n W H = .ok ((r, { W with fs := (W.fs.writeCall fd bs).2 }), H) := by
  rcases hrd with rfl | ⟨r, off, a, rfl, ha, hle⟩
  · exact ⟨_, #[], by simp [writeG, modifyFs]; rfl⟩
  · by_cases hn : n = 0
    · subst hn; exact ⟨_, #[], by simp [writeG, modifyFs]; rfl⟩
    · exact ⟨_, _, by simp [writeG, modifyFs, hn, lm_app, loadBytes, ha, hle]; exact ⟨rfl, rfl⟩⟩

/-! ## Flat and actual heaps -/

/-- A step between heaps that differ from `h`, `H` only in the record of the file's stream (with the same `state`
field) is a step between `h` and `H`. -/
theorem gstep_unflat {w W : World} {h H : Heap} {b : Nat} {s s' : GzState} (hs : w.gz h b = some s)
    (hs' : W.gz H b = some s') {z a z' a' : ZStream} (hz : h.streams s.strm = some z)
    (hz' : H.streams s.strm = some z') (ha : a.state = z.state) (ha' : a'.state = z'.state) (hst : s'.strm = s.strm)
    (g : GStep w (setZ h s.strm a) W (setZ H s.strm a') b []) : GStep w h W H b [] := by
  have hsF : w.gz (setZ h s.strm a) b = some s := hs
  have hsF' : W.gz (setZ H s.strm a') b = some s' := hs'
  have hoF := gzOwned_setZ w h b hs hz ha
  have hoF' := gzOwned_setZ W H b hs' (by rw [hst]; exact hz') (z' := a') ha'
  rw [hst] at hoF'
  obtain ⟨⟨⟨f, fD⟩, hc, hgz⟩, own, -⟩ := g
  simp only [hsF] at f
  refine gstep_mk' hs hs' hst (fun c hcb hlt => hgz c (fun e => hcb (Option.some.inj e).symm) hlt) (fun i hi => ?_)
    (fun k => f.2.1 k (List.not_mem_nil)) (fun c hcl hno => ?_) hc f.2.2.2.2.2.2.1 f.2.2.2.2.2.2.2.1
    f.2.2.2.2.2.2.2.2.1 f.2.2.2.2.2.2.2.2.2 (fun c hcm hlt => ?_)
  · have := f.1 i (by simpa using hi)
    simp only [setZ_streams_ne _ _ hi] at this; exact this
  · have hno' : c ∉ GzOwned w (setZ h s.strm a) (some b) := by rw [hoF]; exact hno
    exact ⟨frame_bytes_eq f hcl hno', (f.2.2.1 c hcl hno').1, (f.2.2.1 c hcl hno').2, (fD c hcl hno').1,
      (fD c hcl hno').2⟩
  · rw [← hoF]; exact own c (by rw [hoF']; exact hcm) hlt

/-- **The output fields and `x.next` of a write handle in the state `GzWX`** change to ones that `GzWBuf.out`
allows (not direct): the state `GzWX` again, and a step between the flat heaps. -/
theorem wx_out {W : World} {H : Heap} {b : Nat} {s : GzState} {z : ZStream} (hx : GzWX W H b s z)
    (z' : ZStream) (he : SameBut z z') (hin : z'.next_in = z.next_in) (hai : z'.avail_in = z.avail_in)
    (nx : Ival BPtr)
    (hout : s.direct = 0 → ∀ c base, GzBufs (setZ H s.strm (flatZ z)) s c base → ∃ ko kx,
      z'.next_out = .ref (.heap c) (base + inSize s + ko) ∧ nx = .val (.ref (.heap c) (base + inSize s + kx)) ∧
      kx ≤ ko ∧ ko + z'.avail_out.toNat = s.size.toNat) :
    GzWX { W with gzs := upd W.gzs b (some { s with next := nx }) } (setZ H s.strm z') b { s with next := nx } z' ∧
      GStep W (setZ H s.strm (flatZ z)) { W with gzs := upd W.gzs b (some { s with next := nx }) }
        (setZ H s.strm (flatZ z')) b [] := by
  obtain ⟨hs, hz, hsz, hv, hX⟩ := hx
  have hsF : W.gz (setZ H s.strm (flatZ z)) b = some s := hs
  have heF : SameBut (flatZ z) (flatZ z') := by
    cases z; cases z'; simp only [SameBut, flatZ, ZStream.mk.injEq] at he ⊢; simp_all
  obtain ⟨v, g1, g⟩ := invWS_gen hv hsF hsz (setZ_streams_same _ _ _) (flatZ z') heF nx
    (fun _ _ _ => Or.inr ⟨rfl, Or.inr rfl⟩) hout
  rw [setZ_setZ] at v g1 g
  have hst : z'.state = z.state := by rw [he]
  have h1 : ({ W with gzs := upd W.gzs b (some { s with next := nx }) } : World).gz (setZ H s.strm z') b =
      some { s with next := nx } := g1
  refine ⟨⟨h1, setZ_streams_same _ _ _, hsz, by rw [setZ_setZ]; exact v, ?_⟩, g⟩
  rcases hX with ⟨c, base, eb, hi⟩ | ⟨hr, ho⟩
  · refine Or.inl ⟨c, base, eb, ?_⟩
    rw [hin, hai]; exact hi
  · have hown : GzOwned { W with gzs := upd W.gzs b (some { s with next := nx }) } (setZ H s.strm z') (some b) =
        GzOwned W H (some b) := by
      simp only [GzOwned, h1, hs, setZ, upd_same, hz, hst]
    refine Or.inr ⟨by rw [hin, hai]; exact hr, fun c hc => ?_⟩
    rw [hown] at hc; rw [hin]; exact ho c hc

/-- The fields that `gz_error` keeps. -/
theorem errOf_keep {s s' : GzState} {e : Int32} (he : ErrOf s e s') :
    s'.strm = s.strm ∧ s'.size = s.size ∧ s'.buffers = s.buffers ∧ s'.«in» = s.«in» ∧ s'.out = s.out ∧
      s'.mode = s.mode ∧ s'.want = s.want ∧ s'.direct = s.direct ∧ s'.reset = s.reset ∧ s'.next = s.next ∧
      s'.fd = s.fd := by
  obtain ⟨h1, -⟩ := he
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [h1] <;> rfl

/-- **`gz_error` on a write handle in the state `GzWX`**: the state `GzWX` again (same stream record). -/
theorem wx_err {w W : World} {h H : Heap} {b : Nat} {s : GzState} {z : ZStream} {e : Int32} (hx : GzWX w h b s z)
    (q : ErrPostX w h b s z e W H) :
    ∃ s', GzWX W H b s' z ∧ ErrOf s e s' ∧ W.fs = w.fs ∧
      GStep w (setZ h s.strm (flatZ z)) W (setZ H s.strm (flatZ z)) b [] := by
  obtain ⟨s', hs', he, hv', hfs, hst, g⟩ := q
  obtain ⟨hs, hz, hsz, hv, hX⟩ := hx
  obtain ⟨k1, k2, k3, -, -, k6, k7, k8, -⟩ := errOf_keep he
  have hz' : H.streams s'.strm = some z := by rw [k1, hst]; exact hz
  refine ⟨s', ⟨hs', hz', by rw [k2]; exact hsz, by rw [k1]; exact hv', ?_⟩, he, hfs, g⟩
  rcases hX with ⟨c, base, eb, hi⟩ | hc
  · refine Or.inl ⟨c, base, by rw [k3]; exact eb, ?_⟩
    simp only [InpW, inSize] at hi ⊢; rw [k6, k7, k8]; exact hi
  · have hfr : FreshBlocks h := hv.2.2.2.1.1
    refine Or.inr (callerIn_step g hfr (gzOwned_setZ w h b hs hz rfl) ?_ hc (Or.inl rfl) (fun _ => Nat.le_refl _))
    have := gzOwned_setZ W H b hs' hz' (z' := flatZ z) rfl
    rw [k1] at this; exact this

/-! ## The message block across a call -/

/-- The message of `s` is still the message of `s'`, or its block is freed in `H` (and was handed out before). -/
def MKeep (s s' : GzState) (H : Heap) : Prop :=
  s'.msg = s.msg ∨ ∀ c ∈ blkOf s.msg, H.bytes c = none ∧ c < H.nextBlk

theorem MKeep.trans {s1 s2 s3 : GzState} {H2 H3 : Heap} (a : MKeep s1 s2 H2) (b : MKeep s2 s3 H3)
    (mono : ∀ c, c < H2.nextBlk → H2.bytes c = none → H3.bytes c = none ∧ c < H3.nextBlk) : MKeep s1 s3 H3 := by
  rcases a with e | d
  · rcases b with e' | d'
    · exact Or.inl (e'.trans e)
    · exact Or.inr fun c hc => d' c (by rw [e]; exact hc)
  · exact Or.inr fun c hc => mono c (d c hc).2 (d c hc).1

/-- The blocks of an open file, as `ownL` lists them once the buffers exist. -/
theorem gzOwned_eq {w : World} {h : Heap} {b : Nat} {s : GzState} (hs : w.gz h b = some s) :
    GzOwned w h (some b) = [b] ++ blkOf s.path ++ blkOf s.msg ++ blkOf s.buffers ++ stBlk h s := by
  simp only [GzOwned, hs]; rfl

theorem owned_ownL {w : World} {h : Heap} {b : Nat} {s : GzState} (hs : w.gz h b = some s) (hsz : s.size ≠ 0)
    {c : Nat} (hc : c ∈ GzOwned w h (some b)) : c ∈ ownL h b s := by
  rw [gzOwned_eq hs] at hc
  simp only [ownL, hsz, ite_false, List.mem_append] at hc ⊢
  rcases hc with (((h1 | h2) | h3) | h4) | h5
  · exact Or.inl (Or.inl (Or.inl h1))
  · exact Or.inl (Or.inl (Or.inr h2))
  · exact Or.inl (Or.inr h3)
  · exact Or.inr (Or.inl h4)
  · exact Or.inr (Or.inr h5)

/-- A dead block stays dead across a step from a write handle in the state `GzWX` (whose blocks are all live). -/
theorem wx_mono {W W' : World} {H H' : Heap} {b : Nat} {s : GzState} {z : ZStream} {i : Nat} {a' : ZStream}
    (hx : GzWX W H b s z) (g : GStep W (setZ H s.strm (flatZ z)) W' (setZ H' i a') b []) :
    ∀ c, c < H.nextBlk → H.bytes c = none → H'.bytes c = none ∧ c < H'.nextBlk := by
  obtain ⟨hs, -, hsz, hv, -⟩ := hx
  have hsF : W.gz (setZ H s.strm (flatZ z)) b = some s := hs
  have hwm := modeOf hsF hv.2.1
  obtain ⟨sh, -⟩ := inv_of hsF hv.1
  intro c hc hd
  have hno : c ∉ GzOwned W (setZ H s.strm (flatZ z)) (some b) := fun m => by
    obtain ⟨d, e⟩ := ownL_liveW sh hwm (gz_live hsF) c (owned_ownL hsF hsz m)
    have e' : H.bytes c = some d := e
    rw [hd] at e'; cases e'
  obtain ⟨⟨⟨fr, -⟩, -, -⟩, -, -⟩ := g
  simp only [hsF] at fr
  exact ⟨fr.2.2.2.2.1 c hc hno hd, Nat.lt_of_lt_of_le hc fr.2.2.2.2.2.2.2.2.2⟩

/-- `gz_error` on a write handle in the state `GzWX` frees the old message, a block handed out before. -/
theorem gz_error_freesX {w : World} {h : Heap} {b : Nat} {s : GzState} {za : ZStream}
    (hz : h.streams s.strm = some za) (hv : GzInvWS w (setZ h s.strm (flatZ za)) (some b))
    (hs : w.gz h b = some s) (e : Int32) (msg : BPtr) (hmsg : msg = .null ∨ CStr h msg)
    (hmk : ∀ c o, msg ≠ .ref (.heap c) o) :
    GSat w h (gz_error (some b) e msg) (fun _ _ H => ∀ c ∈ blkOf s.msg, H.bytes c = none ∧ c < H.nextBlk) := by
  have hlit : LitOk w h := hv.2.2.lit
  have hsF : w.gz (setZ h s.strm (flatZ za)) b = some s := hs
  obtain ⟨⟨b0, s0, e0, hs0, sh, hn⟩, -, hw⟩ := hv
  cases e0; rw [hsF] at hs0; cases hs0
  have hoF : ownL (setZ h s.strm (flatZ za)) b s = ownL h b s := ownL_setZ h b hz rfl
  have hnA : (ownL h b s).Nodup := hoF ▸ hn
  have fr : FreshBlocks h := hw.2.1.1
  obtain ⟨db, hdb⟩ := gz_live hs
  have hdb1 : (freeMsg h s).bytes b = some db := freeMsg_bytes_b hnA hdb
  have hs1 : ({ w with gzs := upd w.gzs b (some (errSt s e)) } : World).gz (freeMsg h s) b = some (errSt s e) := by
    unfold World.gz; rw [hdb1]; simp
  obtain ⟨sh1, -⟩ := err0_keep sh hn e
  rw [freeMsg_setZ] at sh1
  have fr1 : FreshBlocks (freeMsg h s) := (HLess.free h s).freshB fr
  obtain ⟨r, W, H, eq, -, -, -, -, -, x, -, -⟩ := errTail_spec hs1 fr1
    (LitOk.ext (w := w) hlit rfl fun k a e' => by rw [freeMsg_consts]; exact e') sh1.path rfl e rfl msg
    (hmsg.imp_right fun hp => cstr_free hp hmk)
  refine ⟨r, W, H, by
    rw [gz_error_run hs (by obtain ⟨⟩ := sh.msg; constructor <;> assumption) (msg_ne_b hnA) e msg]; exact eq, ?_⟩
  intro c hc
  rcases sh.msg.msg with e1 | ⟨c', d, e1, hd⟩
  · rw [e1] at hc; simp [blkOf] at hc
  · rw [e1] at hc; simp [blkOf] at hc; subst hc
    have hne : s.err ≠ ZlibNg.Inflate.Z_MEM_ERROR := fun e' => by
      have := sh.msg.mem e'; rw [e1] at this; cases this
    have hd' : h.bytes c = some d := hd
    have hlt : c < h.nextBlk := live_lt fr ⟨d, hd'⟩
    have hf : (freeMsg h s).bytes c = none := by unfold freeMsg; rw [e1]; simp [hne]
    have hc' : c < (freeMsg h s).nextBlk := by rw [freeMsg_next]; exact hlt
    exact ⟨by rw [(x.old c hc').1]; exact hf, Nat.lt_of_lt_of_le hc' x.next⟩

/-- `gz_error(state, Z_ERRNO, zstrerror())` in the state `GzWX` frees the old message. -/
theorem gz_error_strX_frees {w : World} {h : Heap} {b : Nat} {s : GzState} {za : ZStream}
    (hz : h.streams s.strm = some za) (hv : GzInvWS w (setZ h s.strm (flatZ za)) (some b))
    (hs : w.gz h b = some s) {α : Type} (r : α) :
    GSat w h (do gz_error (some b) Z_ERRNO (← zstrerror); pure r)
      (fun _ _ H => ∀ c ∈ blkOf s.msg, H.bytes c = none ∧ c < H.nextBlk) := by
  obtain ⟨p, a, e, hc, hk⟩ := zstrerror_spec w h
  refine GSat.bind ⟨p, w, _, e, ?_⟩
  have x := HExt.lit h a
  obtain ⟨hv1, hs1, -⟩ := invX_ext hv hs x (LitOk.ext hv.2.2.lit rfl x.consts)
  exact GSat.bind (GSat.mono (gz_error_freesX (by rw [x.streams]; exact hz) hv1 hs1 _ p (Or.inr hc) hk)
    fun _ W H q => GSat.pure q)

/-- `gz_error(state, e, lit)` in the state `GzWX` frees the old message. -/
theorem gz_error_litX_frees (lit : String) (i : Nat) (hi : gzLits.findIdx? (· == lit) = some i)
    (hl : gzLits[i]? = some lit) (hn : NoNul lit) {w : World} {h : Heap} {b : Nat} {s : GzState} {za : ZStream}
    (hz : h.streams s.strm = some za) (hv : GzInvWS w (setZ h s.strm (flatZ za)) (some b))
    (hs : w.gz h b = some s) (e : Int32) {α : Type} (r : α) :
    GSat w h (do gz_error (some b) e (← gzLit lit); pure r)
      (fun _ _ H => ∀ c ∈ blkOf s.msg, H.bytes c = none ∧ c < H.nextBlk) := by
  refine GSat.bind (GSat.mono (gzLit_spec lit i hi hl hn hv.2.2.lit) fun p W1 H1 q => ?_)
  obtain ⟨hg, -, x, hL, hc, hk⟩ := q
  obtain ⟨v1, e1, -⟩ := invWS_ext hv (show w.gz (setZ h s.strm (flatZ za)) b = some s from hs)
    (hext_setZ x s.strm (flatZ za)) hg (by exact hL)
  have hs1 : W1.gz H1 b = some s := e1
  exact GSat.bind (GSat.mono (gz_error_freesX (by rw [x.streams]; exact hz) v1 hs1 e p (Or.inr ⟨_, hc⟩) hk)
    fun _ W H q => GSat.pure q)

/-! ## The potential -/

/-- A `deflate` call with room in the output does not raise the potential, and lowers it when it produces output. -/
theorem pot_call {ψ : Int32 → C.DeflateState → Nat} {Gr : Nat} (hG : Gr ≤ 2 ^ 28) {f : Int32} {S : Nat}
    {H H' : Heap} {i : Nat} {z z' : ZStream} {sb : Nat} {st st' : C.DeflateState} (hz : H.streams i = some z)
    (hz' : H'.streams i = some z') (hsb : z.state = some sb) (hsb' : z'.state = some sb)
    (hst : H.dstate sb = some st) (hst' : H'.dstate sb = some st') (hai : z'.avail_in ≤ z.avail_in)
    (hao : z'.avail_out ≤ z.avail_out) (hS : 8 ≤ S) (hle : z.avail_out.toNat ≤ S) (h0 : z.avail_out ≠ 0)
    (hmu : ψ f st' + (z.avail_out.toNat - z'.avail_out.toNat) ≤
      ψ f st + Gr * (z.avail_in.toNat - z'.avail_in.toNat) + (if z'.avail_out = 0 then 5 else 0)) :
    pot ψ f S H' i ≤ pot ψ f S H i ∧ (z'.avail_out ≠ z.avail_out → pot ψ f S H' i < pot ψ f S H i) := by
  rw [pot_eq ψ f S hz' hsb' hst', pot_eq ψ f S hz hsb hst]
  simp only [h0, ↓reduceIte]
  have l1 := UInt32.le_iff_toNat_le.mp hai
  have l2 := UInt32.le_iff_toNat_le.mp hao
  have hstrict : z'.avail_out ≠ z.avail_out → (2 ^ 31 + 2 ^ 30) * z'.avail_in.toNat + 3 * ψ f st' +
      2 * (S - (if z'.avail_out = 0 then S else z'.avail_out.toNat)) <
      (2 ^ 31 + 2 ^ 30) * z.avail_in.toNat + 3 * ψ f st + 2 * (S - z.avail_out.toNat) := by
    intro hne
    have hne' : z'.avail_out.toNat ≠ z.avail_out.toNat := fun e => hne (UInt32.toNat_inj.mp e)
    have := pot_arith Gr S z.avail_in.toNat z'.avail_in.toNat z.avail_out.toNat z'.avail_out.toNat (ψ f st)
      (ψ f st') hG l1 l2 hle hS (by
        by_cases e : z'.avail_out = 0
        · have : z'.avail_out.toNat = 0 := by rw [e]; rfl
          simp only [e, ite_true, this] at hmu ⊢; exact hmu
        · have : z'.avail_out.toNat ≠ 0 := fun e2 => e (UInt32.toNat_inj.mp (by simpa using e2))
          simp only [e, ite_false, this] at hmu ⊢; exact hmu) hne'
    by_cases e : z'.avail_out = 0
    · have e2 : z'.avail_out.toNat = 0 := by rw [e]; rfl
      simp only [e, ite_true, e2] at this ⊢; exact this
    · have e2 : z'.avail_out.toNat ≠ 0 := fun e2 => e (UInt32.toNat_inj.mp (by simpa using e2))
      simp only [e, ite_false, e2] at this ⊢; exact this
  refine ⟨?_, hstrict⟩
  by_cases hne : z'.avail_out = z.avail_out
  · have e3 : z'.avail_out ≠ 0 := by rw [hne]; exact h0
    simp only [e3, ↓reduceIte] at hmu ⊢
    rw [hne] at hmu ⊢
    have e2 : Gr * (z.avail_in.toNat - z'.avail_in.toNat) ≤ 2 ^ 28 * (z.avail_in.toNat - z'.avail_in.toNat) :=
      Nat.mul_le_mul_right _ hG
    have e4 : (2 ^ 31 + 2 ^ 30) * z.avail_in.toNat = (2 ^ 31 + 2 ^ 30) * z'.avail_in.toNat +
        (2 ^ 31 + 2 ^ 30) * (z.avail_in.toNat - z'.avail_in.toNat) := by
      rw [← Nat.mul_add]; congr 1; omega
    rw [e4]
    generalize z.avail_in.toNat - z'.avail_in.toNat = k at e2 hmu
    generalize Gr * k = gk at e2 hmu
    omega
  · exact Nat.le_of_lt (hstrict hne)

/-! ## The tail of the loop body: `deflate` -/

/-- Two facts of the same deterministic run. -/
theorem gsat_andC {α : Type} {w : World} {h : Heap} {m : G α} {P Q : α → World → Heap → Prop}
    (p : GSat w h m P) (q : GSat w h m Q) : GSat w h m (fun a W H => P a W H ∧ Q a W H) := by
  obtain ⟨a, W, H, e, pa⟩ := p
  obtain ⟨a', W', H', e', qa⟩ := q
  rw [e] at e'
  simp only [Except.ok.injEq, Prod.mk.injEq] at e'
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e'
  exact ⟨a, W, H, e, pa, qa⟩

theorem lit_dcorrupt : gzLits.findIdx? (· == "internal error: deflate stream corrupt") = some 10 := by
  simp [gzLits, List.findIdx?_cons]
theorem lit_dcorrupt_get : gzLits[10]? = some "internal error: deflate stream corrupt" := by decide
theorem nonul_dcorrupt : NoNul "internal error: deflate stream corrupt" := by decide

/-- What `cTail` leaves (relative to its entry `W`, `H`, `s`, `z`). -/
def TailPost (ψ : Int32 → C.DeflateState → Nat) (flush : Int32) (W : World) (H : Heap) (b : Nat) (s : GzState)
    (z : ZStream) (l' : CompLoop) (W' : World) (H' : Heap) : Prop :=
  ∃ s' z', GzWX W' H' b s' z' ∧ W'.fs = W.fs ∧
    GStep W (setZ H s.strm (flatZ z)) W' (setZ H' s.strm (flatZ z')) b [] ∧ BufAdv z z' ∧
    ((l'.ctl = .ret ∧ ErrOf s ZlibNg.Inflate.Z_STREAM_ERROR s') ∨
      (l'.ctl = .go ∧ s' = s ∧ l'.hv = z.avail_out - z'.avail_out ∧
        pot ψ flush s.size.toNat H' s.strm ≤ pot ψ flush s.size.toNat H s.strm ∧
        (l'.hv ≠ 0 → pot ψ flush s.size.toNat H' s.strm < pot ψ flush s.size.toNat H s.strm) ∧
        (flush ≠ ZlibNg.Inflate.Z_FINISH → z'.avail_in = 0 ∨ z'.avail_out = 0))) ∧ MKeep s s' H'

/-- **`cTail`**: `deflate` on a write handle in the state `GzWX` (not direct) with room in the output. -/
theorem tail_spec (P : DeflateReach.DPending) {ψ : Int32 → C.DeflateState → Nat} {Gr : Nat}
    (hP : DeflatePsi ψ Gr) {W : World} {H : Heap} {b : Nat} {s : GzState} {z : ZStream} (hx : GzWX W H b s z)
    (hd : s.direct = 0) (h0 : z.avail_out ≠ 0) (flush : Int32) (l : CompLoop) (hl : l.ctl = .go) :
    GSat W H (cTail (some b) (some s.strm) flush l) (TailPost ψ flush W H b s z) := by
  obtain ⟨sb, st, hsb, hst, -, -, hS8, -, hle⟩ := wx_facts hx hd
  have hz := hx.2.1
  obtain ⟨r, H', z', e, hz', hadv, hmu, hdone, hx', g⟩ := deflate_stepX P hP.2.2 hx hd flush
  have hsb' : z'.state = some sb := by rw [hadv.2.2.2.2]; exact hsb
  obtain ⟨sb2, st', hsb2, hst', -⟩ := wx_facts hx' hd
  rw [hsb'] at hsb2; cases hsb2
  have hmu' := hmu sb st st' ⟨⟨z, ⟨_, rfl, hz⟩, hsb⟩, hst⟩ ⟨⟨z', ⟨_, rfl, hz'⟩, hsb'⟩, hst'⟩
  obtain ⟨pl, plt⟩ := pot_call hP.1 hz hz' hsb hsb' hst hst' hadv.1 hadv.2.1 hS8 hle h0 hmu'
  unfold cTail
  refine GSat.bind (GSat.lm ⟨_, H, rdZ_run hz _, ?_⟩)
  refine GSat.bind (GSat.lm ⟨r, H', e, ?_⟩)
  apply GSat.ite
  · intro _
    have hx1 := hx'
    obtain ⟨hs', -, -, hv', -⟩ := hx1
    refine GSat.mono (gsat_andC (gz_error_litX _ 10 lit_dcorrupt lit_dcorrupt_get nonul_dcorrupt hz' hv' hs'
      ZlibNg.Inflate.Z_STREAM_ERROR ({ l with ret := r, ctl := .ret } : CompLoop))
      (gz_error_litX_frees _ 10 lit_dcorrupt lit_dcorrupt_get nonul_dcorrupt hz' hv' hs'
      ZlibNg.Inflate.Z_STREAM_ERROR ({ l with ret := r, ctl := .ret } : CompLoop))) fun l' W2 H2 q => ?_
    obtain ⟨⟨rfl, q⟩, hfree⟩ := q
    obtain ⟨s2, hx2, he2, hfs2, g2⟩ := wx_err hx' q
    exact ⟨s2, z', hx2, hfs2, g.trans g2 ⟨s, hx.1⟩ ⟨s, hx'.1⟩, hadv, Or.inl ⟨rfl, he2⟩, Or.inr hfree⟩
  · intro hne
    refine GSat.bind (GSat.lm ⟨_, H', rdZ_run hz' _, GSat.pure ?_⟩)
    refine ⟨s, z', hx', rfl, g, hadv, Or.inr ⟨hl, rfl, rfl, pl, fun h1 => plt fun e2 => h1 ?_,
      fun h1 => hdone h1 (by simpa using hne)⟩, Or.inl rfl⟩
    show z.avail_out - z'.avail_out = 0
    rw [e2]; exact UInt32.sub_self _

/-! ## The head of the loop body -/

theorem gsat_ivget {α : Type} {w : World} {h : Heap} {p : α} {Q : α → World → Heap → Prop} (q : Q p w h) :
    GSat w h (monadLift (Ival.get (.val p)) : G α) Q := ⟨p, w, h, rfl, q⟩

theorem sat_diffW {H : Heap} {c : Nat} {a : Array UInt8} {o1 o2 : Nat} (hb : H.bytes c = some a)
    (h1 : o1 ≤ a.size) (h2 : o2 ≤ o1) (h3 : o1 - o2 < 2 ^ 31) :
    Ptr.diff (Ptr.ref (BRef.heap c) o1) (Ptr.ref (BRef.heap c) o2) H = .ok (Int64.ofInt ((o1 : Int) - o2), H) := by
  have hr : -(2 ^ 63 : Int) ≤ (o1 : Int) - (o2 : Int) ∧ (o1 : Int) - (o2 : Int) < 2 ^ 63 := by omega
  have hb' : Space.get H (BRef.heap c) = some a := hb
  have h2' : o2 ≤ a.size := by omega
  simp only [Ptr.diff, hb', h1, h2', and_self, ↓reduceIte, hr]

/-- The buffers of a write handle in the state `GzWX` (not direct). -/
theorem wx_bufs {W : World} {H : Heap} {b : Nat} {s : GzState} {z : ZStream} (hx : GzWX W H b s z)
    (hd : s.direct = 0) :
    ∃ c base d ko kx, s.buffers = .val (.ref (.heap c) base) ∧ s.out = .val (.ref (.heap c) (base + inSize s)) ∧
      H.bytes c = some d ∧ base + inSize s + s.size.toNat ≤ d.size ∧
      z.next_out = .ref (.heap c) (base + inSize s + ko) ∧ s.next = .val (.ref (.heap c) (base + inSize s + kx)) ∧
      kx ≤ ko ∧ ko + z.avail_out.toNat = s.size.toNat ∧ s.size.toNat ≤ 2 ^ 30 ∧
      (∀ c' base', GzBufs (setZ H s.strm (flatZ z)) s c' base' → c' = c ∧ base' = base) := by
  obtain ⟨hs, hz, hsz, hv, -⟩ := hx
  have hsF : W.gz (setZ H s.strm (flatZ z)) b = some s := hs
  have hwm := modeOf hsF hv.2.1
  obtain ⟨sh, -⟩ := inv_of hsF hv.1
  obtain ⟨c, base, zF, hB, hzF, WB⟩ := (sh.write hwm).bufs hsz
  rw [setZ_streams_same] at hzF; cases hzF
  obtain ⟨ko, kx, eo, ex, hle, hk⟩ := WB.out hd
  obtain ⟨d, hdc, hds⟩ := hB.fits
  have hout2 : outSize s = s.want.toNat := by simp [outSize, hwm, hd]
  have hsw : s.size.toNat = s.want.toNat := by rw [hB.size]
  refine ⟨c, base, d, ko, kx, hB.buffers, hB.out (by rw [hout2]; have := sh.want_lo; omega), hdc,
    by rw [hout2] at hds; omega, eo, ex, hle, hk, by rw [hsw]; exact sh.want_hi, fun c' base' hb' => ?_⟩
  have := hb'.buffers.symm.trans hB.buffers
  simp only [Ival.val.injEq, Ptr.ref.injEq, BRef.heap.injEq] at this
  exact ⟨this.1, this.2⟩

/-! ## The loop body -/

/-- The input of `z` is where `GzWBuf.inp` allows (inside the first `size` bytes of `in`, or none). -/
def InOk (s : GzState) (z : ZStream) : Prop :=
  ∃ c base, s.buffers = .val (.ref (.heap c) base) ∧ InpOk s c base z.next_in z.avail_in

theorem adv_trans {p q r : BPtr} {k1 k2 : Nat} (a : Adv p q k1) (b : Adv q r k2) : Adv p r (k1 + k2) := by
  cases p with
  | null => obtain ⟨rfl, rfl⟩ := a; obtain ⟨rfl, rfl⟩ := b; exact ⟨rfl, rfl⟩
  | ref r0 o => cases a; cases b; simp [Adv, Nat.add_assoc]

theorem adv_zero (p : BPtr) : Adv p p 0 := by cases p <;> simp [Adv]

theorem inOk_adv {s s' : GzState} {z z' : ZStream} (hd : s.direct = 0) (hb : s'.buffers = s.buffers)
    (hsz : s'.size = s.size) (hd' : s'.direct = s.direct) (hi : InOk s z)
    (h1 : z'.avail_in ≤ z.avail_in) (h3 : Adv z.next_in z'.next_in (z.avail_in.toNat - z'.avail_in.toNat)) :
    InOk s' z' := by
  obtain ⟨c, base, eb, hi⟩ := hi
  refine ⟨c, base, by rw [hb]; exact eb, ?_⟩
  have l1 := UInt32.le_iff_toNat_le.mp h1
  simp only [InpOk] at hi ⊢; rw [hsz, hd']
  rcases hi with ⟨k, ek, -, hk⟩ | ⟨e1, e2⟩
  · rw [ek] at h3; simp only [Adv] at h3
    exact Or.inl ⟨k + (z.avail_in.toNat - z'.avail_in.toNat), by rw [h3]; congr 1; omega, by omega, by omega⟩
  · rcases e2 with e2 | e2
    · exact absurd hd e2
    · rw [e2] at h3; simp only [Adv] at h3
      refine Or.inr ⟨?_, Or.inr h3.2⟩
      have : z'.avail_in.toNat = 0 := by rw [e1] at l1; simp at l1; omega
      exact UInt32.toNat_inj.mp (by simpa using this)

/-- The fields of the `gz_state` that the loop of `gz_comp` keeps. -/
structure LFix (s s' : GzState) : Prop where
  fix : WFix s s'
  size : s'.size = s.size
  buffers : s'.buffers = s.buffers
  inp : s'.«in» = s.«in»
  out : s'.out = s.out
  reset : s'.reset = s.reset
  path : s'.path = s.path

theorem LFix.refl (s : GzState) : LFix s s := ⟨WFix.refl s, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem LFix.trans {s1 s2 s3 : GzState} (a : LFix s1 s2) (b : LFix s2 s3) : LFix s1 s3 :=
  ⟨a.1.trans b.1, b.2.trans a.2, b.3.trans a.3, b.4.trans a.4, b.5.trans a.5, b.6.trans a.6, b.7.trans a.7⟩

theorem errOf_path {s s' : GzState} {e : Int32} (he : ErrOf s e s') : s'.path = s.path := by
  obtain ⟨h1, -⟩ := he
  rw [h1]; rfl

theorem LFix.of_err {s s' : GzState} {e : Int32} (he : ErrOf s e s') : LFix s s' := by
  obtain ⟨-, k2, k3, k4, k5, -, -, -, k9, -⟩ := errOf_keep he
  exact ⟨WFix.of_err he, k2, k3, k4, k5, k9, errOf_path he⟩

theorem LFix.next (s : GzState) (nx : Ival BPtr) : LFix s { s with next := nx } :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- What one trip of the loop body of `gz_comp` leaves, from `W`, `H`, `s`, `z`. -/
def BPost (ψ : Int32 → C.DeflateState → Nat) (flush : Int32) (W : World) (H : Heap) (b : Nat) (s : GzState)
    (z : ZStream) (l' : CompLoop) (W' : World) (H' : Heap) : Prop :=
  ∃ s' z', GzWX W' H' b s' z' ∧ LFix s s' ∧ FdWrites s.fd W.fs W'.fs ∧
    GStep W (setZ H s.strm (flatZ z)) W' (setZ H' s.strm (flatZ z')) b [] ∧
    z'.avail_in ≤ z.avail_in ∧ Adv z.next_in z'.next_in (z.avail_in.toNat - z'.avail_in.toNat) ∧
    (InOk s z → InOk s' z') ∧
    (l'.ctl = .ret ∨ (l'.ctl = .go ∧ pot ψ flush s.size.toNat H' s.strm ≤ pot ψ flush s.size.toNat H s.strm ∧
      (l'.hv ≠ 0 → pot ψ flush s.size.toNat H' s.strm < pot ψ flush s.size.toNat H s.strm) ∧
      (l'.hv = 0 → z'.avail_out ≠ 0 ∧ (flush ≠ ZlibNg.Inflate.Z_FINISH → z'.avail_in = 0)))) ∧
    MKeep s s' H' ∧ z'.state = z.state

/-- A head that changes only the output fields and `x.next`, followed by `cTail`. -/
theorem bpost_tail {ψ : Int32 → C.DeflateState → Nat} {flush : Int32} {W W2 W' : World} {H H2 H' : Heap}
    {b : Nat} {s : GzState} {z z2 : ZStream} {nx : Ival BPtr} {l' : CompLoop} (hx : GzWX W H b s z)
    (hd : s.direct = 0) (hs2 : W2.gz H2 b = some { s with next := nx })
    (hfs : FdWrites s.fd W.fs W2.fs)
    (g : GStep W (setZ H s.strm (flatZ z)) W2 (setZ H2 s.strm (flatZ z2)) b [])
    (hin : z2.next_in = z.next_in) (hai : z2.avail_in = z.avail_in) (h0 : z2.avail_out ≠ 0)
    (hst2 : z2.state = z.state)
    (hpot : pot ψ flush s.size.toNat H2 s.strm = pot ψ flush s.size.toNat H s.strm)
    (T : TailPost ψ flush W2 H2 b { s with next := nx } z2 l' W' H') : BPost ψ flush W H b s z l' W' H' := by
  obtain ⟨s', z', hx', hfs', g', hadv, hr, hmk⟩ := T
  have hsF : W.gz (setZ H s.strm (flatZ z)) b = some s := hx.1
  have hs2F : W2.gz (setZ H2 s.strm (flatZ z2)) b = some { s with next := nx } := hs2
  have gg := g.trans g' ⟨s, hsF⟩ ⟨_, hs2F⟩
  obtain ⟨a1, a2, a3, -, a5⟩ := hadv
  rw [hin, hai] at a3; rw [hai] at a1
  have hlf : LFix s s' := by
    rcases hr with ⟨-, he⟩ | ⟨-, rfl, -⟩
    · exact (LFix.next s nx).trans (LFix.of_err he)
    · exact LFix.next s nx
  refine ⟨s', z', hx', hlf, by rw [hfs']; exact hfs, gg, a1, a3,
    fun hi => inOk_adv hd hlf.buffers hlf.size hlf.fix.direct hi a1 a3, ?_, hmk, a5.trans hst2⟩
  rcases hr with ⟨e1, -⟩ | ⟨e1, -, e3, p1, p2, p3⟩
  · exact Or.inl e1
  · refine Or.inr ⟨e1, by rw [← hpot]; exact p1, fun h => by rw [← hpot]; exact p2 h, fun h => ?_⟩
    have e4 : z'.avail_out = z2.avail_out := by
      rw [e3] at h
      have := UInt32.le_iff_toNat_le.mp a2
      have h' := congrArg UInt32.toNat h
      rw [UInt32.toNat_sub_of_le _ _ a2] at h'
      exact UInt32.toNat_inj.mp (by simp at h'; omega)
    refine ⟨by rw [e4]; exact h0, fun hf => ?_⟩
    rcases p3 hf with e5 | e5
    · exact e5
    · exact absurd (e4 ▸ e5) h0

theorem pot_setZ (ψ : Int32 → C.DeflateState → Nat) (f : Int32) (S : Nat) {H : Heap} {i : Nat} {z z' : ZStream}
    (hz : H.streams i = some z) (hst : z'.state = z.state) (hai : z'.avail_in = z.avail_in)
    (hao : (if z'.avail_out = 0 then S else z'.avail_out.toNat) = (if z.avail_out = 0 then S else z.avail_out.toNat)) :
    pot ψ f S (setZ H i z') i = pot ψ f S H i := by
  unfold pot
  rw [setZ_streams_same, hz]
  simp only
  rw [hst, hai, hao]
  rfl

open ZlibNg.Inflate ZlibNg.Deflate in
/-- The rest of the head of the loop body after the write of the output: reset a full output buffer, move
`x.next`, then `cTail` (copied from the translation). -/
def cRT (state : GzPtr) (strm : StreamPtr) (flush : Int32) (s : CompLoop) : G CompLoop := do
  if (← lm (rdZ strm (·.avail_out))) == 0 then
    let sz ← rdG state (·.size)
    lm (wrZ strm fun z => { z with avail_out := sz })
    let o ← (← ldGz state).out.get
    lm (wrZ strm fun z => { z with next_out := o })
    let o ← (← ldGz state).out.get
    wrG state fun st => { st with next := .val o }
  let no ← lm (rdZ strm (·.next_out))
  wrG state fun st => { st with next := .val no }
  cTail state strm flush s

/-- **`cRT`** from a world `W'` that differs from `W` by `write` calls on the file's descriptor. -/
theorem rt_spec (P : DeflateReach.DPending) {ψ : Int32 → C.DeflateState → Nat} {Gr : Nat}
    (hP : DeflatePsi ψ Gr) {W W' : World} {H : Heap} {b : Nat} {s : GzState} {z : ZStream} (hx : GzWX W H b s z)
    (hx' : GzWX W' H b s z) (hd : s.direct = 0) (hfs : FdWrites s.fd W.fs W'.fs)
    (g0 : GStep W (setZ H s.strm (flatZ z)) W' (setZ H s.strm (flatZ z)) b []) (flush : Int32) (l : CompLoop)
    (hl : l.ctl = .go) :
    GSat W' H (cRT (some b) (some s.strm) flush l) (BPost ψ flush W H b s z) := by
  obtain ⟨c, base, d, ko, kx, eb, eo, hdc, hds, eno, enx, hkk, hko, hS, huniq⟩ := wx_bufs hx hd
  have hz := hx.2.1
  have hs' := hx'.1
  have hsz := hx.2.2.1
  unfold cRT
  refine GSat.bind (GSat.lm ⟨_, H, rdZ_run hz _, ?_⟩)
  apply GSat.ite
  · intro ha
    have ha0 : z.avail_out = 0 := by simpa using ha
    refine GSat.bind (GSat.of_eq (rdG_app' hs' _) ?_)
    refine GSat.bind (GSat.lm ⟨(), _, wrZ_run hz _, ?_⟩)
    have hsA : W'.gz (setZ H s.strm { z with avail_out := s.size }) b = some s := hs'
    try dsimp only
    refine GSat.bind (GSat.of_eq (ldGz_app hsA) ?_)
    try dsimp only
    rw [eo]
    refine GSat.bind (gsat_ivget ?_)
    try dsimp only
    refine GSat.bind (GSat.lm ⟨(), _, wrZ_run (setZ_streams_same _ _ _) _, ?_⟩)
    try dsimp only
    rw [setZ_setZ]
    have hsB : W'.gz (setZ H s.strm { { z with avail_out := s.size } with
        next_out := .ref (.heap c) (base + inSize s) }) b = some s := hs'
    refine GSat.bind (GSat.of_eq (ldGz_app hsB) ?_)
    try dsimp only
    rw [eo]
    refine GSat.bind (gsat_ivget ?_)
    try dsimp only
    refine GSat.bind (GSat.of_eq (wrG_app hsB _) ?_)
    try dsimp only
    have hS0 : s.size.toNat ≠ 0 := fun e => hsz (UInt32.toNat_inj.mp (by simpa using e))
    obtain ⟨hxw, gw⟩ := wx_out hx' { { z with avail_out := s.size } with next_out := .ref (.heap c) (base + inSize s) }
      (by rfl) (by rfl) (by rfl) (.val (.ref (.heap c) (base + inSize s))) (fun _ c' base' hb => by
        obtain ⟨rfl, rfl⟩ := huniq c' base' hb
        exact ⟨0, 0, rfl, rfl, Nat.le_refl _, by simp⟩)
    have hs3 := hxw.1
    refine GSat.bind (GSat.lm ⟨_, _, rdZ_run (setZ_streams_same _ _ _) _, ?_⟩)
    try dsimp only
    refine GSat.bind (GSat.of_eq (wrG_app hs3 _) ?_)
    try dsimp only
    simp only [InflateInv.upd_upd]
    refine GSat.mono (tail_spec P hP hxw hd hsz flush l hl) fun l' W6 H6 q => ?_
    refine bpost_tail (z2 := { { z with avail_out := s.size } with next_out := .ref (.heap c) (base + inSize s) }) hx hd hs3 hfs (g0.trans (by rw [setZ_setZ]; exact gw) ⟨s, hx.1⟩ ⟨s, hs'⟩) rfl rfl hsz rfl ?_ q
    refine pot_setZ ψ flush _ hz rfl rfl ?_
    simp only [ha0, hsz, ↓reduceIte]
  · intro ha
    have ha0 : z.avail_out ≠ 0 := by simpa using ha
    obtain ⟨hxw, gw⟩ := wx_out hx' z (by rfl) rfl rfl (.val z.next_out) (fun _ c' base' hb => by
        obtain ⟨rfl, rfl⟩ := huniq c' base' hb
        exact ⟨ko, ko, eno, by rw [eno], Nat.le_refl _, hko⟩)
    rw [setZ_self hz] at hxw
    have hs3 := hxw.1
    refine GSat.bind (GSat.lm ⟨_, _, rdZ_run hz _, ?_⟩)
    try dsimp only
    refine GSat.bind (GSat.of_eq (wrG_app hs' _) ?_)
    try dsimp only
    refine GSat.mono (tail_spec P hP hxw hd ha0 flush l hl) fun l' W6 H6 q => ?_
    exact bpost_tail (H2 := H) hx hd hs3 hfs (g0.trans gw ⟨s, hx.1⟩ ⟨s, hs'⟩) rfl rfl ha0 rfl rfl q

theorem hv_val (n : Nat) (hn : n < 2 ^ 31) : (Int64.ofInt (n : Int)).toUInt64.toUInt32.toNat = n := by
  have h1 : (Int64.ofInt (n : Int)) = Int64.ofNat n := by
    simp [Int64.ofInt, Int64.ofNat]
  rw [h1, UInt32.toNat, UInt64.toUInt32]
  simp only [Int64.ofNat, UInt64.toNat, BitVec.toNat_ofNat, Nat.toUInt32, UInt32.ofNat]
  simp
  omega

/-- **One trip of the loop body of `gz_comp`** on a write handle in the state `GzWX` (not direct). -/
theorem body_spec (P : DeflateReach.DPending) {ψ : Int32 → C.DeflateState → Nat} {Gr : Nat}
    (hP : DeflatePsi ψ Gr) {W : World} {H : Heap} {b : Nat} {s : GzState} {z : ZStream} (hx : GzWX W H b s z)
    (hd : s.direct = 0) (flush : Int32) (l : CompLoop) (hl : l.ctl = .go) :
    GSat W H (compBody (some b) (some s.strm) flush l) (BPost ψ flush W H b s z) := by
  obtain ⟨c, base, d, ko, kx, eb, eo, hdc, hds, eno, enx, hkk, hko, hS, huniq⟩ := wx_bufs hx hd
  have hz := hx.2.1
  have hs := hx.1
  unfold compBody
  refine GSat.bind (GSat.lm ⟨_, H, rdZ_run hz _, ?_⟩)
  try dsimp only
  apply GSat.ite
  · intro _
    refine GSat.bind (GSat.lm ⟨_, H, rdZ_run hz _, ?_⟩)
    try dsimp only
    refine GSat.bind (GSat.of_eq (ldGz_app hs) ?_)
    try dsimp only
    rw [enx]
    refine GSat.bind (gsat_ivget ?_)
    try dsimp only
    rw [eno]
    refine GSat.bind (GSat.lm ⟨_, H, sat_diffW hdc (by omega) (by omega) (by omega), ?_⟩)
    try dsimp only
    have ediff : ((base + inSize s + ko : Nat) : Int) - ((base + inSize s + kx : Nat) : Int) = ((ko - kx : Nat) : Int) := by
      omega
    rw [ediff]
    have hvv := hv_val (ko - kx) (by omega)
    have RT : ∀ W', GzWX W' H b s z → FdWrites s.fd W.fs W'.fs →
        GStep W (setZ H s.strm (flatZ z)) W' (setZ H s.strm (flatZ z)) b [] →
        GSat W' H (cRT (some b) (some s.strm) flush l) (BPost ψ flush W H b s z) :=
      fun W' hx' hf g => rt_spec P hP hx hx' hd hf g flush l hl
    apply GSat.ite
    · intro _
      refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
      try dsimp only
      refine GSat.bind (GSat.of_eq (ldGz_app hs) ?_)
      try dsimp only
      rw [enx]
      refine GSat.bind (gsat_ivget ?_)
      try dsimp only
      obtain ⟨r, bs, ew⟩ := writeG_fd W H s.fd (.ref (.heap c) (base + inSize s + kx))
        (Int64.ofInt ((ko - kx : Nat) : Int)).toUInt64.toUInt32.toUInt64
        (Or.inr ⟨.heap c, base + inSize s + kx, d, rfl, hdc, by simp only [UInt32.toNat_toUInt64]; omega⟩)
      refine GSat.bind (GSat.of_eq ew ?_)
      try dsimp only
      have hx1 : GzWX { W with fs := (W.fs.writeCall s.fd bs).2 } H b s z := hx
      have g1 : GStep W (setZ H s.strm (flatZ z)) { W with fs := (W.fs.writeCall s.fd bs).2 }
          (setZ H s.strm (flatZ z)) b [] := gstep_fs (GStep.refl _ _ _ _) _
      have f1 : FdWrites s.fd W.fs ({ W with fs := (W.fs.writeCall s.fd bs).2 } : World).fs := FdWrites.one _ _ _
      apply GSat.ite
      · intro _
        refine GSat.mono (gsat_andC (gz_error_strX hz hx1.2.2.2.1 hx1.1 ({ l with ctl := .ret } : CompLoop))
          (gz_error_strX_frees hz hx1.2.2.2.1 hx1.1 ({ l with ctl := .ret } : CompLoop)))
          fun l' W2 H2 q => ?_
        obtain ⟨⟨rfl, q⟩, hfree⟩ := q
        obtain ⟨s2, hx2, he2, hfs2, g2⟩ := wx_err hx1 q
        have hst2 : H2.streams = H.streams := q.choose_spec.2.2.2.2.1
        refine ⟨s2, z, hx2, LFix.of_err he2, by rw [hfs2]; exact f1, g1.trans g2 ⟨s, hs⟩ ⟨s, hs⟩,
          UInt32.le_refl _, ?_, fun hi => inOk_adv hd (LFix.of_err he2).buffers (LFix.of_err he2).size
            (LFix.of_err he2).fix.direct hi (UInt32.le_refl _) (by simpa using adv_zero z.next_in), Or.inl rfl,
          Or.inr hfree, rfl⟩
        simpa using adv_zero z.next_in
      · intro _
        have T := RT _ hx1 f1 g1
        dsimp only [cRT, cTail] at T
        exact T
    · intro _
      have T := RT W hx (FdWrites.refl _ _) (GStep.refl _ _ _ _)
      dsimp only [cRT, cTail] at T
      exact T
  · intro ha
    have ha0 : z.avail_out ≠ 0 := by
      intro e; apply ha; simp [e]
    have T := tail_spec P hP hx hd ha0 flush l hl
    dsimp only [cTail] at T
    exact GSat.mono T fun l' W' H' q => bpost_tail (nx := s.next) (H2 := H) (z2 := z) hx hd hs (FdWrites.refl _ _)
      (GStep.refl _ _ _ _) rfl rfl ha0 rfl rfl q

/-! ## The loop -/

/-- The facts the loop of `gz_comp` keeps, from its entry `w0`, `h0`, `s0`, `z0` to `W`, `H`, `s`, `z`. -/
def LFacts (w0 : World) (h0 : Heap) (b : Nat) (s0 : GzState)
    (z0 : ZStream) (W : World) (H : Heap) (s : GzState) (z : ZStream) : Prop :=
  GzWX W H b s z ∧ LFix s0 s ∧ FdWrites s0.fd w0.fs W.fs ∧
    GStep w0 (setZ h0 s0.strm (flatZ z0)) W (setZ H s0.strm (flatZ z)) b [] ∧
    z.avail_in ≤ z0.avail_in ∧ Adv z0.next_in z.next_in (z0.avail_in.toNat - z.avail_in.toNat) ∧
    (InOk s0 z0 → InOk s z) ∧ MKeep s0 s H ∧ z.state = z0.state

/-- The invariant of the loop of `gz_comp`. -/
def LInv (ψ : Int32 → C.DeflateState → Nat) (flush : Int32) (w0 : World) (h0 : Heap) (b : Nat) (s0 : GzState)
    (z0 : ZStream) (l : CompLoop) (W : World) (H : Heap) : Prop :=
  l.ctl = .go ∧ ∃ s z, LFacts w0 h0 b s0 z0 W H s z ∧
    pot ψ flush s0.size.toNat H s0.strm ≤ pot ψ flush s0.size.toNat h0 s0.strm

/-- What the loop of `gz_comp` leaves. -/
def LPost (ψ : Int32 → C.DeflateState → Nat) (flush : Int32) (w0 : World) (h0 : Heap) (b : Nat) (s0 : GzState)
    (z0 : ZStream) (l : CompLoop) (W : World) (H : Heap) : Prop :=
  ∃ s z, LFacts w0 h0 b s0 z0 W H s z ∧
    (l.ctl = .ret ∨ (l.ctl = .go ∧ pot ψ flush s0.size.toNat H s0.strm ≤ pot ψ flush s0.size.toNat h0 s0.strm ∧
      z.avail_out ≠ 0 ∧ (flush ≠ ZlibNg.Inflate.Z_FINISH → z.avail_in = 0)))

theorem lfacts_step {w0 W W' : World} {h0 H H' : Heap} {b : Nat}
    {s0 s s' : GzState} {z0 z z' : ZStream} (hs0 : w0.gz h0 b = some s0) (F : LFacts w0 h0 b s0 z0 W H s z)
    (hx' : GzWX W' H' b s' z') (hlf : LFix s s') (hfs : FdWrites s.fd W.fs W'.fs)
    (g : GStep W (setZ H s.strm (flatZ z)) W' (setZ H' s.strm (flatZ z')) b [])
    (h1 : z'.avail_in ≤ z.avail_in) (h2 : Adv z.next_in z'.next_in (z.avail_in.toNat - z'.avail_in.toNat))
    (h3 : InOk s z → InOk s' z') (hmk : MKeep s s' H') (hzs : z'.state = z.state) :
    LFacts w0 h0 b s0 z0 W' H' s' z' := by
  obtain ⟨hx, f1, f2, f3, f4, f5, f6, f7, f8⟩ := F
  have mono := wx_mono hx g
  have hst : s.strm = s0.strm := f1.fix.strm
  have hfd : s.fd = s0.fd := f1.fix.fd
  rw [hst] at g; rw [hfd] at hfs
  have l1 := UInt32.le_iff_toNat_le.mp h1
  have l2 := UInt32.le_iff_toNat_le.mp f4
  refine ⟨hx', f1.trans hlf, f2.trans hfs, f3.trans g ⟨s0, hs0⟩ ⟨s, hx.1⟩, UInt32.le_trans h1 f4, ?_,
    fun hi => h3 (f6 hi), f7.trans hmk mono, hzs.trans f8⟩
  · have := adv_trans f5 h2
    have e : z0.avail_in.toNat - z.avail_in.toNat + (z.avail_in.toNat - z'.avail_in.toNat) =
        z0.avail_in.toNat - z'.avail_in.toNat := by omega
    rw [e] at this; exact this

/-- **The loop of `gz_comp`** on a write handle in the state `GzWX` (not direct). -/
theorem loop_spec (P : DeflateReach.DPending) {ψ : Int32 → C.DeflateState → Nat} {Gr : Nat}
    (hP : DeflatePsi ψ Gr) {w0 : World} {h0 : Heap} {b : Nat} {s0 : GzState} {z0 : ZStream}
    (hx : GzWX w0 h0 b s0 z0) (hd : s0.direct = 0) (flush : Int32) :
    GSat w0 h0 (gdoWhile (compBody (some b) (some s0.strm) flush) compCond ⟨ZlibNg.Inflate.Z_OK, 0, .go⟩)
      (LPost ψ flush w0 h0 b s0 z0) := by
  have hs0 : w0.gz h0 b = some s0 := hx.1
  refine gsat_gdoWhile (LInv ψ flush w0 h0 b s0 z0) (fun _ _ H => pot ψ flush s0.size.toNat H s0.strm) _
    (fun l W H hI => ?_) ⟨rfl, s0, z0, ⟨hx, LFix.refl s0, FdWrites.refl _ _, GStep.refl _ _ _ _,
      UInt32.le_refl _, by simpa using adv_zero z0.next_in, id, Or.inl rfl, rfl⟩, Nat.le_refl _⟩ ?_
  · obtain ⟨hl, s, z, F, hp⟩ := hI
    have hx1 := F.1
    have hd' : s.direct = 0 := F.2.1.fix.direct.trans hd
    have hstrm : s.strm = s0.strm := F.2.1.fix.strm
    have hsize : s.size = s0.size := F.2.1.size
    have B := body_spec P hP hx1 hd' flush l hl
    rw [hstrm] at B
    refine GSat.mono B fun l1 W1 H1 q => ?_
    obtain ⟨s1, z1, hx2, hlf, hfs, g, h1, h2, h3, hr, hmk, hzs⟩ := q
    have F1 := lfacts_step hs0 F hx2 hlf hfs g h1 h2 h3 hmk hzs
    unfold compCond
    apply GSat.ite
    · intro hc
      refine GSat.pure ⟨fun e => absurd e (by simp), fun _ => ⟨s1, z1, F1, Or.inl ?_⟩⟩
      rcases hr with e | ⟨e, -⟩
      · exact e
      · simp [e] at hc
    · intro hc
      have hgo : l1.ctl = .go := by simpa using hc
      rcases hr with e | ⟨-, pl, plt, p0⟩
      · rw [hgo] at e; cases e
      rw [hstrm, hsize] at pl plt
      refine GSat.pure ⟨fun e => ⟨⟨hgo, s1, z1, F1, Nat.le_trans pl hp⟩, ?_⟩, fun e => ⟨s1, z1, F1, Or.inr ?_⟩⟩
      · exact Nat.lt_of_lt_of_le (plt (by simpa using e)) (Nat.le_refl _)
      · have e' : l1.hv = 0 := by simpa using e
        exact ⟨hgo, Nat.le_trans pl hp, (p0 e').1, (p0 e').2⟩
  · obtain ⟨sb, st, hsb, hst, hdi, hreg, hS8, hS, hle⟩ := wx_facts hx hd
    have hz := hx.2.1
    rw [pot_eq ψ flush _ hz hsb hst]
    have h48 := hP.2.1 h0 (some s0.strm) sb st flush hdi hreg ⟨⟨z0, ⟨_, rfl, hz⟩, hsb⟩, hst⟩
    have hai := z0.avail_in.toNat_lt
    have hif : (if z0.avail_out = 0 then s0.size.toNat else z0.avail_out.toNat) ≤ s0.size.toNat := by
      split <;> omega
    show _ < 2 ^ 64
    omega

end ZlibNgF.Proof.GzWrite
