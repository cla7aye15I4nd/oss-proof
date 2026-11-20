import ZlibNgF.Proof.«gzwrite.c.compspec»

/-!
# The pieces of `gz_comp` (`ZlibNgF`)

`gz_comp` with its loop split out (`compAll`, `compBody`, `compCond`; the body's join points `cTail` and `cRT`),
`write` on a descriptor as an `FdWrites` step (`writeG_fd`), and the change of the output fields and `x.next` of a
write handle in the state `GzWX` (`wx_out`).
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
        (flush ≠ ZlibNg.Inflate.Z_FINISH → z'.avail_in = 0 ∨ z'.avail_out = 0)))

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
    refine GSat.mono (gz_error_litX _ 10 lit_dcorrupt lit_dcorrupt_get nonul_dcorrupt hz' hv' hs'
      ZlibNg.Inflate.Z_STREAM_ERROR ({ l with ret := r, ctl := .ret } : CompLoop)) fun l' W2 H2 q => ?_
    obtain ⟨rfl, q⟩ := q
    obtain ⟨s2, hx2, he2, hfs2, g2⟩ := wx_err hx' q
    exact ⟨s2, z', hx2, hfs2, g.trans g2 ⟨s, hx.1⟩ ⟨s, hx'.1⟩, hadv, Or.inl ⟨rfl, he2⟩⟩
  · intro hne
    refine GSat.bind (GSat.lm ⟨_, H', rdZ_run hz' _, GSat.pure ?_⟩)
    refine ⟨s, z', hx', rfl, g, hadv, Or.inr ⟨hl, rfl, rfl, pl, fun h1 => plt fun e2 => h1 ?_,
      fun h1 => hdone h1 (by simpa using hne)⟩⟩
    show z.avail_out - z'.avail_out = 0
    rw [e2]; exact UInt32.sub_self _

end ZlibNgF.Proof.GzWrite
