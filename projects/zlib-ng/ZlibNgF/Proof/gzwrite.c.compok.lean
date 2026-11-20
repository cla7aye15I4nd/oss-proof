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

end ZlibNgF.Proof.GzWrite
