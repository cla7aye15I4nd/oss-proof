import ZlibNgF.Proof.«gzlib.c.seek»

/-!
# `gzclose_r` releases a read handle (`ZlibNgF`)

`gzclose_r` of a read handle ends the inflate stream and frees the buffers (when they exist), frees the message,
the path and the state, ends the embedded stream and closes the descriptor (`GzReleased`); of a write handle it
returns `Z_STREAM_ERROR` at the mode check.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace ZlibNgF.Proof.GzMode
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Gz ZlibNgF.Proof.GzInv ZlibNgF.Proof.GzSat

/-- The end of `gzclose_r` from the saved error on (`gzread.c:609-615`): the copy of the source text that the
translation repeats after both branches of `if (state->size)`. -/
def closeTail (state : GzPtr) : G Int32 := do
  let err := if (← rdG state (·.err)) == ZlibNg.Inflate.Z_BUF_ERROR then ZlibNg.Inflate.Z_BUF_ERROR else ZlibNg.Inflate.Z_OK
  gz_error state ZlibNg.Inflate.Z_OK .null
  lm (freeB (← (← ldGz state).path.get))
  let ret ← closeG (← rdG state (·.fd))
  gzStateFree state
  return if ret != 0 then Z_ERRNO else err

theorem gzclose_r_eq (b : Nat) : gzclose_r (some b) = (do
    if (← rdG (some b) (·.mode)) != GZ_READ then
      return ZlibNg.Inflate.Z_STREAM_ERROR
    if (← rdG (some b) (·.size)) != 0 then
      let _ ← lm (ZlibNg.Inflate.inflateEnd (← strmOf (some b)))
      gz_buffer_free (some b)
    closeTail (some b)) := rfl

theorem ldGz_live {h : Heap} {b : Nat} {d : Array UInt8} (hb : h.bytes b = some d) (W : World) (s : GzState)
    (hW : W.gzs b = some s) : ldGz (some b) W h = .ok ((s, W), h) :=
  ldGz_app (by unfold World.gz; rw [hb]; exact hW)

/-- `free` of the live heap block `c`. -/
def freeH (h : Heap) (c : Nat) : Heap := { h with bytes := upd h.bytes c none, savedPtrs := upd h.savedPtrs c none }

theorem freeB_app {h : Heap} {c : Nat} {d : Array UInt8} (hd : h.bytes c = some d) :
    freeB (.ref (.heap c) 0) h = .ok ((), freeH h c) := by
  simp [freeB, hd, freeH]

theorem freeH_bytes_ne {h : Heap} {c c' : Nat} (hne : c' ≠ c) : (freeH h c).bytes c' = h.bytes c' := by
  simp [freeH, upd_ne _ _ _ _ hne]

theorem freeH_bytes_eq (h : Heap) (c : Nat) : (freeH h c).bytes c = none := by simp [freeH]

/-- The heap after `closeTail` from `H`, with message freed, path block `cp`, state block `b`, stream `i`. -/
def closeH (H : Heap) (s : GzState) (cp b i : Nat) : Heap :=
  { freeH (freeH (freeMsg H s) cp) b with streams := upd H.streams i none }

theorem closeTail_ok {W : World} {H : Heap} {b : Nat} {s : GzState} {z : ZStream} {cp : Nat} {dp : Array UInt8}
    (hs : W.gz H b = some s) (hm : GzMsg H s) (hmb : ∀ c o, s.msg = .val (.ref (.heap c) o) → c ≠ b)
    (hp : s.path = .val (.ref (.heap cp) 0)) (hdp : H.bytes cp = some dp) (hcpb : cp ≠ b) (hcpm : cp ∉ blkOf s.msg)
    (hz : H.streams s.strm = some z) :
    ∃ r, GzRun (closeTail (some b)) W H r
      { W with fs := (W.fs.closeCall s.fd).2, gzs := upd W.gzs b none } (closeH H s cp b s.strm) := by
  obtain ⟨db, hdb⟩ := gz_live hs
  have hbm : b ∉ blkOf s.msg := by
    intro hb
    unfold blkOf at hb; split at hb
    · next c o e => simp at hb; exact hmb c o e hb.symm
    · simp at hb
  have hdbM : (freeMsg H s).bytes b = some db := by rw [freeMsg_bytes H s b hbm]; exact hdb
  have hdpM : (freeMsg H s).bytes cp = some dp := by rw [freeMsg_bytes H s cp hcpm]; exact hdp
  have hdbP : (freeH (freeMsg H s) cp).bytes b = some db := by rw [freeH_bytes_ne (Ne.symm hcpb)]; exact hdbM
  have hzB : (freeH (freeH (freeMsg H s) cp) b).streams s.strm = some z := by
    simp only [freeH]; rw [freeMsg_streams]; exact hz
  have e := gz_error_null_app hs hm hmb ZlibNg.Inflate.Z_OK
  have hl4 := ldGz_live hdbP { W with fs := (W.fs.closeCall s.fd).2, gzs := upd W.gzs b (some (errSt s ZlibNg.Inflate.Z_OK)) }
    (errSt s ZlibNg.Inflate.Z_OK) (by simp)
  simp [errSt, hp] at hl4
  refine ⟨if (W.fs.closeCall s.fd).1 ≠ 0 then Z_ERRNO else
    if s.err = ZlibNg.Inflate.Z_BUF_ERROR then ZlibNg.Inflate.Z_BUF_ERROR else ZlibNg.Inflate.Z_OK, ?_⟩
  simp only [GzRun, C.run, StateT.run]
  simp [closeTail, rdG_app' hs, e, ldGz_upd hdbM, errSt, hp, Ival.get, liftM, monadLift, MonadLift.monadLift,
    freeB_app hdpM, rdG_upd hdbP, closeG, modifyFs, gzStateFree, hl4, freeB_app hdbP,
    InflateInv.upd_upd, dropStream, hzB, closeH]
  simp [freeH, freeMsg_streams]

/-- `zng_free_aligned` of the buffers of a file: the saved pointer gives the block, which is freed. -/
theorem free_aligned_app {h : Heap} {c base : Nat} {d : Array UInt8} (hd : h.bytes c = some d)
    (hb : base ≤ d.size) (h8 : 8 ≤ base) (hsv : h.savedPtrs c = some (base - 8, .ref (.heap c) 0)) :
    ZlibNg.Zutil.zng_free_aligned (.ref (.heap c) base) h = .ok ((), freeH h c) := by
  have hadd : Ptr.add (.ref (.heap c) base : BPtr) (-8) h = .ok (.ref (.heap c) (base - 8), h) := by
    have := Inftrees.add_ok (r := BRef.heap c) (off := base) (k := -8) (a := d) (h := h) hd hb (by omega) (by omega)
    rw [this]; congr 3; omega
  simp [ZlibNg.Zutil.zng_free_aligned, hadd, loadPtrSlot, hd, hsv, show base - 8 + 8 ≤ d.size by omega, freeB, freeH]

/-- The state after `gz_buffer_free`. -/
def bfSt (s : GzState) : GzState :=
  { s with buffers := .val .null, out := .val .null, «in» := .val .null, size := 0 }

/-- The run of `gzclose_r` on a read handle, up to `closeTail`: with buffers, `inflateEnd` and `gz_buffer_free`. -/
theorem gzclose_r_pre {w : World} {h : Heap} {b : Nat} {s : GzState} (hs : w.gz h b = some s)
    (hr : s.mode = GZ_READ) :
    (s.size = 0 → ∀ r W' H', GzRun (closeTail (some b)) w h r W' H' → GzRun (gzclose_r (some b)) w h r W' H') ∧
    (∀ (H1 : Heap) (c base : Nat) (d : Array UInt8), s.size ≠ 0 →
      C.run (ZlibNg.Inflate.inflateEnd (some s.strm)) h = .ok (ZlibNg.Inflate.Z_OK, H1) →
      s.buffers = .val (.ref (.heap c) base) → H1.bytes c = some d → base ≤ d.size → 8 ≤ base →
      H1.savedPtrs c = some (base - 8, .ref (.heap c) 0) → H1.bytes b = h.bytes b → c ≠ b →
      ∀ r W' H', GzRun (closeTail (some b)) { w with gzs := upd w.gzs b (some (bfSt s)) } (freeH H1 c) r W' H' →
        GzRun (gzclose_r (some b)) w h r W' H') := by
  obtain ⟨db, hdb⟩ := gz_live hs
  refine ⟨fun hz r W' H' e => ?_, fun H1 c base d hz he hbuf hd hbd h8 hsv hb1 hcb r W' H' e => ?_⟩
  · simp only [GzRun, C.run, StateT.run] at e ⊢
    rw [gzclose_r_eq]
    simp [rdG_app' hs, hr, hz, e]
  · simp only [GzRun, C.run, StateT.run] at e ⊢
    simp only [C.run] at he
    have hdb1 : H1.bytes b = some db := by rw [hb1]; exact hdb
    have hs1 : w.gz H1 b = some s := by unfold World.gz at hs ⊢; rw [hdb1]; rw [hdb] at hs; exact hs
    have hdbF : (freeH H1 c).bytes b = some db := by rw [freeH_bytes_ne (Ne.symm hcb)]; exact hdb1
    have hs2 : w.gz (freeH H1 c) b = some s := by unfold World.gz at hs ⊢; rw [hdbF]; rw [hdb] at hs; exact hs
    rw [gzclose_r_eq]
    simp [rdG_app' hs, hr, hz, strmOf_app hs, he, gz_buffer_free, ldGz_app hs1, hbuf, Ival.get, liftM, monadLift,
      MonadLift.monadLift, free_aligned_app hd hbd h8 hsv, wrG_upd hdbF, wrG_app hs2, InflateInv.upd_upd]
    simp [bfSt, hr] at e
    exact e

theorem freeMsg_cases (h : Heap) (s : GzState) : freeMsg h s = h ∨ ∃ c, freeMsg h s = freeH h c := by
  unfold freeMsg; split
  · split
    · exact Or.inl rfl
    · next c _ _ => exact Or.inr ⟨c, rfl⟩
  · exact Or.inl rfl

theorem freeMsg_msg_none {h : Heap} {s : GzState} (hm : GzMsg h s) : ∀ c ∈ blkOf s.msg, (freeMsg h s).bytes c = none := by
  intro c hc
  rcases hm.msg with e | ⟨c', n, e, -⟩
  · rw [e] at hc; simp [blkOf] at hc
  · rw [e] at hc; simp [blkOf] at hc; subst hc
    have hne : s.err ≠ ZlibNg.Inflate.Z_MEM_ERROR := fun e' => by have := hm.mem e'; rw [e] at this; cases this
    unfold freeMsg; rw [e]; simp [hne]

/-- A `GzFrame` for a step that frees only blocks of the file, changes only its stream and its `gz_state`, and keeps
the other parts of the heap. -/
theorem gzframe_gen {w w' : World} {h h' : Heap} {f : GzPtr}
    (hb : ∀ c, c ∉ GzOwned w h f → h'.bytes c = h.bytes c)
    (hst : ∀ i, (∀ b s, f = some b → w.gz h b = some s → i ≠ s.strm) → h'.streams i = h.streams i)
    (hc : h'.consts = h.consts) (hi : h'.istates = h.istates) (ha : h'.iallocs = h.iallocs)
    (hd : h'.dstates = h.dstates) (hda : h'.dallocs = h.dallocs) (hcrc : h'.crcTable = h.crcTable)
    (hx : h'.x2nTable = h.x2nTable) (hba : h'.baseAddr = h.baseAddr) (hn : h'.nextBlk = h.nextBlk)
    (hhd : h'.gzheaders = h.gzheaders)
    (hg : ∀ b, f ≠ some b → b < h.nextBlk → w'.gzs b = w.gzs b) : GzFrame w h w' h' f [] := by
  refine ⟨⟨⟨fun i hi' => ?_, fun k _ => by simp [hhd], fun c _ _ => by simp [hi, ha],
    fun c _ hc' d hd' => ⟨d, by simp only; rw [hb c hc']; exact hd', rfl, fun _ _ _ => rfl⟩,
    fun c _ hc' hn' => by simp only; rw [hb c hc']; exact hn', rfl, hcrc, hx, hba, by simp [hn]⟩,
    fun c _ _ => by simp [hd, hda]⟩, fun k a e => by rw [hc]; exact e, hg⟩
  refine hst i fun b s e hs => ?_
  subst e
  simp only [hs, List.mem_singleton] at hi'
  exact hi'

theorem freeMsg_bytes_none {h : Heap} {s : GzState} {c : Nat} (hc : h.bytes c = none) : (freeMsg h s).bytes c = none :=
  freeMsg_none h s c hc

theorem freeH_none {h : Heap} {c x : Nat} (hx : h.bytes x = none) : (freeH h c).bytes x = none := by
  by_cases e : x = c
  · rw [e]; exact freeH_bytes_eq h c
  · rw [freeH_bytes_ne e]; exact hx

/-- The bytes after `closeTail`. -/
theorem closeH_bytes (H : Heap) (s : GzState) (cp b i x : Nat) :
    ((x ≠ cp ∧ x ≠ b ∧ x ∉ blkOf s.msg) → (closeH H s cp b i).bytes x = H.bytes x) ∧
    ((x = cp ∨ x = b) → (closeH H s cp b i).bytes x = none) ∧
    (H.bytes x = none → (closeH H s cp b i).bytes x = none) ∧
    (GzMsg H s → x ∈ blkOf s.msg → (closeH H s cp b i).bytes x = none) := by
  refine ⟨fun ⟨h1, h2, h3⟩ => ?_, fun hx => ?_, fun hx => ?_, fun hm hx => ?_⟩
  · show (freeH (freeH (freeMsg H s) cp) b).bytes x = _
    rw [freeH_bytes_ne h2, freeH_bytes_ne h1, freeMsg_bytes H s x h3]
  · show (freeH (freeH (freeMsg H s) cp) b).bytes x = _
    rcases hx with rfl | rfl
    · by_cases e : x = b
      · rw [e]; exact freeH_bytes_eq _ _
      · rw [freeH_bytes_ne e]; exact freeH_bytes_eq _ _
    · exact freeH_bytes_eq _ _
  · exact freeH_none (freeH_none (freeMsg_bytes_none hx))
  · exact freeH_none (freeH_none (freeMsg_msg_none hm x hx))

theorem closeH_other (H : Heap) (s : GzState) (cp b i : Nat) :
    (closeH H s cp b i).consts = H.consts ∧ (closeH H s cp b i).istates = H.istates ∧
    (closeH H s cp b i).iallocs = H.iallocs ∧ (closeH H s cp b i).dstates = H.dstates ∧
    (closeH H s cp b i).dallocs = H.dallocs ∧ (closeH H s cp b i).crcTable = H.crcTable ∧
    (closeH H s cp b i).x2nTable = H.x2nTable ∧ (closeH H s cp b i).baseAddr = H.baseAddr ∧
    (closeH H s cp b i).nextBlk = H.nextBlk ∧ (closeH H s cp b i).gzheaders = H.gzheaders ∧
    (closeH H s cp b i).streams = upd H.streams i none := by
  rcases freeMsg_cases H s with e | ⟨c, e⟩ <;> simp [closeH, freeH, e]

end ZlibNgF.Proof.GzMode

namespace ZlibNgF.Proof.GzMode
open C
theorem setFd_ofile (fs : Fs) (fd : Int32) (hfd : ¬ fd < 0) : (fs.setFd fd.toNatClampNeg none).ofile? fd = none := by
  unfold Fs.ofile? Fs.setFd
  simp only [hfd, ite_false]
  split
  · next hlt => simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, hlt]
  · next hlt =>
    have : fd.toNatClampNeg < (fs.fds ++ Array.replicate (fd.toNatClampNeg + 1 - fs.fds.size) none).size := by
      simp; omega
    have h2 : fd.toNatClampNeg < fs.fds.size + (fd.toNatClampNeg + 1 - fs.fds.size) := by omega
    simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, h2]

theorem closeCall_ofile (fs : Fs) (fd : Int32) : (fs.closeCall fd).2.ofile? fd = none := by
  have reg : ∀ w : Fs, (w.closeReg fd).2.ofile? fd = none := by
    intro w
    unfold Fs.closeReg
    split
    · next o ho =>
      have hfd : ¬ fd < 0 := by intro e; unfold Fs.ofile? at ho; simp [e] at ho
      exact setFd_ofile w fd hfd
    · next ho => exact ho
  unfold Fs.closeCall
  simp only
  split
  · split
    · have := reg { fs with ncall := fs.ncall + 1 }
      unfold Fs.ofile? at this ⊢; exact this
    · exact reg _
  · exact reg _
end ZlibNgF.Proof.GzMode

namespace ZlibNgF.Proof.GzMode
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Gz ZlibNgF.Proof.GzInv ZlibNgF.Proof.GzSat

theorem nodup_parts {h : Heap} {b cp : Nat} {s : GzState} (hcp : s.path = .val (.ref (.heap cp) 0))
    (hn : (ownL h b s).Nodup) : cp ≠ b ∧ cp ∉ blkOf s.msg ∧ b ∉ blkOf s.msg ∧
      (s.size ≠ 0 → ∀ x ∈ blkOf s.buffers ++ stBlk h s, x ≠ b ∧ x ≠ cp ∧ x ∉ blkOf s.msg) ∧
      (s.size ≠ 0 → (blkOf s.buffers ++ stBlk h s).Nodup) := by
  unfold ownL at hn
  rw [hcp] at hn
  have hp : blkOf (Ival.val (Ptr.ref (BRef.heap cp) 0)) = [cp] := rfl
  rw [hp] at hn
  rw [List.nodup_append] at hn
  obtain ⟨hn1, hn2, hn3⟩ := hn
  rw [List.nodup_append] at hn1
  obtain ⟨hn11, -, hn13⟩ := hn1
  have e1 : cp ≠ b := fun e => (List.nodup_append.mp hn11).2.2 b (by simp) cp (by simp) e.symm
  refine ⟨e1, fun hc => hn13 cp (by simp) cp hc rfl, fun hc => hn13 b (by simp) b hc rfl, fun hsz x hx => ?_,
    fun hsz => by simpa [hsz] using hn2⟩
  have hx' : x ∈ (if s.size = 0 then [] else blkOf s.buffers ++ stBlk h s) := by simp [hsz, hx]
  refine ⟨fun e => hn3 b (by simp) x hx' e.symm, fun e => hn3 cp (by simp) x hx' e.symm,
    fun hm => hn3 x (by simp [hm]) x hx' rfl⟩

/-- **`gzclose_r` of a read handle** returns, stays in the frame of the file, and releases it. -/
theorem gzclose_r_read {w : World} {h : Heap} {b : Nat} {s : GzState} (hs : w.gz h b = some s) (sh : GzShape h s)
    (hn : (ownL h b s).Nodup) (hr : s.mode = GZ_READ) :
    ∃ r w' h', GzRun (gzclose_r (some b)) w h r w' h' ∧ GzFrame w h w' h' (some b) [] ∧
      GzReleased w h w' h' (some b) := by
  obtain ⟨cp, np, hcp, r0, off0, dp, e0, hdp, -⟩ := sh.path
  cases e0
  have hdp' : h.bytes cp = some dp := hdp
  obtain ⟨hcpb, hcpm, hbm, hrest, hnd2⟩ := nodup_parts hcp hn
  have hmb := msg_ne_b hn
  obtain ⟨z, hz⟩ := sh.strm
  obtain ⟨db, hdb⟩ := gz_live hs
  have hown : ∀ x, x ∈ GzOwned w h (some b) ↔
      x = b ∨ x = cp ∨ x ∈ blkOf s.msg ∨ x ∈ blkOf s.buffers ++ stBlk h s := by
    intro x
    have e : GzOwned w h (some b) = [b] ++ [cp] ++ blkOf s.msg ++ blkOf s.buffers ++ stBlk h s := by
      simp only [GzOwned, hs, hcp]; rfl
    rw [e]; simp only [List.mem_append, List.mem_singleton, or_assoc]
  by_cases hsz : s.size = 0
  · obtain ⟨r, e⟩ := closeTail_ok hs sh.msg hmb hcp hdp' hcpb hcpm hz
    obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11⟩ := closeH_other h s cp b s.strm
    refine ⟨r, _, _, (gzclose_r_pre hs hr).1 hsz _ _ _ e, ?_, ?_⟩
    · refine gzframe_gen (fun x hx => ?_) (fun i hi => ?_) o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 (fun c hc _ => ?_)
      · have := fun h' => hx ((hown x).mpr h')
        exact (closeH_bytes h s cp b s.strm x).1 ⟨fun e => this (Or.inr (Or.inl e)), fun e => this (Or.inl e),
          fun e => this (Or.inr (Or.inr (Or.inl e)))⟩
      · rw [o11, upd_ne _ _ _ _ (hi b s rfl hs)]
      · have hcb : c ≠ b := fun e => hc (by rw [e])
        simp [upd_ne _ _ _ _ hcb]
    · intro b' s' e1 e2
      cases e1; rw [hs] at e2; cases e2
      refine ⟨fun x hx => ?_, by simp, by rw [o11]; simp, closeCall_ofile _ _⟩
      rcases (hown x).mp hx with h1 | h1 | h1 | h1
      · exact (closeH_bytes h s cp b s.strm x).2.1 (Or.inr h1)
      · exact (closeH_bytes h s cp b s.strm x).2.1 (Or.inl h1)
      · exact (closeH_bytes h s cp b s.strm x).2.2.2 sh.msg h1
      · exact (closeH_bytes h s cp b s.strm x).2.2.1 (sh.dead hsz x h1).1
  · have R := sh.read hr
    obtain ⟨c, base, z0, hb, hi, hz0, -, -, -⟩ := R.bufs hsz
    rw [hz] at hz0; cases hz0
    obtain ⟨i, z1, sb, e1, hz1, hsb, he⟩ := InflateControl.inflateEnd_inv hi
    cases e1
    rw [hz] at hz1; cases hz1
    have hcL : c ∈ blkOf s.buffers ++ stBlk h s := by simp [hb.buffers, blkOf]
    have hsbL : sb ∈ blkOf s.buffers ++ stBlk h s := by simp [stBlk, hz, hsb]
    obtain ⟨hcb, hccp, hcm⟩ := hrest hsz c hcL
    obtain ⟨hsbb, hsbcp, hsbm⟩ := hrest hsz sb hsbL
    have hcsb : c ≠ sb := by
      have := hnd2 hsz
      rw [hb.buffers] at this
      simp [blkOf, stBlk, hz, hsb] at this
      exact this
    obtain ⟨d, hd, hds⟩ := hb.fits
    let H1 : Heap :=
      { h with
        bytes := upd h.bytes sb none
        savedPtrs := upd h.savedPtrs sb none
        streams := upd h.streams s.strm (some { z with state := none }) }
    have hH1b : ∀ x, x ≠ sb → H1.bytes x = h.bytes x := fun x hx => by simp [H1, upd_ne _ _ _ _ hx]
    have hd1 : H1.bytes c = some d := by rw [hH1b c hcsb]; exact hd
    have hsv1 : H1.savedPtrs c = some (base - 8, .ref (.heap c) 0) := by
      simp only [H1]; rw [upd_ne _ _ _ _ hcsb]; exact hb.hdr.2
    let H2 := freeH H1 c
    have hH2b : ∀ x, x ≠ sb → x ≠ c → H2.bytes x = h.bytes x := fun x h1 h2 => by
      simp only [H2]; rw [freeH_bytes_ne h2, hH1b x h1]
    have hdb2 : H2.bytes b = some db := by rw [hH2b b (Ne.symm hsbb) (Ne.symm hcb)]; exact hdb
    have hs2 : ({ w with gzs := upd w.gzs b (some (bfSt s)) } : World).gz H2 b = some (bfSt s) := by
      unfold World.gz; rw [hdb2]; simp
    have hm2 : GzMsg H2 (bfSt s) := by
      refine ⟨?_, sh.msg.mem⟩
      rcases sh.msg.msg with e | hm
      · exact Or.inl e
      · refine Or.inr (ownBlk_keep hm fun x hx => hH2b x (fun e => hsbm (e ▸ hx)) (fun e => hcm (e ▸ hx)))
    have hdp2 : H2.bytes cp = some dp := by rw [hH2b cp (Ne.symm hsbcp) (Ne.symm hccp)]; exact hdp'
    have hz2 : H2.streams (bfSt s).strm = some { z with state := none } := by simp [H2, H1, freeH, bfSt]
    obtain ⟨r, e⟩ := closeTail_ok hs2 hm2 hmb hcp hdp2 hcpb hcpm hz2
    have hrun := (gzclose_r_pre hs hr).2 H1 c base d hsz he hb.buffers hd1 (by have := hb.fits; omega) hb.hdr.1 hsv1
      (hH1b b (Ne.symm hsbb)) hcb r _ _ e
    obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11⟩ := closeH_other H2 (bfSt s) cp b (bfSt s).strm
    refine ⟨r, _, _, hrun, ?_, ?_⟩
    · refine gzframe_gen (fun x hx => ?_) (fun j hj => ?_) o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 (fun c' hc' _ => ?_)
      · have hx' := fun h' => hx ((hown x).mpr h')
        rw [(closeH_bytes H2 (bfSt s) cp b (bfSt s).strm x).1 ⟨fun e => hx' (Or.inr (Or.inl e)),
          fun e => hx' (Or.inl e), fun e => hx' (Or.inr (Or.inr (Or.inl e)))⟩]
        exact hH2b x (fun e => hx' (Or.inr (Or.inr (Or.inr (e ▸ hsbL)))))
          (fun e => hx' (Or.inr (Or.inr (Or.inr (e ▸ hcL)))))
      · have hj' := hj b s rfl hs
        rw [o11]; simp [bfSt, H2, H1, freeH, upd_ne _ _ _ _ hj']
      · have hcb' : c' ≠ b := fun e => hc' (by rw [e])
        simp [upd_ne _ _ _ _ hcb']
    · intro b' s' e1 e2
      cases e1; rw [hs] at e2; cases e2
      refine ⟨fun x hx => ?_, by simp, by rw [o11]; simp [bfSt], closeCall_ofile _ _⟩
      rcases (hown x).mp hx with h1 | h1 | h1 | h1
      · exact (closeH_bytes H2 (bfSt s) cp b (bfSt s).strm x).2.1 (Or.inr h1)
      · exact (closeH_bytes H2 (bfSt s) cp b (bfSt s).strm x).2.1 (Or.inl h1)
      · exact (closeH_bytes H2 (bfSt s) cp b (bfSt s).strm x).2.2.2 hm2 h1
      · refine (closeH_bytes H2 (bfSt s) cp b (bfSt s).strm x).2.2.1 ?_
        rw [hb.buffers] at h1
        simp only [blkOf, stBlk, hz, hsb, List.mem_append, List.mem_singleton] at h1
        rcases h1 with rfl | rfl
        · exact freeH_bytes_eq _ _
        · simp only [H2]; rw [freeH_bytes_ne hcsb.symm]; simp [H1]

end ZlibNgF.Proof.GzMode
