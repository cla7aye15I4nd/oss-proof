import ZlibNgF.Proof.«public-gzopen»
import ZlibNgF.Proof.«inflate.c.reach»
import ZlibNgF.Proof.«deflate.c.reach»

/-!
# Read handles and write handles (`ZlibNgF`)

The mode of an open file never changes, so the reachable files split by mode:

* a read handle has `GzInvR`: the invariant `GzInv`, mode `GZ_READ`, and a well-formed world and heap (`GzWFr`: the
  clauses of `GzWF` other than the bound on objects). Other files reach a read handle only through caller steps,
  which leave a well-formed world (`GzKeeps`), and the read-side calls only read the file system, so the bounds on
  the input stay;
* a write handle has `GzInvWS`: the invariant `GzInv`, mode `GZ_WRITE`, and a well-formed heap (`GzWFw`: the
  clauses of `GzWF` other than the bounds on the input, which writes grow, and on objects). The read-side calls on a
  write handle need only `GzInvW` (live state, mode, positions, message).

`greach (W : GWriteSteps) (R : GReadPending) : GzReachable w h f → GzInvR w h f ∨ GzInvWS w h f`. `GWriteSteps`
holds what the write side owes: the write-side calls (`gzwrite.c`) keep `GzInvWS` on a write handle (the caller
steps keep it: `caller_keepsW`). `GReadPending` holds the read-side calls on read handles not proved yet.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace ZlibNgF.Proof.GzMode
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Gz ZlibNgF.Proof.GzInv ZlibNgF.Proof.GzSat

/-- The file `f` is open with mode `m`. -/
def GzModeIs (w : World) (h : Heap) (f : GzPtr) (m : Int32) : Prop :=
  ∃ b s, f = some b ∧ w.gz h b = some s ∧ s.mode = m

/-- The clauses of `GzWF` that a read handle keeps: all but the bound on the size of objects (a `strerror` text is
a static object of any size). -/
def GzWFr (w : World) (h : Heap) : Prop :=
  CrcGlobals h ∧ DFreshBlocks h ∧
  (∀ b, h.nextBlk ≤ b → w.gzs b = none) ∧
  (∀ b s, w.gz h b = some s → ∃ z, h.streams s.strm = some z) ∧
  w.fs.budget < 2 ^ 61 ∧ (∀ d ∈ w.fs.nodes, d.size < 2 ^ 61) ∧
  (∀ n v, w.fs.lseekChoice n = .value v → v = -1 ∨ 0 ≤ v) ∧ LitOk w h

theorem GzWFr.of {w : World} {h : Heap} (hwf : GzWF w h) : GzWFr w h :=
  ⟨hwf.1, hwf.2.1, hwf.2.2.2.1, hwf.2.2.2.2.1, hwf.2.2.2.2.2.1, hwf.2.2.2.2.2.2.1, hwf.2.2.2.2.2.2.2.1, hwf.lit⟩

theorem GzWFr.lit {w : World} {h : Heap} (hw : GzWFr w h) : LitOk w h := hw.2.2.2.2.2.2.2

/-- **The invariant of a read handle.** -/
def GzInvR (w : World) (h : Heap) (f : GzPtr) : Prop := GzInv w h f ∧ GzModeIs w h f GZ_READ ∧ GzWFr w h

/-- The clauses of `GzWF` that a write handle keeps: all but the bounds on the input (writes grow the files) and on
the size of objects. -/
def GzWFw (w : World) (h : Heap) : Prop :=
  CrcGlobals h ∧ DFreshBlocks h ∧
  (∀ b, h.nextBlk ≤ b → w.gzs b = none) ∧
  (∀ b s, w.gz h b = some s → ∃ z, h.streams s.strm = some z) ∧ LitOk w h

theorem GzWFw.of {w : World} {h : Heap} (hwf : GzWF w h) : GzWFw w h :=
  ⟨hwf.1, hwf.2.1, hwf.2.2.2.1, hwf.2.2.2.2.1, hwf.lit⟩

theorem GzWFw.lit {w : World} {h : Heap} (hw : GzWFw w h) : LitOk w h := hw.2.2.2.2

/-- **The invariant of a write handle.** -/
def GzInvWS (w : World) (h : Heap) (f : GzPtr) : Prop := GzInv w h f ∧ GzModeIs w h f GZ_WRITE ∧ GzWFw w h

/-- What the read-side calls need of a write handle. -/
def GzInvW (w : World) (h : Heap) (f : GzPtr) : Prop :=
  ∃ b s, f = some b ∧ w.gz h b = some s ∧ s.mode = GZ_WRITE ∧ GzPos s ∧ GzMsg h s

theorem GzInvWS.weak {w : World} {h : Heap} {f : GzPtr} (hv : GzInvWS w h f) : GzInvW w h f := by
  obtain ⟨⟨b, s, rfl, hs, sh, -⟩, ⟨b', s', e, hs', hm⟩, -⟩ := hv
  cases e; rw [hs] at hs'; cases hs'
  exact ⟨b, s, rfl, hs, hm, sh.pos, sh.msg⟩

theorem inv_of {w : World} {h : Heap} {b : Nat} {s : GzState} (hs : w.gz h b = some s)
    (hv : GzInv w h (some b)) : GzShape h s ∧ (ownL h b s).Nodup := by
  obtain ⟨b', s', e, hs', sh, hn⟩ := hv
  cases e; rw [hs] at hs'; cases hs'; exact ⟨sh, hn⟩

/-! ## Heap changes that leave the objects of a file alone -/

/-- `h'` keeps, from `h`, the embedded stream of `s` and the objects of the blocks `L` (the header records may
change: neither the inflate state of a read handle nor the deflate state of a write handle has one registered). -/
structure HK (h h' : Heap) (s : GzState) (L : List Nat) : Prop where
  strm : h'.streams s.strm = h.streams s.strm
  bytes : ∀ c ∈ L, h'.bytes c = h.bytes c
  ist : ∀ c ∈ L, h'.istates c = h.istates c
  ial : ∀ c ∈ L, h'.iallocs c = h.iallocs c
  dst : ∀ c ∈ L, h'.dstates c = h.dstates c
  dal : ∀ c ∈ L, h'.dallocs c = h.dallocs c
  base : h'.baseAddr = h.baseAddr
  next : h.nextBlk ≤ h'.nextBlk
  dead : s.size = 0 → ∀ c ∈ blkOf s.buffers ++ stBlk h s, h.bytes c = none → c < h.nextBlk → h'.bytes c = none
  saved : ∀ c ∈ L, h'.savedPtrs c = h.savedPtrs c

theorem ownBlk_keep {h h' : Heap} {p : Ival BPtr} (hp : OwnedBlk h p) (hb : ∀ c ∈ blkOf p, h'.bytes c = h.bytes c) :
    OwnedBlk h' p := by
  obtain ⟨c, d, rfl, hd⟩ := hp
  exact ⟨c, d, rfl, by rw [hb c (by simp [blkOf])]; exact hd⟩

theorem ownStr_keep {h h' : Heap} {p : Ival BPtr} (hp : OwnedStr h p) (hb : ∀ c ∈ blkOf p, h'.bytes c = h.bytes c) :
    OwnedStr h' p := by
  obtain ⟨c, n, rfl, r, off, d, e1, e2, e3⟩ := hp
  cases e1
  exact ⟨c, n, rfl, .heap c, 0, d, rfl, by show h'.bytes c = _; rw [hb c (by simp [blkOf])]; exact e2, e3⟩

theorem stBlk_of {h : Heap} {s : GzState} {z : ZStream} {c : Nat} (hz : h.streams s.strm = some z)
    (hc : z.state = some c) : c ∈ stBlk h s := by
  simp [stBlk, hz, hc]

/-- **Transfer.** The fields of a file carry over to a heap that keeps its objects. -/
theorem shape_keep {h h' : Heap} {b : Nat} {s : GzState} (sh : GzShape h s) (hk : HK h h' s (ownL h b s)) :
    GzShape h' s ∧ ownL h' b s = ownL h b s := by
  have hst : stBlk h' s = stBlk h s := by simp only [stBlk, hk.strm]
  have hown : ownL h' b s = ownL h b s := by simp only [ownL, hst]
  refine ⟨?_, hown⟩
  have hbufs : ∀ c base, s.size ≠ 0 → GzBufs h s c base → GzBufs h' s c base := by
    intro c base hsz hb
    obtain ⟨d, hd, hds⟩ := hb.fits
    have hcL : c ∈ ownL h b s := by simp [ownL, hsz, hb.buffers, blkOf]
    refine ⟨hb.size, hb.buffers, hb.inp, hb.out, ⟨d, ?_, hds⟩, hb.hdr.1, by rw [hk.saved c hcL]; exact hb.hdr.2⟩
    rw [hk.bytes c hcL]; exact hd
  refine ⟨sh.mode, ownStr_keep sh.path fun c hc => hk.bytes c (by simp only [ownL, List.mem_append]; exact Or.inl (Or.inl (Or.inr hc))),
    by rw [hk.strm]; exact sh.strm, sh.want_lo, sh.want_hi, sh.size, sh.pos,
    ⟨?_, sh.msg.mem⟩, fun hr => ?_, fun hw => ?_, fun hz c hc => ?_⟩
  · rcases sh.msg.msg with e | hm
    · exact Or.inl e
    · exact Or.inr (ownBlk_keep hm fun c hc => hk.bytes c (by simp only [ownL, List.mem_append]; exact Or.inl (Or.inr hc)))
  · have R := sh.read hr
    refine ⟨R.how, fun hsz => ?_, R.nobuf, R.skip_have, fun hz0 => (R.fresh hz0).of_streams hk.strm, R.look, R.pos_have, R.look_pos, R.gzip_direct,
      fun e z hz => R.copy_in e z (by rw [hk.strm] at hz; exact hz)⟩
    obtain ⟨c, base, z, hb, hi, hz, hhv, hai, hreg, hmsg⟩ := R.bufs hsz
    obtain ⟨i, z0, sb, st, al, e, hz0, hsb, hst0, hal, core⟩ := hi
    cases e
    rw [hz] at hz0; cases hz0
    have hsbL : sb ∈ ownL h b s := by
      simp only [ownL, hsz, ite_false]; simp [stBlk_of hz hsb]
    have hcs : InflateInv.Inv h' (some s.strm) := by
      refine InflateReach.caller_inv ⟨s.strm, z, sb, st, al, rfl, hz, hsb, hst0, hal, core⟩
        ⟨s.strm, z, z, sb, rfl, hz, by rw [hk.strm]; exact hz, hsb, rfl, hk.bytes sb hsbL, hk.ist sb hsbL,
          hk.ial sb hsbL, fun k g hr' _ => absurd (hreg _ hr') (by simp), hk.base, hk.next⟩
    refine ⟨c, base, z, hbufs c base hsz hb, hcs, by rw [hk.strm]; exact hz, hhv, hai, fun hp hr' => hreg hp ?_, hmsg⟩
    obtain ⟨sb', st', ⟨z', ⟨i', e', hz'⟩, hsb'⟩, hst', hhd⟩ := hr'
    cases e'
    rw [hk.strm, hz] at hz'; cases hz'
    rw [hsb] at hsb'; cases hsb'
    refine ⟨sb, st', ⟨z, ⟨_, rfl, hz⟩, hsb⟩, ?_, hhd⟩
    have hb' := hk.bytes sb hsbL
    have hi' := hk.ist sb hsbL
    simp only [Heap.istate, hb', hi'] at hst' ⊢; exact hst'
  · have Wr := sh.write hw
    refine ⟨fun hsz => ?_, fun hz0 => by rw [hk.strm]; exact Wr.nobuf hz0, Wr.have0⟩
    obtain ⟨c, base, z, hb, hz, W⟩ := Wr.bufs hsz
    have hnh' : ∀ sb st k, z.state = some sb → h'.dstate sb = some st → st.gzhead ≠ .val (some k) := by
      intro sb st k hsb hst
      have hsbL : sb ∈ ownL h b s := by
        simp only [ownL, hsz, ite_false]; simp [stBlk_of hz hsb]
      refine W.nohdr sb st k hsb ?_
      simp only [Heap.dstate, hk.bytes sb hsbL, hk.dst sb hsbL] at hst ⊢; exact hst
    refine ⟨c, base, z, hbufs c base hsz hb, by rw [hk.strm]; exact hz, ⟨fun hdir => ?_, hnh', W.inp, W.nostate, W.out⟩⟩
    obtain ⟨hd, hsd⟩ := W.deflate hdir
    obtain ⟨i, z0, sb, st, al, e, hz0, hsb, hst0, hal, core⟩ := hd
    cases e
    rw [hz] at hz0; cases hz0
    have hsbL : sb ∈ ownL h b s := by
      simp only [ownL, hsz, ite_false]; simp [stBlk_of hz hsb]
    have hc : DCallerStep h h' (some s.strm) :=
      ⟨s.strm, z, z, sb, st, rfl, hz, by rw [hk.strm]; exact hz, hsb, hst0, rfl, hk.bytes sb hsbL, hk.dst sb hsbL,
        hk.dal sb hsbL, fun k g hk' _ => absurd hk' (W.nohdr sb st k hsb hst0),
        hk.base, hk.next⟩
    exact ⟨DeflateReach.caller_inv ⟨s.strm, z, sb, st, al, rfl, hz, hsb, hst0, hal, core⟩ hc,
      DeflateSide.caller_side hsd hc⟩
  · rw [hst] at hc
    exact ⟨hk.dead hz c hc (sh.dead hz c hc).1 (sh.dead hz c hc).2, Nat.lt_of_lt_of_le (sh.dead hz c hc).2 hk.next⟩

/-! ## Steps of each kind -/

section Steps
variable (w : World) (h : Heap) (w' : World) (h' : Heap) (f : GzPtr)

def SBuffer : Prop := ∃ n r, GzRun (gzbuffer f n) w h r w' h'
def SRead : Prop := ∃ buf len r, (len.toInt32 ≥ 0 → GzOut w h f buf len.toNat) ∧ GzRun (gzread f buf len) w h r w' h'
def SFread : Prop := ∃ buf size nitems r, (size.toNat * nitems.toNat < 2 ^ 64 → GzOut w h f buf (size.toNat * nitems.toNat)) ∧
    GzRun (gzfread buf size nitems f) w h r w' h'
def SGetc : Prop := ∃ r, GzRun (gzgetc f) w h r w' h'
def SGetc_ : Prop := ∃ r, GzRun (gzgetc_ f) w h r w' h'
def SUngetc : Prop := ∃ c r, GzRun (gzungetc c f) w h r w' h'
def SGets : Prop := ∃ buf len r, (len ≥ 1 → GzOut w h f buf len.toNatClampNeg ∨ buf = .null) ∧
    GzRun (gzgets f buf len) w h r w' h'
def SDirect : Prop := ∃ r, GzRun (gzdirect f) w h r w' h'
def SWrite : Prop := ∃ buf len r, (len.toInt32 ≥ 0 → GzIn w h f buf len.toNat) ∧ GzRun (gzwrite f buf len) w h r w' h'
def SFwrite : Prop := ∃ buf size nitems r, (size.toNat * nitems.toNat < 2 ^ 64 → GzIn w h f buf (size.toNat * nitems.toNat)) ∧
    GzRun (gzfwrite buf size nitems f) w h r w' h'
def SPutc : Prop := ∃ c r, GzRun (gzputc f c) w h r w' h'
def SPuts : Prop := ∃ s r, CStr h s ∧ OutsideGz w h f s ∧ GzRun (gzputs f s) w h r w' h'
def SPrintf : Prop := ∃ fmt r, CStr h fmt ∧ GzRun (gzprintf f fmt) w h r w' h'
def SVprintf : Prop := ∃ fmt r, CStr h fmt ∧ GzRun (gzvprintf f fmt) w h r w' h'
def SFlush : Prop := ∃ fl r, GzRun (gzflush f fl) w h r w' h'
def SSetparams : Prop := ∃ l s r, GzRun (gzsetparams f l s) w h r w' h'
def SSeek64 : Prop := ∃ off wh r, GzRun (gzseek64 f off wh) w h r w' h'
def SSeek : Prop := ∃ off wh r, GzRun (gzseek f off wh) w h r w' h'
def SRewind : Prop := ∃ r, GzRun (gzrewind f) w h r w' h'
def STell64 : Prop := ∃ r, GzRun (gztell64 f) w h r w' h'
def STell : Prop := ∃ r, GzRun (gztell f) w h r w' h'
def SOffset64 : Prop := ∃ r, GzRun (gzoffset64 f) w h r w' h'
def SOffset : Prop := ∃ r, GzRun (gzoffset f) w h r w' h'
def SEof : Prop := ∃ r, GzRun (gzeof f) w h r w' h'
def SError : Prop := ∃ e r, GzRun (gzerror f e) w h r w' h'
def SClearerr : Prop := ∃ r, GzRun (gzclearerr f) w h r w' h'

/-- The write-side calls (`gzwrite.c`). -/
def GzWStep : Prop :=
  SWrite w h w' h' f ∨ SFwrite w h w' h' f ∨ SPutc w h w' h' f ∨ SPuts w h w' h' f ∨ SPrintf w h w' h' f ∨
  SVprintf w h w' h' f ∨ SFlush w h w' h' f ∨ SSetparams w h w' h' f

end Steps

/-- `S` keeps the invariant of read handles. -/
def KeepsR (S : World → Heap → World → Heap → GzPtr → Prop) : Prop :=
  ∀ w h w' h' f, GzInvR w h f → S w h w' h' f → GzInvR w' h' f

/-- `S` keeps the invariant of write handles. -/
def KeepsW (S : World → Heap → World → Heap → GzPtr → Prop) : Prop :=
  ∀ w h w' h' f, GzInvWS w h f → S w h w' h' f → GzInvWS w' h' f

/-- **Between calls, a handle that may still turn out transparent holds fewer than two bytes of input.** While `how` is
`LOOK` and transparent reading is allowed (`direct ≠ 0`), the input buffer has fewer than two bytes: `gz_look` either
leaves `LOOK` (it switches to `COPY` or `GZIP`), or reads no input past the test `avail_in < 2`. So the next
`gz_look` calls `gz_avail` (which fails on a pending error) before it can copy input to the output. Not a clause of
`GzRead`: inside `gz_look` it fails between `gz_avail` and the switch. -/
def LookIdle (w : World) (h : Heap) (f : GzPtr) : Prop :=
  ∀ b s z, f = some b → w.gz h b = some s → h.streams s.strm = some z →
    s.how = LOOK → s.direct ≠ 0 → z.avail_in.toNat < 2

/-- `S` keeps the invariant of read handles together with `LookIdle`. -/
def KeepsRI (S : World → Heap → World → Heap → GzPtr → Prop) : Prop :=
  ∀ w h w' h' f, GzInvR w h f → LookIdle w h f → S w h w' h' f → GzInvR w' h' f ∧ LookIdle w' h' f

theorem idle_mk {w : World} {h : Heap} {b : Nat} {s : GzState} (hs : w.gz h b = some s)
    (H : ∀ z, h.streams s.strm = some z → s.how = LOOK → s.direct ≠ 0 → z.avail_in.toNat < 2) :
    LookIdle w h (some b) := by
  intro b' s' z e hs' hz
  cases e; rw [hs] at hs'; cases hs'; exact H z hz

theorem idle_get {w : World} {h : Heap} {b : Nat} {s : GzState} {z : ZStream} (hi : LookIdle w h (some b))
    (hs : w.gz h b = some s) (hz : h.streams s.strm = some z) : s.how = LOOK → s.direct ≠ 0 → z.avail_in.toNat < 2 :=
  hi b s z rfl hs hz

/-- `LookIdle` carries over to a state with the same `how`, `direct` and stream, and the same stream record. -/
theorem idle_same {w W : World} {h H : Heap} {b : Nat} {s s' : GzState} (hi : LookIdle w h (some b))
    (hs : w.gz h b = some s) (hs' : W.gz H b = some s') (e1 : s'.how = s.how) (e2 : s'.direct = s.direct)
    (e3 : s'.strm = s.strm) (e4 : H.streams s.strm = h.streams s.strm) : LookIdle W H (some b) := by
  refine idle_mk hs' fun z hz h1 h2 => ?_
  rw [e3, e4] at hz; rw [e1] at h1; rw [e2] at h2
  exact idle_get hi hs hz h1 h2

/-- `LookIdle` of a state whose stream has no input. -/
theorem idle_zero {w : World} {h : Heap} {b : Nat} {s : GzState} (hs : w.gz h b = some s)
    (H : ∀ z, h.streams s.strm = some z → z.avail_in = 0) : LookIdle w h (some b) :=
  idle_mk hs fun z hz _ _ => by rw [H z hz]; decide

/-- `LookIdle` of a read handle that is not looking at transparent-capable input, or has no buffers. -/
theorem idle_of {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvR w h (some b)) (hs : w.gz h b = some s)
    (hc : s.how ≠ LOOK ∨ s.direct = 0 ∨ s.size = 0) : LookIdle w h (some b) := by
  refine idle_mk hs fun z hz h1 h2 => ?_
  rcases hc with hc | hc | hc
  · exact absurd h1 hc
  · exact absurd hc h2
  · obtain ⟨⟨b', s', e, hs', sh, -⟩, hm, -⟩ := hv
    cases e; rw [hs] at hs'; cases hs'
    have hr : s.mode = GZ_READ := by
      obtain ⟨b2, s2, e2, hs2, hm2⟩ := hm; cases e2; rw [hs] at hs2; cases hs2; exact hm2
    obtain ⟨z', hz', -, -, h0⟩ := (sh.read hr).fresh hc
    rw [hz] at hz'; cases hz'; rw [h0]; decide

/-- **What the write side owes**: on a write handle, the write-side calls keep `GzInvWS` (the caller's steps keep it:
`caller_keepsW`). -/
structure GWriteSteps : Prop where
  step : KeepsW GzWStep

/-! ## Calls that return at the mode check -/

section ModeCheck
variable {w : World} {h : Heap} {b : Nat} {s : GzState} (hs : w.gz h b = some s)
include hs

theorem gzwrite_read (hm : s.mode = GZ_READ) (buf : BPtr) (len : UInt32) : GzRun (gzwrite (some b) buf len) w h 0 w h := by
  simp [GzRun, C.run, StateT.run, gzwrite, rdG_app' hs, hm, GZ_READ, GZ_WRITE]

theorem gzfwrite_read (hm : s.mode = GZ_READ) (buf : BPtr) (size nitems : UInt64) :
    GzRun (gzfwrite buf size nitems (some b)) w h 0 w h := by
  by_cases hz : size = 0 <;> simp [GzRun, C.run, StateT.run, gzfwrite, rdG_app' hs, hm, hz, GZ_READ, GZ_WRITE]

theorem gzputc_read (hm : s.mode = GZ_READ) (c : Int32) : GzRun (gzputc (some b) c) w h (-1) w h := by
  simp [GzRun, C.run, StateT.run, gzputc, rdG_app' hs, strmOf_app hs, hm, GZ_READ, GZ_WRITE]

theorem gzputs_read (hm : s.mode = GZ_READ) (p : BPtr) : GzRun (gzputs (some b) p) w h (-1) w h := by
  simp [GzRun, C.run, StateT.run, gzputs, rdG_app' hs, hm, GZ_READ, GZ_WRITE]

theorem gzvprintf_read (hm : s.mode = GZ_READ) (p : BPtr) :
    GzRun (gzvprintf (some b) p) w h ZlibNg.Inflate.Z_STREAM_ERROR w h := by
  simp [GzRun, C.run, StateT.run, gzvprintf, rdG_app' hs, strmOf_app hs, hm, GZ_READ, GZ_WRITE]

theorem gzprintf_read (hm : s.mode = GZ_READ) (p : BPtr) :
    GzRun (gzprintf (some b) p) w h ZlibNg.Inflate.Z_STREAM_ERROR w h := by
  have e := gzvprintf_read hs hm p
  simp only [GzRun, C.run, StateT.run] at e ⊢
  simp [gzprintf, e]

theorem gzflush_read (hm : s.mode = GZ_READ) (fl : Int32) :
    GzRun (gzflush (some b) fl) w h ZlibNg.Inflate.Z_STREAM_ERROR w h := by
  simp [GzRun, C.run, StateT.run, gzflush, rdG_app' hs, hm, GZ_READ, GZ_WRITE]

theorem gzsetparams_read (hm : s.mode = GZ_READ) (l st : Int32) :
    GzRun (gzsetparams (some b) l st) w h ZlibNg.Inflate.Z_STREAM_ERROR w h := by
  simp [GzRun, C.run, StateT.run, gzsetparams, rdG_app' hs, strmOf_app hs, hm, GZ_READ, GZ_WRITE]

theorem gzread_write (hm : s.mode = GZ_WRITE) (buf : BPtr) (len : UInt32) :
    GzRun (gzread (some b) buf len) w h (-1) w h := by
  simp [GzRun, C.run, StateT.run, gzread, rdG_app' hs, hm, GZ_READ, GZ_WRITE]

theorem gzfread_write (hm : s.mode = GZ_WRITE) (buf : BPtr) (size nitems : UInt64) :
    GzRun (gzfread buf size nitems (some b)) w h 0 w h := by
  by_cases hz : size = 0 <;> simp [GzRun, C.run, StateT.run, gzfread, rdG_app' hs, hm, hz, GZ_READ, GZ_WRITE]

theorem gzgetc_write (hm : s.mode = GZ_WRITE) : GzRun (gzgetc (some b)) w h (-1) w h := by
  simp [GzRun, C.run, StateT.run, gzgetc, rdG_app' hs, hm, GZ_READ, GZ_WRITE]

theorem gzgetc__write (hm : s.mode = GZ_WRITE) : GzRun (gzgetc_ (some b)) w h (-1) w h := by
  simp [GzRun, C.run, StateT.run, gzgetc_, gzgetc, rdG_app' hs, hm, GZ_READ, GZ_WRITE]

theorem gzungetc_write (hm : s.mode = GZ_WRITE) (c : Int32) : GzRun (gzungetc c (some b)) w h (-1) w h := by
  simp [GzRun, C.run, StateT.run, gzungetc, rdG_app' hs, hm, GZ_READ, GZ_WRITE]

theorem gzgets_write (hm : s.mode = GZ_WRITE) (buf : BPtr) (len : Int32) :
    GzRun (gzgets (some b) buf len) w h .null w h := by
  by_cases e1 : buf = .null
  · simp [GzRun, C.run, StateT.run, gzgets, e1]
  · by_cases e2 : len < 1
    · simp [GzRun, C.run, StateT.run, gzgets, e2]
    · simp [GzRun, C.run, StateT.run, gzgets, rdG_app' hs, hm, e1, e2, GZ_READ, GZ_WRITE]

theorem gzdirect_write (hm : s.mode = GZ_WRITE) :
    GzRun (gzdirect (some b)) w h (if s.direct = 1 then 1 else 0) w h := by
  simp [GzRun, C.run, StateT.run, gzdirect, rdG_app' hs, hm, GZ_READ, GZ_WRITE]

theorem gzrewind_write (hm : s.mode = GZ_WRITE) : GzRun (gzrewind (some b)) w h (-1) w h := by
  simp [GzRun, C.run, StateT.run, gzrewind, rdG_app' hs, hm, GZ_READ, GZ_WRITE]

theorem gzclose_r_write (hm : s.mode = GZ_WRITE) :
    GzRun (gzclose_r (some b)) w h ZlibNg.Inflate.Z_STREAM_ERROR w h := by
  simp [GzRun, C.run, StateT.run, gzclose_r, rdG_app' hs, hm, GZ_READ, GZ_WRITE]

end ModeCheck

/-! ## Reads and stores of a state just stored -/

@[simp] theorem stlift_app {α : Type} (m : M α) (w : World) (h : Heap) :
    (StateT.lift m : G α) w h = match m h with | .ok (a, h') => .ok ((a, w), h') | .error e => .error e :=
  lm_app m w h

theorem gz_live {w : World} {h : Heap} {b : Nat} {s : GzState} (hs : w.gz h b = some s) : ∃ d, h.bytes b = some d := by
  unfold World.gz at hs; split at hs
  · next d hd => exact ⟨d, hd⟩
  · cases hs

theorem gzs_of {w : World} {h : Heap} {b : Nat} {s : GzState} (hs : w.gz h b = some s) : w.gzs b = some s := by
  unfold World.gz at hs; split at hs
  · exact hs
  · cases hs

theorem ldGz_upd {h : Heap} {b : Nat} {d : Array UInt8} (hb : h.bytes b = some d) (w : World) (s : GzState) :
    ldGz (some b) { w with gzs := upd w.gzs b (some s) } h = .ok ((s, { w with gzs := upd w.gzs b (some s) }), h) :=
  ldGz_app (by unfold World.gz; simp [hb])

theorem rdG_upd {α : Type} {h : Heap} {b : Nat} {d : Array UInt8} (hb : h.bytes b = some d) (w : World) (s : GzState)
    (g : GzState → α) :
    rdG (some b) g { w with gzs := upd w.gzs b (some s) } h = .ok ((g s, { w with gzs := upd w.gzs b (some s) }), h) :=
  rdG_app' (by unfold World.gz; simp [hb]) g

theorem wrG_upd {h : Heap} {b : Nat} {d : Array UInt8} (hb : h.bytes b = some d) (w : World) (s : GzState)
    (f : GzState → GzState) :
    wrG (some b) f { w with gzs := upd w.gzs b (some s) } h = .ok (((), { w with gzs := upd w.gzs b (some (f s)) }), h) := by
  rw [wrG_app (s := s) (by unfold World.gz; simp [hb])]
  simp [InflateInv.upd_upd]

theorem strmOf_upd {h : Heap} {b : Nat} {d : Array UInt8} (hb : h.bytes b = some d) (w : World) (s : GzState) :
    strmOf (some b) { w with gzs := upd w.gzs b (some s) } h = .ok ((some s.strm, { w with gzs := upd w.gzs b (some s) }), h) :=
  strmOf_app (by unfold World.gz; simp [hb])

theorem write_ne_read : GZ_WRITE ≠ GZ_READ := by decide
theorem read_ne_write : GZ_READ ≠ GZ_WRITE := by decide

/-! ## `gz_error` without a message -/

/-- The heap after `gz_error` frees the message of `s` (when it is a heap string and `err` is not
`Z_MEM_ERROR`). -/
def freeMsg (h : Heap) (s : GzState) : Heap :=
  match s.msg with
  | .val (.ref (.heap c) 0) =>
    if s.err = ZlibNg.Inflate.Z_MEM_ERROR then h
    else { h with bytes := upd h.bytes c none, savedPtrs := upd h.savedPtrs c none }
  | _ => h

/-- The state after `gz_error(state, e, NULL)`. -/
def errSt (s : GzState) (e : Int32) : GzState :=
  { s with msg := .val .null,
           «have» := if e ≠ ZlibNg.Inflate.Z_OK ∧ e ≠ ZlibNg.Inflate.Z_BUF_ERROR then 0 else s.«have»,
           err := e }

theorem gz_error_null {w : World} {h : Heap} {b : Nat} {s : GzState} (hs : w.gz h b = some s) (hm : GzMsg h s)
    (hbc : ∀ c o, s.msg = .val (.ref (.heap c) o) → c ≠ b) (e : Int32) : GzRun (gz_error (some b) e .null) w h () { w with gzs := upd w.gzs b (some (errSt s e)) } (freeMsg h s) := by
  obtain ⟨db, hdb⟩ := gz_live hs
  rcases hm.msg with hn | ⟨c, d, hc, e2⟩
  · by_cases he : e ≠ ZlibNg.Inflate.Z_OK ∧ e ≠ ZlibNg.Inflate.Z_BUF_ERROR
    · simp [GzRun, C.run, StateT.run, gz_error, ldGz_app hs, wrG_app hs, hn, freeMsg, errSt, he,
        Ival.get, liftM, monadLift, MonadLift.monadLift, wrG_upd hdb, ldGz_upd hdb, rdG_upd hdb]
    · simp [GzRun, C.run, StateT.run, gz_error, ldGz_app hs, wrG_app hs, hn, freeMsg, errSt, he,
        Ival.get, liftM, monadLift, MonadLift.monadLift, wrG_upd hdb, ldGz_upd hdb, rdG_upd hdb]
  · have hd : h.bytes c = some d := e2
    by_cases hme : s.err = ZlibNg.Inflate.Z_MEM_ERROR
    · exact absurd (hm.mem hme) (by rw [hc]; simp)
    have hcb := hbc c 0 hc
    have hdb1 : (upd h.bytes c none) b = some db := by rw [upd_ne _ _ _ _ hcb.symm]; exact hdb
    have hs1 : w.gz { h with bytes := upd h.bytes c none, savedPtrs := upd h.savedPtrs c none } b = some s := by
      unfold World.gz at hs ⊢; simp only [hdb1]; rw [hdb] at hs; exact hs
    by_cases he : e ≠ ZlibNg.Inflate.Z_OK ∧ e ≠ ZlibNg.Inflate.Z_BUF_ERROR <;>
    simp [GzRun, C.run, StateT.run, gz_error, ldGz_app hs, rdG_app' hs, wrG_app hs1, hc, freeMsg, errSt, he, hme,
        Ival.get, liftM, monadLift, MonadLift.monadLift, wrG_upd (h := { h with bytes := upd h.bytes c none, savedPtrs := upd h.savedPtrs c none }) hdb1,
        ldGz_upd (h := { h with bytes := upd h.bytes c none, savedPtrs := upd h.savedPtrs c none }) hdb1, freeB, hd]

theorem gz_error_null_app {w : World} {h : Heap} {b : Nat} {s : GzState} (hs : w.gz h b = some s) (hm : GzMsg h s)
    (hbc : ∀ c o, s.msg = .val (.ref (.heap c) o) → c ≠ b) (e : Int32) :
    gz_error (some b) e .null w h = .ok (((), { w with gzs := upd w.gzs b (some (errSt s e)) }), freeMsg h s) :=
  gz_error_null hs hm hbc e

/-- The state after the `GZ_READ` part of `gzclearerr`. -/
def clrSt (s : GzState) : GzState := if s.mode = GZ_READ then { s with eof := 0, past := 0 } else s

theorem gzclearerr_run {w : World} {h : Heap} {b : Nat} {s : GzState} (hs : w.gz h b = some s)
    (hm : s.mode = GZ_READ ∨ s.mode = GZ_WRITE) (hmsg : GzMsg h s)
    (hbc : ∀ c o, s.msg = .val (.ref (.heap c) o) → c ≠ b) :
    GzRun (gzclearerr (some b)) w h () { w with gzs := upd w.gzs b (some (errSt (clrSt s) ZlibNg.Inflate.Z_OK)) }
      (freeMsg h s) := by
  have hmode : ¬(¬s.mode = GZ_READ ∧ ¬s.mode = GZ_WRITE) := by
    rcases hm with hm | hm <;> simp [hm]
  obtain ⟨db, hdb⟩ := gz_live hs
  by_cases hr : s.mode = GZ_READ
  · have hs2 : ({ w with gzs := upd w.gzs b (some { s with eof := 0, past := 0 }) } : World).gz h b =
        some { s with eof := 0, past := 0 } := gz_upd_same hs _
    have e := gz_error_null_app (w := { w with gzs := upd w.gzs b (some { s with eof := 0, past := 0 }) }) hs2
      ⟨hmsg.msg, hmsg.mem⟩ hbc ZlibNg.Inflate.Z_OK
    simp only [hr] at e
    simp only [GzRun, C.run, StateT.run]
    simp [gzclearerr, rdG_app' hs, wrG_app hs, hmode, hr, wrG_upd hdb, clrSt]
    rw [e]; simp [InflateInv.upd_upd, freeMsg]
  · have e := gz_error_null_app hs hmsg hbc ZlibNg.Inflate.Z_OK
    have hw : s.mode = GZ_WRITE := hm.resolve_left hr
    simp only [GzRun, C.run, StateT.run]
    simp [gzclearerr, rdG_app' hs, hmode, hr, hw, clrSt, e, write_ne_read]

/-- The fields of a state that the invariant reads (other than `msg` and `err`) agree. -/
structure Agree (s s' : GzState) : Prop where
  hv : s'.«have» = s.«have»
  next : s'.next = s.next
  pos : s'.pos = s.pos
  mode : s'.mode = s.mode
  path : s'.path = s.path
  size : s'.size = s.size
  want : s'.want = s.want
  inp : s'.«in» = s.«in»
  out : s'.out = s.out
  buffers : s'.buffers = s.buffers
  direct : s'.direct = s.direct
  how : s'.how = s.how
  skip : s'.skip = s.skip
  strm : s'.strm = s.strm

theorem Agree.inS {s s' : GzState} (a : Agree s s') : inSize s' = inSize s := by
  unfold GzInv.inSize; rw [a.mode, a.want]

theorem Agree.outS {s s' : GzState} (a : Agree s s') : outSize s' = outSize s := by
  unfold GzInv.outSize; rw [a.mode, a.want, a.direct]

theorem Agree.bufs {h : Heap} {s s' : GzState} {c base : Nat} (a : Agree s s') (hb : GzBufs h s c base) :
    GzBufs h s' c base :=
  ⟨by rw [a.size, a.want]; exact hb.size, by rw [a.buffers]; exact hb.buffers, by rw [a.inp]; exact hb.inp,
    fun e => by rw [a.out, a.inS]; exact hb.out (by rw [← a.outS]; exact e),
    by rw [a.inS, a.outS]; exact hb.fits, hb.hdr⟩

theorem Agree.posOf {s s' : GzState} (a : Agree s s') (p : GzPos s) : GzPos s' :=
  ⟨by rw [a.skip]; exact p.1, by rw [a.pos, a.skip]; exact p.2, by rw [a.pos]; exact p.3,
    fun e => by rw [a.pos]; exact p.4 (by rw [← a.mode]; exact e)⟩

/-- **Fields that agree.** A state that agrees with `s` on the fields the invariant reads keeps the invariant,
given its message. -/
theorem shape_congr {h : Heap} {s s' : GzState} (sh : GzShape h s) (a : Agree s s') (hm : GzMsg h s') :
    GzShape h s' := by
  refine ⟨by rw [a.mode]; exact sh.mode, by rw [a.path]; exact sh.path, by rw [a.strm]; exact sh.strm,
    by rw [a.want]; exact sh.want_lo, by rw [a.want]; exact sh.want_hi, by rw [a.size, a.want]; exact sh.size,
    a.posOf sh.pos, hm, fun hr => ?_, fun hw => ?_, fun hz c hc => ?_⟩
  · have R := sh.read (by rw [← a.mode]; exact hr)
    refine ⟨by rw [a.how]; exact R.how, fun hsz => ?_, by rw [a.size, a.hv]; exact R.nobuf,
      by rw [a.skip, a.pos, a.hv]; exact R.skip_have, fun hz => (R.fresh (by rw [← a.size]; exact hz)).of_strm a.strm,
      fun hz => by rw [a.how]; exact R.look (by rw [← a.size]; exact hz),
      by rw [a.pos, a.hv]; exact R.pos_have, by rw [a.how, a.direct, a.pos, a.hv]; exact R.look_pos,
      by rw [a.how, a.direct]; exact R.gzip_direct,
      fun e z hz => R.copy_in (by rw [a.how] at e; exact e) z (by rw [a.strm] at hz; exact hz)⟩
    obtain ⟨c, base, z, hb, hi, hz, hhv, hai, hreg, hmsg⟩ := R.bufs (by rw [← a.size]; exact hsz)
    refine ⟨c, base, z, a.bufs hb, by rw [a.strm]; exact hi, by rw [a.strm]; exact hz, ?_, ?_, ?_, hmsg⟩
    · rw [a.hv, a.next, a.inS, a.outS]; exact hhv
    · rw [a.inS]; exact hai
    · rw [a.strm]; exact hreg
  · have Wr := sh.write (by rw [← a.mode]; exact hw)
    refine ⟨fun hsz => ?_, fun hz0 => by rw [a.strm, a.direct]; exact Wr.nobuf (by rw [← a.size]; exact hz0),
      by rw [a.hv]; exact Wr.have0⟩
    obtain ⟨c, base, z, hb, hz, W⟩ := Wr.bufs (by rw [← a.size]; exact hsz)
    refine ⟨c, base, z, a.bufs hb, by rw [a.strm]; exact hz, ⟨?_, W.nohdr, ?_, by rw [a.direct]; exact W.nostate, ?_⟩⟩
    · rw [a.direct, a.strm]; exact W.deflate
    · rw [a.size, a.direct]; exact W.inp
    · rw [a.direct, a.next, a.inS, a.size]; exact W.out
  · have e : blkOf s'.buffers ++ stBlk h s' = blkOf s.buffers ++ stBlk h s := by simp only [stBlk, a.buffers, a.strm]
    rw [e] at hc; exact sh.dead (by rw [← a.size]; exact hz) c hc

theorem ownL_congr {h : Heap} {b : Nat} {s s' : GzState} (a : Agree s s') (hm : s'.msg = s.msg) :
    ownL h b s' = ownL h b s := by
  simp only [ownL, stBlk, a.path, hm, a.size, a.buffers, a.strm]

/-- A state that differs only in `eof`, `past`, `err` and `msg` keeps the fields, given its message. -/
theorem shape_msg {h : Heap} {s : GzState} (sh : GzShape h s) (eof past err : Int32) (msg : Ival BPtr)
    (hm : GzMsg h { s with eof := eof, past := past, err := err, msg := msg }) :
    GzShape h { s with eof := eof, past := past, err := err, msg := msg } :=
  shape_congr sh ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hm

theorem errSt_clr (s : GzState) : errSt (clrSt s) ZlibNg.Inflate.Z_OK =
    { s with eof := (clrSt s).eof, past := (clrSt s).past, err := ZlibNg.Inflate.Z_OK, msg := .val .null } := by
  unfold errSt clrSt; by_cases hm : s.mode = GZ_READ <;> simp [hm]

theorem freeMsg_streams (h : Heap) (s : GzState) : (freeMsg h s).streams = h.streams := by
  unfold freeMsg; split
  · split <;> rfl
  · rfl

/-- `freeMsg` changes the bytes of the message block only. -/
theorem freeMsg_bytes (h : Heap) (s : GzState) (c : Nat) (hc : c ∉ blkOf s.msg) :
    (freeMsg h s).bytes c = h.bytes c := by
  unfold freeMsg; split
  · next c' e =>
    rw [e] at hc
    have hne : c ≠ c' := fun e' => hc (by simp [blkOf, e'])
    split
    · rfl
    · simp only; rw [upd_ne _ _ _ _ hne]
  · rfl

theorem freeMsg_saved (h : Heap) (s : GzState) (c : Nat) (hc : c ∉ blkOf s.msg) :
    (freeMsg h s).savedPtrs c = h.savedPtrs c := by
  unfold freeMsg; split
  · next c' e =>
    rw [e] at hc
    have hne : c ≠ c' := fun e' => hc (by simp [blkOf, e'])
    split
    · rfl
    · simp only; rw [upd_ne _ _ _ _ hne]
  · rfl

theorem freeMsg_none (h : Heap) (s : GzState) (c : Nat) (hc : h.bytes c = none) : (freeMsg h s).bytes c = none := by
  unfold freeMsg; split
  · split
    · exact hc
    · next c' _ _ =>
      show (upd h.bytes c' none) c = none
      by_cases e : c = c'
      · rw [e]; simp
      · rw [upd_ne _ _ _ _ e]; exact hc
  · exact hc

/-- The fields after `gz_error` with no message (`err` `Z_OK`, as `gzclearerr`), on the heap that frees the old
message. -/
theorem clear_keep {h : Heap} {b : Nat} {s : GzState} (sh : GzShape h s) (hn : (ownL h b s).Nodup) :
    GzShape (freeMsg h s) (errSt (clrSt s) ZlibNg.Inflate.Z_OK) ∧
      (ownL (freeMsg h s) b (errSt (clrSt s) ZlibNg.Inflate.Z_OK)).Nodup := by
  rw [errSt_clr]
  generalize (clrSt s).eof = e1
  generalize (clrSt s).past = e2
  have sh1 := shape_msg sh e1 e2 ZlibNg.Inflate.Z_OK (.val .null) ⟨Or.inl rfl, fun _ => rfl⟩
  have hL : ownL h b { s with eof := e1, past := e2, err := ZlibNg.Inflate.Z_OK, msg := .val .null } =
      [b] ++ blkOf s.path ++ (if s.size = 0 then [] else blkOf s.buffers ++ stBlk h s) := by
    simp [ownL, blkOf, stBlk]
  have hnot : ∀ c ∈ ownL h b { s with eof := e1, past := e2, err := ZlibNg.Inflate.Z_OK, msg := .val .null },
      c ∉ blkOf s.msg := by
    rw [hL]
    intro c hc hcm
    unfold ownL at hn
    rw [List.nodup_append] at hn
    simp only [List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · exact (List.nodup_append.mp hn.1).2.2 c (List.mem_append.mpr (Or.inl hc)) c hcm rfl
    · exact (List.nodup_append.mp hn.1).2.2 c (List.mem_append.mpr (Or.inr hc)) c hcm rfl
    · exact hn.2.2 c (List.mem_append.mpr (Or.inr hcm)) c hc rfl
  have hk : HK h (freeMsg h s) { s with eof := e1, past := e2, err := ZlibNg.Inflate.Z_OK, msg := .val .null }
      (ownL h b { s with eof := e1, past := e2, err := ZlibNg.Inflate.Z_OK, msg := .val .null }) := by
    refine ⟨by rw [freeMsg_streams], fun c hc => freeMsg_bytes h s c (hnot c hc), ?_, ?_, ?_, ?_, ?_, ?_,
      fun _ c _ hc0 _ => freeMsg_none h s c hc0, fun c hc => freeMsg_saved h s c (hnot c hc)⟩ <;>
      (try intro c _) <;> (unfold freeMsg; split <;> (try split) <;> first | rfl | exact Nat.le_refl _)
  obtain ⟨sh2, e2'⟩ := shape_keep sh1 hk
  refine ⟨sh2, ?_⟩
  rw [e2', hL]
  unfold ownL at hn
  rw [List.nodup_append] at hn ⊢
  refine ⟨(List.nodup_append.mp hn.1).1, hn.2.1, fun a ha b' hb' => hn.2.2 a (List.mem_append.mpr (Or.inl ha)) b' hb'⟩

/-! ## Well-formedness after a step -/

/-- A heap that differs from `h` at most by freed blocks (bytes and saved pointers), added static strings and
changed (not ended) `z_stream` records. -/
structure HLess (h h' : Heap) : Prop where
  bytes : ∀ c d, h'.bytes c = some d → h.bytes c = some d
  streams : ∀ i z, h.streams i = some z → ∃ z', h'.streams i = some z'
  istates : h'.istates = h.istates
  iallocs : h'.iallocs = h.iallocs
  dstates : h'.dstates = h.dstates
  dallocs : h'.dallocs = h.dallocs
  crc : h'.crcTable = h.crcTable
  x2n : h'.x2nTable = h.x2nTable
  next : h'.nextBlk = h.nextBlk
  base : h'.baseAddr = h.baseAddr
  hdr : h'.gzheaders = h.gzheaders
  consts : ∀ k a, h.consts k = some a → h'.consts k = some a

theorem HLess.refl (h : Heap) : HLess h h :=
  ⟨fun _ _ e => e, fun _ z e => ⟨z, e⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ e => e⟩

theorem HLess.free (h : Heap) (s : GzState) : HLess h (freeMsg h s) := by
  unfold freeMsg; split
  · split
    · exact HLess.refl h
    · next c _ _ =>
      refine ⟨fun c' d e => ?_, fun _ z e => ⟨z, e⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ e => e⟩
      by_cases hc : c' = c
      · subst hc; simp at e
      · simp only [upd_ne _ _ _ _ hc] at e; exact e
  · exact HLess.refl h

theorem HLess.lit (h : Heap) (a : Array UInt8) :
    HLess h { h with consts := upd h.consts h.consts.arr.size (some a) } :=
  ⟨fun _ _ e => e, fun _ z e => ⟨z, e⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun k b e => GzReach.consts_grow h a k b e⟩

/-- `GzWFr` after a step that stores `s'` into the state of block `b` (or keeps it), changes the file system within
`FsLe`, and changes the heap within `HLess`. -/
theorem wfr_step {w W : World} {h h' : Heap} {b : Nat} {s : GzState} (hw : GzWFr w h) (hs : w.gz h b = some s)
    (hg : ∀ c, c ≠ b → W.gzs c = w.gzs c) (hgb : ∀ s', W.gzs b = some s' → s'.strm = s.strm)
    (hf : GzOpen.FsLe w.fs W.fs) (hl : HLess h h') (hL : LitOk W h') : GzWFr W h' := by
  obtain ⟨hc, ⟨hfr, hdf⟩, hgz, hst, hb, hn, hlk, -⟩ := hw
  obtain ⟨d0, hd0⟩ := gz_live hs
  have hbn : b < h.nextBlk := by
    refine Nat.lt_of_not_le fun e => ?_
    rw [(hfr b e).2.2] at hd0; cases hd0
  have fs := GzOpen.FsLe.wf ⟨hb, hn, hlk⟩ hf
  refine ⟨⟨by rw [hl.crc]; exact hc.1, by rw [hl.x2n]; exact hc.2⟩, ⟨fun c e => ?_, fun c e => ?_⟩, fun c e => ?_,
    fun c s2 e => ?_, fs.1, fs.2.1, fs.2.2, hL⟩
  · rw [hl.next] at e
    refine ⟨by rw [hl.istates]; exact (hfr c e).1, by rw [hl.iallocs]; exact (hfr c e).2.1, ?_⟩
    cases e' : h'.bytes c with
    | none => rfl
    | some d => have := (hfr c e).2.2; rw [hl.bytes c d e'] at this; cases this
  · rw [hl.next] at e
    rw [hl.dstates, hl.dallocs]; exact hdf c e
  · rw [hl.next] at e
    rw [hg c (by omega)]; exact hgz c e
  · unfold World.gz at e
    split at e
    · next d hd =>
      by_cases hcb : c = b
      · subst hcb; rw [hgb s2 e]; obtain ⟨z, hz⟩ := hst c s hs; exact hl.streams _ z hz
      · rw [hg c hcb] at e
        obtain ⟨z, hz⟩ := hst c s2 (by unfold World.gz; rw [hl.bytes c d hd]; exact e)
        exact hl.streams _ z hz
    · cases e

/-- `GzWFw` after a step that stores into the state of block `b` (or keeps it) and changes the heap within
`HLess`. -/
theorem wfw_step {w W : World} {h h' : Heap} {b : Nat} {s : GzState} (hw : GzWFw w h) (hs : w.gz h b = some s)
    (hg : ∀ c, c ≠ b → W.gzs c = w.gzs c) (hgb : ∀ s', W.gzs b = some s' → s'.strm = s.strm)
    (hl : HLess h h') (hL : LitOk W h') : GzWFw W h' := by
  obtain ⟨hc, ⟨hfr, hdf⟩, hgz, hst, -⟩ := hw
  obtain ⟨d0, hd0⟩ := gz_live hs
  have hbn : b < h.nextBlk := by
    refine Nat.lt_of_not_le fun e => ?_
    rw [(hfr b e).2.2] at hd0; cases hd0
  refine ⟨⟨by rw [hl.crc]; exact hc.1, by rw [hl.x2n]; exact hc.2⟩, ⟨fun c e => ?_, fun c e => ?_⟩, fun c e => ?_,
    fun c s2 e => ?_, hL⟩
  · rw [hl.next] at e
    refine ⟨by rw [hl.istates]; exact (hfr c e).1, by rw [hl.iallocs]; exact (hfr c e).2.1, ?_⟩
    cases e' : h'.bytes c with
    | none => rfl
    | some d => have := (hfr c e).2.2; rw [hl.bytes c d e'] at this; cases this
  · rw [hl.next] at e
    rw [hl.dstates, hl.dallocs]; exact hdf c e
  · rw [hl.next] at e
    rw [hg c (by omega)]; exact hgz c e
  · unfold World.gz at e
    split at e
    · next d hd =>
      by_cases hcb : c = b
      · subst hcb; rw [hgb s2 e]; obtain ⟨z, hz⟩ := hst c s hs; exact hl.streams _ z hz
      · rw [hg c hcb] at e
        obtain ⟨z, hz⟩ := hst c s2 (by unfold World.gz; rw [hl.bytes c d hd]; exact e)
        exact hl.streams _ z hz
    · cases e

/-- `GzWFw` after a store into the state of block `b` that keeps its stream. -/
theorem wfw_store {w : World} {h : Heap} {b : Nat} {s : GzState} (hw : GzWFw w h) (hs : w.gz h b = some s)
    (s' : GzState) (hstrm : s'.strm = s.strm) : GzWFw { w with gzs := upd w.gzs b (some s') } h :=
  wfw_step hw hs (fun c hc => by simp [upd_ne _ _ _ _ hc]) (fun s2 e2 => by simp at e2; rw [← e2, hstrm])
    (HLess.refl h) (LitOk.ext hw.lit rfl fun _ _ e => e)

/-- A step within `HLess` whose freed blocks are the file's, which only adds static strings and changes only the
file's `gz_state`, is in the frame of the file. -/
theorem gzframe_less {w w' : World} {h h' : Heap} {f : GzPtr} (hl : HLess h h')
    (hst : ∀ i, (∀ b s, f = some b → w.gz h b = some s → i ≠ s.strm) → h'.streams i = h.streams i)
    (hc : ∀ k a, h.consts k = some a → h'.consts k = some a)
    (hb : ∀ c, c ∉ GzOwned w h f → h'.bytes c = h.bytes c)
    (hg : ∀ b, f ≠ some b → b < h.nextBlk → w'.gzs b = w.gzs b) : GzFrame w h w' h' f [] := by
  refine ⟨⟨⟨fun i hi => ?_, fun k _ => by simp [hl.hdr], fun c _ _ => by simp [hl.istates, hl.iallocs],
    fun c _ hc' d hd => ⟨d, by simp only; rw [hb c hc']; exact hd, rfl, fun _ _ _ => rfl⟩,
    fun c _ hc' hn => by simp only; rw [hb c hc']; exact hn, rfl, hl.crc, hl.x2n, hl.base, by simp [hl.next]⟩,
    fun c _ _ => by simp [hl.dstates, hl.dallocs]⟩, hc, hg⟩
  refine hst i fun b s e hs => ?_
  subst e
  simp only [hs, List.mem_singleton] at hi
  exact hi

/-! ## `gzbuffer` -/

theorem gzbuffer_run {w : World} {h : Heap} {b : Nat} {s : GzState} (hs : w.gz h b = some s)
    (hm : s.mode = GZ_READ ∨ s.mode = GZ_WRITE) (n : UInt32) :
    (s.size ≠ 0 ∧ GzRun (gzbuffer (some b) n) w h (-1) w h) ∨
    (s.size = 0 ∧ ∃ v : UInt32, 8 ≤ v.toNat ∧ v.toNat ≤ 2 ^ 30 ∧
      GzRun (gzbuffer (some b) n) w h 0 { w with gzs := upd w.gzs b (some { s with want := v }) } h) := by
  have hmode : ¬(¬s.mode = GZ_READ ∧ ¬s.mode = GZ_WRITE) := by
    rcases hm with hm | hm <;> simp [hm]
  by_cases hz : s.size = 0
  · right
    refine ⟨hz, ?_⟩
    have hmax : GZBUFSIZE_MAX.toNat = 2 ^ 30 := by decide
    by_cases h1 : n > GZBUFSIZE_MAX
    · refine ⟨GZBUFSIZE_MAX, by rw [hmax]; decide, by rw [hmax]; exact Nat.le_refl _, ?_⟩
      have h2 : ¬ GZBUFSIZE_MAX < 8 := by decide
      simp [GzRun, C.run, StateT.run, gzbuffer, rdG_app' hs, wrG_app hs, hmode, hz, h1, h2]
    · by_cases h2 : n < 8
      · refine ⟨8, by decide, by decide, ?_⟩
        simp [GzRun, C.run, StateT.run, gzbuffer, rdG_app' hs, wrG_app hs, hmode, hz, h1, h2]
      · refine ⟨n, ?_, ?_, ?_⟩
        · have := UInt32.le_iff_toNat_le.mp (UInt32.not_lt.mp h2); simpa using this
        · have := UInt32.le_iff_toNat_le.mp (UInt32.not_lt.mp h1); rw [hmax] at this; exact this
        · simp [GzRun, C.run, StateT.run, gzbuffer, rdG_app' hs, wrG_app hs, hmode, hz, h1, h2]
  · left
    exact ⟨hz, by simp [GzRun, C.run, StateT.run, gzbuffer, rdG_app' hs, hmode, hz]⟩

/-! ## Each kind of step keeps the invariant of its handle -/

theorem gdet {α : Type} {m : G α} {w : World} {h : Heap} {r r2 : α} {w' w2 : World} {h' h2 : Heap}
    (e1 : GzRun m w h r w' h') (e2 : GzRun m w h r2 w2 h2) : r = r2 ∧ w' = w2 ∧ h' = h2 := by
  unfold GzRun at e1 e2; rw [e1] at e2; cases e2; exact ⟨rfl, rfl, rfl⟩

/-- The parts of the invariant of either handle. -/

theorem parts' {w : World} {h : Heap} {f : GzPtr} (hv : GzInvR w h f ∨ GzInvWS w h f) : GzInv w h f := by
  rcases hv with ⟨hv, -⟩ | ⟨hv, -⟩ <;> exact hv

theorem modeOf {w : World} {h : Heap} {b : Nat} {s : GzState} {m : Int32} (hs : w.gz h b = some s)
    (hm : GzModeIs w h (some b) m) : s.mode = m := by
  obtain ⟨b', s', e, hs', hm'⟩ := hm
  cases e; rw [hs] at hs'; cases hs'; exact hm'

/-- After a store of `s'` into the state of block `b`, the file is open with `s'`. -/
theorem inv_store {w : World} {h h' : Heap} {b : Nat} {s s' : GzState} (hs : w.gz h b = some s)
    (hb : ∀ d, h.bytes b = some d → h'.bytes b = some d) (sh : GzShape h' s') (hn : (ownL h' b s').Nodup) :
    GzInv { w with gzs := upd w.gzs b (some s') } h' (some b) ∧
      ({ w with gzs := upd w.gzs b (some s') } : World).gz h' b = some s' := by
  obtain ⟨d, hd⟩ := gz_live hs
  have e : ({ w with gzs := upd w.gzs b (some s') } : World).gz h' b = some s' := by
    unfold World.gz; rw [hb d hd]; simp
  exact ⟨⟨b, s', rfl, e, sh, hn⟩, e⟩

/-- A step that changes neither the world nor the heap keeps both invariants. -/
theorem keepsR_same {S : World → Heap → World → Heap → GzPtr → Prop}
    (hS : ∀ w h w' h' b s, w.gz h b = some s → s.mode = GZ_READ → S w h w' h' (some b) → w' = w ∧ h' = h) :
    KeepsR S := by
  intro w h w' h' f hv hst
  obtain ⟨⟨b, s, rfl, hs, sh, hn⟩, hm, hw⟩ := hv
  obtain ⟨rfl, rfl⟩ := hS w h w' h' b s hs (modeOf hs hm) hst
  exact ⟨⟨b, s, rfl, hs, sh, hn⟩, hm, hw⟩

theorem keepsW_same {S : World → Heap → World → Heap → GzPtr → Prop}
    (hS : ∀ w h w' h' b s, w.gz h b = some s → s.mode = GZ_WRITE → S w h w' h' (some b) → w' = w ∧ h' = h) :
    KeepsW S := by
  intro w h w' h' f hv hst
  obtain ⟨⟨b, s, rfl, hs, sh, hn⟩, hm, hw⟩ := hv
  obtain ⟨rfl, rfl⟩ := hS w h w' h' b s hs (modeOf hs hm) hst
  exact ⟨⟨b, s, rfl, hs, sh, hn⟩, hm, hw⟩

/-- The write-side calls return at the mode check on a read handle. -/
theorem wstep_keepsR : KeepsR GzWStep := by
  refine keepsR_same fun w h w' h' b s hs hm hst => ?_
  rcases hst with ⟨buf, len, r, -, e⟩ | ⟨buf, sz, ni, r, -, e⟩ | ⟨c, r, e⟩ | ⟨p, r, -, -, e⟩ | ⟨p, r, -, e⟩ |
    ⟨p, r, -, e⟩ | ⟨fl, r, e⟩ | ⟨l, st, r, e⟩
  · exact (gdet e (gzwrite_read hs hm buf len)).2
  · exact (gdet e (gzfwrite_read hs hm buf sz ni)).2
  · exact (gdet e (gzputc_read hs hm c)).2
  · exact (gdet e (gzputs_read hs hm p)).2
  · exact (gdet e (gzprintf_read hs hm p)).2
  · exact (gdet e (gzvprintf_read hs hm p)).2
  · exact (gdet e (gzflush_read hs hm fl)).2
  · exact (gdet e (gzsetparams_read hs hm l st)).2

theorem read_keepsW : KeepsW SRead := keepsW_same fun _ _ _ _ _ _ hs hm ⟨buf, len, _, _, e⟩ =>
  (gdet e (gzread_write hs hm buf len)).2
theorem fread_keepsW : KeepsW SFread := keepsW_same fun _ _ _ _ _ _ hs hm ⟨buf, sz, ni, _, _, e⟩ =>
  (gdet e (gzfread_write hs hm buf sz ni)).2
theorem getc_keepsW : KeepsW SGetc := keepsW_same fun _ _ _ _ _ _ hs hm ⟨_, e⟩ =>
  (gdet e (gzgetc_write hs hm)).2
theorem getc__keepsW : KeepsW SGetc_ := keepsW_same fun _ _ _ _ _ _ hs hm ⟨_, e⟩ =>
  (gdet e (gzgetc__write hs hm)).2
theorem ungetc_keepsW : KeepsW SUngetc := keepsW_same fun _ _ _ _ _ _ hs hm ⟨c, _, e⟩ =>
  (gdet e (gzungetc_write hs hm c)).2
theorem gets_keepsW : KeepsW SGets := keepsW_same fun _ _ _ _ _ _ hs hm ⟨buf, len, _, _, e⟩ =>
  (gdet e (gzgets_write hs hm buf len)).2
theorem direct_keepsW : KeepsW SDirect := keepsW_same fun _ _ _ _ _ _ hs hm ⟨_, e⟩ =>
  (gdet e (gzdirect_write hs hm)).2
theorem rewind_keepsW : KeepsW SRewind := keepsW_same fun _ _ _ _ _ _ hs hm ⟨_, e⟩ =>
  (gdet e (gzrewind_write hs hm)).2

/-- A step that changes at most the file system (within `FsLe`), the static strings (adding one) and the freed
blocks outside the file's own, leaving the `gz_state` objects, keeps both invariants. -/
theorem keeps_outside {S : World → Heap → World → Heap → GzPtr → Prop}
    (hS : ∀ w h w' h' f, (GzInvR w h f ∨ GzInvWS w h f) → S w h w' h' f →
      w'.gzs = w.gzs ∧ GzOpen.FsLe w.fs w'.fs ∧ (h' = h ∨ ∃ a, h' = { h with consts := upd h.consts h.consts.arr.size (some a) }) ∧
      (LitOk w h → LitOk w' h')) :
    KeepsR S ∧ KeepsW S := by
  have key : ∀ w h w' h' f, (GzInvR w h f ∨ GzInvWS w h f) → S w h w' h' f →
      GzInv w' h' f ∧ (∀ m, GzModeIs w h f m → GzModeIs w' h' f m) ∧ (GzWFr w h → GzWFr w' h') ∧
        (GzWFw w h → GzWFw w' h') := by
    intro w h w' h' f hv0 hst
    obtain ⟨hg, hf, hh, hL⟩ := hS w h w' h' f hv0 hst
    have hv : GzInv w h f := by rcases hv0 with ⟨hv, -⟩ | ⟨hv, -⟩ <;> exact hv
    obtain ⟨b, s, rfl, hs, sh, hn⟩ := hv
    have hl : HLess h h' := by
      rcases hh with e | ⟨a, e⟩ <;> rw [e]
      · exact HLess.refl h
      · exact HLess.lit h a
    have hs' : w'.gz h' b = some s := by
      unfold World.gz at hs ⊢; rw [hg]; rcases hh with e | ⟨a, e⟩ <;> rw [e] <;> exact hs
    have hk : HK h h' s (ownL h b s) := by
      rcases hh with e | ⟨a, e⟩ <;> rw [e]
      · exact ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, Nat.le_refl _,
          fun _ _ _ e _ => e, fun _ _ => rfl⟩
      · exact ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, Nat.le_refl _,
          fun _ _ _ e _ => e, fun _ _ => rfl⟩
    obtain ⟨sh', e⟩ := shape_keep sh hk
    have hgb : ∀ s', w'.gzs b = some s' → s'.strm = s.strm := by
      intro s' e'
      rw [hg, gzs_of hs] at e'; cases e'; rfl
    exact ⟨⟨b, s, rfl, hs', sh', by rw [e]; exact hn⟩, fun m hm => ⟨b, s, rfl, hs', modeOf hs hm⟩, fun hw =>
      wfr_step (W := w') hw hs (fun c _ => by rw [hg]) hgb hf hl (hL hw.lit), fun hw =>
      wfw_step (W := w') hw hs (fun c _ => by rw [hg]) hgb hl (hL hw.lit)⟩
  refine ⟨fun w h w' h' f hv hst => ?_, fun w h w' h' f hv hst => ?_⟩
  · obtain ⟨a, b, c, -⟩ := key w h w' h' f (Or.inl hv) hst
    exact ⟨a, b _ hv.2.1, c hv.2.2⟩
  · obtain ⟨a, b, -, c⟩ := key w h w' h' f (Or.inr hv) hst
    exact ⟨a, b _ hv.2.1, c hv.2.2⟩

theorem tell64_keeps : KeepsR STell64 ∧ KeepsW STell64 := keeps_outside fun w h w' h' f hv ⟨r, e⟩ => by
  obtain ⟨r', e'⟩ := GzReach.gztell64_inv (Or.inr (parts' hv))
  obtain ⟨-, rfl, rfl⟩ := gdet e e'
  exact ⟨rfl, GzOpen.FsLe.refl _, Or.inl rfl, id⟩

theorem tell_keeps : KeepsR STell ∧ KeepsW STell := keeps_outside fun w h w' h' f hv ⟨r, e⟩ => by
  obtain ⟨r', e'⟩ := GzReach.gztell_inv (Or.inr (parts' hv))
  obtain ⟨-, rfl, rfl⟩ := gdet e e'
  exact ⟨rfl, GzOpen.FsLe.refl _, Or.inl rfl, id⟩

theorem eof_keeps : KeepsR SEof ∧ KeepsW SEof := keeps_outside fun w h w' h' f hv ⟨r, e⟩ => by
  obtain ⟨r', e'⟩ := GzReach.gzeof_inv (Or.inr (parts' hv))
  obtain ⟨-, rfl, rfl⟩ := gdet e e'
  exact ⟨rfl, GzOpen.FsLe.refl _, Or.inl rfl, id⟩

theorem error_keeps : KeepsR SError ∧ KeepsW SError := keeps_outside fun w h w' h' f hv ⟨ee, r, e⟩ => by
  obtain ⟨r', w2, h2, e', -, hg, hf, hh, hL⟩ := GzReach.gzerror_inv ee (Or.inr (parts' hv))
  obtain ⟨-, rfl, rfl⟩ := gdet e e'
  exact ⟨hg, by rw [hf]; exact GzOpen.FsLe.refl _, hh, hL⟩

/-- `gzoffset64` and `gzoffset` on a write handle, or on a read handle in a world whose `lseek` values are `-1` or
not negative. -/
theorem offset_fs {w : World} {h : Heap} {f : GzPtr} (hv : GzInv w h f) {S : G Int64}
    (hrun : (∀ b s, f = some b → w.gz h b = some s → s.mode = GZ_READ →
      ∀ n v, w.fs.lseekChoice n = .value v → v = -1 ∨ 0 ≤ v) → (f = none ∨ GzInv w h f) →
      ∃ r fs', GzRun S w h r { w with fs := fs' } h ∧ (fs' = w.fs ∨ ∃ fd, fs' = (w.fs.lseekCall fd 0 SEEK_CUR).2))
    {w' : World} {h' : Heap} {r : Int64} (e : GzRun S w h r w' h')
    (hl : ∀ b s, f = some b → w.gz h b = some s → s.mode = GZ_READ →
      ∀ n v, w.fs.lseekChoice n = .value v → v = -1 ∨ 0 ≤ v) :
    w'.gzs = w.gzs ∧ GzOpen.FsLe w.fs w'.fs ∧ (h' = h ∨ ∃ a, h' = { h with consts := upd h.consts h.consts.arr.size (some a) }) ∧
      (LitOk w h → LitOk w' h') := by
  obtain ⟨r', fs', e', hfs⟩ := hrun hl (Or.inr hv)
  obtain ⟨-, rfl, rfl⟩ := gdet e e'
  refine ⟨rfl, ?_, Or.inl rfl, id⟩
  rcases hfs with rfl | ⟨fd, rfl⟩
  · exact GzOpen.FsLe.refl _
  · exact GzOpen.lseekCall_le _ _ _ _

theorem lseek_ok {w : World} {h : Heap} {f : GzPtr} (hv : GzInvR w h f ∨ GzInvWS w h f) :
    ∀ b s, f = some b → w.gz h b = some s → s.mode = GZ_READ →
      ∀ n v, w.fs.lseekChoice n = .value v → v = -1 ∨ 0 ≤ v := by
  intro b s e hs hm
  rcases hv with ⟨-, -, hw⟩ | ⟨-, hm', -⟩
  · exact hw.2.2.2.2.2.2.1
  · cases e; exact absurd (hm.symm.trans (modeOf hs hm')) read_ne_write

theorem offset64_keeps : KeepsR SOffset64 ∧ KeepsW SOffset64 := keeps_outside fun _ _ _ _ _ hv ⟨_, e⟩ =>
  offset_fs (parts' hv) (fun hl hv' => GzReach.gzoffset64_inv hl hv') e (lseek_ok hv)

theorem offset_keeps : KeepsR SOffset ∧ KeepsW SOffset := keeps_outside fun _ _ _ _ _ hv ⟨_, e⟩ =>
  offset_fs (parts' hv) (fun hl hv' => GzReach.gzoffset_inv hl hv') e (lseek_ok hv)

theorem msg_ne_b {h : Heap} {b : Nat} {s : GzState} (hn : (ownL h b s).Nodup) :
    ∀ c o, s.msg = .val (.ref (.heap c) o) → c ≠ b := by
  intro c o hm hcb
  subst hcb
  unfold ownL at hn
  rw [hm] at hn
  simp [blkOf, List.nodup_append] at hn

/-- Both invariants after a store of `s'` (with the mode of `s`) into the state, on a heap within `HLess` that keeps
the state's block. -/
theorem keeps_store {w : World} {h h' : Heap} {b : Nat} {s s' : GzState} (hs : w.gz h b = some s)
    (hl : HLess h h') (hb : ∀ d, h.bytes b = some d → h'.bytes b = some d) (sh : GzShape h' s')
    (hn : (ownL h' b s').Nodup) (hmode : s'.mode = s.mode) (hstrm : s'.strm = s.strm) :
    (GzInvR w h (some b) → GzInvR { w with gzs := upd w.gzs b (some s') } h' (some b)) ∧
    (GzInvWS w h (some b) → GzInvWS { w with gzs := upd w.gzs b (some s') } h' (some b)) := by
  obtain ⟨hi, e⟩ := inv_store hs hb sh hn
  refine ⟨fun hv => ⟨hi, ⟨b, s', rfl, e, by rw [hmode]; exact modeOf hs hv.2.1⟩, ?_⟩,
    fun hv => ⟨hi, ⟨b, s', rfl, e, by rw [hmode]; exact modeOf hs hv.2.1⟩, ?_⟩⟩
  · refine wfr_step hv.2.2 hs (fun c hc => by simp [upd_ne _ _ _ _ hc]) (fun s2 e2 => ?_) (GzOpen.FsLe.refl _) hl
      (LitOk.ext hv.2.2.lit rfl hl.consts)
    simp at e2; rw [← e2, hstrm]
  · refine wfw_step hv.2.2 hs (fun c hc => by simp [upd_ne _ _ _ _ hc]) (fun s2 e2 => ?_) hl
      (LitOk.ext hv.2.2.lit rfl hl.consts)
    simp at e2; rw [← e2, hstrm]

theorem buffer_keeps : KeepsR SBuffer ∧ KeepsW SBuffer := by
  have key : ∀ w h w' h' b s, w.gz h b = some s → GzShape h s → (ownL h b s).Nodup → SBuffer w h w' h' (some b) →
      (w' = w ∧ h' = h) ∨ ∃ v : UInt32, w' = { w with gzs := upd w.gzs b (some { s with want := v }) } ∧ h' = h ∧
        GzShape h { s with want := v } ∧ (ownL h b { s with want := v }).Nodup := by
    intro w h w' h' b s hs sh hn ⟨n, r, e⟩
    rcases gzbuffer_run hs sh.mode n with ⟨-, e'⟩ | ⟨hz, v, h8, h30, e'⟩
    · obtain ⟨-, e1, e2⟩ := gdet e e'; exact Or.inl ⟨e1, e2⟩
    · obtain ⟨-, e1, e2⟩ := gdet e e'
      refine Or.inr ⟨v, e1, e2, ?_, hn⟩
      exact ⟨sh.mode, sh.path, sh.strm, h8, h30, Or.inl hz, ⟨sh.pos.1, sh.pos.2, sh.pos.3, sh.pos.4⟩,
        ⟨sh.msg.msg, sh.msg.mem⟩, fun hr => ⟨(sh.read hr).how, fun e => absurd hz e, (sh.read hr).nobuf,
          (sh.read hr).skip_have, (sh.read hr).fresh, (sh.read hr).look,
          (sh.read hr).pos_have, (sh.read hr).look_pos, (sh.read hr).gzip_direct, (sh.read hr).copy_in⟩, fun hw => ⟨fun e => absurd hz e, (sh.write hw).nobuf,
          (sh.write hw).have0⟩, fun _ => sh.dead hz⟩
  refine ⟨fun w h w' h' f hv hst => ?_, fun w h w' h' f hv hst => ?_⟩
  · obtain ⟨b, s, rfl, hs, sh, hn⟩ := hv.1
    rcases key w h w' h' b s hs sh hn hst with ⟨e1, e2⟩ | ⟨v, e1, e2, sh', hn'⟩ <;> rw [e1, e2]
    · exact hv
    · exact (keeps_store hs (HLess.refl h) (fun _ e => e) sh' hn' rfl rfl).1 hv
  · obtain ⟨b, s, rfl, hs, sh, hn⟩ := hv.1
    rcases key w h w' h' b s hs sh hn hst with ⟨e1, e2⟩ | ⟨v, e1, e2, sh', hn'⟩ <;> rw [e1, e2]
    · exact hv
    · exact (keeps_store hs (HLess.refl h) (fun _ e => e) sh' hn' rfl rfl).2 hv

theorem clrSt_mode (s : GzState) : (errSt (clrSt s) ZlibNg.Inflate.Z_OK).mode = s.mode := by
  by_cases hm : s.mode = GZ_READ <;> simp [errSt, clrSt, hm]

theorem clrSt_strm (s : GzState) : (errSt (clrSt s) ZlibNg.Inflate.Z_OK).strm = s.strm := by
  by_cases hm : s.mode = GZ_READ <;> simp [errSt, clrSt, hm]

theorem clearerr_keeps : KeepsR SClearerr ∧ KeepsW SClearerr := by
  have key : ∀ w h w' h' b s, w.gz h b = some s → GzShape h s → (ownL h b s).Nodup → SClearerr w h w' h' (some b) →
      w' = { w with gzs := upd w.gzs b (some (errSt (clrSt s) ZlibNg.Inflate.Z_OK)) } ∧ h' = freeMsg h s := by
    intro w h w' h' b s hs sh hn ⟨r, e⟩
    obtain ⟨-, e1, e2⟩ := gdet e (gzclearerr_run hs sh.mode sh.msg (msg_ne_b hn))
    exact ⟨e1, e2⟩
  have hb : ∀ h b s, (ownL h b s).Nodup → ∀ d, h.bytes b = some d → (freeMsg h s).bytes b = some d := by
    intro h b s hn d hd
    rw [freeMsg_bytes h s b fun hc => ?_]; exact hd
    revert hc
    cases e : s.msg with
    | uninit => simp [blkOf]
    | val p =>
      cases p with
      | null => simp [blkOf]
      | ref r o =>
        cases r with
        | heap c => simp only [blkOf, List.mem_singleton]; intro e'; exact msg_ne_b hn c o e e'.symm
        | const k => simp [blkOf]
        | str k => simp [blkOf]
  refine ⟨fun w h w' h' f hv hst => ?_, fun w h w' h' f hv hst => ?_⟩
  · obtain ⟨b, s, rfl, hs, sh, hn⟩ := hv.1
    obtain ⟨e1, e2⟩ := key w h w' h' b s hs sh hn hst
    rw [e1, e2]
    obtain ⟨sh', hn'⟩ := clear_keep (b := b) sh hn
    exact (keeps_store hs (HLess.free h s) (hb h b s hn) sh' hn' (clrSt_mode s) (clrSt_strm s)).1 hv
  · obtain ⟨b, s, rfl, hs, sh, hn⟩ := hv.1
    obtain ⟨e1, e2⟩ := key w h w' h' b s hs sh hn hst
    rw [e1, e2]
    obtain ⟨sh', hn'⟩ := clear_keep (b := b) sh hn
    exact (keeps_store hs (HLess.free h s) (hb h b s hn) sh' hn' (clrSt_mode s) (clrSt_strm s)).2 hv

/-! ## Caller steps on a read handle -/

theorem ownL_owned {w : World} {h : Heap} {b : Nat} {s : GzState} (hs : w.gz h b = some s) :
    ∀ c ∈ ownL h b s, c ∈ GzOwned w h (some b) := by
  intro c hc
  simp only [GzOwned, hs]
  unfold ownL at hc
  simp only [List.mem_append] at hc ⊢
  rcases hc with ((hc | hc) | hc) | hc
  · exact Or.inl (Or.inl (Or.inl (Or.inl hc)))
  · exact Or.inl (Or.inl (Or.inl (Or.inr (by unfold blkOf at hc; split at hc <;> simp_all))))
  · exact Or.inl (Or.inl (Or.inr (by unfold blkOf at hc; split at hc <;> simp_all)))
  · split at hc
    · simp at hc
    · simp only [List.mem_append] at hc
      rcases hc with hc | hc
      · exact Or.inl (Or.inr (by unfold blkOf at hc; split at hc <;> simp_all))
      · exact Or.inr (by unfold stBlk at hc; exact hc)

theorem dead_owned {w : World} {h : Heap} {b : Nat} {s : GzState} (hs : w.gz h b = some s) :
    ∀ c ∈ blkOf s.buffers ++ stBlk h s, c ∈ GzOwned w h (some b) := by
  intro c hc
  simp only [GzOwned, hs]
  simp only [List.mem_append] at hc ⊢
  rcases hc with hc | hc
  · exact Or.inl (Or.inr (by unfold blkOf at hc; split at hc <;> simp_all))
  · exact Or.inr (by unfold stBlk at hc; exact hc)

theorem macro_keepsR {w : World} {h : Heap} {w' : World} {h' : Heap} {f : GzPtr} (hv : GzInvR w h f)
    (hc : GzGetcMacro w h w' h' f) : GzInvR w' h' f := by
  obtain ⟨b, s, nx, rfl, hs, hhv, hnx, nx', hadd, e1, e2⟩ := hc
  rw [e1, e2]
  obtain ⟨⟨b0, s0, e0, hs0, sh, hn⟩, hm, hw⟩ := hv
  cases e0; rw [hs] at hs0; cases hs0
  have hr := modeOf hs hm
  have R := sh.read hr
  have hsz : s.size ≠ 0 := fun e => hhv (R.nobuf e)
  obtain ⟨c, base, z, hb, hi, hz, hhv', hai, hreg, hmsg⟩ := R.bufs hsz
  obtain ⟨p, hp, k, hpk, hlo, hhi⟩ := hhv'.resolve_left hhv
  rw [hnx] at hp; cases hp
  obtain ⟨d, hd, hds⟩ := hb.fits
  have h1 : 1 ≤ s.«have».toNat := by
    have : s.«have».toNat ≠ 0 := fun e => hhv (UInt32.toNat_inj.mp (by simpa using e))
    omega
  have hadd' : C.run (Ptr.add (.ref (.heap c) (base + k) : BPtr) 1) h =
      .ok (.ref (.heap c) (((base + k : Nat) : Int) + 1).toNat, h) :=
    Inftrees.add_ok (r := BRef.heap c) (a := d) hd (by omega) (by omega) (by push_cast; omega)
  rw [hpk] at hadd
  rw [hadd] at hadd'; cases hadd'
  have hk1 : (((base + k : Nat) : Int) + 1).toNat = base + (k + 1) := by omega
  have hhm : (s.«have» - 1).toNat = s.«have».toNat - 1 := by
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simpa using h1)]; simp
  have hph := R.pos_have
  have hpos : s.pos.toInt + 1 < 2 ^ 63 := by
    have : GZ_OFF_MAX.toInt = 9223372036854775807 := by decide
    omega
  have hp1 : (s.pos + 1).toInt = s.pos.toInt + 1 := by
    have l1 := s.pos.le_toInt
    have l2 : (Int64.minValue).toInt = -9223372036854775808 := by decide
    rw [Int64.toInt_add, Int64.toInt_one]
    exact Int.bmod_eq_of_le (by omega) (by omega)
  have P := sh.pos
  have hmax : GZ_OFF_MAX.toInt = 9223372036854775807 := by decide
  let s' : GzState := { s with «have» := s.«have» - 1, pos := s.pos + 1, next := .val (.ref (.heap c) (((base + k : Nat) : Int) + 1).toNat) }
  have sh' : GzShape h s' := by
    refine ⟨sh.mode, sh.path, sh.strm, sh.want_lo, sh.want_hi, sh.size,
      ⟨P.1, ?_, ?_, fun e => absurd (hr.symm.trans e) read_ne_write⟩, ⟨sh.msg.msg, sh.msg.mem⟩,
      fun _ => ⟨R.how, fun _ => ⟨c, base, z, ⟨hb.size, hb.buffers, hb.inp, hb.out, ⟨d, hd, hds⟩, hb.hdr⟩, hi, hz, ?_, hai, hreg, hmsg⟩,
        fun e => absurd e hsz, ?_, fun e => absurd e hsz, fun e => absurd e hsz, ?_, fun hL hD => ?_, R.gzip_direct, R.copy_in⟩,
        fun e => absurd (hr.symm.trans e) read_ne_write, fun e => absurd e hsz⟩
    · show (s.pos + 1).toInt + s.skip.toInt ≤ GZ_OFF_MAX.toInt
      rw [hp1]
      by_cases hk : s.skip = 0
      · rw [hk]; simp; rw [hmax]; omega
      · have := R.skip_have hk; omega
    · show -GZ_OFF_MAX.toInt ≤ (s.pos + 1).toInt
      rw [hp1]; have := P.3; omega
    · right
      refine ⟨.ref (.heap c) (base + (k + 1)), by show Ival.val (Ptr.ref (BRef.heap c) _) = _; rw [hk1], k + 1, rfl, ?_, ?_⟩
      · show inSize s ≤ k + 1; omega
      · show k + 1 + (s.«have» - 1).toNat ≤ inSize s + outSize s; rw [hhm]; omega
    · intro hk
      show (s.pos + 1).toInt + s.skip.toInt + ((s.«have» - 1).toNat : Int) ≤ GZ_OFF_MAX.toInt
      rw [hp1, hhm]; have := R.skip_have hk; omega
    · show (s.pos + 1).toInt + ((s.«have» - 1).toNat : Int) ≤ GZ_OFF_MAX.toInt
      rw [hp1, hhm]; omega
    · show (s.pos + 1).toInt + ((s.«have» - 1).toNat : Int) ≤ 0
      rw [hp1, hhm]; have := R.look_pos hL hD; omega
  have hn' : (ownL h b s').Nodup := hn
  exact (keeps_store hs (HLess.refl h) (fun _ e => e) sh' hn' rfl rfl).1 ⟨⟨b, s, rfl, hs, sh, hn⟩, hm, hw⟩

theorem keeps_keepsR {w : World} {h : Heap} {w' : World} {h' : Heap} {f : GzPtr} (hv : GzInvR w h f)
    (hc : GzKeeps w h w' h' f) : GzInvR w' h' f := by
  obtain ⟨hwf, hnb, hba, b, s, rfl, hs, hs', hstr, hobj⟩ := hc
  obtain ⟨⟨b0, s0, e0, hs0, sh, hn⟩, hm, -⟩ := hv
  cases e0; rw [hs] at hs0; cases hs0
  have hk : HK h h' s (ownL h b s) := by
    refine ⟨hstr, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, hba, hnb,
      fun _ c hc hc0 _ => by rw [(hobj c (dead_owned hs c hc)).1]; exact hc0,
      fun c hc => (hobj c (ownL_owned hs c hc)).2.2.2.2.2⟩
    · exact (hobj c (ownL_owned hs c hc)).1
    · exact (hobj c (ownL_owned hs c hc)).2.1
    · exact (hobj c (ownL_owned hs c hc)).2.2.1
    · exact (hobj c (ownL_owned hs c hc)).2.2.2.1
    · exact (hobj c (ownL_owned hs c hc)).2.2.2.2.1
  obtain ⟨sh', e⟩ := shape_keep sh hk
  exact ⟨⟨b, s, rfl, hs', sh', by rw [e]; exact hn⟩, ⟨b, s, rfl, hs', modeOf hs hm⟩, GzWFr.of hwf⟩

theorem caller_keepsR : KeepsR GzCallerStep := by
  intro w h w' h' f hv hc
  rcases hc with hc | hc
  · exact macro_keepsR hv hc
  · exact keeps_keepsR hv hc

/-! ## Caller steps on a write handle -/

/-- The `gzgetc()` macro needs buffered output, and a write handle has none (`x.have` is 0). -/
theorem macro_keepsW {w : World} {h : Heap} {w' : World} {h' : Heap} {f : GzPtr} (hv : GzInvWS w h f)
    (hc : GzGetcMacro w h w' h' f) : GzInvWS w' h' f := by
  obtain ⟨b, s, nx, rfl, hs, hhv, -⟩ := hc
  obtain ⟨⟨b0, s0, e0, hs0, sh, -⟩, hm, -⟩ := hv
  cases e0; rw [hs] at hs0; cases hs0
  exact absurd (sh.write (modeOf hs hm)).have0 hhv

theorem keeps_keepsW {w : World} {h : Heap} {w' : World} {h' : Heap} {f : GzPtr} (hv : GzInvWS w h f)
    (hc : GzKeeps w h w' h' f) : GzInvWS w' h' f := by
  obtain ⟨hwf, hnb, hba, b, s, rfl, hs, hs', hstr, hobj⟩ := hc
  obtain ⟨⟨b0, s0, e0, hs0, sh, hn⟩, hm, -⟩ := hv
  cases e0; rw [hs] at hs0; cases hs0
  have hk : HK h h' s (ownL h b s) := by
    refine ⟨hstr, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, hba, hnb,
      fun _ c hc hc0 _ => by rw [(hobj c (dead_owned hs c hc)).1]; exact hc0,
      fun c hc => (hobj c (ownL_owned hs c hc)).2.2.2.2.2⟩
    · exact (hobj c (ownL_owned hs c hc)).1
    · exact (hobj c (ownL_owned hs c hc)).2.1
    · exact (hobj c (ownL_owned hs c hc)).2.2.1
    · exact (hobj c (ownL_owned hs c hc)).2.2.2.1
    · exact (hobj c (ownL_owned hs c hc)).2.2.2.2.1
  obtain ⟨sh', e⟩ := shape_keep sh hk
  exact ⟨⟨b, s, rfl, hs', sh', by rw [e]; exact hn⟩, ⟨b, s, rfl, hs', modeOf hs hm⟩, GzWFw.of hwf⟩

/-- **The caller's steps keep the invariant of a write handle** (the `caller` field of `GWriteSteps`). -/
theorem caller_keepsW : KeepsW GzCallerStep := by
  intro w h w' h' f hv hc
  rcases hc with hc | hc
  · exact macro_keepsW hv hc
  · exact keeps_keepsW hv hc

end ZlibNgF.Proof.GzMode
