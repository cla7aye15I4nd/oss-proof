import ZlibNgF.Proof.«gzwrite.c.comp»

/-!
# The input fields of the stream of a write handle (`ZlibNgF`)

Between calls, `GzWBuf.inp` puts the input of the deflate stream inside `in` (or makes it empty). Inside `gz_write`,
the large direct path points `next_in` into the caller's buffer and runs `gz_comp` on it (patch 0011 points it back at
`in` afterwards). There the invariant holds of the *flat* heap, where the stream's input is empty (`flatZ`), and the
caller's range is described apart. `setZ`: the heap with stream `i` replaced. `invWS_setIn`: a write handle with
buffers keeps its invariant when its input fields change to ones that `GzWBuf.inp` allows.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace ZlibNgF.Proof.GzWrite
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Gz ZlibNgF.Proof.GzInv ZlibNgF.Proof.GzSat ZlibNgF.Proof.GzMode
open ZlibNgF.Proof.GzWriteNeeds

/-- The heap `h` with stream `i` set to `z`. -/
abbrev setZ (h : Heap) (i : Nat) (z : ZStream) : Heap := { h with streams := upd h.streams i (some z) }

/-- The stream `z` with no input. -/
def flatZ (z : ZStream) : ZStream := { z with next_in := .null, avail_in := 0 }

theorem upd_self {α : Type} [Inhabited α] (t : Tbl α) (k : Nat) (a : α) (hk : t k = a) (hne : a ≠ default) :
    upd t k a = t := by
  have hs : k < t.arr.size := Tbl.lt_size_of_get_ne t k (by rw [hk]; exact hne)
  cases t with
  | mk arr =>
    simp only [upd, Tbl.set] at hs ⊢
    rw [ite_eq_left_of_eq_true _ _ (eq_true hs)]
    congr 1
    apply Array.ext_getElem?
    intro j
    simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    split
    · next e =>
      subst e
      have : (⟨arr⟩ : Tbl α).get k = a := hk
      simp [Tbl.get_eq, Array.getElem?_eq_getElem hs] at this ⊢
      exact this.symm
    · rfl

theorem setZ_setZ (h : Heap) (i : Nat) (z z' : ZStream) : setZ (setZ h i z) i z' = setZ h i z' := by
  simp [setZ, InflateInv.upd_upd]

theorem setZ_self {h : Heap} {i : Nat} {z : ZStream} (hz : h.streams i = some z) : setZ h i z = h := by
  unfold setZ
  rw [upd_self h.streams i (some z) hz (by simp [default])]

@[simp] theorem setZ_streams_same (h : Heap) (i : Nat) (z : ZStream) : (setZ h i z).streams i = some z := by
  simp [setZ]

theorem setZ_streams_ne (h : Heap) {i j : Nat} (z : ZStream) (hne : j ≠ i) : (setZ h i z).streams j = h.streams j := by
  simp [setZ, upd_ne _ _ _ _ hne]

/-- What `GzWBuf.inp` asks of input fields `p`, `n` of a handle with buffers. -/
def InpOk (s : GzState) (c base : Nat) (p : BPtr) (n : UInt32) : Prop :=
  Inside c base 0 s.size.toNat p n.toNat ∨ (n = 0 ∧ (s.direct ≠ 0 ∨ p = .null))

/-- **The input fields of a write handle with buffers** change to fields that `GzWBuf.inp` allows: the invariant
holds, and it is a step of the file. -/
theorem invWS_setZ {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvWS w h (some b))
    (hs : w.gz h b = some s) (hsz : s.size ≠ 0) {z : ZStream} (hz : h.streams s.strm = some z) (z' : ZStream)
    (he : z' = { z with next_in := z'.next_in, avail_in := z'.avail_in })
    (hinp : ∀ c base, GzBufs h s c base → InpOk s c base z'.next_in z'.avail_in) :
    GzInvWS w (setZ h s.strm z') (some b) ∧ w.gz (setZ h s.strm z') b = some s ∧
      GStep w h w (setZ h s.strm z') b [] := by
  have hwm := modeOf hs hv.2.1
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  have hwf := hv.2.2
  obtain ⟨c, base, z1, hB, hz1, WB⟩ := (sh.write hwm).bufs hsz
  rw [hz] at hz1; cases hz1
  have hz' : (setZ h s.strm z').streams s.strm = some z' := setZ_streams_same _ _ _
  have hsW : w.gz (setZ h s.strm z') b = some s := hs
  have hB' : GzBufs (setZ h s.strm z') s c base := ⟨hB.size, hB.buffers, hB.inp, hB.out, hB.fits, hB.hdr⟩
  have hst : z'.state = z.state := by rw [he]
  have hno : z'.next_out = z.next_out ∧ z'.avail_out = z.avail_out := by rw [he]; exact ⟨rfl, rfl⟩
  have hWB' : GzWBuf (setZ h s.strm z') s c base z' := by
    refine ⟨fun hdir => ?_, fun sb st k e1 e2 => WB.nohdr sb st k (hst ▸ e1) e2, hinp c base hB,
      fun e => hst ▸ WB.nostate e, fun e => hno.1 ▸ hno.2 ▸ WB.out e⟩
    obtain ⟨hd, hsd⟩ := WB.deflate hdir
    obtain ⟨i, z0, sb, st, al, e, hz0, hsb, hst0, hal, core⟩ := hd
    cases e
    rw [hz] at hz0; cases hz0
    have hc : DCallerStep h (setZ h s.strm z') (some s.strm) := by
      refine ⟨s.strm, z, z', sb, st, rfl, hz, hz', hsb, hst0, ?_, rfl, rfl, rfl,
        fun k g hk' _ => absurd hk' (WB.nohdr sb st k hsb hst0), rfl, Nat.le_refl _⟩
      rw [he]
    exact ⟨DeflateReach.caller_inv ⟨s.strm, z, sb, st, al, rfl, hz, hsb, hst0, hal, core⟩ hc,
      DeflateSide.caller_side hsd hc⟩
  have hstB : stBlk (setZ h s.strm z') s = stBlk h s := by simp [stBlk, hz, hst]
  have hown' : ownL (setZ h s.strm z') b s = ownL h b s := by simp only [ownL, hstB]
  have shape : GzShape (setZ h s.strm z') s := by
    refine ⟨sh.mode, sh.path, ⟨_, hz'⟩, sh.want_lo, sh.want_hi, sh.size, sh.pos, ⟨sh.msg.1, sh.msg.2⟩,
      fun hr => absurd (hwm.symm.trans hr) write_ne_read,
      fun _ => ⟨fun _ => ⟨c, base, z', hB', hz', hWB'⟩, fun e => absurd e hsz, (sh.write hwm).have0⟩,
      fun e => absurd e hsz⟩
  have wf : GzWFw w (setZ h s.strm z') := by
    refine ⟨hwf.1, hwf.2.1, hwf.2.2.1, fun x s2 hx => ?_, hwf.lit⟩
    obtain ⟨z5, hz5⟩ := hwf.2.2.2.1 x s2 hx
    by_cases e5 : s2.strm = s.strm
    · rw [e5]; exact ⟨_, hz'⟩
    · exact ⟨z5, by rw [setZ_streams_ne _ _ e5]; exact hz5⟩
  refine ⟨⟨⟨b, s, rfl, hsW, shape, by rw [hown']; exact hn⟩, ⟨b, s, rfl, hsW, hwm⟩, wf⟩, hsW, ?_⟩
  refine gstep_mk' hs hsW rfl (fun _ _ _ => rfl) (fun i hi => setZ_streams_ne _ _ hi) (fun _ => rfl)
    (fun _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩) (fun _ _ e => e) rfl rfl rfl (Nat.le_refl _) (fun x hx _ => ?_)
  simp only [GzOwned, hsW, hs, hz', hz, hst] at hx ⊢; exact hx

/-- **The input fields of a write handle with buffers** change to fields that `GzWBuf.inp` allows: the invariant
holds, and it is a step of the file. -/
theorem invWS_setIn {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvWS w h (some b))
    (hs : w.gz h b = some s) (hsz : s.size ≠ 0) {z : ZStream} (hz : h.streams s.strm = some z) (p : BPtr)
    (n : UInt32) (hinp : ∀ c base, GzBufs h s c base → InpOk s c base p n) :
    GzInvWS w (setZ h s.strm { z with next_in := p, avail_in := n }) (some b) ∧
      w.gz (setZ h s.strm { z with next_in := p, avail_in := n }) b = some s ∧
      GStep w h w (setZ h s.strm { z with next_in := p, avail_in := n }) b [] :=
  invWS_setZ hv hs hsz hz _ rfl hinp

/-- The flat heap of a write handle with buffers keeps its invariant. -/
theorem invWS_flat {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvWS w h (some b))
    (hs : w.gz h b = some s) (hsz : s.size ≠ 0) {z : ZStream} (hz : h.streams s.strm = some z) :
    GzInvWS w (setZ h s.strm (flatZ z)) (some b) ∧ GStep w h w (setZ h s.strm (flatZ z)) b [] := by
  obtain ⟨v, -, g⟩ := invWS_setIn hv hs hsz hz .null 0 fun _ _ _ => Or.inr ⟨rfl, Or.inr rfl⟩
  exact ⟨v, g⟩

/-- Back from the flat heap: the actual input fields satisfy `GzWBuf.inp`. -/
theorem invWS_unflat {w : World} {h : Heap} {b : Nat} {s : GzState} {z : ZStream} (hz : h.streams s.strm = some z)
    (hv : GzInvWS w (setZ h s.strm (flatZ z)) (some b)) (hs : w.gz h b = some s) (hsz : s.size ≠ 0)
    (hinp : ∀ c base, GzBufs h s c base → InpOk s c base z.next_in z.avail_in) :
    GzInvWS w h (some b) ∧ GStep w (setZ h s.strm (flatZ z)) w h b [] := by
  have e : setZ (setZ h s.strm (flatZ z)) s.strm { (flatZ z) with next_in := z.next_in, avail_in := z.avail_in } = h := by
    rw [setZ_setZ]; exact setZ_self hz
  obtain ⟨v, -, g⟩ := invWS_setIn hv hs hsz (setZ_streams_same _ _ _) z.next_in z.avail_in
    fun c base hb => hinp c base ⟨hb.size, hb.buffers, hb.inp, hb.out, hb.fits, hb.hdr⟩
  rw [e] at v g
  exact ⟨v, g⟩

/-! ## The input of `gz_comp`: in `in`, or a caller range -/

/-- A caller range for the input of the stream `z` of file `b`: readable, outside the file's blocks. -/
def CallerIn (w : World) (h : Heap) (b : Nat) (z : ZStream) : Prop :=
  ReadSlice h z.next_in z.avail_in.toNat ∧ OutsideGz w h (some b) z.next_in

/-- Input fields `p`, `n` anywhere inside the `in` region (`2 size` bytes, which `gzvprintf` fills), or no input as
`GzWBuf.inp` allows it. -/
def InpW (s : GzState) (c base : Nat) (p : BPtr) (n : UInt32) : Prop :=
  Inside c base 0 (inSize s) p n.toNat ∨ (n = 0 ∧ (s.direct ≠ 0 ∨ p = .null))

/-- Where the input of the stream `z` of a write handle `s` with buffers may be: inside the `in` region, or a caller
range. -/
def InX (w : World) (h : Heap) (b : Nat) (s : GzState) (z : ZStream) : Prop :=
  (∃ c base, s.buffers = .val (.ref (.heap c) base) ∧ InpW s c base z.next_in z.avail_in) ∨ CallerIn w h b z

/-- The input that `GzWBuf.inp` allows is inside the `in` region. -/
theorem inpW_of_ok {s : GzState} {c base : Nat} (hw : s.mode = GZ_WRITE) (hsz : s.size = s.want) {p : BPtr}
    {n : UInt32} (hi : InpOk s c base p n) : InpW s c base p n := by
  have : inSize s = 2 * s.want.toNat := by simp [inSize, hw]
  rcases hi with ⟨k, e, h1, h2⟩ | e
  · exact Or.inl ⟨k, e, h1, by rw [this]; rw [hsz] at h2; omega⟩
  · exact Or.inr e

/-- **A write handle with buffers whose input is in `in` or in a caller range**: the invariant holds of the flat
heap (`flatZ`), and the input is described by `InX`. -/
def GzWX (w : World) (h : Heap) (b : Nat) (s : GzState) (z : ZStream) : Prop :=
  w.gz h b = some s ∧ h.streams s.strm = some z ∧ s.size ≠ 0 ∧
    GzInvWS w (setZ h s.strm (flatZ z)) (some b) ∧ InX w h b s z

theorem gzOwned_setZ (w : World) (h : Heap) (b : Nat) {s : GzState} (hs : w.gz h b = some s) {z z' : ZStream}
    (hz : h.streams s.strm = some z) (hst : z'.state = z.state) :
    GzOwned w (setZ h s.strm z') (some b) = GzOwned w h (some b) := by
  have hs' : w.gz (setZ h s.strm z') b = some s := hs
  simp [GzOwned, hs, hs', hz, hst]

/-- `GzWX` of a write handle with the invariant and buffers. -/
theorem wx_of_inv {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvWS w h (some b))
    (hs : w.gz h b = some s) (hsz : s.size ≠ 0) : ∃ z, GzWX w h b s z ∧ GStep w h w (setZ h s.strm (flatZ z)) b [] := by
  have hwm := modeOf hs hv.2.1
  obtain ⟨sh, -⟩ := inv_of hs hv.1
  obtain ⟨c, base, z, hB, hz, WB⟩ := (sh.write hwm).bufs hsz
  obtain ⟨v, g⟩ := invWS_flat hv hs hsz hz
  refine ⟨z, ⟨hs, hz, hsz, v, Or.inl ⟨c, base, hB.buffers, inpW_of_ok hwm hB.size ?_⟩⟩, g⟩
  rcases WB.inp with e | ⟨e1, e2⟩
  · exact Or.inl e
  · exact Or.inr ⟨e1, e2⟩

/-- Back from `GzWX` when the input is not a caller range. -/
theorem inv_of_wx {w : World} {h : Heap} {b : Nat} {s : GzState} {z : ZStream} (hx : GzWX w h b s z)
    (hin : ∃ c base, s.buffers = .val (.ref (.heap c) base) ∧ InpOk s c base z.next_in z.avail_in) :
    GzInvWS w h (some b) ∧ GStep w (setZ h s.strm (flatZ z)) w h b [] := by
  obtain ⟨hs, hz, hsz, hv, -⟩ := hx
  obtain ⟨c, base, eb, hi⟩ := hin
  refine invWS_unflat hz hv hs hsz fun c' base' hb => ?_
  rw [hb.buffers] at eb; cases eb; exact hi

/-- A caller range stays one across a step of the file (between flat heaps, which have the bytes and the owned
blocks of the actual heaps). -/
theorem callerIn_step {w W : World} {h H : Heap} {b : Nat} {i : Nat} {zf zf' : ZStream}
    (g : GStep w (setZ h i zf) W (setZ H i zf') b []) (hfr : FreshBlocks h)
    (hown : GzOwned w (setZ h i zf) (some b) = GzOwned w h (some b))
    (hown' : GzOwned W (setZ H i zf') (some b) = GzOwned W H (some b))
    {z z' : ZStream} (hc : CallerIn w h b z) (hp : z'.next_in = z.next_in ∨ ∃ r o k, z.next_in = .ref r o ∧
      z'.next_in = .ref r (o + k) ∧ k + z'.avail_in.toNat ≤ z.avail_in.toNat)
    (hn : z'.next_in = z.next_in → z'.avail_in.toNat ≤ z.avail_in.toNat) : CallerIn W H b z' := by
  obtain ⟨⟨r, off, d, ep, hd, hle⟩, ho⟩ := hc
  obtain ⟨⟨⟨fr, fd⟩, fc, -⟩, own, -⟩ := g
  have hget : Space.get H r = some d := by
    cases r with
    | heap c =>
      have hcl : c < h.nextBlk := live_lt hfr ⟨d, hd⟩
      have hno : c ∉ GzOwned w (setZ h i zf) (some b) := by
        rw [hown]; intro m; exact ho c m off ep
      have := frame_bytes_eq fr hcl hno
      show H.bytes c = some d
      have e2 : (setZ H i zf').bytes c = (setZ h i zf).bytes c := this
      exact e2.trans hd
    | const k => exact fc k d hd
    | str k => exact hd
  have hout : OutsideGz W H (some b) z'.next_in := by
    intro c hc off e
    rw [← hown'] at hc
    by_cases hlt : c < h.nextBlk
    · have m := own c hc hlt
      rw [hown] at m
      rcases hp with e1 | ⟨r1, o1, k, e1, e2, -⟩
      · rw [e1] at e; exact ho c m off e
      · rw [e2] at e; cases e; rw [ep] at e1; cases e1; exact ho c m off ep
    · rcases hp with e1 | ⟨r1, o1, k, e1, e2, -⟩
      · rw [e1, ep] at e; cases e; exact hlt (live_lt hfr ⟨d, hd⟩)
      · rw [e2] at e; cases e; rw [ep] at e1; cases e1; exact hlt (live_lt hfr ⟨d, hd⟩)
  refine ⟨?_, hout⟩
  rcases hp with e1 | ⟨r1, o1, k, e1, e2, hk⟩
  · exact ⟨r, off, d, by rw [e1, ep], hget, by have := hn e1; omega⟩
  · rw [ep] at e1; cases e1
    exact ⟨r, off + k, d, e2, hget, by omega⟩

end ZlibNgF.Proof.GzWrite
