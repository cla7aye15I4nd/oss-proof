import ZlibNgF.Proof.«gzwrite.c.init»

/-!
# The deflate calls of the write side, and `gz_comp` (`ZlibNgF`)

`invWS_dcall`: a call of the deflate stream of a write handle with buffers (not direct) that keeps the frame of the
stream (its record, its state block, and writes into the buffer block only), the deflate invariant and `DSide`,
`DKeep`, and leaves the buffer pointers where `GzWBuf` wants them, keeps the invariant of the handle and is a step
of the file. From it: `deflate_stepW` (`deflate`, given `DPending` and the `deflate` clause of `DeflateGz`) and
`reset_stepW` (`deflateReset`). `streamIO_W`: the buffers of the stream are valid for `deflate`. `writeG_ok`: `write`
of a readable range; `gz_error_strW`: `gz_error(state, Z_ERRNO, strerror(errno))`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace ZlibNgF.Proof.GzWrite
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Gz ZlibNgF.Proof.GzInv ZlibNgF.Proof.GzSat ZlibNgF.Proof.GzMode
open ZlibNgF.Proof.GzWriteNeeds

/-- A block older than `h` that is not a library block and that no write range points into keeps its bytes. -/
theorem frame_bytes_eq' {h h' : Heap} {S L G : List Nat} {wr : List (BPtr × Nat)} (f : Frame h h' S L G wr)
    {c : Nat} (hc : c < h.nextBlk) (hL : c ∉ L) (hw : ∀ x ∈ wr, ∀ off, x.1 ≠ .ref (.heap c) off) :
    h'.bytes c = h.bytes c := by
  obtain ⟨-, -, -, hb, hn, -⟩ := f
  cases e : h.bytes c with
  | none => exact hn c hc hL e
  | some d =>
    obtain ⟨d', e', hsz, hq⟩ := hb c hc hL d e
    rw [e']; congr 1
    apply Array.ext hsz
    intro j h1 h2
    have := hq j h2 (fun x hx off ho => absurd ho (hw x hx off))
    rwa [getElem!_pos d' j h1, getElem!_pos d j h2] at this

/-- A deflate call of a write handle with buffers keeps the invariant (see the module comment). -/
theorem invWS_dcall {W : World} {H H' : Heap} {b : Nat} {s : GzState} (hv : GzInvWS W H (some b))
    (hs : W.gz H b = some s) (hsz : s.size ≠ 0) (hd : s.direct = 0) {c base : Nat} {z : ZStream}
    (hB : GzBufs H s c base) (hz : H.streams s.strm = some z) {sb : Nat} (hsb : z.state = some sb)
    {wr : List (BPtr × Nat)} (f : DFrame H H' [s.strm] [sb] [] wr)
    (hwr : ∀ x ∈ wr, ∀ c' off, x.1 = .ref (.heap c') off → c' = c)
    {z' : ZStream} (hz' : H'.streams s.strm = some z') (hst' : z'.state = z.state)
    (hinp : Inside c base 0 s.size.toNat z'.next_in z'.avail_in.toNat ∨ (z'.avail_in = 0 ∧ z'.next_in = .null))
    (hout : ∃ ko kx, z'.next_out = .ref (.heap c) (base + inSize s + ko) ∧
      s.next = .val (.ref (.heap c) (base + inSize s + kx)) ∧ kx ≤ ko ∧ ko + z'.avail_out.toNat = s.size.toNat)
    (hk : DKeep H H' (some s.strm)) (hdi : DeflateInv.DInv H' (some s.strm) ∧ DeflateSide.DSide H' (some s.strm)) :
    GzInvWS W H' (some b) ∧ W.gz H' b = some s ∧ GStep W H W H' b [] := by
  have hwm := modeOf hs hv.2.1
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  have hwf := hv.2.2
  have fr : FreshBlocks H := hwf.2.1.1
  obtain ⟨db, hdb⟩ := gz_live hs
  have hbn : b < H.nextBlk := live_lt fr ⟨db, hdb⟩
  have hlt : ∀ x ∈ ownL H b s, x < H.nextBlk := fun x hx => live_lt fr (ownL_liveW sh hwm ⟨db, hdb⟩ x hx)
  have hcL : c ∈ ownL H b s := by simp [ownL, hsz, hB.buffers, blkOf]
  have hsbL : sb ∈ ownL H b s := by simp only [ownL, hsz, ite_false]; simp [stBlk, hz, hsb]
  obtain ⟨⟨fS, fG, fI, fB, fN, fC, fcrc, fx2n, fbase, fnext⟩, fD⟩ := f
  have hold : ∀ x, x < H.nextBlk → x ≠ sb → x ≠ c → H'.bytes x = H.bytes x := fun x hx h1 h2 =>
    frame_bytes_eq' ⟨fS, fG, fI, fB, fN, fC, fcrc, fx2n, fbase, fnext⟩ hx (by simpa using h1)
      (fun y hy off e => h2 (hwr y hy x off e))
  -- the file's own blocks other than the buffers and the state block
  have hsplit : ownL H b s = ([b] ++ blkOf s.path ++ blkOf s.msg) ++ [c, sb] := by
    simp [ownL, hsz, hB.buffers, blkOf, stBlk, hz, hsb]
  obtain ⟨-, hn2, hdis⟩ := List.nodup_append.mp (hsplit ▸ hn)
  have hcs : c ≠ sb := by simp at hn2; exact hn2
  have hne : ∀ x ∈ [b] ++ blkOf s.path ++ blkOf s.msg, x ≠ sb ∧ x ≠ c := fun x hx =>
    ⟨hdis x hx sb (by simp), hdis x hx c (by simp)⟩
  have hkeep : ∀ x ∈ [b] ++ blkOf s.path ++ blkOf s.msg, H'.bytes x = H.bytes x := fun x hx =>
    hold x (hlt x (by rw [hsplit]; exact List.mem_append_left _ hx)) (hne x hx).1 (hne x hx).2
  have hbW : W.gz H' b = some s := by
    unfold World.gz at hs ⊢; rw [hkeep b (by simp)]; exact hs
  obtain ⟨c1, base1, z1, hB1, hz1, WB1⟩ := (sh.write hwm).bufs hsz
  rw [hz] at hz1; cases hz1
  have hB' : GzBufs H' s c base := by
    obtain ⟨d, hd, hds⟩ := hB.fits
    obtain ⟨d', e', hsz', -⟩ := fB c (hlt c hcL) (by simpa using hcs) d hd
    refine ⟨hB.size, hB.buffers, hB.inp, hB.out, ⟨d', e', by rw [hsz']; exact hds⟩, hB.hdr.1, ?_⟩
    rw [hk.1 c (hlt c hcL) (fun z0 ⟨i0, e0, hz0⟩ e2 => by
      cases e0; rw [hz] at hz0; cases hz0; rw [hsb] at e2; cases e2; exact hcs rfl)]
    exact hB.hdr.2
  have hWB' : GzWBuf H' s c base z' := by
    refine ⟨fun _ => hdi, fun sb' st' k e1 e2 hk' => ?_, ?_, fun e => absurd hd e, fun _ => hout⟩
    · rcases hk.2.2 (some k) ⟨sb', st', ⟨⟨z', ⟨_, rfl, hz'⟩, e1⟩, e2⟩, hk'⟩ with e3 | e3
      · cases e3
      · obtain ⟨b0, st0, ⟨⟨z0, ⟨i0, e0, hz0⟩, hb0⟩, hst0⟩, hg0⟩ := e3
        cases e0; rw [hz] at hz0; cases hz0
        exact WB1.nohdr b0 st0 k hb0 hst0 hg0
    · rcases hinp with e1 | ⟨e1, e2⟩
      · exact Or.inl e1
      · exact Or.inr ⟨e1, Or.inr e2⟩
  have hown' : ownL H' b s = ownL H b s := by simp [ownL, stBlk, hz', hz, hst']
  have hpath : ∀ x ∈ blkOf s.path, H'.bytes x = H.bytes x := fun x hx => hkeep x (by simp [hx])
  have hmsg : ∀ x ∈ blkOf s.msg, H'.bytes x = H.bytes x := fun x hx => hkeep x (by simp [hx])
  have shape : GzShape H' s := by
    refine ⟨sh.mode, ownStr_keep sh.path hpath, ⟨_, hz'⟩, sh.want_lo, sh.want_hi, sh.size, sh.pos,
      ⟨?_, sh.msg.2⟩, fun hr => absurd (hwm.symm.trans hr) write_ne_read,
      fun _ => ⟨fun _ => ⟨c, base, z', hB', hz', hWB'⟩, fun e => absurd e hsz, (sh.write hwm).have0⟩,
      fun e => absurd e hsz⟩
    rcases sh.msg.1 with e1 | e1
    · exact Or.inl e1
    · exact Or.inr (ownBlk_keep e1 hmsg)
  have hcl : ∀ x, H.bytes x ≠ none → W.gz H x = W.gzs x := fun x hx => by
    unfold World.gz; cases e : H.bytes x with
    | none => exact absurd e hx
    | some _ => rfl
  have hliveC : H.bytes c ≠ none := by obtain ⟨d, hd, -⟩ := hB.fits; rw [hd]; simp
  have hliveS : H.bytes sb ≠ none := by
    obtain ⟨d, hd⟩ := ownL_liveW sh hwm ⟨db, hdb⟩ sb hsbL; rw [hd]; simp
  have wf : GzWFw W H' := by
    refine ⟨⟨by rw [fcrc]; exact hwf.1.1, by rw [fx2n]; exact hwf.1.2⟩, hk.2.1 hwf.2.1,
      fun x hx => hwf.2.2.1 x (Nat.le_trans fnext hx), fun x s2 hx => ?_,
      LitOk.ext hwf.lit rfl fun k a e => by rw [fC]; exact e⟩
    have h2 : W.gz H x = some s2 := by
      unfold World.gz at hx
      split at hx
      · next d hd =>
        by_cases hxl : x < H.nextBlk
        · by_cases h1 : x = sb
          · subst h1; rw [hcl _ hliveS]; exact hx
          · by_cases h3 : x = c
            · subst h3; rw [hcl _ hliveC]; exact hx
            · rw [hold x hxl h1 h3] at hd; unfold World.gz; rw [hd]; exact hx
        · rw [hwf.2.2.1 x (by omega)] at hx; cases hx
      · cases hx
    obtain ⟨z5, hz5⟩ := hwf.2.2.2.1 x s2 h2
    by_cases e5 : s2.strm = s.strm
    · rw [e5]; exact ⟨_, hz'⟩
    · exact ⟨z5, by rw [fS _ (by simpa using e5)]; exact hz5⟩
  refine ⟨⟨⟨b, s, rfl, hbW, shape, by rw [hown']; exact hn⟩, ⟨b, s, rfl, hbW, hwm⟩, wf⟩, hbW, ?_⟩
  refine gstep_mk' hs hbW rfl (fun _ _ _ => rfl) (fun i hi => fS i (by simpa using hi))
    (fun k => fG k (by simp)) (fun x hx hno => ?_) (fun k a e => by rw [fC]; exact e) fcrc fx2n fbase fnext
    (fun x hx _ => ?_)
  · have h1 : x ≠ sb := fun e => hno (ownL_owned hs x (e ▸ hsbL))
    have h3 : x ≠ c := fun e => hno (ownL_owned hs x (e ▸ hcL))
    have hxs : x ∉ [sb] := by simpa using h1
    exact ⟨hold x hx h1 h3, (fI x hx hxs).1, (fI x hx hxs).2, (fD x hx hxs).1, (fD x hx hxs).2⟩
  · simp only [GzOwned, hbW, hs, hz', hz, hst'] at hx ⊢; exact hx

/-- `write(fd, p, n)` of `n` readable bytes: no fault, only the file system changes. -/
theorem writeG_ok (W : World) (H : Heap) (fd : Int32) (p : BPtr) (n : UInt64)
    (hrd : n = 0 ∨ ∃ r off a, p = .ref r off ∧ Space.get H r = some a ∧ off + n.toNat ≤ a.size) :
    ∃ r fs', writeG fd p n W H = .ok ((r, { W with fs := fs' }), H) := by
  rcases hrd with rfl | ⟨r, off, a, rfl, ha, hle⟩
  · exact ⟨_, _, by simp [writeG, modifyFs]; exact ⟨rfl, rfl⟩⟩
  · by_cases hn : n = 0
    · subst hn; exact ⟨_, _, by simp [writeG, modifyFs]; exact ⟨rfl, rfl⟩⟩
    · exact ⟨_, _, by simp [writeG, modifyFs, hn, lm_app, loadBytes, ha, hle]; exact ⟨rfl, rfl⟩⟩

/-- A world that differs only in its file system has the same `gz_state` objects. -/
theorem invWS_fs {W : World} {H : Heap} {b : Nat} (hv : GzInvWS W H (some b)) (fs' : Fs) :
    GzInvWS { W with fs := fs' } H (some b) := hv

theorem gstep_fs {w W : World} {h H : Heap} {b : Nat} (g : GStep w h W H b []) (fs' : Fs) :
    GStep w h { W with fs := fs' } H b [] := by
  obtain ⟨⟨a, c, d⟩, o, t⟩ := g; exact ⟨⟨a, c, d⟩, o, t⟩

/-- `gz_error(state, Z_ERRNO, zstrerror())` on a write handle. -/
theorem gz_error_strW {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvWS w h (some b))
    (hs : w.gz h b = some s) {α : Type} (r : α) :
    GSat w h (do gz_error (some b) Z_ERRNO (← zstrerror); pure r)
      (fun r' W H => r' = r ∧ ErrPost w h b s Z_ERRNO W H) := by
  obtain ⟨p, a, e, hc, hk⟩ := zstrerror_spec w h
  refine GSat.bind ⟨p, w, _, e, ?_⟩
  have x := HExt.lit h a
  obtain ⟨hv1, hs1, st1⟩ := invWS_ext hv hs x rfl (LitOk.ext hv.2.2.lit rfl x.consts)
  refine GSat.bind (GSat.mono (gz_error_invW hv1 hs1 _ p (Or.inr hc) hk) fun _ W H q => ?_)
  obtain ⟨s', hs', he, hv', hf', st2⟩ := q
  exact GSat.pure ⟨rfl, s', hs', he, hv', hf', st1.trans st2 ⟨s, hs⟩ ⟨s, hs1⟩⟩

/-- The buffers of the deflate stream of a write handle with buffers are valid for `deflate`: the input inside the
`in` part, the output inside the `out` part of the buffer block, no header registered. -/
theorem streamIO_W {H : Heap} {s : GzState} {c base : Nat} {z : ZStream} (hB : GzBufs H s c base)
    (hz : H.streams s.strm = some z) (hwm : s.mode = GZ_WRITE) (hd : s.direct = 0) (WB : GzWBuf H s c base z)
    {sb : Nat} (hsb : z.state = some sb) (hcs : c ≠ sb) (hdi : DeflateInv.DInv H (some s.strm)) :
    DStreamIO H (some s.strm) := by
  obtain ⟨i, z0, sb0, st, al, e0, hz0, hsb0, hst, -, core⟩ := hdi
  cases e0; rw [hz] at hz0; cases hz0; rw [hsb] at hsb0; cases hsb0
  obtain ⟨hp, hhp⟩ := core.gzhead
  have hhp' : st.gzhead = .val hp := hhp
  have hnone : hp = none := by
    cases hp with
    | none => rfl
    | some k => exact absurd hhp' (WB.nohdr sb st k hsb hst)
  subst hnone
  obtain ⟨d, hd', hds⟩ := hB.fits
  have hin : inSize s = 2 * s.want.toNat := by simp [inSize, hwm]
  have hout : outSize s = s.want.toNat := by simp [outSize, hwm, hd]
  obtain ⟨ko, kx, eo, -, -, hko⟩ := WB.out hd
  refine ⟨z, sb, none, ⟨_, rfl, hz⟩, hsb, ⟨sb, st, ⟨⟨z, ⟨_, rfl, hz⟩, hsb⟩, hst⟩, hhp'⟩, ?_⟩
  refine ⟨fun k e => absurd e (by simp), ?_, ?_, ?_, fun r hr => ?_⟩
  · rcases WB.inp with ⟨k, ek, -, hk⟩ | ⟨e1, e2⟩
    · rw [hB.size] at hk; exact Or.inr ⟨.heap c, base + k, d, ek, hd', by rw [hin, hout] at hds; omega⟩
    · rcases e2 with e2 | e2
      · exact absurd hd e2
      · exact Or.inl e2
  · exact Or.inr ⟨c, _, d, eo, hd', by rw [hin, hout] at hds; rw [hB.size] at hko; omega⟩
  · intro off e; rw [eo] at e; cases e; exact hcs rfl
  · rcases hr with rfl | ⟨k, e, -⟩
    · refine ⟨?_, ?_⟩
      · rcases WB.inp with ⟨k, ek, -, hk⟩ | ⟨e1, e2⟩
        · rw [hB.size] at hk; simp only [eo, ek, Disjoint]; right; right; rw [hin]; omega
        · rcases e2 with e2 | e2
          · exact absurd hd e2
          · simp [eo, e2, Disjoint]
      · intro off e
        rcases WB.inp with ⟨k, ek, -, -⟩ | ⟨-, e2⟩
        · rw [ek] at e; cases e; exact hcs rfl
        · rcases e2 with e2 | e2
          · exact absurd hd e2
          · rw [e2] at e; cases e
    · cases e

/-- The `deflate` clause of `DeflateGz` for a potential `ψ` and growth `G`. -/
def DeflateClause (ψ : Int32 → C.DeflateState → Nat) (G : Nat) : Prop :=
  ∀ (h h' : Heap) (s : StreamPtr) (flush r : Int32), DeflateInv.DInv h s → DeflateSide.DSide h s → CrcGlobals h →
    DStreamIO h s → C.run (ZlibNg.Deflate.deflate s flush) h = .ok (r, h') →
    CallOk (ψ flush) G 5 h h' s ∧ DKeep h h' s ∧ (flush ≠ ZlibNg.Inflate.Z_FINISH → r ≠ ZlibNg.Inflate.Z_STREAM_ERROR →
      ∀ z', StreamAt h' s z' → z'.avail_in = 0 ∨ z'.avail_out = 0)

/-- The buffer positions of `GzWBuf` after a call that moves the buffer fields (`BufAdv`). -/
theorem wbuf_adv {s : GzState} {c base : Nat} {z z' : ZStream} (hd : s.direct = 0)
    (hinp : Inside c base 0 s.size.toNat z.next_in z.avail_in.toNat ∨ (z.avail_in = 0 ∧ (s.direct ≠ 0 ∨ z.next_in = .null)))
    (hout : ∃ ko kx, z.next_out = .ref (.heap c) (base + inSize s + ko) ∧
      s.next = .val (.ref (.heap c) (base + inSize s + kx)) ∧ kx ≤ ko ∧ ko + z.avail_out.toNat = s.size.toNat)
    (ha : BufAdv z z') :
    (Inside c base 0 s.size.toNat z'.next_in z'.avail_in.toNat ∨ (z'.avail_in = 0 ∧ z'.next_in = .null)) ∧
    (∃ ko kx, z'.next_out = .ref (.heap c) (base + inSize s + ko) ∧
      s.next = .val (.ref (.heap c) (base + inSize s + kx)) ∧ kx ≤ ko ∧ ko + z'.avail_out.toNat = s.size.toNat) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := ha
  have l1 := UInt32.le_iff_toNat_le.mp h1
  have l2 := UInt32.le_iff_toNat_le.mp h2
  refine ⟨?_, ?_⟩
  · rcases hinp with ⟨k, ek, -, hk⟩ | ⟨e1, e2⟩
    · rw [ek] at h3; simp only [Adv] at h3
      exact Or.inl ⟨k + (z.avail_in.toNat - z'.avail_in.toNat), by rw [h3]; congr 1; omega, by omega, by omega⟩
    · rcases e2 with e2 | e2
      · exact absurd hd e2
      · rw [e2] at h3; simp only [Adv] at h3
        refine Or.inr ⟨?_, h3.2⟩
        have : z'.avail_in.toNat = 0 := by rw [e1] at l1; simp at l1; omega
        exact UInt32.toNat_inj.mp (by simpa using this)
  · obtain ⟨ko, kx, eo, ex, hle, hk⟩ := hout
    rw [eo] at h4; simp only [Adv] at h4
    exact ⟨ko + (z.avail_out.toNat - z'.avail_out.toNat), kx, by rw [h4]; congr 1; omega, ex, by omega, by omega⟩

/-- **`deflate`** on the stream of a write handle with buffers (not direct): no fault, the buffer fields move
(`BufAdv`), the measure and progress facts of `DeflateGz`, and the invariant of the handle. -/
theorem deflate_stepW (P : DeflateReach.DPending) {ψ : Int32 → C.DeflateState → Nat} {G : Nat}
    (hD : DeflateClause ψ G)
    {W : World} {H : Heap} {b : Nat} {s : GzState} (hv : GzInvWS W H (some b)) (hs : W.gz H b = some s)
    (hsz : s.size ≠ 0) (hd : s.direct = 0) (flush : Int32) :
    ∃ r H' z z', ZlibNg.Deflate.deflate (some s.strm) flush H = .ok (r, H') ∧ H.streams s.strm = some z ∧
      H'.streams s.strm = some z' ∧ BufAdv z z' ∧
      (∀ sb st st', DStateOf H (some s.strm) sb st → DStateOf H' (some s.strm) sb st' →
        ψ flush st' + (z.avail_out.toNat - z'.avail_out.toNat) ≤
          ψ flush st + G * (z.avail_in.toNat - z'.avail_in.toNat) + (if z'.avail_out = 0 then 5 else 0)) ∧
      (flush ≠ ZlibNg.Inflate.Z_FINISH → r ≠ ZlibNg.Inflate.Z_STREAM_ERROR → z'.avail_in = 0 ∨ z'.avail_out = 0) ∧
      GzInvWS W H' (some b) ∧ W.gz H' b = some s ∧ GStep W H W H' b [] := by
  have hwm := modeOf hs hv.2.1
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  obtain ⟨c, base, z, hB, hz, WB⟩ := (sh.write hwm).bufs hsz
  obtain ⟨hdi, hside⟩ := WB.deflate hd
  have hdi0 := hdi
  obtain ⟨i, z0, sb, st, al, e0, hz0, hsb, hst, -, -⟩ := hdi0
  cases e0; rw [hz] at hz0; cases hz0
  have hcs : c ≠ sb := by
    have hsplit : ownL H b s = ([b] ++ blkOf s.path ++ blkOf s.msg) ++ [c, sb] := by
      simp [ownL, hsz, hB.buffers, blkOf, stBlk, hz, hsb]
    have := (List.nodup_append.mp (hsplit ▸ hn)).2.1
    simp at this; exact this
  have hio := streamIO_W hB hz hwm hd WB hsb hcs hdi
  obtain ⟨r, H', e, f, -, hdi', hside'⟩ := P.deflate H (some s.strm) flush hdi hside hv.2.2.1 hio
  obtain ⟨hco, hk, hdone⟩ := hD H H' (some s.strm) flush r hdi hside hv.2.2.1 hio e
  obtain ⟨z', ⟨i', e1, hz'⟩, hadv, hmu⟩ := hco z ⟨_, rfl, hz⟩
  cases e1
  have hsi : stateIds H (some s.strm) = [sb] := by simp [stateIds, hz, hsb]
  have hdo : dOutputRanges H (some s.strm) = [(z.next_out, z.avail_out.toNat)] := by simp [dOutputRanges, hz]
  rw [hsi, hdo] at f
  obtain ⟨ko, kx, eo, -, -, -⟩ := WB.out hd
  obtain ⟨hinp', hout'⟩ := wbuf_adv hd WB.inp (WB.out hd) hadv
  obtain ⟨hv', hs', g⟩ := invWS_dcall hv hs hsz hd hB hz hsb (by simpa [streamIds] using f)
    (fun x hx c' off e2 => by simp at hx; rw [hx, eo] at e2; cases e2; rfl) hz' hadv.2.2.2.2 hinp' hout' hk
    ⟨hdi', hside'⟩
  exact ⟨r, H', z, z', e, hz, hz', hadv, hmu, fun h1 h2 => hdone h1 h2 z' ⟨_, rfl, hz'⟩, hv', hs', g⟩

/-- **`deflateReset`** on the stream of a write handle with buffers (not direct): no fault, the buffer fields stay,
and the invariant of the handle. -/
theorem reset_stepW (G : DeflateGz) {W : World} {H : Heap} {b : Nat} {s : GzState} (hv : GzInvWS W H (some b))
    (hs : W.gz H b = some s) (hsz : s.size ≠ 0) (hd : s.direct = 0) :
    ∃ r H' z z', ZlibNg.Deflate.deflateReset (some s.strm) H = .ok (r, H') ∧ H.streams s.strm = some z ∧
      H'.streams s.strm = some z' ∧ BufSame z z' ∧
      GzInvWS W H' (some b) ∧ W.gz H' b = some s ∧ GStep W H W H' b [] := by
  have hwm := modeOf hs hv.2.1
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  obtain ⟨c, base, z, hB, hz, WB⟩ := (sh.write hwm).bufs hsz
  obtain ⟨hdi, -⟩ := WB.deflate hd
  obtain ⟨i, z0, sb, e0, hz0, hsb, r, H', e, -, hdi', f, hfo⟩ := DeflateReset.reset_inv hdi
  cases e0; rw [hz] at hz0; cases hz0
  obtain ⟨z', ⟨i', e1, hz'⟩, hsame, hk⟩ := G.2.1 H H' (some s.strm) r z hdi ⟨_, rfl, hz⟩ (by simpa [C.run] using e)
  cases e1
  obtain ⟨n1, n2, n3, n4, n5⟩ := hsame
  have hadv : BufAdv z z' := ⟨by rw [n2]; exact UInt32.le_refl _, by rw [n4]; exact UInt32.le_refl _,
    by rw [n1, n2]; cases z.next_in <;> simp [Adv], by rw [n3, n4]; cases z.next_out <;> simp [Adv], n5⟩
  obtain ⟨hinp', hout'⟩ := wbuf_adv hd WB.inp (WB.out hd) hadv
  obtain ⟨hv', hs', g⟩ := invWS_dcall hv hs hsz hd hB hz hsb (by simpa [streamIds] using f)
    (fun x hx => by simp at hx) hz' n5 hinp' hout' hk ⟨hdi', DeflateSide.side_fresh hdi' hfo⟩
  exact ⟨r, H', z, z', e, hz, hz', ⟨n1, n2, n3, n4, n5⟩, hv', hs', g⟩

end ZlibNgF.Proof.GzWrite
