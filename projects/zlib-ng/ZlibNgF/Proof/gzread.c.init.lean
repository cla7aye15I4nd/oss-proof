import ZlibNgF.Proof.«gzread.c.look»

/-!
# `gz_read_init` on a read handle (`ZlibNgF`)

`gz_read_init` runs when a read handle has no buffers yet (`size == 0`). It allocates the buffers
(`gz_buffer_alloc`: one fresh block from `zng_alloc_aligned`) and calls `inflateInit2(strm, 31)` (one fresh block
for the inflate state). On success the handle has buffers and an inflate stream with the invariant; when an
allocation fails the buffers are freed (`gz_buffer_free`), the error is `Z_MEM_ERROR`, and the handle is again a
read handle without buffers.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace ZlibNgF.Proof.GzMode
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Gz ZlibNgF.Proof.GzInv ZlibNgF.Proof.GzSat

/-! ## Small facts -/

theorem strLit_ver (H : Heap) : strLitRef ZLIB_VERSION H = .ok (.ref (.str 0) 0, H) := by
  simp [strLitRef, ZLIB_VERSION, strTable, List.findIdx?_cons]

/-- `inflateInit2_(strm, MAX_WBITS + 16, ZLIB_VERSION, sizeof(z_stream))`: the version check passes. -/
theorem init2__ver (st : StreamPtr) (H : Heap) :
    ZlibNg.Inflate.inflateInit2_ st (ZlibNg.Inflate.MAX_WBITS + 16) (.ref (.str 0) 0) SIZEOF_Z_STREAM.toInt32 H =
      ZlibNg.Inflate.inflateInit2 st 31 H := by
  have e : ZlibNg.Inflate.CHECK_VER_STSIZE (.ref (.str 0) 0) SIZEOF_Z_STREAM.toInt32 H = .ok (false, H) := by
    simp [bind_app, strTable, ZlibNg.Inflate.CHECK_VER_STSIZE, index8, Ptr.index, Ptr.add, Ptr.load, Space.get,
      Heap.getBytes, SIZEOF_Z_STREAM]
    rfl
  simp only [ZlibNg.Inflate.inflateInit2_, bind_app, e]
  rfl

theorem GSat.congr {α : Type} {w w' : World} {h h' : Heap} {m m' : G α} {Q : α → World → Heap → Prop}
    (e : m w h = m' w' h') (q : GSat w' h' m' Q) : GSat w h m Q := by
  obtain ⟨r, W, H, e2, q⟩ := q
  exact ⟨r, W, H, by rw [e]; exact e2, q⟩

/-- `zng_alloc_aligned` when the allocation fails. -/
theorem alloc_aligned_fail {h : Heap} (size : UInt32) (hok : h.allocOk h.nalloc = false) :
    ZlibNg.Zutil.zng_alloc_aligned size 64 h = .ok (.null, { h with nalloc := h.nalloc + 1 }) := by
  simp [ZlibNg.Zutil.zng_alloc_aligned, bind_app, allocB, hok]

/-! ## `gz_buffer_alloc` when the allocation fails -/

theorem gz_buffer_alloc_fail {w : World} {h : Heap} {b : Nat} {s : GzState} (hs : w.gz h b = some s)
    (hr : s.mode = GZ_READ) (hok : h.allocOk h.nalloc = false) :
    gz_buffer_alloc (some b) w h =
      (do gz_error (some b) ZlibNg.Inflate.Z_MEM_ERROR (← gzLit "out of memory"); return (-1 : Int32))
        { w with gzs := upd w.gzs b (some (bfSt s)) } { h with nalloc := h.nalloc + 1 } := by
  obtain ⟨d, hd⟩ := gz_live hs
  have hsA : w.gz { h with nalloc := h.nalloc + 1 } b = some s := hs
  have hdA : ({ h with nalloc := h.nalloc + 1 } : Heap).bytes b = some d := hd
  simp [gz_buffer_alloc, rdG_app' hs, hr, GZ_READ, GZ_WRITE, alloc_aligned_fail _ hok, wrG_app hsA,
    ldGz_upd hdA, wrG_upd hdA, rdG_upd hdA, Ival.get, liftM, monadLift, MonadLift.monadLift, gz_buffer_free,
    ZlibNg.Zutil.zng_free_aligned, InflateInv.upd_upd, bfSt]

/-! ## A read handle whose buffers were freed again -/

/-- `H` is `h` after blocks from `h.nextBlk` on were allocated and freed again, and the stream `i` changed. -/
structure FailH (h H : Heap) (i : Nat) : Prop where
  old : ∀ c, c < h.nextBlk → H.bytes c = h.bytes c
  new : ∀ c, h.nextBlk ≤ c → H.bytes c = none
  next : h.nextBlk ≤ H.nextBlk
  streams : ∀ j, j ≠ i → H.streams j = h.streams j
  istates : H.istates = h.istates
  iallocs : H.iallocs = h.iallocs
  dstates : H.dstates = h.dstates
  dallocs : H.dallocs = h.dallocs
  crc : H.crcTable = h.crcTable
  x2n : H.x2nTable = h.x2nTable
  base : H.baseAddr = h.baseAddr
  hdr : H.gzheaders = h.gzheaders
  consts : H.consts = h.consts

/-- A read handle without buffers stays one, with its buffer pointers cleared, on a heap where blocks were allocated
and freed again and the stream got other allocator fields (`inflateInit2` that failed). -/
theorem fail_inv {w : World} {h H : Heap} {b : Nat} {s : GzState} (hv : GzInvR w h (some b))
    (hs : w.gz h b = some s) (h0 : s.size = 0) (x : FailH h H s.strm) {z z' : ZStream}
    (hz : h.streams s.strm = some z) (hz' : H.streams s.strm = some z') (hst : z'.state = z.state)
    (hza : z'.zalloc = .null ∨ z'.zalloc = .zcalloc) (hzf : z'.zfree = .null ∨ z'.zfree = .zcfree)
    (hai : z'.avail_in = 0) :
    GzInvR { w with gzs := upd w.gzs b (some (bfSt s)) } H (some b) ∧
      GStep w h { w with gzs := upd w.gzs b (some (bfSt s)) } H b [] := by
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  have hr := modeOf hs hv.2.1
  have hw := hv.2.2
  have fr : FreshBlocks h := hw.2.1.1
  obtain ⟨db, hdb⟩ := gz_live hs
  have hlt : ∀ c ∈ ownL h b s, c < h.nextBlk := fun c hc => live_lt fr (ownL_live sh hr ⟨db, hdb⟩ c hc)
  have hbn : b < h.nextBlk := hlt b (by simp [ownL])
  have hdbH : H.bytes b = some db := by rw [x.old b hbn]; exact hdb
  have hsH : ({ w with gzs := upd w.gzs b (some (bfSt s)) } : World).gz H b = some (bfSt s) := by
    unfold World.gz; rw [hdbH]; simp
  have hst' : stBlk H (bfSt s) = stBlk h s := by simp [stBlk, bfSt, hz, hz', hst]
  have hL : ownL H b (bfSt s) = ownL h b s := by simp [ownL, bfSt, h0, blkOf]
  have hR := sh.read hr
  have shH : GzShape H (bfSt s) := by
    refine ⟨sh.mode, ownStr_keep sh.path fun c hc => x.old c (hlt c (by simp only [ownL, List.mem_append]; exact Or.inl (Or.inl (Or.inr hc)))),
      ⟨z', hz'⟩, sh.want_lo, sh.want_hi, Or.inl rfl, ⟨sh.pos.1, sh.pos.2, sh.pos.3, sh.pos.4⟩, ⟨?_, sh.msg.mem⟩,
      fun _ => ⟨hR.how, fun e => absurd rfl e, fun _ => hR.nobuf h0, hR.skip_have, fun _ => ⟨z', hz', hza, hzf, hai⟩, fun _ => hR.look h0,
        hR.pos_have, hR.look_pos, hR.gzip_direct,
        fun _ z2 hz2 => by have e := hz2.symm.trans hz'; cases e; exact hai⟩,
      fun hw' => absurd (hr.symm.trans hw') read_ne_write, fun _ c hc => ?_⟩
    · rcases sh.msg.msg with e | hm
      · exact Or.inl e
      · exact Or.inr (ownBlk_keep hm fun c hc => x.old c (hlt c (by simp only [ownL, List.mem_append]; exact Or.inl (Or.inr hc))))
    · have hc' : c ∈ blkOf s.buffers ++ stBlk h s := by
        rw [← hst'] at *; simp only [bfSt, blkOf, List.nil_append] at hc; exact List.mem_append_right _ hc
      obtain ⟨e1, e2⟩ := sh.dead h0 c hc'
      exact ⟨by rw [x.old c e2]; exact e1, Nat.lt_of_lt_of_le e2 x.next⟩
  have hnH : (ownL H b (bfSt s)).Nodup := by rw [hL]; exact hn
  -- the well-formedness, through a heap with the larger block counter
  let h1 : Heap := { h with nextBlk := H.nextBlk, nalloc := H.nalloc }
  have x1 : HExt h h1 := ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl, x.next, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    fun _ _ e => e⟩
  have hgb : ∀ s', w.gzs b = some s' → s'.strm = s.strm := fun s' e => by rw [gzs_of hs] at e; cases e; rfl
  have hw1 : GzWFr w h1 := wfr_ext hw hs (fun _ _ => rfl) hgb (GzOpen.FsLe.refl _) x1 (LitOk.ext hw.lit rfl x1.consts)
  have hs1 : w.gz h1 b = some s := hs
  have hl : HLess h1 H := by
    refine ⟨fun c d e => ?_, fun j zj e => ?_, x.istates, x.iallocs, x.dstates, x.dallocs, x.crc, x.x2n, rfl, x.base,
      x.hdr, fun k a e => by rw [x.consts]; exact e⟩
    · by_cases hc : c < h.nextBlk
      · rw [x.old c hc] at e; exact e
      · rw [x.new c (by omega)] at e; cases e
    · by_cases hj : j = s.strm
      · subst hj; exact ⟨z', hz'⟩
      · rw [x.streams j hj]; exact ⟨zj, e⟩
  have wfH : GzWFr { w with gzs := upd w.gzs b (some (bfSt s)) } H :=
    wfr_step hw1 hs1 (fun c hc => by simp [upd_ne _ _ _ _ hc]) (fun s2 e2 => by simp at e2; rw [← e2]; rfl)
      (GzOpen.FsLe.refl _) hl (LitOk.ext hw.lit rfl hl.consts)
  refine ⟨⟨⟨b, bfSt s, rfl, hsH, shH, hnH⟩, ⟨b, bfSt s, rfl, hsH, hr⟩, wfH⟩, ?_⟩
  refine gstep_mk hs hsH rfl (fun c hc _ => by simp [upd_ne _ _ _ _ hc]) x.streams x.hdr
    (fun c hc _ => ⟨x.old c hc, by rw [x.istates], by rw [x.iallocs], by rw [x.dstates], by rw [x.dallocs]⟩)
    (fun k a e => by rw [x.consts]; exact e) x.crc x.x2n x.base x.next (fun c hc _ => ?_)
  have e1 : GzOwned { w with gzs := upd w.gzs b (some (bfSt s)) } H (some b) =
      [b] ++ blkOf s.path ++ blkOf s.msg ++ ([] : List Nat) ++ stBlk h s := by
    rw [← hst']; simp only [GzOwned, hsH]; rfl
  have e2 : GzOwned w h (some b) = [b] ++ blkOf s.path ++ blkOf s.msg ++ blkOf s.buffers ++ stBlk h s := by
    simp only [GzOwned, hs]; rfl
  rw [e1] at hc; rw [e2]
  simp only [List.mem_append, List.not_mem_nil, or_false] at hc ⊢
  rcases hc with hc | hc
  · exact Or.inl (Or.inl hc)
  · exact Or.inr hc

/-! ## A read handle with new buffers and a new inflate state -/

/-- `H` is `h` with two new blocks `c0 = h.nextBlk` (the buffers) and `c0 + 1` (the inflate state), and the stream `i`
changed. -/
structure OkH (h H : Heap) (i c0 : Nat) : Prop where
  hc0 : c0 = h.nextBlk
  old : ∀ c, c < c0 → H.bytes c = h.bytes c ∧ H.istates c = h.istates c ∧ H.iallocs c = h.iallocs c
  new : ∀ c, c0 + 2 ≤ c → H.bytes c = h.bytes c ∧ H.istates c = h.istates c ∧ H.iallocs c = h.iallocs c
  next : H.nextBlk = c0 + 2
  streams : ∀ j, j ≠ i → H.streams j = h.streams j
  dstates : H.dstates = h.dstates
  dallocs : H.dallocs = h.dallocs
  crc : H.crcTable = h.crcTable
  x2n : H.x2nTable = h.x2nTable
  base : H.baseAddr = h.baseAddr
  hdr : H.gzheaders = h.gzheaders
  consts : H.consts = h.consts

theorem ok_inv {w : World} {h H : Heap} {b : Nat} {s : GzState} (hv : GzInvR w h (some b))
    (hs : w.gz h b = some s) (h0 : s.size = 0) {c0 o : Nat} (x : OkH h H s.strm c0)
    {a : Array UInt8} (ha : H.bytes c0 = some a) (has : a.size = 8 + 3 * s.want.toNat + 64)
    (ho : 8 ≤ o ∧ o < 72) (hsv : H.savedPtrs c0 = some (o - 8, .ref (.heap c0) 0))
    (hinv : InflateInv.Inv H (some s.strm)) {z' : ZStream} {st' : InflateState}
    (hz' : H.streams s.strm = some z') (hzs : z'.state = some (c0 + 1)) (hst' : H.istate (c0 + 1) = some st')
    (hhd : st'.head = .val none) (hai : z'.avail_in = 0) (hmsg : z'.msg = .null) :
    GzInvR { w with gzs := upd w.gzs b (some (baSt s c0 o)) } H (some b) ∧
      GStep w h { w with gzs := upd w.gzs b (some (baSt s c0 o)) } H b [] := by
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  have hr := modeOf hs hv.2.1
  have hw := hv.2.2
  have fr : FreshBlocks h := hw.2.1.1
  obtain ⟨db, hdb⟩ := gz_live hs
  have hlt : ∀ c ∈ ownL h b s, c < c0 := fun c hc => by
    rw [x.hc0]; exact live_lt fr (ownL_live sh hr ⟨db, hdb⟩ c hc)
  have hbn : b < c0 := hlt b (by simp [ownL])
  have hdbH : H.bytes b = some db := by rw [(x.old b hbn).1]; exact hdb
  let s3 := baSt s c0 o
  have hsH : ({ w with gzs := upd w.gzs b (some s3) } : World).gz H b = some s3 := by
    unfold World.gz; rw [hdbH]; simp
  have hR := sh.read hr
  have hwl := sh.want_lo
  have hwh := sh.want_hi
  have hsz : s3.size ≠ 0 := by
    show s.want ≠ 0; intro e; rw [e] at hwl; simp at hwl
  have hin : inSize s3 = s.want.toNat := by simp [inSize, s3, baSt, hr, read_ne_write]
  have hout : outSize s3 = 2 * s.want.toNat := by simp [outSize, s3, baSt, hr, read_ne_write]
  have hB : GzBufs H s3 c0 o :=
    ⟨rfl, rfl, rfl, fun _ => by rw [hin]; rfl, ⟨a, ha, by rw [hin, hout, has]; omega⟩, ho.1, hsv⟩
  have hreg : ∀ hp, RegisteredHeader H (some s3.strm) hp → hp = none := by
    intro hp ⟨b', st, ⟨zz, ⟨i, e, hzz⟩, hsb⟩, hist, hh⟩
    cases e; change H.streams s.strm = some zz at hzz; rw [hz'] at hzz; cases hzz; rw [hzs] at hsb; cases hsb
    rw [hst'] at hist; cases hist; rw [hhd] at hh; cases hh; rfl
  have shH : GzShape H s3 := by
    refine ⟨sh.mode, ownStr_keep sh.path fun c hc => (x.old c (hlt c (by simp only [ownL, List.mem_append]; exact Or.inl (Or.inl (Or.inr hc))))).1,
      ⟨z', hz'⟩, sh.want_lo, sh.want_hi, Or.inr rfl, ⟨sh.pos.1, sh.pos.2, sh.pos.3, sh.pos.4⟩, ⟨?_, sh.msg.mem⟩,
      fun _ => ⟨hR.how, fun _ => ⟨c0, o, z', hB, hinv, hz', Or.inl (hR.nobuf h0), Or.inl hai, hreg, Or.inl hmsg⟩,
        fun e => absurd e hsz, hR.skip_have, fun e => absurd e hsz, fun e => absurd e hsz, hR.pos_have, hR.look_pos, hR.gzip_direct,
        fun _ z2 hz2 => by have e := hz2.symm.trans hz'; cases e; exact hai⟩,
      fun hw' => absurd (hr.symm.trans hw') read_ne_write, fun e => absurd e hsz⟩
    rcases sh.msg.msg with e | hm
    · exact Or.inl e
    · exact Or.inr (ownBlk_keep hm fun c hc => (x.old c (hlt c (by simp only [ownL, List.mem_append]; exact Or.inl (Or.inr hc)))).1)
  have hL0 : ownL h b s = [b] ++ blkOf s.path ++ blkOf s.msg := by simp [ownL, h0]
  have hL : ownL H b s3 = ownL h b s ++ [c0, c0 + 1] := by
    have hw0 : ¬ s.want = 0 := hsz
    rw [hL0]; simp [ownL, hw0, s3, baSt, blkOf, stBlk, hz', hzs]
  have hnH : (ownL H b s3).Nodup := by
    rw [hL, List.nodup_append]
    refine ⟨hn, by simp, fun p hp q hq => ?_⟩
    have := hlt p hp
    simp at hq; omega
  have hgb : ∀ s', w.gzs b = some s' → s'.strm = s.strm := fun s' e => by rw [gzs_of hs] at e; cases e; rfl
  obtain ⟨hc, ⟨hfr, hdf⟩, hgz, hstr, hbud, hnod, hlk, hlit⟩ := hw
  have wfH : GzWFr { w with gzs := upd w.gzs b (some s3) } H := by
    refine ⟨⟨by rw [x.crc]; exact hc.1, by rw [x.x2n]; exact hc.2⟩, ⟨fun c e => ?_, fun c e => ?_⟩, fun c e => ?_,
      fun c s2 e => ?_, hbud, hnod, hlk, LitOk.ext hlit rfl fun k a e => by rw [x.consts]; exact e⟩
    · rw [x.next] at e
      obtain ⟨e1, e2, e3⟩ := x.new c e
      have := hfr c (by rw [← x.hc0]; omega)
      exact ⟨by rw [e2]; exact this.1, by rw [e3]; exact this.2.1, by rw [e1]; exact this.2.2⟩
    · rw [x.next] at e; rw [x.dstates, x.dallocs]; exact hdf c (by rw [← x.hc0]; omega)
    · rw [x.next] at e
      have : c ≠ b := by omega
      simp only [upd_ne _ _ _ _ this]; exact hgz c (by rw [← x.hc0]; omega)
    · by_cases hcb : c = b
      · subst hcb; rw [hsH] at e; cases e; exact ⟨z', hz'⟩
      · unfold World.gz at e
        simp only [upd_ne _ _ _ _ hcb] at e
        split at e
        · next d hd =>
          have hc0 : c < c0 := by
            refine Nat.lt_of_not_le fun hle => ?_
            have := hgz c (by rw [← x.hc0]; exact hle); rw [this] at e; cases e
          obtain ⟨z0, hz0⟩ := hstr c s2 (by unfold World.gz; rw [← (x.old c hc0).1, hd]; exact e)
          by_cases hj : s2.strm = s.strm
          · rw [hj]; exact ⟨z', hz'⟩
          · rw [x.streams _ hj]; exact ⟨z0, hz0⟩
        · cases e
  refine ⟨⟨⟨b, s3, rfl, hsH, shH, hnH⟩, ⟨b, s3, rfl, hsH, hr⟩, wfH⟩, ?_⟩
  refine gstep_mk hs hsH rfl (fun c hc _ => by simp [upd_ne _ _ _ _ hc]) x.streams x.hdr
    (fun c hc _ => ?_) (fun k a e => by rw [x.consts]; exact e) x.crc x.x2n x.base (by rw [x.next, x.hc0]; omega)
    (fun c hc hlt' => ?_)
  · have hc' : c < c0 := by rw [x.hc0]; exact hc
    obtain ⟨e1, e2, e3⟩ := x.old c hc'
    exact ⟨e1, e2, e3, by rw [x.dstates], by rw [x.dallocs]⟩
  · have e1 : GzOwned { w with gzs := upd w.gzs b (some s3) } H (some b) = ownL H b s3 := by
      simp only [GzOwned, hsH, ownL, hsz, ite_false, stBlk, List.append_assoc]; rfl
    have e2 : GzOwned w h (some b) = [b] ++ blkOf s.path ++ blkOf s.msg ++ blkOf s.buffers ++ stBlk h s := by
      simp only [GzOwned, hs]; rfl
    rw [e1, hL, hL0] at hc; rw [e2]
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    have := x.hc0
    rcases hc with hc | hc | hc
    · exact Or.inl (Or.inl hc)
    · omega
    · omega

/-! ## `gz_error` with a string literal -/

/-- A step that only adds static strings (and their keys) keeps a read handle and is a step of a call on it. -/
theorem ext_step {W W2 : World} {H H2 : Heap} {b : Nat} {s : GzState} (hv : GzInvR W H (some b))
    (hs : W.gz H b = some s) (hg : W2.gzs = W.gzs) (hf : W2.fs = W.fs) (x : HExt H H2) (hL : LitOk W2 H2) :
    W2.gz H2 b = some s ∧ GzInvR W2 H2 (some b) ∧ GStep W H W2 H2 b [] := by
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  have hr := modeOf hs hv.2.1
  have hw := hv.2.2
  have fr : FreshBlocks H := hw.2.1.1
  obtain ⟨db, hdb⟩ := gz_live hs
  have hlt : ∀ c ∈ ownL H b s, c < H.nextBlk := fun c hc => live_lt fr (ownL_live sh hr ⟨db, hdb⟩ c hc)
  have hbn : b < H.nextBlk := hlt b (by simp [ownL])
  obtain ⟨sh', e⟩ := shape_keep sh (HK_ext x s _ hlt)
  have hs2 : W2.gz H2 b = some s := by
    unfold World.gz at hs ⊢; rw [(x.old b hbn).1, hg]; exact hs
  have hgb : ∀ s', W2.gzs b = some s' → s'.strm = s.strm := fun s' e' => by
    rw [hg, gzs_of hs] at e'; cases e'; rfl
  refine ⟨hs2, ⟨⟨b, s, rfl, hs2, sh', by rw [e]; exact hn⟩, ⟨b, s, rfl, hs2, hr⟩,
    wfr_ext hw hs (fun c _ => by rw [hg]) hgb (by rw [hf]; exact GzOpen.FsLe.refl _) x hL⟩, ?_⟩
  refine gstep_mk hs hs2 rfl (fun c _ _ => by rw [hg]) (fun i _ => by rw [x.streams]) x.hdr
    (fun c hc _ => ⟨(x.old c hc).1, by rw [x.istates], by rw [x.iallocs], by rw [x.dstates], by rw [x.dallocs]⟩)
    x.consts x.crc x.x2n x.base x.next (fun c hc _ => ?_)
  simp only [GzOwned, hs2, hs, x.streams] at hc ⊢
  exact hc

/-- `gz_error(state, e, lit)` with a literal of the table on a read handle. -/
theorem err_lit {W : World} {H : Heap} {b : Nat} {s : GzState} (hv : GzInvR W H (some b))
    (hs : W.gz H b = some s) (e : Int32) (lit : String) (i : Nat) (hi : gzLits.findIdx? (· == lit) = some i)
    (hn : NoNul lit) :
    GSat W H (gzLit lit) (fun p W2 H2 => GSat W2 H2 (gz_error (some b) e p) (fun _ W' H' =>
      ∃ s', W'.gz H' b = some s' ∧ ErrOf s e s' ∧ GzInvR W' H' (some b) ∧ W'.fs = W.fs ∧ GStep W H W' H' b [])) := by
  refine GSat.mono (gzLit_spec lit i hi (GzReach.gzLits_of_idx hi) hn hv.2.2.lit) fun p W2 H2 q => ?_
  obtain ⟨hg, hf, x, hL, hcs, hmk⟩ := q
  obtain ⟨hs2, hv2, g2⟩ := ext_step hv hs hg hf x hL
  refine GSat.mono (gz_error_inv hv2 hs2 e p (Or.inr ⟨_, hcs⟩) hmk) fun _ W' H' q => ?_
  obtain ⟨s', h1, h2, h3, -, h5, h6⟩ := q
  exact ⟨s', h1, h2, h3, by rw [h5, hf], g2.trans h6 ⟨s, hs⟩ ⟨s, hs2⟩⟩

/-! ## `gz_buffer_free` of the buffers just made -/

theorem gz_buffer_free_app {W : World} {H : Heap} {b c base : Nat} {s : GzState} (hs : W.gz H b = some s)
    (hbuf : s.buffers = .val (.ref (.heap c) base)) {d : Array UInt8} (hd : H.bytes c = some d)
    (hbd : base ≤ d.size) (h8 : 8 ≤ base) (hsv : H.savedPtrs c = some (base - 8, .ref (.heap c) 0)) (hcb : c ≠ b) :
    gz_buffer_free (some b) W H = .ok (((), { W with gzs := upd W.gzs b (some (bfSt s)) }), freeH H c) := by
  obtain ⟨db, hdb⟩ := gz_live hs
  have hdbF : (freeH H c).bytes b = some db := by rw [freeH_bytes_ne (Ne.symm hcb)]; exact hdb
  have hs2 : W.gz (freeH H c) b = some s := by unfold World.gz at hs ⊢; rw [hdbF]; rw [hdb] at hs; exact hs
  simp [gz_buffer_free, ldGz_app hs, hbuf, Ival.get, liftM, monadLift, MonadLift.monadLift,
    free_aligned_app hd hbd h8 hsv, wrG_upd hdbF, wrG_app hs2, InflateInv.upd_upd, bfSt]

section Init
open ZlibNgF.Proof.InflateAlloc ZlibNgF.Proof.InflateReset ZlibNg.Inflate
open ZlibNgF.Proof.InflateInv (Live setZS upd_upd)

/-- The heap after a successful `inflateInit2(strm, 31)`: the allocation of `alloc_inflate`, the stream and the new
state. -/
theorem init2_31_eq {h : Heap} {i : Nat} {z : ZStream} (hz : h.streams i = some z)
    (hza : z.zalloc = .null ∨ z.zalloc = .zcalloc) (hzf : z.zfree = .null ∨ z.zfree = .zcfree)
    (hfs : h.istates h.nextBlk = none) (hfa : h.iallocs h.nextBlk = none) (hok : h.allocOk h.nalloc = true) :
    ∃ z' st', z'.msg = .null ∧ inflateInit2 (some i) 31 h = .ok (Z_OK,
      setZS (allocHeap { h with streams := upd h.streams i (some (initZ z)) } .zcfree) i z' h.nextBlk st') := by
  rw [init2_pre hz hza hzf 31]
  have hza0 : (({ h with streams := upd h.streams i (some (initZ z)) } : Heap).streams i).map ZStream.zalloc =
      some .zcalloc := by simp [initZ]
  simp only [bind_app, alloc_ok hza0 hfs hfa hok]
  let H0 : Heap := { h with streams := upd h.streams i (some (initZ z)) }
  let b := h.nextBlk
  let p := (PADSZ (h.baseAddr (.heap b)) 64).toNat
  let z2 : ZStream := { initZ z with state := some b }
  let st2 := initS (h.garbage (2 ^ 40 + b)) i b p
  let H2 := setZS (allocHeap H0 .zcfree) i z2 b st2
  have L2 : Live H2 i z2 b st2 := by
    refine ⟨by simp [H2, setZS], rfl, ⟨allocBytes H0, by simp [H2, setZS, H0, b]⟩, by simp [H2, setZS],
      by simp [z2, initZ], by simp [z2, initZ], ⟨b, rfl⟩, rfl, by show HEAD ≤ HEAD; decide, by show HEAD ≤ SYNC; decide⟩
  obtain ⟨wrap, wb', -, eR⟩ := (reset2_run L2 31).resolve_left fun e => by
    obtain ⟨H, eH⟩ := reset2_31 L2
    rw [eH] at e; simp [Z_OK, Z_STREAM_ERROR] at e
  refine ⟨rkZ z2 wrap, rkS b (rS (r2S st2 wrap wb')), rfl, ?_⟩
  simp [-Nat.reducePow, H2, setZS, z2, st2, initS, H0, b, p, upd_upd, initZ] at eR
  simp [-Nat.reducePow, ldAllocs, Heap.iallocsOf, Ival.get, wrS, ldState, stState, Heap.istate, wrZ, ldStream,
    stStream, upd_upd, initZ, eR, Z_OK, setZS, z2, st2, initS, b, p, H0]

end Init

/-! ## `gz_read_init` -/

/-- `s'` is `s` with other buffers, error and message. -/
def SameBut (s s' : GzState) : Prop :=
  s' = { s with size := s'.size, buffers := s'.buffers, «in» := s'.«in», out := s'.out, err := s'.err, msg := s'.msg }

theorem sameBut_err {s s1 s2 : GzState} {e : Int32} (hhv : s.«have» = 0) (h1 : SameBut s s1) (h2 : ErrOf s1 e s2) :
    SameBut s s2 := by
  obtain ⟨q2, -⟩ := h2
  unfold SameBut at h1 ⊢
  rw [q2]; rw [h1]
  cases s; simp only at hhv; subst hhv
  simp [errSt]

/-- What `gz_read_init` leaves on a read handle without buffers: a read handle, a step of the call, the same file
system, and a state that differs from `s` at most in the buffers, the error and the message; with buffers on
success. -/
def InitPost (w : World) (h : Heap) (b : Nat) (s : GzState) (r : Int32) (W : World) (H : Heap) : Prop :=
  GzInvR W H (some b) ∧ GStep w h W H b [] ∧ W.fs = w.fs ∧
    ∃ s', W.gz H b = some s' ∧ SameBut s s' ∧ (r = 0 ∧ s'.size ≠ 0 ∧ s'.err = s.err ∨ r = -1) ∧
      (∀ z', H.streams s.strm = some z' → z'.avail_in = 0) ∧ (r = -1 → ¬(s'.err = ZlibNg.Inflate.Z_OK ∨ s'.err = ZlibNg.Inflate.Z_BUF_ERROR))

/-- A read handle without buffers has no input (`FreshStrm`). -/
theorem fresh_avail {W : World} {H : Heap} {b : Nat} {s : GzState} (hv : GzInvR W H (some b))
    (hs : W.gz H b = some s) (h0 : s.size = 0) : ∀ z', H.streams s.strm = some z' → z'.avail_in = 0 := by
  intro z' hz'
  obtain ⟨sh, -⟩ := inv_of hs hv.1
  obtain ⟨z, hz, -, -, ha⟩ := (sh.read (modeOf hs hv.2.1)).fresh h0
  rw [hz] at hz'; cases hz'; exact ha

set_option maxRecDepth 20000 in
open ZlibNgF.Proof.InflateAlloc (initZ allocHeap) in
/-- **`gz_read_init`** on a read handle without buffers. -/
theorem gz_read_init_spec {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvR w h (some b))
    (hs : w.gz h b = some s) (h0 : s.size = 0) : GSat w h (gz_read_init (some b)) (InitPost w h b s) := by
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  have hr := modeOf hs hv.2.1
  have hR := sh.read hr
  have hhv : s.«have» = 0 := hR.nobuf h0
  obtain ⟨z, hz, hza, hzf, hai⟩ := hR.fresh h0
  have fr : FreshBlocks h := hv.2.2.2.1.1
  obtain ⟨db, hdb⟩ := gz_live hs
  have hbn : b < h.nextBlk := live_lt fr ⟨db, hdb⟩
  -- the end of an error path: one more `gz_error` with "out of memory" may follow
  have tailErr : ∀ (W1 : World) (H1 : Heap) (s1 : GzState), GzInvR W1 H1 (some b) → W1.gz H1 b = some s1 →
      GStep w h W1 H1 b [] → W1.fs = w.fs → SameBut s s1 → s1.size = 0 →
      GSat W1 H1 (gzLit "out of memory") (fun p W2 H2 => GSat W2 H2 (gz_error (some b) ZlibNg.Inflate.Z_MEM_ERROR p)
        (fun _ W3 H3 => InitPost w h b s (-1) W3 H3)) := by
    intro W1 H1 s1 hv1 hs1 g1 hf1 hb1 hz1
    refine GSat.mono (err_lit hv1 hs1 ZlibNg.Inflate.Z_MEM_ERROR "out of memory" 0 GzReach.lit_oom (by decide))
      fun p W2 H2 q => GSat.mono q fun _ W3 H3 q3 => ?_
    obtain ⟨s3, hs3, he3, hv3, hf3, g3⟩ := q3
    have hsb := sameBut_err hhv hb1 he3
    have hz3 : s3.size = 0 := by rw [he3.1]; exact hz1
    have hst3 : s3.strm = s.strm := by rw [hsb]
    exact ⟨hv3, g1.trans g3 ⟨s, hs⟩ ⟨s1, hs1⟩, hf3.trans hf1, s3, hs3, hsb, Or.inr rfl,
      fun z' hz' => fresh_avail hv3 hs3 hz3 z' (by rw [hst3]; exact hz'),
      fun _ => by rcases he3.2 with e | e <;> rw [e] <;> decide⟩
  unfold gz_read_init
  refine GSat.bind ?_
  cases hok : h.allocOk h.nalloc
  · -- the buffers cannot be allocated
    have x : FailH h { h with nalloc := h.nalloc + 1 } s.strm :=
      ⟨fun _ _ => rfl, fun c hc => (fr c hc).2.2, Nat.le_refl _, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl⟩
    obtain ⟨hv1, g1⟩ := fail_inv hv hs h0 x hz hz rfl hza hzf hai
    have hsA : w.gz { h with nalloc := h.nalloc + 1 } b = some s := hs
    have hs1 := gz_upd_same hsA (bfSt s)
    refine GSat.congr (gz_buffer_alloc_fail hs hr hok) ?_
    refine GSat.bind (GSat.mono (err_lit hv1 hs1 ZlibNg.Inflate.Z_MEM_ERROR "out of memory" 0 GzReach.lit_oom
      (by decide)) fun p W2 H2 q => GSat.bind (GSat.mono q fun _ W3 H3 q3 => GSat.pure ?_))
    obtain ⟨s3, hs3, he3, hv3, hf3, g3⟩ := q3
    apply GSat.ite
    · intro _
      refine GSat.bind (GSat.mono (tailErr W3 H3 s3 hv3 hs3 (g1.trans g3 ⟨s, hs⟩ ⟨_, hs1⟩) hf3
        (sameBut_err hhv (show SameBut s (bfSt s) from rfl) he3) (by rw [he3.1]; rfl)) fun p W4 H4 q => GSat.bind (GSat.mono q fun _ W5 H5 q5 => GSat.pure q5))
    · intro hne; exact absurd (by decide) hne
  · -- the buffers are allocated
    have hlo := sh.want_lo
    have hwh := sh.want_hi
    have hfr0 := fr h.nextBlk (Nat.le_refl _)
    have hfr1 := fr (h.nextBlk + 1) (by omega)
    refine GSat.of_eq (gz_buffer_alloc_ok hs hr hlo hwh hfr0.2.2 hok) ?_
    have ho := alOff_bounds (h.baseAddr (.heap h.nextBlk))
    generalize alOff (h.baseAddr (.heap h.nextBlk)) = o at ho ⊢
    let c0 := h.nextBlk
    let n := 8 + 3 * s.want.toNat + 64
    let arr : Array UInt8 := Array.ofFn (n := n) fun i => Junk.of (h.garbage h.nalloc i.val)
    let H1 := alH h n o
    have hcb : c0 ≠ b := by omega
    have hbc : b ≠ h.nextBlk := by omega
    have hdb1 : H1.bytes b = some db := by simp [H1, alH, upd_ne _ _ _ _ hbc, hdb]
    have hsH1 : w.gz H1 b = some s := by unfold World.gz at hs ⊢; rw [hdb1]; rw [hdb] at hs; exact hs
    have hs1 := gz_upd_same hsH1 (baSt s c0 o)
    have hz1 : H1.streams s.strm = some z := hz
    have hfs1 : H1.istates H1.nextBlk = none := hfr1.1
    have hfa1 : H1.iallocs H1.nextBlk = none := hfr1.2.1
    apply GSat.ite
    · intro hc; exact absurd hc (by decide)
    intro _
    refine GSat.bind (GSat.of_eq (strmOf_app hs1) ?_)
    refine GSat.bind (GSat.lm ⟨_, H1, strLit_ver H1, ?_⟩)
    cases hok2 : h.allocOk (h.nalloc + 1)
    · -- `inflateInit2` cannot allocate its state
      have hok2' : H1.allocOk H1.nalloc = false := hok2
      have e := init2_31_fail hz1 hza hzf hok2'
      refine GSat.bind (GSat.lm ⟨_, _, by rw [init2__ver]; exact e, ?_⟩)
      apply GSat.ite
      · intro _
        let H1f : Heap := { H1 with streams := upd H1.streams s.strm (some (initZ z)), nalloc := H1.nalloc + 1 }
        have hdA : H1f.bytes c0 = some arr := by simp [H1f, H1, alH, arr, n, c0]
        have hsvA : H1f.savedPtrs c0 = some (o - 8, .ref (.heap c0) 0) := by simp [H1f, H1, alH, c0]
        have hsF : ({ w with gzs := upd w.gzs b (some (baSt s c0 o)) } : World).gz H1f b = some (baSt s c0 o) := hs1
        refine GSat.bind (GSat.of_eq (gz_buffer_free_app hsF rfl hdA (by simp [arr, n]; omega) ho.1 hsvA hcb) ?_)
        have x : FailH h (freeH H1f c0) s.strm := by
          refine ⟨fun c hc => ?_, fun c hc => ?_, by simp [freeH, H1f, H1, alH], fun j hj => ?_, rfl, rfl, rfl, rfl,
            rfl, rfl, rfl, rfl, rfl⟩
          · have hne : c ≠ h.nextBlk := by omega
            rw [freeH_bytes_ne hne]; simp [H1f, H1, alH, upd_ne _ _ _ _ hne]
          · by_cases hc0 : c = c0
            · rw [hc0]; exact freeH_bytes_eq _ _
            · have hne : c ≠ h.nextBlk := hc0
              rw [freeH_bytes_ne hc0]; simp [H1f, H1, alH, upd_ne _ _ _ _ hne]; exact (fr c hc).2.2
          · simp [freeH, H1f, H1, alH, upd_ne _ _ _ _ hj]
        obtain ⟨hv1, g1⟩ := fail_inv hv hs h0 x hz (z' := initZ z) (by simp [freeH, H1f])
          rfl (Or.inr rfl) (Or.inr rfl) hai
        have ew : ({ ({ w with gzs := upd w.gzs b (some (baSt s c0 o)) } : World) with
            gzs := upd (upd w.gzs b (some (baSt s c0 o))) b (some (bfSt (baSt s c0 o))) } : World) =
            { w with gzs := upd w.gzs b (some (bfSt s)) } := by
          simp only [InflateInv.upd_upd]; rfl
        rw [ew]
        have hsW : ({ w with gzs := upd w.gzs b (some (bfSt s)) } : World).gz (freeH H1f c0) b = some (bfSt s) :=
          by
            have : (freeH H1f c0).bytes b = some db := by rw [freeH_bytes_ne (Ne.symm hcb)]; exact hdb1
            unfold World.gz; rw [this]; simp
        refine GSat.bind ?_
        exact GSat.mono (tailErr _ _ _ hv1 hsW g1 rfl rfl rfl)
          fun p W2 H2 q => GSat.bind (GSat.mono q fun _ W3 H3 q3 => GSat.pure q3)
      · intro hne; exact absurd (by decide) hne
    · -- `inflateInit2` succeeds
      have hok2' : H1.allocOk H1.nalloc = true := hok2
      obtain ⟨z', st', hzm, e⟩ := init2_31_eq hz1 hza hzf hfs1 hfa1 hok2'
      obtain ⟨r, h', e', -, hinv, -, hhead, -⟩ := ZlibNgF.Proof.InflateAlloc.init2_ok hz1 hza hzf hfs1 hfa1 31
      rw [e] at e'
      obtain ⟨rfl, rfl⟩ : ZlibNg.Inflate.Z_OK = r ∧ _ = h' := by simpa using e'
      refine GSat.bind (GSat.lm ⟨_, _, by rw [init2__ver]; exact e, ?_⟩)
      apply GSat.ite
      · intro hc; exact absurd hc (by decide)
      intro _
      refine GSat.pure ?_
      obtain ⟨z2, st2, hz2, hzs2, hst2, hhd2, -, hai2⟩ := hhead rfl
      have x : OkH h (InflateInv.setZS (allocHeap { H1 with streams := upd H1.streams s.strm (some (initZ z)) } .zcfree)
          s.strm z' H1.nextBlk st') s.strm c0 := by
        refine ⟨rfl, fun c hc => ?_, fun c hc => ?_, ?_, fun j hj => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals try simp only [InflateInv.setZS, allocHeap, H1, alH, c0]
        · have h1 : c ≠ h.nextBlk + 1 := by omega
          have h2 : c ≠ h.nextBlk := by omega
          simp [InflateInv.setZS, allocHeap, H1, alH, upd_ne _ _ _ _ h1, upd_ne _ _ _ _ h2]
        · have h1 : c ≠ h.nextBlk + 1 := by omega
          have h2 : c ≠ h.nextBlk := by omega
          simp [InflateInv.setZS, allocHeap, H1, alH, upd_ne _ _ _ _ h1, upd_ne _ _ _ _ h2]
        · simp [InflateInv.setZS, allocHeap, H1, alH, upd_ne _ _ _ _ hj]
      have h1 : h.nextBlk ≠ h.nextBlk + 1 := by omega
      have ha : (InflateInv.setZS (allocHeap { H1 with streams := upd H1.streams s.strm (some (initZ z)) } .zcfree)
          s.strm z' H1.nextBlk st').bytes c0 = some arr := by
        simp [InflateInv.setZS, allocHeap, H1, alH, upd_ne _ _ _ _ h1, arr, n, c0]
      have hsv : (InflateInv.setZS (allocHeap { H1 with streams := upd H1.streams s.strm (some (initZ z)) } .zcfree)
          s.strm z' H1.nextBlk st').savedPtrs c0 = some (o - 8, .ref (.heap c0) 0) := by
        simp [InflateInv.setZS, allocHeap, H1, alH, upd_ne _ _ _ _ h1, c0]
      have hz2' : z2 = z' := by
        simp [InflateInv.setZS] at hz2; exact hz2.symm
      obtain ⟨hvI, gI⟩ := ok_inv hv hs h0 x ha (by simp [arr, n]) ho hsv (hinv rfl) hz2 hzs2 hst2 hhd2
        (by rw [hai2]; exact hai) (by rw [hz2']; exact hzm)
      refine ⟨hvI, gI, rfl, baSt s c0 o, ?_, rfl, Or.inl ⟨rfl, ?_, rfl⟩, fun z3 hz3 => ?_, fun e => absurd e (by decide)⟩
      · have hb2 : b ≠ h.nextBlk + 1 := by omega
        unfold World.gz
        simp [InflateInv.setZS, allocHeap, H1, alH, upd_ne _ _ _ _ hb2, upd_ne _ _ _ _ hbc, hdb]; rfl
      · show s.want ≠ 0; intro e0; rw [e0] at hlo; simp at hlo
      · have e3 : z3 = z2 := by
          have := hz2; simp only [InflateInv.setZS] at this hz3; rw [hz3] at this; exact Option.some.inj this
        rw [e3, hai2]; exact hai

end ZlibNgF.Proof.GzMode
