import ZlibNgF.Proof.«gzwrite.c.putc»

/-!
# `gzvprintf` and `gzprintf` (`ZlibNgF`)

`gzvprintf_spec`: on a write handle, with a format string outside the blocks of the file, `gzvprintf` keeps the
invariant `GzInvWS` and is a step of the file, given `GzCompSpec` and `DeflateGz`. With patch 0021 the input left in
`in` is moved to its start (`pf_norm`); the text goes into the `size` bytes after it (`vsn_spec`: `vsnprintf` writes
only there); with `size` bytes or more of input, `gz_comp` runs on the first `size` bytes, entered through `GzWX` (the
input may reach past the first `size` bytes of `in`), and the rest is moved to the start (`pf_comp`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace ZlibNgF.Proof.GzWrite
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Gz ZlibNgF.Proof.GzInv ZlibNgF.Proof.GzSat ZlibNgF.Proof.GzMode
open ZlibNgF.Proof.GzWriteNeeds

/-! ## Heap steps -/

theorem memmove_hbuf {H : Heap} {c od os n : Nat} {a : Array UInt8} (ha : H.bytes c = some a)
    (h1 : od + n ≤ a.size) (h2 : os + n ≤ a.size) :
    ∃ H', Ptr.memmove (Ptr.ref (BRef.heap c) od : BPtr) (Ptr.ref (BRef.heap c) os) n H = .ok ((), H') ∧
      HBuf H H' c od (od + n) := by
  refine ⟨{ H with bytes := upd H.bytes c (some (ZlibNgF.Proof.InflateDict.copyFold a od os (List.range' 0 n) a)) },
    ?_, ?_⟩
  · simp only [Ptr.memmove, ZlibNgF.Proof.InflateDict.space_get_heap, ha, h1, h2, and_self, ↓reduceIte]
    simp only [Space.ro, Heap.isRo, Bool.false_eq_true, ↓reduceIte, Space.modify, Heap.modifyBytes,
      Tbl.modify_opt _ c _ a ha]
    rw [ZlibNgF.Proof.InflateDict.memcpy_loop]
  · refine ⟨_, rfl, fun c' hc' => upd_ne _ _ _ _ hc', fun e => (by rw [ha] at e; cases e), fun a' ha' => ?_⟩
    rw [ha] at ha'; cases ha'
    exact ⟨_, upd_same _ _ _, ZlibNgF.Proof.InflateDict.copyFold_size _ _ _ _ _, fun j hj =>
      ZlibNgF.Proof.InflateDict.copyFold_get _ _ _ _ _ j (fun i hi => ChunkMem.mem_range'_bound hi hj)⟩

theorem storeBytes_hbuf {H : Heap} {c off cap : Nat} {a bs : Array UInt8} (ha : H.bytes c = some a)
    (hc : off + cap ≤ a.size) (hb : bs.size ≤ cap) :
    ∃ H', storeBytes (.ref (.heap c) off) bs cap H = .ok ((), H') ∧ HBuf H H' c off (off + cap) := by
  refine ⟨_, GzOpen.storeBytes_heap ha hc hb, ?_⟩
  refine ⟨_, rfl, fun c' hc' => ?_, fun e => (by rw [ha] at e; cases e), fun a' ha' => ?_⟩
  · rw [GzOpen.modify_some _ c a _ ha c']; simp [hc']
  · rw [ha] at ha'; cases ha'
    refine ⟨GzOpen.stored a bs off, by rw [GzOpen.modify_some _ c a _ ha c]; simp,
      GzOpen.stored_size a bs off (by omega), fun j hj => ?_⟩
    rw [GzOpen.stored_get a bs off (by omega)]
    have : ¬ (off ≤ j ∧ j < off + bs.size) := by omega
    simp [this]

/-- `vsnprintf` into `size` bytes of block `c`: a format string outside block `c`, the next oracle call, and only the
`size` bytes change. -/
theorem vsn_spec {W : World} {H : Heap} {c off : Nat} {a : Array UInt8} (ha : H.bytes c = some a) (size : UInt64)
    (hs : off + size.toNat ≤ a.size) {fmt : BPtr} {n : Nat} (hf : CStringLen H fmt n) :
    GSat W H (vsnprintfG (.ref (.heap c) off) size fmt) (fun r W' H' =>
      W' = { W with nprintf := W.nprintf + 1 } ∧ r = W.printfRet W.nprintf ∧ HBuf H H' c off (off + size.toNat)) := by
  obtain ⟨bs0, e0, -, -⟩ := GzOpen.strBytes_of hf
  unfold vsnprintfG
  refine GSat.bind (GSat.lm ⟨bs0, H, e0, ?_⟩)
  refine GSat.bind (GSat.of_eq (gget_app W H) ?_)
  refine GSat.bind (GSat.of_eq (gset_app _ W H) ?_)
  refine GSat.ite (fun hz => GSat.ite (fun _ => ?_) (fun _ => ?_)) (fun _ => GSat.pure ⟨rfl, rfl, HBuf.refl _ _ _ _⟩)
  · obtain ⟨H', e, x⟩ := storeBytes_hbuf (cap := size.toNat) ha hs (bs := ((W.printfOut W.nprintf).extract 0
      (min (W.printfRet W.nprintf).toNatClampNeg (size.toNat - 1)) ++ Array.replicate
      (min (W.printfRet W.nprintf).toNatClampNeg (size.toNat - 1) - min (min (W.printfRet W.nprintf).toNatClampNeg
      (size.toNat - 1)) (W.printfOut W.nprintf).size) 0).push 0) (by
        have : size.toNat ≠ 0 := fun e' => by simp at hz; exact hz (UInt64.toNat_inj.mp (by simpa using e'))
        simp; omega)
    exact GSat.bind (GSat.of_eq (by rw [lm_app, e]) (GSat.pure ⟨rfl, rfl, x⟩))
  · obtain ⟨H', e, x⟩ := storeBytes_hbuf (cap := size.toNat) ha hs
      (bs := (W.printfOut W.nprintf).extract 0 size.toNat) (by simp [Nat.min_le_left])
    exact GSat.bind (GSat.of_eq (by rw [lm_app, e]) (GSat.pure ⟨rfl, rfl, x⟩))

/-- `gz_error` with a literal of the table, then any continuation. -/
theorem err_cont (lit : String) (i : Nat) (hi : gzLits.findIdx? (· == lit) = some i) (hl : gzLits[i]? = some lit)
    (hn : NoNul lit) {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvWS w h (some b))
    (hs : w.gz h b = some s) (e : Int32) {α : Type} (k : G α) {Q : α → World → Heap → Prop}
    (hk : ∀ W H, ErrPost w h b s e W H → GSat W H k Q) :
    GSat w h (do gz_error (some b) e (← gzLit lit); k) Q := by
  refine GSat.bind (GSat.mono (gzLit_spec lit i hi hl hn hv.2.2.lit) fun p W1 H1 q => ?_)
  obtain ⟨hg, hf, x, hL, hc, hk'⟩ := q
  obtain ⟨hv1, hs1, st1⟩ := invWS_ext hv hs x hg hL
  refine GSat.bind (GSat.mono (gz_error_invW hv1 hs1 e p (Or.inr ⟨_, hc⟩) hk') fun _ W H q => ?_)
  obtain ⟨s', hs', he, hv', hf', st2⟩ := q
  exact hk W H ⟨s', hs', he, hv', by rw [hf', hf], st1.trans st2 ⟨s, hs⟩ ⟨s, hs1⟩⟩

/-- `return state->err` on a write handle. -/
theorem ret_err {w W : World} {h H : Heap} {b : Nat} {s : GzState} (hv : GzInvWS W H (some b))
    (hs : W.gz H b = some s) (g : GStep w h W H b []) :
    GSat W H (do return (← rdG (some b) (·.err))) (CallPost w h b) := by
  refine ⟨s.err, W, H, ?_, hv, g⟩
  simp [rdG_app' hs]

/-- A C string outside the file stays one across a step of the file. -/
theorem cstr_step {w W : World} {h H : Heap} {b : Nat} (g : GStep w h W H b []) (hfr : FreshBlocks h)
    {p : BPtr} {n : Nat} (hc : CStringLen h p n) (ho : OutsideGz w h (some b) p) :
    CStringLen H p n ∧ OutsideGz W H (some b) p := by
  obtain ⟨r, off, d, ep, hd, h1, h2, h3⟩ := hc
  have hr : ReadSlice h p 0 := ⟨r, off, d, ep, hd, by omega⟩
  obtain ⟨-, ho'⟩ := callerBuf_step g hfr hr ho
  obtain ⟨⟨⟨fr, fd⟩, fc, -⟩, -, -⟩ := g
  have hget : Space.get H r = some d := by
    cases r with
    | heap c =>
      have hcl : c < h.nextBlk := live_lt hfr ⟨d, hd⟩
      have hno : c ∉ GzOwned w h (some b) := fun m => ho c m off ep
      have e2 : ({ H with consts := h.consts } : Heap).bytes c = h.bytes c := frame_bytes_eq fr hcl hno
      exact e2.trans hd
    | const k => exact fc k d hd
    | str k => exact hd
  exact ⟨⟨r, off, d, ep, hget, h1, h2, h3⟩, ho'⟩

/-- A C string outside block `cb` stays one across stores into block `cb`. -/
theorem cstr_hbuf {H H' : Heap} {cb lo hi : Nat} (x : HBuf H H' cb lo hi) {p : BPtr} {n : Nat}
    (hc : CStringLen H p n) (hp : ∀ off, p ≠ .ref (.heap cb) off) : CStringLen H' p n := by
  obtain ⟨t, rfl, hne, -, -⟩ := x
  obtain ⟨r, off, d, ep, hd, h1, h2, h3⟩ := hc
  refine ⟨r, off, d, ep, ?_, h1, h2, h3⟩
  cases r with
  | heap c =>
    have : c ≠ cb := fun e => hp off (by rw [ep, e])
    show t c = some d; rw [hne c this]; exact hd
  | const k => exact hd
  | str k => exact hd

/-- The `vsnprintf` call counter is not part of a file. -/
theorem gstep_nprintf {W : World} {H : Heap} {b : Nat} {s : GzState} (hs : W.gz H b = some s) (k : Nat) :
    GStep W H { W with nprintf := k } H b [] :=
  gstep_mk hs hs rfl (fun _ _ _ => rfl) (fun _ _ => rfl) rfl (fun _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩)
    (fun _ _ e => e) rfl rfl rfl (Nat.le_refl _) (fun _ hc _ => hc)

theorem i32_toInt_of_u32 (x : Int32) (h : x.toUInt32.toNat < 2 ^ 31) : x.toInt = x.toUInt32.toNat := by
  have e := BitVec.toInt_eq_toNat_cond x.toBitVec
  have h2 : x.toInt = x.toBitVec.toInt := rfl
  have h3 : x.toUInt32.toNat = x.toBitVec.toNat := rfl
  split at e <;> omega

/-! ## After the text is formatted -/

open ZlibNg.Inflate (rdZ wrZ) in
/-- `gzvprintf` after a good `vsnprintf` (copied from the translation). -/
def pfLen (state : GzPtr) (strm : StreamPtr) (len : Int32) : G Int32 := do
  let room ← lm (chkI64 (GZ_OFF_MAX.toInt - (← rdG state (·.pos)).toInt))
  if len.toInt64 > room then
    gz_error state ZlibNg.Inflate.Z_DATA_ERROR (← (gzLit "write position does not fit in z_off64_t"))
    return (← rdG state (·.err))
  lm (wrZ strm fun z => { z with avail_in := z.avail_in + len.toUInt32 })
  let np ← lm (chkI64 ((← rdG state (·.pos)).toInt + len.toInt))
  wrG state fun st => { st with pos := np }
  if (← lm (rdZ strm (·.avail_in))) ≥ (← rdG state (·.size)) then
    let left := (← lm (rdZ strm (·.avail_in))) - (← rdG state (·.size))
    let sz ← rdG state (·.size)
    lm (wrZ strm fun z => { z with avail_in := sz })
    if (← gz_comp state ZlibNg.Deflate.Z_NO_FLUSH) == -1 then
      return (← rdG state (·.err))
    let i ← (← ldGz state).«in».get
    lm (Ptr.memmove i (← lm (i.add (Int.ofNat (← rdG state (·.size)).toNat))) left.toNat)
    let i ← (← ldGz state).«in».get
    lm (wrZ strm fun z => { z with next_in := i })
    lm (wrZ strm fun z => { z with avail_in := left })
  return len

/-- The input of `gz_comp` after it ran on `size` bytes from `in`: inside the first `size` bytes. -/
theorem comp_inp {s : GzState} {c base : Nat} {z z' : ZStream} (hk : z.next_in = .ref (.heap c) base)
    (ha : z'.avail_in ≤ z.avail_in)
    (hadv : s.direct = 0 → Adv z.next_in z'.next_in (z.avail_in.toNat - z'.avail_in.toNat))
    (hdir : s.direct ≠ 0 → z'.next_in = z.next_in) (he : z.avail_in.toNat = s.size.toNat) :
    InpOk s c base z'.next_in z'.avail_in := by
  have ha' := UInt32.le_iff_toNat_le.mp ha
  by_cases hd : s.direct = 0
  · have a := hadv hd
    rw [hk] at a
    simp only [Adv] at a
    exact Or.inl ⟨z.avail_in.toNat - z'.avail_in.toNat, a, Nat.zero_le _, by omega⟩
  · exact Or.inl ⟨0, by rw [hdir hd, hk]; simp, Nat.le_refl _, by omega⟩

theorem pf_len (C : GzCompSpec) (G : DeflateGz) {w W : World} {h H : Heap} {b : Nat} {s s1 : GzState}
    {z : ZStream} {c base : Nat} (hv : GzInvWS W H (some b)) (hs : W.gz H b = some s1) (g : GStep w h W H b [])
    (hs0 : ∃ s0, w.gz h b = some s0) (zf : ZFix s s1) (hsk : s1.skip = 0) (hsz : s1.size ≠ 0)
    (hB : GzBufs H s1 c base) (hz : H.streams s.strm = some z) (hk : z.next_in = .ref (.heap c) base)
    (hA : z.avail_in.toNat ≤ s1.size.toNat) (len : Int32) (hl0 : len ≠ 0)
    (hl1 : len.toUInt32.toNat < s1.size.toNat) :
    GSat W H (pfLen (some b) (some s.strm) len) (CallPost w h b) := by
  have hstrm : s1.strm = s.strm := zf.strm
  have hwm := modeOf hs hv.2.1
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  have hP := sh.pos
  have hpw := hP.write_pos hwm
  have hps := hP.pos_skip
  have hsk0 : s1.skip.toInt = 0 := by rw [hsk]; rfl
  have hmax : GZ_OFF_MAX.toInt = 2 ^ 63 - 1 := by decide
  have hsw : s1.size.toNat = s1.want.toNat := by rw [hB.size]
  have hw30 := sh.want_hi
  have hin : inSize s1 = 2 * s1.want.toNat := by simp [inSize, hwm]
  have hli : len.toInt = len.toUInt32.toNat := i32_toInt_of_u32 len (by omega)
  have hl0' : len.toUInt32.toNat ≠ 0 := by
    intro e; apply hl0; apply Int32.toInt_inj.mp; rw [hli, e]; rfl
  unfold pfLen
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  refine GSat.bind (GSat.of_eq (a := Int64.ofInt (GZ_OFF_MAX.toInt - s1.pos.toInt))
    (by simp only [lm_app, chkI64_ok (v := GZ_OFF_MAX.toInt - s1.pos.toInt) (by omega) (by omega)]; rfl) ?_)
  have hroom : (Int64.ofInt (GZ_OFF_MAX.toInt - s1.pos.toInt)).toInt = GZ_OFF_MAX.toInt - s1.pos.toInt :=
    Int64.toInt_ofInt_of_le (by omega) (by omega)
  refine GSat.ite (fun _ => err_cont _ 13 lit_wpos lit_wpos_get nonul_wpos hv hs _ _ fun W' H' q => ?_)
    (fun hle => ?_)
  · obtain ⟨s', hs', -, hv', -, g'⟩ := q
    exact ret_err hv' hs' (g.trans g' hs0 ⟨s1, hs⟩)
  have hle' : len.toInt ≤ GZ_OFF_MAX.toInt - s1.pos.toInt := by
    have := Int64.not_lt.mp hle
    have e2 := Int64.le_iff_toInt_le.mp this
    rw [hroom, Int32.toInt_toInt64] at e2; exact e2
  -- the flat heap: the input may now reach past `size` bytes
  have hz1 : H.streams s1.strm = some z := by rw [hstrm]; exact hz
  obtain ⟨hvF, gF⟩ := invWS_flat hv hs hsz hz1
  rw [hstrm] at hvF gF
  refine GSat.bind (GSat.of_eq (a := ()) (w' := W)
    (h' := setZ H s.strm { z with avail_in := z.avail_in + len.toUInt32 }) (by simp [lm_app, wrZ_run hz]) ?_)
  have hai : (z.avail_in + len.toUInt32).toNat = z.avail_in.toNat + len.toUInt32.toNat := by
    rw [UInt32.toNat_add]; omega
  have hs1 : W.gz (setZ H s.strm { z with avail_in := z.avail_in + len.toUInt32 }) b = some s1 := hs
  refine GSat.bind (GSat.of_eq (rdG_app' hs1 _) ?_)
  refine GSat.bind (GSat.of_eq (a := Int64.ofInt (s1.pos.toInt + len.toInt))
    (by simp only [lm_app, chkI64_ok (v := s1.pos.toInt + len.toInt) (by omega) (by omega)]; rfl) ?_)
  refine GSat.bind (GSat.of_eq (wrG_app hs1 _) ?_)
  have hp1 : (Int64.ofInt (s1.pos.toInt + len.toInt)).toInt = s1.pos.toInt + len.toInt :=
    Int64.toInt_ofInt_of_le (by omega) (by omega)
  have hsF : W.gz (setZ H s.strm (flatZ z)) b = some s1 := hs
  obtain ⟨shF, hnF⟩ := inv_of hsF hvF.1
  have sh2 := shape_posW shF hwm (Int64.ofInt (s1.pos.toInt + len.toInt)) s1.skip
    ⟨by dsimp only; omega, by dsimp only; rw [hp1]; omega, by dsimp only; rw [hp1]; omega,
      fun _ => by dsimp only; rw [hp1]; omega⟩
  obtain ⟨hv2, hs2, g2⟩ := invWS_store hvF hsF sh2 hnF hwm rfl (fun c' hc _ => by
    simp only [GzOwned, gz_upd_same hsF, hsF] at hc ⊢; exact hc)
  generalize hW2 : ({ W with gzs := upd W.gzs b (some { s1 with pos := Int64.ofInt (s1.pos.toInt + len.toInt) }) } :
    World) = W2 at hv2 hs2 g2 ⊢
  generalize hs2e : ({ s1 with pos := Int64.ofInt (s1.pos.toInt + len.toInt), skip := s1.skip } : GzState) = s2
    at hv2 hs2 g2
  have hs2a : W2.gz (setZ H s.strm { z with avail_in := z.avail_in + len.toUInt32 }) b = some s2 := hs2
  have e2 : ZFix s1 s2 ∧ s2.size = s1.size ∧ s2.skip = s1.skip ∧ s2.buffers = s1.buffers ∧ s2.«in» = s1.«in» ∧
      s2.strm = s.strm := by
    rw [← hs2e]; exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, hstrm⟩
  obtain ⟨zf2, hsz2, hsk2, hbf2, hin2, hstrm2⟩ := e2
  have g02 : GStep w h W2 (setZ H s.strm (flatZ z)) b [] := (g.trans gF hs0 ⟨s1, hs⟩).trans g2 hs0 ⟨s1, hsF⟩
  refine GSat.bind (GSat.of_eq (a := z.avail_in + len.toUInt32) (w' := W2)
    (h' := setZ H s.strm { z with avail_in := z.avail_in + len.toUInt32 })
    (by simp [lm_app, rdZ_run (setZ_streams_same _ _ _)]) ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs2a _) ?_)
  rw [hsz2]
  refine GSat.ite (fun hge => ?_) (fun hlt => ?_)
  · -- `size` bytes or more: compress the first `size`
    have hge' := UInt32.le_iff_toNat_le.mp hge
    rw [hai] at hge'
    refine GSat.bind (GSat.of_eq (a := z.avail_in + len.toUInt32) (w' := W2)
    (h' := setZ H s.strm { z with avail_in := z.avail_in + len.toUInt32 })
    (by simp [lm_app, rdZ_run (setZ_streams_same _ _ _)]) ?_)
    refine GSat.bind (GSat.of_eq (rdG_app' hs2a _) ?_)
    refine GSat.bind (GSat.of_eq (rdG_app' hs2a _) ?_)
    rw [hsz2]
    refine GSat.bind (GSat.of_eq (a := ()) (w' := W2)
      (h' := setZ H s.strm { z with avail_in := s1.size }) (by simp [lm_app, wrZ_run (setZ_streams_same _ _ _), setZ_setZ]) ?_)
    have hfl : setZ (setZ H s.strm { z with avail_in := s1.size }) s.strm (flatZ { z with avail_in := s1.size }) =
        setZ H s.strm (flatZ z) := by rw [setZ_setZ]; rfl
    have hs3 : W2.gz (setZ H s.strm { z with avail_in := s1.size }) b = some s2 := hs2
    have hz3 : (setZ H s.strm { z with avail_in := s1.size }).streams s2.strm = some { z with avail_in := s1.size } := by
      rw [hstrm2]; exact setZ_streams_same _ _ _
    have wx : GzWX W2 (setZ H s.strm { z with avail_in := s1.size }) b s2 { z with avail_in := s1.size } := by
      refine ⟨hs3, hz3, by rw [hsz2]; exact hsz, by rw [hstrm2, hfl]; exact hv2, Or.inl ⟨c, base, ?_, Or.inl ⟨0, ?_,
        Nat.le_refl _, ?_⟩⟩⟩
      · rw [hbf2]; exact hB.buffers
      · show z.next_in = _; rw [hk]; simp
      · show 0 + s1.size.toNat ≤ inSize s2
        have : inSize s2 = inSize s1 := by simp [inSize, ← hs2e]
        rw [this, hin]; omega
    obtain ⟨ψ, Gr, hψ⟩ := psi_of G
    refine GSat.bind (GSat.mono (C G ψ Gr hψ W2 _ b ZlibNg.Deflate.Z_NO_FLUSH _ _ hs3 hz3 (Or.inr wx))
      fun rc W3 H3 q => ?_)
    obtain ⟨s3, z3, hs3', hz3', fx, hbuf, -, gF3, -, -, hwx, -, hav, hadv, hdir, hrc, hok, -, -⟩ := q
    dsimp only at hz3' hadv hdir hav
    rw [hstrm2] at hz3'
    have hsz3 : s3.size ≠ 0 := by rw [(hbuf (by rw [hsz2]; exact hsz)).1, hsz2]; exact hsz
    have hx3 := hwx hsz3
    have hbf3 : s3.buffers = s1.buffers := by rw [(hbuf (by rw [hsz2]; exact hsz)).2.1, hbf2]
    have hin3 : s3.«in» = s1.«in» := by rw [(hbuf (by rw [hsz2]; exact hsz)).2.2.1, hin2]
    have hsz3' : s3.size = s1.size := by rw [(hbuf (by rw [hsz2]; exact hsz)).1, hsz2]
    have hinp : InpOk s3 c base z3.next_in z3.avail_in := by
      have := comp_inp (s := s3) (z := { z with avail_in := s1.size }) (z' := z3) hk hav
        (fun hd => hadv (by rw [hsz2]; exact hsz) (by rw [← fx.direct]; exact hd)) (fun hd => hdir (by rw [← fx.direct]; exact hd))
        (by rw [hsz3'])
      exact this
    obtain ⟨hv3, g3u⟩ := inv_of_wx hx3 ⟨c, base, by rw [hbf3]; exact hB.buffers, hinp⟩
    have hstrm3 : s3.strm = s.strm := by rw [fx.strm, hstrm2]
    rw [hstrm3] at g3u
    rw [hstrm2, hfl] at gF3
    have g03 : GStep w h W3 H3 b [] := (g02.trans gF3 hs0 ⟨s2, hs2⟩).trans g3u hs0 ⟨s3, hs3'⟩
    refine GSat.ite (fun _ => ret_err hv3 hs3' g03) (fun hne => ?_)
    -- move the rest to the start of `in`
    have hr0 : rc = 0 := by rcases hrc with e | e; exact e; simp [e] at hne
    have ha3 : z3.avail_in = 0 := (hok hr0).2.1 (by decide)
    obtain ⟨sh3, hn3⟩ := inv_of hs3' hv3.1
    have hwm3 := modeOf hs3' hv3.2.1
    obtain ⟨c3, base3, -, hB3, -, -⟩ := (sh3.write hwm3).bufs hsz3
    have ecb : c3 = c ∧ base3 = base := by
      have := hB3.buffers; rw [hbf3, hB.buffers] at this; cases this; exact ⟨rfl, rfl⟩
    obtain ⟨rfl, rfl⟩ := ecb
    obtain ⟨d3, hd3, hds3⟩ := hB3.fits
    have hw3 : s3.want = s1.want := by rw [fx.want, zf2.want]
    have hin3' : inSize s3 = 2 * s1.want.toNat := by simp [inSize, hwm3, hw3]
    have hg3 : Space.get H3 (BRef.heap c3) = some d3 := hd3
    refine GSat.bind (GSat.of_eq (ldGz_app hs3') ?_)
    rw [hB3.inp]
    refine GSat.bind (GSat.of_eq (liftM_get_val _ _ _) ?_)
    refine GSat.bind (GSat.of_eq (rdG_app' hs3' _) ?_)
    rw [hsz3']
    refine GSat.bind (GSat.of_eq (a := Ptr.ref (BRef.heap c3) (base3 + s1.size.toNat)) (w' := W3) (h' := H3)
      (by rw [lm_app, padd_ok hg3 _ (by omega)]) ?_)
    have hleft : (z.avail_in + len.toUInt32 - s1.size).toNat = z.avail_in.toNat + len.toUInt32.toNat - s1.size.toNat := by
      rw [UInt32.toNat_sub_of_le _ _ hge, hai]
    obtain ⟨H4, em, x4⟩ := memmove_hbuf hd3 (od := base3) (os := base3 + s1.size.toNat)
      (n := (z.avail_in + len.toUInt32 - s1.size).toNat) (by omega) (by omega)
    refine GSat.bind (GSat.of_eq (a := ()) (w' := W3) (h' := H4) (by rw [lm_app, em]) ?_)
    obtain ⟨hcb, hpth, hstb, hown⟩ := bufBlk hs3' hn3 hsz3 hB3
    obtain ⟨hv4, hs4, g4⟩ := invWS_hbuf hv3 hs3' x4 hcb hpth hstb hown
    have hz4 : H4.streams s3.strm = some z3 := by obtain ⟨t, e, -⟩ := x4; rw [e, hstrm3]; exact hz3'
    refine GSat.bind (GSat.of_eq (ldGz_app hs4) ?_)
    rw [hB3.inp]
    refine GSat.bind (GSat.of_eq (liftM_get_val _ _ _) ?_)
    obtain ⟨hv5, hs5, g5⟩ := invWS_setIn hv4 hs4 hsz3 hz4 (.ref (.heap c3) base3) z3.avail_in (fun c' base' hb => by
      have e := hb.buffers; rw [hB3.buffers] at e; cases e
      exact Or.inl ⟨0, by simp, Nat.le_refl _, by rw [ha3]; simp⟩)
    rw [hstrm3] at hz4 hv5 hs5 g5
    refine GSat.bind (GSat.of_eq (a := ()) (w' := W3)
      (h' := setZ H4 s.strm { z3 with next_in := .ref (.heap c3) base3, avail_in := z3.avail_in })
      (by simp [lm_app, wrZ_run hz4]) ?_)
    have hz5 := setZ_streams_same H4 s.strm { z3 with next_in := .ref (.heap c3) base3, avail_in := z3.avail_in }
    obtain ⟨hv6, hs6, g6⟩ := invWS_setIn hv5 hs5 hsz3 (by rw [hstrm3]; exact hz5) (.ref (.heap c3) base3)
      (z.avail_in + len.toUInt32 - s1.size) (fun c' base' hb => by
        have e := hb.buffers; rw [hB3.buffers] at e; cases e
        exact Or.inl ⟨0, by simp, Nat.le_refl _, by rw [hleft, hsz3']; omega⟩)
    rw [hstrm3] at hv6 hs6 g6
    refine GSat.bind (GSat.of_eq (a := ()) (w' := W3)
      (h' := setZ (setZ H4 s.strm { z3 with next_in := .ref (.heap c3) base3, avail_in := z3.avail_in }) s.strm
        { z3 with next_in := .ref (.heap c3) base3, avail_in := z.avail_in + len.toUInt32 - s1.size })
      (by simp [lm_app, wrZ_run hz5]) ?_)
    exact GSat.pure ⟨hv6, (((g03.trans g4 hs0 ⟨s3, hs3'⟩).trans g5 hs0 ⟨s3, hs4⟩).trans g6 hs0 ⟨s3, hs5⟩)⟩
  · -- fewer than `size` bytes: the input is inside `size` bytes again
    have hlt' : ¬ s1.size.toNat ≤ (z.avail_in + len.toUInt32).toNat := fun h' => hlt (UInt32.le_iff_toNat_le.mpr h')
    rw [hai] at hlt'
    have hfl1 : setZ (setZ H s.strm { z with avail_in := z.avail_in + len.toUInt32 }) s.strm
        (flatZ { z with avail_in := z.avail_in + len.toUInt32 }) = setZ H s.strm (flatZ z) := by rw [setZ_setZ]; rfl
    obtain ⟨hv5, g5⟩ := invWS_unflat (s := s2) (h := setZ H s.strm { z with avail_in := z.avail_in + len.toUInt32 })
      (by rw [hstrm2]; exact setZ_streams_same _ _ _) (by rw [hstrm2, hfl1]; exact hv2) hs2a (by rw [hsz2]; exact hsz)
      (fun c' base' hb => by
        have e := hb.buffers; rw [hbf2, hB.buffers] at e; cases e
        refine Or.inl ⟨0, ?_, Nat.le_refl _, ?_⟩
        · show z.next_in = _; rw [hk]; simp
        · show 0 + (z.avail_in + len.toUInt32).toNat ≤ s2.size.toNat
          rw [hai, hsz2]; omega)
    rw [hstrm2, hfl1] at g5
    exact GSat.pure ⟨hv5, g02.trans g5 hs0 ⟨s2, hs2⟩⟩

/-! ## Formatting -/

open ZlibNg.Inflate (rdZ wrZ) in
/-- `gzvprintf` after the input is at the start of `in` (copied from the translation). -/
def pfTail (state : GzPtr) (strm : StreamPtr) (format : BPtr) : G Int32 := do
  let d ← lm (Ptr.diff (← lm (rdZ strm (·.next_in))) (← (← ldGz state).«in».get))
  let a ← lm ((← (← ldGz state).«in».get).add d.toInt)
  let next ← lm (a.add (Int.ofNat (← lm (rdZ strm (·.avail_in))).toNat))
  lm (store8 (← lm (next.add (Int.ofNat ((← rdG state (·.size)) - 1).toNat))) 0)
  let len ← vsnprintfG next (← rdG state (·.size)).toUInt64 format
  let bad ← if len == 0 || len.toUInt32 ≥ (← rdG state (·.size)) then pure true
    else do pure ((← lm (index8 next (Int.ofNat ((← rdG state (·.size)) - 1).toNat))) != 0)
  if bad then
    return 0
  pfLen state strm len

theorem pf_tail (C : GzCompSpec) (G : DeflateGz) {w W : World} {h H : Heap} {b : Nat} {s s1 : GzState}
    {z : ZStream} {c base : Nat} (hv : GzInvWS W H (some b)) (hs : W.gz H b = some s1) (g : GStep w h W H b [])
    (hs0 : ∃ s0, w.gz h b = some s0) (zf : ZFix s s1) (hsk : s1.skip = 0) (hsz : s1.size ≠ 0)
    (hB : GzBufs H s1 c base) (hz : H.streams s.strm = some z) (hk : z.next_in = .ref (.heap c) base)
    (hA : z.avail_in.toNat ≤ s1.size.toNat) {fmt : BPtr} {n : Nat} (hf : CStringLen H fmt n)
    (ho : OutsideGz W H (some b) fmt) :
    GSat W H (pfTail (some b) (some s.strm) fmt) (CallPost w h b) := by
  have hwm := modeOf hs hv.2.1
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  have hsw : s1.size.toNat = s1.want.toNat := by rw [hB.size]
  have hw30 := sh.want_hi
  have hw8 := sh.want_lo
  have hin : inSize s1 = 2 * s1.want.toNat := by simp [inSize, hwm]
  obtain ⟨d, hd, hds⟩ := hB.fits
  have hg : Space.get H (BRef.heap c) = some d := hd
  obtain ⟨hcb, hpth, hstb, hown⟩ := bufBlk hs hn hsz hB
  have hfc : ∀ off, fmt ≠ .ref (.heap c) off := fun off e => ho c hown off e
  unfold pfTail
  refine GSat.bind (GSat.of_eq (a := z.next_in) (w' := W) (h' := H) (by simp [lm_app, rdZ_run hz]) ?_)
  refine GSat.bind (GSat.of_eq (ldGz_app hs) ?_)
  rw [hB.inp, hk]
  refine GSat.bind (GSat.of_eq (liftM_get_val _ _ _) ?_)
  refine GSat.bind (GSat.of_eq (a := Int64.ofInt ((base : Int) - base)) (w' := W) (h' := H)
    (by rw [lm_app, pdiff_ok hd (by omega) (Nat.le_refl _) (by omega)]) ?_)
  refine GSat.bind (GSat.of_eq (ldGz_app hs) ?_)
  rw [hB.inp]
  refine GSat.bind (GSat.of_eq (liftM_get_val _ _ _) ?_)
  have e0 : (Int64.ofInt ((base : Int) - base)).toInt = Int.ofNat 0 := by simp
  refine GSat.bind (GSat.of_eq (a := Ptr.ref (BRef.heap c) (base + 0)) (w' := W) (h' := H)
    (by rw [lm_app, e0, padd_ok hg 0 (by omega)]) ?_)
  refine GSat.bind (GSat.of_eq (a := z.avail_in) (w' := W) (h' := H) (by simp [lm_app, rdZ_run hz]) ?_)
  refine GSat.bind (GSat.of_eq (a := Ptr.ref (BRef.heap c) (base + 0 + z.avail_in.toNat)) (w' := W) (h' := H)
    (by rw [lm_app, padd_ok hg _ (by omega)]) ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  have hs1 : (s1.size - 1).toNat = s1.size.toNat - 1 := by
    rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by simp; omega))]; simp
  refine GSat.bind (GSat.of_eq (a := Ptr.ref (BRef.heap c) (base + 0 + z.avail_in.toNat + (s1.size - 1).toNat))
    (w' := W) (h' := H) (by rw [lm_app, padd_ok hg _ (by omega)]) ?_)
  have hst := store8_heap hd (off := base + 0 + z.avail_in.toNat + (s1.size - 1).toNat) (by omega) 0
  refine GSat.bind (GSat.of_eq (a := ()) (w' := W) (by rw [lm_app, hst]) ?_)
  have x2 := HBuf.store8 hd (lo := base) (hi := base + inSize s1) (off := base + 0 + z.avail_in.toNat + (s1.size - 1).toNat)
    (by omega) (by omega) 0
  obtain ⟨hv2, hs2, g2⟩ := invWS_hbuf hv hs x2 hcb hpth hstb hown
  have hf2 := cstr_hbuf x2 hf hfc
  generalize ({ H with bytes := H.bytes.modify c (Option.map fun a' => a'.set! (base + 0 + z.avail_in.toNat +
    (s1.size - 1).toNat) 0) } : Heap) = H2 at hv2 hs2 g2 x2 hf2 ⊢
  obtain ⟨t2, eH2, -, -, hsz2⟩ := x2
  obtain ⟨d2, hd2, hds2, -⟩ := hsz2 d hd
  have hd2' : H2.bytes c = some d2 := by rw [eH2]; exact hd2
  refine GSat.bind (GSat.of_eq (rdG_app' hs2 _) ?_)
  refine GSat.bind (GSat.mono (vsn_spec (W := W) hd2' s1.size.toUInt64 (off := base + 0 + z.avail_in.toNat)
    (by rw [UInt32.toNat_toUInt64]; omega) hf2) fun len W3 H3 q => ?_)
  obtain ⟨rfl, -, x3⟩ := q
  rw [UInt32.toNat_toUInt64] at x3
  have g2n := gstep_nprintf hs2 (W.nprintf + 1)
  have hv2n : GzInvWS { W with nprintf := W.nprintf + 1 } H2 (some b) := hv2
  have hs2n : ({ W with nprintf := W.nprintf + 1 } : World).gz H2 b = some s1 := hs2
  have hB2 : GzBufs H2 s1 c base := ⟨hB.size, hB.buffers, hB.inp, hB.out, ⟨d2, hd2', by omega⟩, hB.hdr.1,
    by rw [eH2]; exact hB.hdr.2⟩
  obtain ⟨hcb2, hpth2, hstb2, hown2⟩ := bufBlk hs2n (by obtain ⟨-, h2⟩ := inv_of hs2n hv2n.1; exact h2) hsz hB2
  obtain ⟨hv3, hs3, g3⟩ := invWS_hbuf hv2n hs2n x3 hcb2 hpth2 hstb2 hown2
  have g03 : GStep w h { W with nprintf := W.nprintf + 1 } H3 b [] :=
    (((g.trans g2 hs0 ⟨s1, hs⟩).trans g2n hs0 ⟨s1, hs2⟩).trans g3 hs0 ⟨s1, hs2n⟩)
  obtain ⟨t3, eH3, -, -, hsz3⟩ := x3
  obtain ⟨d3, hd3, hds3, -⟩ := hsz3 d2 hd2'
  have hd3' : H3.bytes c = some d3 := by rw [eH3]; exact hd3
  have hz2 : H2.streams s.strm = some z := by rw [eH2]; exact hz
  have hz3 : H3.streams s.strm = some z := by rw [eH3]; exact hz2
  have hB3 : GzBufs H3 s1 c base := ⟨hB.size, hB.buffers, hB.inp, hB.out, ⟨d3, hd3', by omega⟩, hB.hdr.1,
    by rw [eH3]; exact hB2.hdr.2⟩
  refine GSat.bind (GSat.of_eq (rdG_app' hs3 _) ?_)
  refine GSat.ite (fun _ => ?_) (fun hc => ?_)
  · exact GSat.bind (GSat.pure (GSat.ite (fun _ => GSat.pure ⟨hv3, g03⟩) (fun h' => absurd rfl h')))
  · have hc' : len ≠ 0 ∧ len.toUInt32 < s1.size := by simp at hc; exact ⟨hc.1, hc.2⟩
    refine GSat.bind (GSat.of_eq (rdG_app' hs3 _) ?_)
    obtain ⟨v, ev⟩ : ∃ v, index8 (Ptr.ref (BRef.heap c) (base + 0 + z.avail_in.toNat))
        (Int.ofNat (s1.size - 1).toNat) H3 = .ok (v, H3) :=
      ⟨_, index8_heap _ hd3' (by omega)⟩
    refine GSat.bind (GSat.of_eq (by rw [lm_app, ev]) (GSat.bind (GSat.pure ?_)))
    exact GSat.ite (fun _ => GSat.pure ⟨hv3, g03⟩) (fun _ => pf_len C G hv3 hs3 g03 hs0 zf hsk hsz hB3 hz3 hk hA len
      hc'.1 (UInt32.lt_iff_toNat_lt.mp hc'.2))

/-! ## The input moved to the start of `in` (patch 0021), and the whole call -/

open ZlibNg.Inflate (rdZ wrZ) in
/-- `gzvprintf` after the pending seek (copied from the translation). -/
def pfNorm (state : GzPtr) (strm : StreamPtr) (format : BPtr) : G Int32 := do
  if (← lm (rdZ strm (·.avail_in))) == 0 then
    let i ← (← ldGz state).«in».get
    lm (wrZ strm fun z => { z with next_in := i })
  else if (← lm (rdZ strm (·.next_in))) != (← (← ldGz state).«in».get) then
    lm (Ptr.memmove (← (← ldGz state).«in».get) (← lm (rdZ strm (·.next_in))) (← lm (rdZ strm (·.avail_in))).toNat)
    let i ← (← ldGz state).«in».get
    lm (wrZ strm fun z => { z with next_in := i })
  pfTail state strm format

/-- `gzvprintf` after the buffers are made (copied from the translation). -/
def pfSkip (state : GzPtr) (strm : StreamPtr) (format : BPtr) : G Int32 := do
  if (← rdG state (·.skip)) != 0 then
    if (← gz_zero state) == -1 then
      return (← rdG state (·.err))
  pfNorm state strm format

theorem gzvprintf_eq (b : Nat) (fmt : BPtr) : gzvprintf (some b) fmt = (do
    let strm ← strmOf (some b)
    if (← rdG (some b) (·.mode)) != GZ_WRITE || (← rdG (some b) (·.err)) != ZlibNg.Inflate.Z_OK then
      return ZlibNg.Inflate.Z_STREAM_ERROR
    if (← rdG (some b) (·.size)) == 0 then
      if (← gz_write_init (some b)) == -1 then
        return (← rdG (some b) (·.err))
    pfSkip (some b) strm fmt) := rfl

theorem pf_norm (C : GzCompSpec) (G : DeflateGz) {w W : World} {h H : Heap} {b : Nat} {s s1 : GzState}
    (hv : GzInvWS W H (some b)) (hs : W.gz H b = some s1) (g : GStep w h W H b [])
    (hs0 : ∃ s0, w.gz h b = some s0) (zf : ZFix s s1) (hsk : s1.skip = 0) (hsz : s1.size ≠ 0) {fmt : BPtr} {n : Nat}
    (hf : CStringLen H fmt n) (ho : OutsideGz W H (some b) fmt) :
    GSat W H (pfNorm (some b) (some s.strm) fmt) (CallPost w h b) := by
  have hstrm : s1.strm = s.strm := zf.strm
  have hwm := modeOf hs hv.2.1
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  obtain ⟨c, base, z, hB, hz, WB⟩ := (sh.write hwm).bufs hsz
  have hz' : H.streams s.strm = some z := by rw [← hstrm]; exact hz
  have hfr : FreshBlocks H := hv.2.2.2.1.1
  have hsw : s1.size.toNat = s1.want.toNat := by rw [hB.size]
  have hin : inSize s1 = 2 * s1.want.toNat := by simp [inSize, hwm]
  obtain ⟨d, hd, hds⟩ := hB.fits
  -- `next_in = in` with the input in `size` bytes
  have fin : ∀ {H1 : Heap} {z1 : ZStream}, GzInvWS W H1 (some b) → W.gz H1 b = some s1 → GStep W H W H1 b [] →
      GzBufs H1 s1 c base → H1.streams s1.strm = some z1 → z1.avail_in.toNat ≤ s1.size.toNat →
      GSat W (setZ H1 s.strm { z1 with next_in := .ref (.heap c) base })
        (pfTail (some b) (some s.strm) fmt) (CallPost w h b) := by
    intro H1 z1 hv1 hs1 g1 hB1 hz1 hA1
    obtain ⟨hv2, hs2, g2⟩ := invWS_setIn hv1 hs1 hsz hz1 (.ref (.heap c) base) z1.avail_in (fun c' base' hb => by
      have e := hb.buffers; rw [hB1.buffers] at e; cases e
      exact Or.inl ⟨0, by simp, Nat.le_refl _, by omega⟩)
    rw [hstrm] at hv2 hs2 g2
    have g02 : GStep w h W (setZ H1 s.strm { z1 with next_in := .ref (.heap c) base }) b [] :=
      (g.trans g1 hs0 ⟨s1, hs⟩).trans g2 hs0 ⟨s1, hs1⟩
    obtain ⟨hf2, ho2⟩ := cstr_step (g1.trans g2 ⟨s1, hs⟩ ⟨s1, hs1⟩) hfr hf ho
    have hB2 : GzBufs (setZ H1 s.strm { z1 with next_in := .ref (.heap c) base }) s1 c base :=
      ⟨hB1.size, hB1.buffers, hB1.inp, hB1.out, hB1.fits, hB1.hdr⟩
    exact pf_tail C G hv2 hs2 g02 hs0 zf hsk hsz hB2 (setZ_streams_same _ _ _) rfl hA1 hf2 ho2
  unfold pfNorm
  refine GSat.bind (GSat.of_eq (a := z.avail_in) (w' := W) (h' := H) (by simp [lm_app, rdZ_run hz']) ?_)
  refine GSat.ite (fun hai => ?_) (fun hai => ?_)
  · have hai0 : z.avail_in = 0 := by simpa using hai
    refine GSat.bind (GSat.of_eq (ldGz_app hs) ?_)
    rw [hB.inp]
    refine GSat.bind (GSat.of_eq (liftM_get_val _ _ _) ?_)
    refine GSat.bind (GSat.of_eq (a := ()) (w' := W) (h' := setZ H s.strm { z with next_in := .ref (.heap c) base })
      (by simp [lm_app, wrZ_run hz']) ?_)
    exact fin hv hs (GStep.refl W H b []) hB hz (by rw [hai0]; simp)
  · have hai0 : z.avail_in ≠ 0 := by simpa using hai
    obtain ⟨k, hk, -, hkA⟩ := WB.inp.resolve_right (fun ⟨e, _⟩ => hai0 e)
    refine GSat.bind (GSat.of_eq (a := z.next_in) (w' := W) (h' := H) (by simp [lm_app, rdZ_run hz']) ?_)
    refine GSat.bind (GSat.of_eq (ldGz_app hs) ?_)
    rw [hB.inp, hk]
    refine GSat.bind (GSat.of_eq (liftM_get_val _ _ _) ?_)
    refine GSat.ite (fun hne => ?_) (fun heq => ?_)
    · refine GSat.bind (GSat.of_eq (ldGz_app hs) ?_)
      rw [hB.inp]
      refine GSat.bind (GSat.of_eq (liftM_get_val _ _ _) ?_)
      refine GSat.bind (GSat.of_eq (a := z.next_in) (w' := W) (h' := H) (by simp [lm_app, rdZ_run hz']) ?_)
      refine GSat.bind (GSat.of_eq (a := z.avail_in) (w' := W) (h' := H) (by simp [lm_app, rdZ_run hz']) ?_)
      rw [hk]
      obtain ⟨H1, em, x1⟩ := memmove_hbuf hd (od := base) (os := base + k) (n := z.avail_in.toNat) (by omega)
        (by omega)
      refine GSat.bind (GSat.of_eq (a := ()) (w' := W) (h' := H1) (by rw [lm_app, em]) ?_)
      obtain ⟨hcb, hpth, hstb, hown⟩ := bufBlk hs hn hsz hB
      obtain ⟨hv1, hs1, g1⟩ := invWS_hbuf hv hs x1 hcb hpth hstb hown
      obtain ⟨t1, eH1, -, -, hsz1⟩ := x1
      obtain ⟨d1, hd1, hds1, -⟩ := hsz1 d hd
      have hB1 : GzBufs H1 s1 c base := ⟨hB.size, hB.buffers, hB.inp, hB.out, ⟨d1, by rw [eH1]; exact hd1, by omega⟩,
        hB.hdr.1, by rw [eH1]; exact hB.hdr.2⟩
      have hz1 : H1.streams s1.strm = some z := by rw [eH1]; exact hz
      refine GSat.bind (GSat.of_eq (ldGz_app hs1) ?_)
      rw [hB.inp]
      refine GSat.bind (GSat.of_eq (liftM_get_val _ _ _) ?_)
      refine GSat.bind (GSat.of_eq (a := ()) (w' := W) (h' := setZ H1 s.strm { z with next_in := .ref (.heap c) base })
        (by simp [lm_app, wrZ_run (by rw [← hstrm]; exact hz1 : H1.streams s.strm = some z)]) ?_)
      exact fin hv1 hs1 g1 hB1 hz1 (by omega)
    · have hk0 : k = 0 := by
        have : Ptr.ref (BRef.heap c) (base + k) = (Ptr.ref (BRef.heap c) base : BPtr) := by simpa using heq
        simp at this; omega
      subst hk0
      have hsame : setZ H s.strm { z with next_in := .ref (.heap c) base } = H := by
        have e : z.next_in = .ref (.heap c) base := by simpa using hk
        rw [← e]
        exact setZ_self hz'
      have := fin hv hs (GStep.refl W H b []) hB hz (by omega)
      rw [hsame] at this
      exact this

theorem pf_skip (C : GzCompSpec) (G : DeflateGz) {w W : World} {h H : Heap} {b : Nat} {s s1 : GzState}
    (hv : GzInvWS W H (some b)) (hs : W.gz H b = some s1) (g : GStep w h W H b [])
    (hs0 : ∃ s0, w.gz h b = some s0) (zf : ZFix s s1) (hsz : s1.size ≠ 0) {fmt : BPtr} {n : Nat}
    (hf : CStringLen H fmt n) (ho : OutsideGz W H (some b) fmt) :
    GSat W H (pfSkip (some b) (some s.strm) fmt) (CallPost w h b) := by
  unfold pfSkip
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  refine GSat.ite (fun hk => ?_) (fun hk => pf_norm C G hv hs g hs0 zf (by simpa using hk) hsz hf ho)
  refine GSat.bind (GSat.mono (gz_zero_spec C G hv hs (by simpa using hk)) fun rz W2 H2 q => ?_)
  obtain ⟨s2, hs2, hv2, g2, zf2, hrz, hok⟩ := q
  refine GSat.ite (fun _ => ret_err hv2 hs2 (g.trans g2 hs0 ⟨s1, hs⟩)) (fun hne => ?_)
  have hr0 : rz = 0 := by rcases hrz with e | e; exact e; simp [e] at hne
  obtain ⟨hf2, ho2⟩ := cstr_step g2 hv.2.2.2.1.1 hf ho
  exact pf_norm C G hv2 hs2 (g.trans g2 hs0 ⟨s1, hs⟩) hs0 (zf.trans zf2) (hok hr0).1 (hok hr0).2 hf2 ho2

/-- **`gzvprintf`** on a write handle, with a format string outside the blocks of the file. -/
theorem gzvprintf_spec (C : GzCompSpec) (G : DeflateGz) {w : World} {h : Heap} {b : Nat} {s : GzState}
    (hv : GzInvWS w h (some b)) (hs : w.gz h b = some s) (fmt : BPtr) (hf : CStr h fmt)
    (ho : OutsideGz w h (some b) fmt) :
    GSat w h (gzvprintf (some b) fmt) (CallPost w h b) := by
  obtain ⟨n, hn⟩ := hf
  rw [gzvprintf_eq]
  refine GSat.bind (GSat.of_eq (strmOf_app hs) ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  refine GSat.ite (fun _ => GSat.pure (CallPost.refl hv _)) (fun _ => ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  by_cases hz : s.size = 0
  · refine GSat.ite (fun _ => ?_) (fun hc => by simp [hz] at hc)
    refine GSat.bind (GSat.mono (gz_write_init_spec G hv hs hz) fun r W H q => ?_)
    obtain ⟨s', hs', hv', g, -, fx, hr'⟩ := q
    refine GSat.ite (fun _ => ret_err hv' hs' g) (fun hc => ?_)
    rcases hr' with ⟨rfl, hsz⟩ | rfl
    · obtain ⟨hf2, ho2⟩ := cstr_step g hv.2.2.2.1.1 hn ho
      exact pf_skip C G hv' hs' g ⟨s, hs⟩ (ZFix.of_w fx) hsz hf2 ho2
    · simp at hc
  · refine GSat.ite (fun hc => by simp at hc; exact absurd hc hz) (fun _ => ?_)
    exact pf_skip C G hv hs (GStep.refl w h b []) ⟨s, hs⟩ (ZFix.refl s) hz hn ho

/-- **`gzprintf`** on a write handle, with a format string outside the blocks of the file. -/
theorem gzprintf_spec (C : GzCompSpec) (G : DeflateGz) {w : World} {h : Heap} {b : Nat} {s : GzState}
    (hv : GzInvWS w h (some b)) (hs : w.gz h b = some s) (fmt : BPtr) (hf : CStr h fmt)
    (ho : OutsideGz w h (some b) fmt) :
    GSat w h (gzprintf (some b) fmt) (CallPost w h b) := by
  exact gzvprintf_spec C G hv hs fmt hf ho

end ZlibNgF.Proof.GzWrite
