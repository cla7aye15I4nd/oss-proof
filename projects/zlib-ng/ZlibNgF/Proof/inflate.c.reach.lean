import ZlibNgF.Proof.«public-inflate-control»
import ZlibNgF.Proof.«public-inflate-init»
import ZlibNgF.Proof.«inflate.c.copy»
import ZlibNgF.Proof.«adler32_c.c.safety»

/-!
# Reachable inflate streams have the structural invariant (`ZlibNgF`)

`reach_inv`: `InflateReachable h s → Inv h s`, by induction over `InflateReachable`. Every constructor case is proved
here except the steps whose preservation lemma does not exist yet; those are the fields of `Pending`, so the
induction is finished once `Pending` is proved (see the plan in `Proof/inflate.c.invariant.lean`).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InflateReach
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNgF.Proof.InflateInv

/-- The obligation still to prove: preservation of the invariant by `inflate`. -/
structure Pending : Prop where
  inflate : ∀ (h h' : Heap) (s : StreamPtr) (flush r : Int32), Inv h s → StreamIO h s →
    C.run (ZlibNg.Inflate.inflate s flush) h = .ok (r, h') → Inv h' s

/-- `adler32_c` on a readable buffer does not fault and changes nothing (`Proof/adler32_c.c.safety.lean`). -/
theorem adlerSafe : InflateWindow.AdlerSafe := fun _ a _ o _ n hg hle =>
  let ⟨v, e, _⟩ := Adler32Safe.adler32_c_safe hg a o n hle
  ⟨v, e⟩

/-- Two runs of one computation on one heap agree. -/
theorem det {α : Type} {m : M α} {h h' h'' : Heap} {r r' : α} (e : C.run m h = .ok (r, h'))
    (e' : C.run m h = .ok (r', h'')) : h' = h'' := by
  rw [e] at e'; cases e'; rfl

/-- A caller step keeps the invariant: it changes only the buffer fields of the `z_stream`. -/
theorem caller_inv {h h' : Heap} {s : StreamPtr} (hv : Inv h s) (hc : CallerStep h h' s) : Inv h' s := by
  obtain ⟨i, z, b, st, al, rfl, hz, hb, hst, hal, c⟩ := hv
  obtain ⟨i', z1, z', b', e1, hz1, hz', hb', ez, hbytes, histates, hiallocs, hhead, _, _⟩ := hc
  obtain rfl : i' = i := (Option.some.inj e1).symm
  obtain rfl : z1 = z := Option.some.inj (hz1.symm.trans hz)
  obtain rfl : b' = b := Option.some.inj (hb'.symm.trans hb)
  have hs' : z'.state = z1.state := by rw [ez]
  have hst' : h'.istate b' = some st := by simp only [Heap.istate, hbytes, histates]; exact hst
  have hal' : h'.iallocsOf b' = some al := by simp only [Heap.iallocsOf, hbytes, hiallocs]; exact hal
  refine ⟨i', z', b', st, al, rfl, hz', hs'.trans hb, hst', hal', ?_⟩
  have za : z'.zalloc = z1.zalloc := by rw [ez]
  have zf : z'.zfree = z1.zfree := by rw [ez]
  refine { c with toShape := ?_, head := ?_ }
  · exact { c.toShape with
      zalloc := za.trans c.zalloc
      zfree := zf.trans c.zfree
      window := by rw [hbytes]; exact c.window }
  · rcases c.head with hh | ⟨k, g, hk, hg⟩
    · exact Or.inl hh
    · refine Or.inr ⟨k, g, hk, ?_⟩
      rw [hhead (some k) ⟨b', st, ⟨z1, ⟨i', rfl, hz1⟩, hb'⟩, hst, hk⟩ k rfl]
      exact hg

/-- `inflateGetHeader(strm, Z_NULL)` returns only when it changes nothing (on a gzip stream it faults). -/
theorem getHeader_none {h h' : Heap} {s : StreamPtr} {r : Int32} (hv : Inv h s)
    (e : C.run (inflateGetHeader s none) h = .ok (r, h')) : h' = h := by
  obtain ⟨i, z, b, st, al, rfl, L, _, _⟩ := InflateInv.live hv
  by_cases hc : (st.wrap &&& 2) = 0
  · have e0 : C.run (inflateGetHeader (some i) none) h = .ok (Z_STREAM_ERROR, h) := by
      simp [C.run, inflateGetHeader, bind_app, L.check, L.stateOf, rdS, ldState_app L.istate, hc]
    exact det e e0
  · obtain ⟨d, hd⟩ := L.hd
    simp [C.run, inflateGetHeader, bind_app, L.check, L.stateOf, rdS, hc, ZlibNg.Inflate.wrS, ldState, stState,
      Heap.istate, hd, L.hst, ldHeader] at e

/-- Every public step keeps the invariant, given the pending preservation lemmas. -/
theorem step_inv (P : Pending) {h h' : Heap} {s : StreamPtr} (hv : Inv h s) (hs : InflateStep h h' s) :
    Inv h' s := by
  rcases hs with ⟨flush, r, hio, e⟩ | ⟨r, hio, hsi, e⟩ | ⟨r, e⟩ | ⟨d, n, r, hd, hnb, e⟩ |
    ⟨d, hasLen, r, hd, hnb, e⟩ | ⟨hp, r, hok, -, e⟩ | ⟨bits, value, r, e⟩ | ⟨r, e⟩ | ⟨r, e⟩ |
    ⟨w, r, e⟩ | ⟨c, r, e⟩ | ⟨v, r, e⟩ | ⟨r, e⟩ | ⟨r, e⟩ | ⟨dst, r, hdst, hne, e⟩
  · exact P.inflate h h' s flush r hv hio e
  · obtain ⟨_, _, e0, hi, _⟩ := InflateSync.sync_inv hv hio hsi
    rw [det e e0]; exact hi
  · obtain ⟨_, e0⟩ := InflateControl.inflateSyncPoint_inv hv
    rw [det e e0]; exact hv
  · obtain ⟨_, _, e0, hi, _⟩ := InflateWindow.setDict_inv adlerSafe hv hd hnb
    rw [det e e0]; exact hi
  · obtain ⟨_, _, e0, hi, _⟩ := InflateDict.getDict_inv hasLen hv hd hnb
    rw [det e e0]; exact hi
  · rcases hok with rfl | ⟨k, g, rfl, hg, _⟩
    · rw [getHeader_none hv e]; exact hv
    · obtain ⟨_, _, e0, hi, _⟩ := InflateControl.inflateGetHeader_inv hv k g hg
      rw [det e e0]; exact hi
  · obtain ⟨_, _, e0, hi, _⟩ := InflateReset.prime_inv hv bits value
    rw [det e e0]; exact hi
  · obtain ⟨_, _, _, _, _, e0, hi⟩ := InflateReset.reset_inv hv
    rw [det e e0]; exact hi
  · obtain ⟨_, _, _, _, _, e0, hi⟩ := InflateReset.resetKeep_inv hv
    rw [det e e0]; exact hi
  · rcases InflateReset.reset2_inv hv w with e0 | ⟨_, _, _, _, _, _, _, e0, hi⟩
    · rw [det e e0]; exact hv
    · rw [det e e0]; exact hi
  · obtain ⟨_, e0, hi, _⟩ := InflateControl.inflateValidate_inv hv c
    rw [det e e0]; exact hi
  · have e0 : C.run (inflateUndermine s v) h = .ok (Z_DATA_ERROR, h) := rfl
    rw [det e e0]; exact hv
  · obtain ⟨_, e0⟩ := InflateControl.inflateMark_inv hv
    rw [det e e0]; exact hv
  · obtain ⟨_, e0⟩ := InflateControl.inflateCodesUsed_inv hv
    rw [det e e0]; exact hv
  · exact (InflateCopy.copy_inv hv hdst hne e).1

/-- A successful `inflateInit2` on a stream ready for initialisation leaves the invariant. -/
theorem init2_inv' {h h' : Heap} {s : StreamPtr} {wb : Int32} (hi : InitReady h s)
    (e : inflateInit2 s wb h = .ok (Z_OK, h')) : Inv h' s := by
  rcases hi with rfl | ⟨z, ⟨i, rfl, hz⟩, hza, hzf⟩
  · exact absurd e (by simp [inflateInit2, Z_STREAM_ERROR, Z_OK])
  · exact InflateAlloc.init2_inv hz hza hzf wb e

/-- **The induction.** Every reachable stream has the structural invariant, given the pending preservation lemmas. -/
theorem reach_inv (P : Pending) {h : Heap} {s : StreamPtr} (hr : InflateReachable h s) : Inv h s := by
  induction hr with
  | init h h' s version size hi hv e =>
    obtain ⟨c, hc⟩ := InflateInit.checkVer_ok h version size hv
    cases c
    · simp only [C.run, inflateInit_, bind_app, hc, Bool.false_eq_true, ↓reduceIte] at e
      exact init2_inv' hi e
    · simp [C.run, inflateInit_, bind_app, hc, Z_VERSION_ERROR, Z_OK] at e
  | init2 h h' s wb version size hi hv e =>
    obtain ⟨c, hc⟩ := InflateInit.checkVer_ok h version size hv
    cases c
    · simp only [C.run, inflateInit2_, bind_app, hc, Bool.false_eq_true, ↓reduceIte] at e
      exact init2_inv' hi e
    · simp [C.run, inflateInit2_, bind_app, hc, Z_VERSION_ERROR, Z_OK] at e
  | copy h h' src dst _ hdst hne e ih => exact (InflateCopy.copy_inv ih hdst hne e).2 rfl
  | step h h' s _ hs ih => exact step_inv P ih hs
  | caller h h' s _ hc ih => exact caller_inv ih hc

/-! ## The registered goals, given `Pending`

These show that the goals close as soon as `Pending` is proved; they are not registered results. -/

open ZlibNgF.Spec.Safety

theorem stateIds_of {h : Heap} {i : Nat} {z : ZStream} {b : Nat} (hz : h.streams i = some z)
    (hb : z.state = some b) : stateIds h (some i) = [b] := by
  simp [stateIds, hz, hb]

/-- The frame of a call that changes stream `i` and the state of its block `b`. -/
theorem frame_setZS {h : Heap} {i : Nat} {z z' : ZStream} {b : Nat} {st' : InflateState}
    (hz : h.streams i = some z) (hb : z.state = some b) (hd : List Nat) (w : List (BPtr × Nat)) :
    Frame h (setZS h i z' b st') (streamIds (some i)) (stateIds h (some i)) hd w := by
  rw [stateIds_of hz hb]
  refine ⟨fun j hj => ?_, fun _ _ => rfl, fun b' _ hb' => ⟨?_, rfl⟩, fun _ _ _ data hd' => ⟨data, hd', rfl,
    fun _ _ _ => rfl⟩, fun _ _ _ hn => hn, rfl, rfl, rfl, rfl, Nat.le_refl _⟩
  · have : j ≠ i := by simpa [streamIds] using hj
    simp [setZS, this]
  · have : b' ≠ b := by simpa using hb'
    simp [setZS, this]

theorem inflateMark_safety_of (P : Pending) : Goal.inflateMark_safety := by
  intro h s _ hh
  rcases hh with hn | hn | hr
  · exact ⟨_, InflateControl.inflateMark_noState (Or.inl hn)⟩
  · exact ⟨_, InflateControl.inflateMark_noState (Or.inr hn)⟩
  · exact InflateControl.inflateMark_inv (reach_inv P hr)

theorem inflateSyncPoint_safety_of (P : Pending) : Goal.inflateSyncPoint_safety := by
  intro h s _ hh
  rcases hh with hn | hn | hr
  · exact InflateControl.inflateSyncPoint_noState (Or.inl hn)
  · exact InflateControl.inflateSyncPoint_noState (Or.inr hn)
  · exact InflateControl.inflateSyncPoint_inv (reach_inv P hr)

theorem inflateCodesUsed_safety_of (P : Pending) : Goal.inflateCodesUsed_safety := by
  intro h s _ hh
  rcases hh with hn | hn | hr
  · exact InflateControl.inflateCodesUsed_noState (Or.inl hn)
  · exact InflateControl.inflateCodesUsed_noState (Or.inr hn)
  · exact InflateControl.inflateCodesUsed_inv (reach_inv P hr)

theorem inflateReset_safety_of (P : Pending) : Goal.inflateReset_safety := by
  intro h s _ hh
  rcases hh with hn | hn | hr
  · exact ⟨_, _, InflateControl.inflateReset_noState (Or.inl hn), InflateInit.frame_refl h _ _ _ _⟩
  · exact ⟨_, _, InflateControl.inflateReset_noState (Or.inr hn), InflateInit.frame_refl h _ _ _ _⟩
  · obtain ⟨i, z, b, st, al, rfl, L, _, _⟩ := InflateInv.live (reach_inv P hr)
    exact ⟨_, _, InflateReset.reset_run L, frame_setZS L.hz L.hb _ _⟩

theorem inflateResetKeep_safety_of (P : Pending) : Goal.inflateResetKeep_safety := by
  intro h s _ hh
  rcases hh with hn | hn | hr
  · exact ⟨_, _, InflateControl.inflateResetKeep_noState (Or.inl hn), InflateInit.frame_refl h _ _ _ _⟩
  · exact ⟨_, _, InflateControl.inflateResetKeep_noState (Or.inr hn), InflateInit.frame_refl h _ _ _ _⟩
  · obtain ⟨i, z, b, st, al, rfl, L, _, _⟩ := InflateInv.live (reach_inv P hr)
    exact ⟨_, _, InflateReset.resetKeep_run L, frame_setZS L.hz L.hb _ _⟩

theorem inflateReset2_safety_of (P : Pending) : Goal.inflateReset2_safety := by
  intro h s w _ hh
  rcases hh with hn | hn | hr
  · exact ⟨_, _, InflateControl.inflateReset2_noState (Or.inl hn) w, InflateInit.frame_refl h _ _ _ _⟩
  · exact ⟨_, _, InflateControl.inflateReset2_noState (Or.inr hn) w, InflateInit.frame_refl h _ _ _ _⟩
  · obtain ⟨i, z, b, st, al, rfl, L, _, _⟩ := InflateInv.live (reach_inv P hr)
    rcases InflateReset.reset2_run L w with e | ⟨_, _, _, e⟩
    · exact ⟨_, _, e, InflateInit.frame_refl h _ _ _ _⟩
    · exact ⟨_, _, e, frame_setZS L.hz L.hb _ _⟩

theorem inflateGetDictionary_safety_of (P : Pending) : Goal.inflateGetDictionary_safety := by
  intro h s d hasLen _ hh hd hnb
  rcases hh with hn | hn | hr
  · exact ⟨_, _, InflateDict.getDict_noState (Or.inl hn) d hasLen, InflateInit.frame_refl h _ _ _ _⟩
  · exact ⟨_, _, InflateDict.getDict_noState (Or.inr hn) d hasLen, InflateInit.frame_refl h _ _ _ _⟩
  · obtain ⟨r, h', e, _, f⟩ := InflateDict.getDict_inv hasLen (reach_inv P hr) hd hnb
    exact ⟨r, h', e, f⟩

theorem inflateSetDictionary_safety_of (P : Pending) : Goal.inflateSetDictionary_safety := by
  intro h s d n _ hh hd hnb
  rcases hh with hn | hn | hr
  · exact ⟨_, _, InflateWindow.setDict_noState (Or.inl hn) d n, InflateInit.frame_refl h _ _ _ _⟩
  · exact ⟨_, _, InflateWindow.setDict_noState (Or.inr hn) d n, InflateInit.frame_refl h _ _ _ _⟩
  · obtain ⟨r, h', e, _, f⟩ := InflateWindow.setDict_inv adlerSafe (reach_inv P hr) hd hnb
    exact ⟨r, h', e, f⟩

theorem inflateSync_safety_of (P : Pending) : Goal.inflateSync_safety := by
  intro h s _ hh hio
  rcases hh with hn | hn | hr
  · exact ⟨_, _, InflateSync.sync_noState (Or.inl hn), InflateInit.frame_refl h _ _ _ _⟩
  · exact ⟨_, _, InflateSync.sync_noState (Or.inr hn), InflateInit.frame_refl h _ _ _ _⟩
  · obtain ⟨r, h', e, _, f⟩ := InflateSync.sync_inv (reach_inv P hr) (hio hr).1 (hio hr).2
    exact ⟨r, h', e, f⟩

theorem inflateCopy_safety_of (P : Pending) : Goal.inflateCopy_safety := by
  intro h dst src _ hfr hh hdst hne
  rcases hh with hn | hn | hr
  · exact ⟨_, _, InflateCopy.copy_noState (Or.inl hn) dst, InflateInit.frame_refl h _ _ _ _⟩
  · exact ⟨_, _, InflateCopy.copy_noState (Or.inr hn) dst, InflateInit.frame_refl h _ _ _ _⟩
  · exact InflateCopy.copy_safe (reach_inv P hr) hfr hdst hne

/-- A frame from agreement outside the named streams, blocks and headers. -/
theorem frame_of {h h' : Heap} {S B G : List Nat} (hs : ∀ i, i ∉ S → h'.streams i = h.streams i)
    (hg : ∀ k, k ∉ G → h'.gzheaders k = h.gzheaders k)
    (hb : ∀ b, b ∉ B → h'.istates b = h.istates b ∧ h'.iallocs b = h.iallocs b ∧ h'.bytes b = h.bytes b)
    (hc : h'.consts = h.consts) (hcrc : h'.crcTable = h.crcTable) (hx : h'.x2nTable = h.x2nTable)
    (hbase : h'.baseAddr = h.baseAddr) (hn : h.nextBlk ≤ h'.nextBlk) : Frame h h' S B G [] :=
  ⟨hs, hg, fun b _ hb' => ⟨(hb b hb').1, (hb b hb').2.1⟩, fun b _ hb' d hd => ⟨d, by rw [(hb b hb').2.2]; exact hd,
    rfl, fun _ _ _ => rfl⟩, fun b _ hb' hn' => by rw [(hb b hb').2.2]; exact hn', hc, hcrc, hx, hbase, hn⟩

theorem inflatePrime_safety_of (P : Pending) : Goal.inflatePrime_safety := by
  intro h s bits value _ hh
  rcases hh with hn | hn | hr
  · exact ⟨_, _, InflateControl.inflatePrime_noState (Or.inl hn) bits value, InflateInit.frame_refl h _ _ _ _⟩
  · exact ⟨_, _, InflateControl.inflatePrime_noState (Or.inr hn) bits value, InflateInit.frame_refl h _ _ _ _⟩
  · obtain ⟨r, h', e, _, hor⟩ := InflateReset.prime_inv (reach_inv P hr) bits value
    refine ⟨r, h', e, ?_⟩
    rcases hor with he | ⟨b, st', ⟨z, ⟨i, rfl, hz⟩, hzb⟩, rfl⟩
    · rw [he]; exact InflateInit.frame_refl h _ _ _ _
    · rw [stateIds_of hz hzb]
      exact frame_of (fun _ _ => rfl) (fun _ _ => rfl)
        (fun c hc => ⟨upd_ne _ _ _ _ (by simpa using hc), rfl, rfl⟩) rfl rfl rfl rfl (Nat.le_refl _)

theorem inflateValidate_safety_of (P : Pending) : Goal.inflateValidate_safety := by
  intro h s check _ hh
  rcases hh with hn | hn | hr
  · exact ⟨_, _, InflateControl.inflateValidate_noState (Or.inl hn) check, InflateInit.frame_refl h _ _ _ _⟩
  · exact ⟨_, _, InflateControl.inflateValidate_noState (Or.inr hn) check, InflateInit.frame_refl h _ _ _ _⟩
  · obtain ⟨h', e, _, b, ⟨z, ⟨i, rfl, hz⟩, hzb⟩, he⟩ := InflateControl.inflateValidate_inv (reach_inv P hr) check
    refine ⟨_, h', e, ?_⟩
    rw [stateIds_of hz hzb]
    have hi : h'.istates = upd h.istates b (h'.istates b) := by
      have := congrArg Heap.istates he; exact this
    refine frame_of (fun _ _ => by rw [he]) (fun _ _ => by rw [he]) (fun c hc => ⟨?_, by rw [he], by rw [he]⟩)
      (by rw [he]) (by rw [he]) (by rw [he]) (by rw [he]) (by rw [he]; exact Nat.le_refl _)
    rw [hi]; exact upd_ne _ _ _ _ (by simpa using hc)

theorem inflateGetHeader_safety_of (P : Pending) : Goal.inflateGetHeader_safety := by
  intro h s hp _ hh hpn hok
  rcases hok with hn | ⟨k, g, rfl, hg, -⟩
  · exact absurd hn hpn
  rcases hh with hn | hn | hr
  · exact ⟨_, _, InflateControl.inflateGetHeader_noState (Or.inl hn) _, InflateInit.frame_refl h _ _ _ _⟩
  · exact ⟨_, _, InflateControl.inflateGetHeader_noState (Or.inr hn) _, InflateInit.frame_refl h _ _ _ _⟩
  · obtain ⟨r, h', e, _, hor⟩ := InflateControl.inflateGetHeader_inv (reach_inv P hr) k g hg
    refine ⟨r, h', e, ?_⟩
    rcases hor with he | ⟨b, st', ⟨z, ⟨i, rfl, hz⟩, hzb⟩, rfl⟩
    · rw [he]; exact InflateInit.frame_refl h _ _ _ _
    · rw [stateIds_of hz hzb]
      exact frame_of (fun _ _ => rfl) (fun c hc => upd_ne _ _ _ _ (by simpa using hc))
        (fun c hc => ⟨upd_ne _ _ _ _ (by simpa using hc), rfl, rfl⟩) rfl rfl rfl rfl (Nat.le_refl _)

theorem inflateEnd_safety_of (P : Pending) : Goal.inflateEnd_safety := by
  intro h s _ hh
  rcases hh with hn | hn | hr
  · exact ⟨_, _, InflateControl.inflateEnd_noState (Or.inl hn), InflateInit.frame_refl h _ _ _ _⟩
  · exact ⟨_, _, InflateControl.inflateEnd_noState (Or.inr hn), InflateInit.frame_refl h _ _ _ _⟩
  · obtain ⟨i, z, b, rfl, hz, hzb, e⟩ := InflateControl.inflateEnd_inv (reach_inv P hr)
    refine ⟨_, _, e, ?_⟩
    rw [stateIds_of hz hzb]
    exact frame_of (fun c hc => upd_ne _ _ _ _ (by simpa [streamIds] using hc)) (fun _ _ => rfl)
      (fun c hc => ⟨rfl, rfl, upd_ne _ _ _ _ (by simpa using hc)⟩) rfl rfl rfl rfl (Nat.le_refl _)

end ZlibNgF.Proof.InflateReach
