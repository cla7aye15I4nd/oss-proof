import ZlibNgF.Proof.«gzlib.c.open»
import ZlibNgF.Proof.«public-uncompress»

/-!
# The safety of `gzopen`, `gzopen64` and `gzdopen` (`ZlibNgF`)

`gzopen` and `gzopen64` are `gz_open(path, -1, mode)` (`gz_open_spec`). `gzdopen` formats `"<fd:%d>"` into a local
`char path[32]`, calls `gz_open(path, fd, mode)` and ends the local array.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.GzOpenPublic
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Gz ZlibNgF.Proof.GzSat ZlibNgF.Proof.GzOpen ZlibNgF.Proof.GzInv

theorem gzopen_spec {w : World} {h : Heap} (hwf : GzWF w h) (path mode : BPtr) (hp : path = .null ∨ CStr h path)
    (hm : mode = .null ∨ CStr h mode) : GSat w h (gzopen path mode) (OpenPost w h) :=
  gz_open_spec hwf path mode (-1) hp hm

theorem gzopen64_spec {w : World} {h : Heap} (hwf : GzWF w h) (path mode : BPtr) (hp : path = .null ∨ CStr h path)
    (hm : mode = .null ∨ CStr h mode) : GSat w h (gzopen64 path mode) (OpenPost w h) :=
  gz_open_spec hwf path mode (-1) hp hm

theorem gzopen_safety : Goal.gzopen_safety := by
  intro w h path mode hwf hp hm
  obtain ⟨r, w', h', e, q⟩ := gzopen_spec hwf path mode hp hm
  exact ⟨r, w', h', e, q.2.1, q.1⟩

theorem gzopen64_safety : Goal.gzopen64_safety := by
  intro w h path mode hwf hp hm
  obtain ⟨r, w', h', e, q⟩ := gzopen64_spec hwf path mode hp hm
  exact ⟨r, w', h', e, q.2.1, q.1⟩

/-! ## `gzdopen` -/

/-- A zero byte in an object ends a C string there or before. -/
theorem cstr_of_zero {h : Heap} {r : BRef} {off : Nat} {d : Array UInt8} (hd : Space.get h r = some d) :
    ∀ j, off + j < d.size → d[off + j]! = 0 → CStr h (.ref r off) := by
  intro j
  refine Nat.strongRecOn j ?_
  intro j ih hj hz
  by_cases hex : ∃ i, i < j ∧ d[off + i]! = 0
  · obtain ⟨i, hi, hzi⟩ := hex
    exact ih i hi (by omega) hzi
  · exact ⟨j, r, off, d, rfl, hd, by omega, hz, fun i hi e => hex ⟨i, hi, e⟩⟩

/-- The heap with the local array `char path[32]`. -/
def locH (h : Heap) : Heap :=
  { h with
    bytes := upd h.bytes h.nextBlk (some (Array.ofFn (n := 32) fun i => Junk.of (h.garbage (2 ^ 41 + h.nextBlk) i.val)))
    nextBlk := h.nextBlk + 1 }

theorem localBlock_32 (h : Heap) : localBlock 32 h = .ok (.ref (.heap h.nextBlk) 0, locH h) := rfl

/-- The heap after `snprintf(path, 32, "<fd:%d>", fd)`: a string in the local array. -/
theorem snprintfFd_ok (h : Heap) (fd : Int32) : ∃ r H, snprintfFd (.ref (.heap h.nextBlk) 0) 32 fd (locH h) = .ok (r, H) ∧
    (∀ c, c ≠ h.nextBlk → H.bytes c = h.bytes c) ∧ (∃ d, H.bytes h.nextBlk = some d ∧ d.size = 32) ∧
    CStr H (.ref (.heap h.nextBlk) 0) ∧ H.nextBlk = h.nextBlk + 1 ∧ HSame h H ∧ H.streams = h.streams := by
  generalize hout : (s!"<fd:{fd.toInt}>".toUTF8.data : Array UInt8) = out
  let arr : Array UInt8 := Array.ofFn (n := 32) fun i => Junk.of (h.garbage (2 ^ 41 + h.nextBlk) i.val)
  have ha : (locH h).bytes h.nextBlk = some arr := by simp [locH, arr]
  have hk : min out.size 31 ≤ 31 := Nat.min_le_right _ _
  have hbs : ((out.extract 0 (min out.size 31)).push 0).size = min out.size 31 + 1 := by simp
  have est := storeBytes_heap (h := locH h) (c := h.nextBlk) (off := 0) (cap := 32)
    (bs := (out.extract 0 (min out.size 31)).push 0) ha (by simp [arr]) (by omega)
  refine ⟨if out.size < 2 ^ 31 then Int32.ofNat out.size else -1,
    { locH h with
      bytes := (locH h).bytes.modify h.nextBlk (Option.map fun _ => stored arr ((out.extract 0 (min out.size 31)).push 0) 0) },
    by simp only [snprintfFd]; rw [hout]; simp [snprintfOut, est], ?_⟩
  have hget : ∀ x, ((locH h).bytes.modify h.nextBlk (Option.map fun _ => stored arr ((out.extract 0 (min out.size 31)).push 0) 0)) x =
      if x = h.nextBlk then some (stored arr ((out.extract 0 (min out.size 31)).push 0) 0) else (locH h).bytes x :=
    modify_some _ _ _ _ ha
  have hsz : (stored arr ((out.extract 0 (min out.size 31)).push 0) 0).size = 32 := by
    rw [stored_size _ _ _ (by simp [arr]; omega)]; simp [arr]
  refine ⟨fun c hc => by simp only [hget]; simp [hc, locH, upd_ne _ _ _ _ hc], ⟨_, by simp only [hget]; simp, hsz⟩,
    cstr_of_zero (d := stored arr ((out.extract 0 (min out.size 31)).push 0) 0) (by show Heap.getBytes _ (.heap h.nextBlk) = _; simp only [Heap.getBytes]; rw [hget]; simp)
      (min out.size 31) (by simp only [Nat.zero_add]; omega) ?_, rfl,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  rw [Nat.zero_add, stored_get _ _ _ (by simp [arr]; omega)]
  simp [hbs, Array.getElem_push]

/-- The world after the local array is made and filled. -/
theorem wf_local {w : World} {h HS : Heap} (hwf : GzWF w h) (hby : ∀ c, c ≠ h.nextBlk → HS.bytes c = h.bytes c)
    (hdL : ∃ d, HS.bytes h.nextBlk = some d ∧ d.size = 32) (hn : HS.nextBlk = h.nextBlk + 1) (same : HSame h HS)
    (hstr : HS.streams = h.streams) : GzWF w HS := by
  obtain ⟨dL, hdL, hdLs⟩ := hdL
  refine gzWF_mk ⟨by rw [same.crc]; exact hwf.1.1, by rw [same.x2n]; exact hwf.1.2⟩
    ⟨fun c hc => ⟨by rw [same.istates]; exact (hwf.2.1.1 c (by omega)).1, by rw [same.iallocs]; exact (hwf.2.1.1 c (by omega)).2.1,
      by rw [hby c (by omega)]; exact (hwf.2.1.1 c (by omega)).2.2⟩,
     fun c hc => ⟨by rw [same.dstates]; exact (hwf.2.1.2 c (by omega)).1, by rw [same.dallocs]; exact (hwf.2.1.2 c (by omega)).2⟩⟩
    (objBound_old hwf.2.2.1 same.consts fun c d hd => ?_) (fun c hc => hwf.2.2.2.1 c (by omega)) (fun c s hs => ?_)
    (fsWF_of hwf)
  · by_cases e : c = h.nextBlk
    · subst e; rw [hdL] at hd; cases hd; exact Or.inr (by omega)
    · rw [hby c e] at hd; exact Or.inl hd
  · by_cases e : c = h.nextBlk
    · subst e; unfold World.gz at hs; rw [hdL, gzs_beyond hwf] at hs; cases hs
    · rw [gz_of_bytes (hby c e)] at hs; rw [hstr]; exact hwf.2.2.2.2.1 c s hs

/-- The end of `gzdopen`: the local array is gone. -/
theorem post_drop {w : World} {h HS : Heap} {r : GzPtr} {W : World} {H : Heap} (hwf : GzWF w h)
    (hby : ∀ c, c ≠ h.nextBlk → HS.bytes c = h.bytes c) (hn : HS.nextBlk = h.nextBlk + 1) (same : HSame h HS)
    (hstr : HS.streams = h.streams) (q : OpenPost w HS r W H) :
    OpenPost w h r W { H with bytes := upd H.bytes h.nextBlk none } := by
  obtain ⟨wf2, ⟨⟨⟨_, g1, i1, b1, n1, _, c1, x1, a1, k1⟩, d1⟩, s1, cs1, gz1⟩, succ⟩ := q
  have hL : W.gzs h.nextBlk = none := by rw [gz1 _ (by omega)]; exact gzs_beyond hwf
  have hgz : ∀ c, c ≠ h.nextBlk → W.gz { H with bytes := upd H.bytes h.nextBlk none } c = W.gz H c :=
    fun c e => gz_of_bytes (by simp [upd_ne _ _ _ _ e])
  refine ⟨gzWF_mk wf2.1 ⟨fun c hc => ⟨(wf2.2.1.1 c hc).1, (wf2.2.1.1 c hc).2.1, ?_⟩, wf2.2.1.2⟩
    (objBound_old wf2.2.2.1 rfl fun c d hd => ?_) wf2.2.2.2.1 (fun c s hs => ?_) (fsWF_of wf2),
    ⟨⟨⟨fun _ _ => rfl, fun k hk => by rw [g1 k hk, same.gzheaders], fun c hc hn' => ?_, fun c hc hn' d hd => ?_,
      fun c hc hn' hd => ?_, rfl, by rw [c1, same.crc], by rw [x1, same.x2n], by rw [a1, same.base], by have := k1; simp only at this ⊢; omega⟩,
      fun c hc hn' => ?_⟩, fun j z hz => s1 j z (by rw [hstr]; exact hz), fun k a e => cs1 k a (by rw [same.consts]; exact e),
      fun c hc => by rw [gz1 c (by omega)]⟩, fun b e => ?_⟩
  · by_cases e : c = h.nextBlk
    · subst e; simp
    · simp only; rw [upd_ne _ _ _ _ e]; exact (wf2.2.1.1 c hc).2.2
  · by_cases e : c = h.nextBlk
    · subst e; simp at hd
    · simp only at hd; rw [upd_ne _ _ _ _ e] at hd; exact Or.inl hd
  · by_cases e : c = h.nextBlk
    · subst e; unfold World.gz at hs; simp at hs
    · rw [hgz c e] at hs; exact wf2.2.2.2.2.1 c s hs
  · obtain ⟨e1, e2⟩ := i1 c (by omega) hn'
    exact ⟨by rw [e1, same.istates], by rw [e2, same.iallocs]⟩
  · have hne : c ≠ h.nextBlk := by omega
    obtain ⟨d', e1, e2, e3⟩ := b1 c (by omega) hn' d (by rw [hby c hne]; exact hd)
    exact ⟨d', by simp only; rw [upd_ne _ _ _ _ hne]; exact e1, e2, e3⟩
  · have hne : c ≠ h.nextBlk := by omega
    simp only; rw [upd_ne _ _ _ _ hne]; exact n1 c (by omega) hn' (by rw [hby c hne]; exact hd)
  · obtain ⟨e1, e2⟩ := d1 c (by omega) hn'
    exact ⟨by rw [e1, same.dstates], by rw [e2, same.dallocs]⟩
  · obtain ⟨⟨b0, s, e0, hs, sh, hnd⟩, s', hs', hnone, hsz, hmsg, c, hpc, hc⟩ := succ b e
    cases e0
    rw [hs] at hs'; cases hs'
    have hcL : c ≠ h.nextBlk := by omega
    have hbL : b ≠ h.nextBlk := by
      intro e2; subst e2; unfold World.gz at hs; rw [hL] at hs; split at hs <;> cases hs
    have hs2 : W.gz { H with bytes := upd H.bytes h.nextBlk none } b = some s := by rw [hgz b hbL]; exact hs
    refine ⟨⟨b, s, rfl, hs2, ?_, hnd⟩, s, hs2, by rw [← hstr]; exact hnone, hsz, hmsg, c, hpc, by omega⟩
    obtain ⟨c', n', e', hcs'⟩ := sh.path
    rw [hpc] at e'; cases e'
    obtain ⟨r', off', d', e1, e2, e3⟩ := hcs'
    cases e1
    have hsz0 : ¬ s.size ≠ 0 := fun e => e hsz
    refine ⟨sh.mode, ⟨c, n', hpc, .heap c, 0, d', rfl, by show (upd H.bytes h.nextBlk none) c = _; rw [upd_ne _ _ _ _ hcL]; exact e2, e3⟩,
      sh.strm, sh.want_lo, sh.want_hi, sh.size, sh.pos, ⟨Or.inl hmsg, fun _ => hmsg⟩,
      fun hr => ⟨(sh.read hr).how, fun e => absurd e hsz0, (sh.read hr).nobuf, (sh.read hr).skip_have⟩, fun _ => ⟨fun e => absurd e hsz0⟩,
      fun hz c2 hc2 => ?_⟩
    show (upd H.bytes h.nextBlk none) c2 = none
    by_cases e : c2 = h.nextBlk
    · rw [e]; simp
    · rw [upd_ne _ _ _ _ e]; exact sh.dead hz c2 hc2

theorem gzdopen_spec {w : World} {h : Heap} (hwf : GzWF w h) (fd : Int32) (mode : BPtr)
    (hm : mode = .null ∨ CStr h mode) : GSat w h (gzdopen fd mode) (OpenPost w h) := by
  unfold gzdopen
  by_cases e : (fd == -1) = true
  · simp only [e, ite_true]
    exact GSat.pure (post_refl hwf h.nalloc)
  · simp only [e, Bool.false_eq_true, ite_false]
    refine GSat.bind (GSat.lm ⟨_, _, localBlock_32 h, ?_⟩)
    obtain ⟨r, HS, eS, hby, hdL, hcs, hnS, sameS, hstrS⟩ := snprintfFd_ok h fd
    refine GSat.bind (GSat.lm ⟨_, _, eS, ?_⟩)
    have wfS := wf_local hwf hby hdL hnS sameS hstrS
    have hmS : mode = .null ∨ CStr HS mode := by
      rcases hm with e | ⟨n, hcs⟩
      · exact Or.inl e
      · refine Or.inr ⟨n, cstr_of_get (fun r d hd => ?_) hcs⟩
        cases r with
        | heap c =>
          have hc : c < h.nextBlk := by
            refine Nat.lt_of_not_le fun hc => ?_
            have := (hwf.2.1.1 c hc).2.2
            have hd' : h.bytes c = some d := hd
            rw [this] at hd'; cases hd'
          show HS.bytes c = some d
          rw [hby c (by omega)]; exact hd
        | const c => show HS.consts c = some d; rw [sameS.consts]; exact hd
        | str k => exact hd
    refine GSat.bind (GSat.mono (gz_open_spec wfS _ mode fd (Or.inr hcs) hmS) fun r W H q => ?_)
    obtain ⟨dL, hdL', -⟩ := hdL
    obtain ⟨d', e1, -, -⟩ := q.2.1.1.1.2.2.2.1 h.nextBlk (by omega) (by simp) dL hdL'
    refine GSat.bind (GSat.lm ⟨(), _, Uncompress.dropLocal_app e1, ?_⟩)
    exact GSat.pure (post_drop hwf hby hnS sameS hstrS q)

theorem gzdopen_safety : Goal.gzdopen_safety := by
  intro w h fd mode hwf hm
  obtain ⟨r, w', h', e, q⟩ := gzdopen_spec hwf fd mode hm
  exact ⟨r, w', h', e, q.2.1, q.1⟩

/-! ## A successful opening call leaves the invariant -/

theorem open_inv {m : G GzPtr} {w : World} {h : Heap} {f : GzPtr} {w' : World} {h' : Heap}
    (hs : GSat w h m (OpenPost w h)) (e : GzRun m w h f w' h') (hne : f ≠ none) : GzInv w' h' f ∧ GzWF w' h' := by
  obtain ⟨r, w2, h2, e2, q⟩ := hs
  have e' : m w h = .ok ((f, w'), h') := e
  rw [e2] at e'
  cases e'
  cases f with
  | none => exact absurd rfl hne
  | some b => exact ⟨(q.2.2 b rfl).1, q.1⟩

end ZlibNgF.Proof.GzOpenPublic
