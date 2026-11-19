import ZlibNgF.Proof.«deflate.c.init»

/-!
# `deflateReset`, `deflateResetKeep` on an invariant stream (`ZlibNgF`)

From the runs on `SH` heaps in `Proof/deflate.c.init.lean`: on a stream with the structural invariant both calls
return `Z_OK`, keep the invariant and change only the stream record and the stream's block; on a stream that the
state check rejects they return `Z_STREAM_ERROR` and change nothing.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.DeflateReset
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.InflateSync (Sat)
open ZlibNgF.Proof.InflateInv (upd_upd)

theorem upd_self {β : Type} (t : Tbl (Option β)) (k : Nat) (v : β) (h : t k = some v) : upd t k (some v) = t := by
  have hk : k < t.arr.size := Tbl.lt_size_of_get_ne t k (by rw [h]; simp [default])
  unfold upd Tbl.set
  simp only [hk, ite_true]
  congr 1
  apply Array.ext_getElem?
  intro x
  simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  split
  · rename_i e; subst e
    have := h; simp only [Tbl.get_eq] at this
    rw [Array.getElem?_eq_getElem hk] at this ⊢
    simp at this; simp [this]
  · rfl

theorem SH_self {h : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8}
    (hz : h.streams i = some z) (hs : h.dstates b = some st) (hd : h.bytes b = some d) : SH h i z b st d = h := by
  simp only [SH, upd_self _ _ _ hz, upd_self _ _ _ hs, upd_self _ _ _ hd]

theorem dframe_SH (h : Heap) (i : Nat) (z : ZStream) (b : Nat) (st : DeflateState) (d : Array UInt8) :
    DFrame h (SH h i z b st d) [i] [b] [] [] := by
  refine ⟨⟨fun j hj => ?_, fun _ _ => rfl, fun c _ hc => ⟨rfl, rfl⟩, fun c _ hc data hd => ⟨data, ?_, rfl,
    fun _ _ _ => rfl⟩, fun c _ hc hn => ?_, rfl, rfl, rfl, rfl, Nat.le_refl _⟩, fun c _ hc => ⟨?_, rfl⟩⟩
  · simp only [SH]; exact upd_ne _ _ _ _ (by simpa using hj)
  · simp only [SH]; rw [upd_ne _ _ _ _ (by simpa using hc)]; exact hd
  · simp only [SH]; rw [upd_ne _ _ _ _ (by simpa using hc)]; exact hn
  · simp only [SH]; exact upd_ne _ _ _ _ (by simpa using hc)

/-- What `deflateReset` / `deflateResetKeep` leave: `Z_OK`, the invariant, and a change of the stream record and
the stream's block only. -/
def ResetPost (h : Heap) (i b : Nat) (r : Int32) (h' : Heap) : Prop :=
  r = Z_OK ∧ DInv h' (some i) ∧ DFrame h h' [i] [b] [] []

theorem reset_inv {h : Heap} {s : StreamPtr} (hv : DInv h s) :
    ∃ i z b, s = some i ∧ h.streams i = some z ∧ z.state = some b ∧
      Sat h (deflateReset s) (fun r h' => ResetPost h i b r h') := by
  obtain ⟨i, z, b, st, al, rfl, L, hal, c⟩ := live hv
  obtain ⟨pb, hpb⟩ := c.pbuf
  obtain ⟨ho, d, hd, hh, hho⟩ := c.head
  have hda : h.dallocs b = some al := by simpa [Heap.dallocsOf, hd] using hal
  refine ⟨i, z, b, rfl, L.hz, L.hb, ?_⟩
  rw [← SH_self L.hz L.hst hd]
  refine Sat.mono (reset_SH ⟨L.za, L.zf, L.hb, L.ab, L.sm, L.lo, L.hi⟩ c.wrap hpb c.trees.1 c.trees.2.1 c.trees.2.2
    hh hho c.level.1 c.level.2) ?_
  rintro r h' ⟨rfl, A, B, C, cf, lm, ib, d', rfl, hd', hA, hB, hC⟩
  refine ⟨rfl, ⟨i, rkZ z st.wrap, b, lmS (trS b (rkS st) A B C) cf lm ib, al, rfl, by simp [SH], L.hb,
    by simp [Heap.dstate, SH], ?_, ?_⟩, ?_⟩
  · simp [Heap.dallocsOf, SH, hda]
  · exact {
      zalloc := c.zalloc
      zfree := c.zfree
      strm := c.strm
      alloc_bufs := c.alloc_bufs
      al_state := c.al_state
      al_zfree := c.al_zfree
      al_buf := c.al_buf
      status_lo := st_lo _
      status_hi := st_hi _
      wrap := c.wrap
      gzhead := ⟨_, rfl⟩
      w_size := c.w_size
      pbuf := ⟨pb, hpb⟩
      head := ⟨ho, d', (by simp [SH]), hh, (by omega)⟩
      level := c.level
      trees := ⟨hA, hB, hC⟩ }
  · rw [SH_self L.hz L.hst hd]
    exact dframe_SH _ _ _ _ _ _

theorem resetKeep_inv {h : Heap} {s : StreamPtr} (hv : DInv h s) :
    ∃ i z b, s = some i ∧ h.streams i = some z ∧ z.state = some b ∧
      Sat h (deflateResetKeep s) (fun r h' => ResetPost h i b r h') := by
  obtain ⟨i, z, b, st, al, rfl, L, hal, c⟩ := live hv
  obtain ⟨pb, hpb⟩ := c.pbuf
  obtain ⟨ho, d, hd, hh, hho⟩ := c.head
  have hda : h.dallocs b = some al := by simpa [Heap.dallocsOf, hd] using hal
  refine ⟨i, z, b, rfl, L.hz, L.hb, ?_⟩
  rw [← SH_self L.hz L.hst hd]
  refine Sat.mono (resetKeep_SH ⟨L.za, L.zf, L.hb, L.ab, L.sm, L.lo, L.hi⟩ c.wrap hpb c.trees.1 c.trees.2.1
    c.trees.2.2) ?_
  rintro r h' ⟨rfl, A, B, C, rfl, hA, hB, hC⟩
  refine ⟨rfl, ⟨i, rkZ z st.wrap, b, trS b (rkS st) A B C, al, rfl, by simp [SH], L.hb,
    by simp [Heap.dstate, SH], ?_, ?_⟩, ?_⟩
  · simp [Heap.dallocsOf, SH, hda]
  · exact {
      zalloc := c.zalloc
      zfree := c.zfree
      strm := c.strm
      alloc_bufs := c.alloc_bufs
      al_state := c.al_state
      al_zfree := c.al_zfree
      al_buf := c.al_buf
      status_lo := st_lo _
      status_hi := st_hi _
      wrap := c.wrap
      gzhead := ⟨_, rfl⟩
      w_size := c.w_size
      pbuf := ⟨pb, hpb⟩
      head := ⟨ho, d, (by simp [SH]), hh, hho⟩
      level := c.level
      trees := ⟨hA, hB, hC⟩ }
  · rw [SH_self L.hz L.hst hd]
    exact dframe_SH _ _ _ _ _ _

theorem resetKeep_noState {h : Heap} {s : StreamPtr} (hn : DNoState h s) :
    deflateResetKeep s h = .ok (Z_STREAM_ERROR, h) := by
  simp only [deflateResetKeep, bind_app, stateCheck_noState hn, ↓reduceIte]; rfl

theorem reset_noState {h : Heap} {s : StreamPtr} (hn : DNoState h s) :
    deflateReset s h = .ok (Z_STREAM_ERROR, h) := by
  simp only [deflateReset, bind_app, resetKeep_noState hn]; rfl

end ZlibNgF.Proof.DeflateReset
