import ZlibNgF.Proof.«infback.c.init»

/-!
# The call-back decoder: `inflateBackInit_` safety and the non-vacuity of the `inflateBack` premises (`ZlibNgF`)

`Goal.inflateBackInit__safety` is in `Proof/infback.c.init.lean`. Here: a heap with a zero `z_stream` whose `next_in`
holds one byte, a 256-byte window, `inflateBackInit_` with `windowBits` 8 and the library's version, and call-backs
that hand out nothing (`in()` returns 0, `out()` returns 0). The invariant `I` says that no more input will come and
that the chunk is either empty or the one byte of the first buffer, which stays allocated.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.Infback
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Inflate ZlibNg.Infback ZlibNgF.Proof.InfbackInit

/-- The first input buffer: block 1, one byte. -/
def inp : BPtr := .ref (.heap 1) 0
/-- The window: block 0, 256 bytes. -/
def win : BPtr := .ref (.heap 0) 0

/-- The starting heap. -/
def backHeap : Heap :=
  { streams := upd .empty 0 (some ({ next_in := inp, avail_in := 1 } : ZStream))
    bytes := upd (upd .empty 0 (some (Array.replicate 256 0))) 1 (some #[0])
    nextBlk := 2 }

/-- `in()` that has no input. -/
def inNone : InCb := fun _ cur => pure (0, cur)
/-- `out()` that accepts everything. -/
def outOk : OutCb := fun _ _ _ => pure 0

/-- The invariant of the call-backs (see the module comment). -/
def backI (h : Heap) (p : BPtr) (m t : Nat) : Prop :=
  t = 0 ∧ 1 < h.nextBlk ∧ (m = 0 ∨ (p = inp ∧ m = 1 ∧ ∃ d, h.bytes 1 = some d ∧ 1 ≤ d.size))

theorem keep_refl (h : Heap) (i b : Nat) (w : BPtr) : BackKeep h h i b w :=
  ⟨rfl, rfl, rfl, rfl, fun _ _ d _ hd => ⟨d, hd, rfl⟩, rfl, Nat.le_refl _⟩

theorem callbacks (n : Nat) : BackCallbacks 0 2 win n inNone .null outOk .null backI where
  chunk := by
    intro h p m t ⟨_, _, hm⟩ hm0
    rcases hm with hm | ⟨rfl, rfl, d, hd, hs⟩
    · exact absurd hm hm0
    · refine ⟨⟨.heap 1, 0, d, rfl, hd, by omega⟩, Or.inl (by simp), ?_⟩
      intro off e
      simp [inp] at e
  stable := by
    intro h h' p m t ⟨ht, hn, hm⟩ f hnb
    refine ⟨ht, by omega, ?_⟩
    rcases hm with hm | ⟨hp, hm1, d, hd, hs⟩
    · exact Or.inl hm
    · obtain ⟨d', hd', hsz, -⟩ := f.2.2.2.1 1 hn (by simp) d hd
      exact Or.inr ⟨hp, hm1, d', hd', by omega⟩
  input := by
    intro h cur p m t ⟨ht, hn, _⟩
    exact ⟨0, cur, h, rfl, by simp, ⟨by simp [ht], hn, Or.inl rfl⟩, keep_refl h 0 2 win⟩
  output := by
    intro h len p m t _ hI
    exact ⟨0, h, rfl, hI, keep_refl h 0 2 win⟩

theorem fresh : FreshBlocks backHeap := by
  intro b hb
  have h0 : b ≠ 0 := by simp [backHeap] at hb; omega
  have h1 : b ≠ 1 := by simp [backHeap] at hb; omega
  refine ⟨Tbl.get_empty_opt b, Tbl.get_empty_opt b, ?_⟩
  show upd (upd .empty 0 _) 1 _ b = none
  rw [upd_ne _ _ _ _ h1, upd_ne _ _ _ _ h0, Tbl.get_empty_opt]

theorem backHeap_b0 : backHeap.bytes 0 = some (Array.replicate 256 0) := by
  show upd (upd .empty 0 _) 1 _ 0 = _
  rw [upd_ne _ _ _ _ (by decide), upd_same]

theorem backHeap_b1 : backHeap.bytes 1 = some #[0] := upd_same _ _ _

/-- The witness on every heap with the stream, the window and the input buffer of `backHeap`. -/
theorem nonvac_gen (h : Heap) (hz : h.streams 0 = some ({ next_in := inp, avail_in := 1 } : ZStream))
    (hb0 : h.bytes 0 = some (Array.replicate 256 0)) (hb1 : h.bytes 1 = some #[0]) (hn : h.nextBlk = 2)
    (hfr : FreshBlocks h) (hok : h.allocOk h.nalloc = true) : Goal.inflateBack_nonvacuous := by
  obtain ⟨H1, e, f, z', hz', hst, hni, hai⟩ := backInit_ok hz (Or.inl rfl) (Or.inl rfl) hfr hok 8 win
    (by simp [win]) (by decide) (by decide)
  have hc : CHECK_VER_STSIZE (.ref (.str 0) 0) 112 h = .ok (false, h) := rfl
  have hrun : C.run (inflateBackInit_ (some 0) 8 win (.ref (.str 0) 0) 112) h = .ok (Z_OK, H1) := by
    simp only [C.run, inflateBackInit_, bind_app, hc, Bool.false_eq_true, ↓reduceIte]
    exact e
  have hreach : BackReachable H1 (some 0) win (2 ^ (8 : Int32).toInt.toNat) := by
    refine BackReachable.init h H1 (some 0) 8 win (.ref (.str 0) 0) 112
      (Or.inr ⟨_, ⟨0, rfl, hz⟩, Or.inl rfl, Or.inl rfl⟩) (Or.inr ⟨.str 0, 0, _, rfl, rfl, ?_⟩) ?_ hrun
    · simp [Heap.litBytes]
    · exact ⟨0, 0, Array.replicate 256 0, rfl, hb0, by rw [Array.size_replicate]; decide⟩
  have hnb : h.nextBlk ≤ H1.nextBlk := f.2.2.2.2.2.2.2.2.2
  obtain ⟨d1, hd1, hsz1, -⟩ := f.2.2.2.1 1 (by omega) (by simp) #[0] hb1
  have hni' : z'.next_in = inp := hni
  have hnn : z'.next_in ≠ .null := by rw [hni']; simp [inp]
  have hav : z'.avail_in = 1 := hai
  rw [hn] at hst
  refine ⟨H1, some 0, win, _, z', inNone, .null, outOk, .null, backI, hreach, ?_, ⟨0, rfl, hz'⟩, hnn,
    by rw [hav]; decide⟩
  refine ⟨0, z', 2, 0, rfl, hz', hst, callbacks _, ?_, ?_⟩
  · simp only [hnn, ↓reduceIte, hav]
    exact ⟨rfl, by omega, Or.inr ⟨hni', rfl, d1, hd1, by simp [hsz1]⟩⟩
  · simp only [hnn, ↓reduceIte, hav]; decide

theorem inflateBack_nonvacuous : Goal.inflateBack_nonvacuous :=
  nonvac_gen backHeap (upd_same _ _ _) backHeap_b0 backHeap_b1 rfl fresh rfl

end ZlibNgF.Proof.Infback
