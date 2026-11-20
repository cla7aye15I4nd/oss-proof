import ZlibNgF.Proof.«public-inflate-control»
import ZlibNgF.Proof.«public-inflate-init»

/-!
# `inflateGetDictionary` (`ZlibNgF`)

The run of `Ptr.memcpy` into a heap block (`memcpy_heap`): the destination block gets an array of the same size that
differs from the old one only in the copied range; every other block and every typed object stay. Then
`inflateGetDictionary` on an invariant stream: no fault, only the caller's dictionary bytes change, the invariant holds
after.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InflateDict
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNgF.Proof.InflateInv

/-! ## `memcpy` into a heap block -/

/-- The loop of `Ptr.memcpy` as a fold over the copied indices. -/
def copyFold (src : Array UInt8) (od os : Nat) (l : List Nat) (a : Array UInt8) : Array UInt8 :=
  l.foldl (fun out i => out.set! (od + i) src[os + i]!) a

theorem copyFold_size (src : Array UInt8) (od os : Nat) (l : List Nat) (a : Array UInt8) :
    (copyFold src od os l a).size = a.size := by
  induction l generalizing a with
  | nil => rfl
  | cons x l ih =>
    simp only [copyFold, List.foldl_cons] at ih ⊢
    rw [ih]; simp [Array.set!_eq_setIfInBounds]

theorem copyFold_get (src : Array UInt8) (od os : Nat) (l : List Nat) (a : Array UInt8) (j : Nat)
    (hj : ∀ i ∈ l, od + i ≠ j) : (copyFold src od os l a)[j]! = a[j]! := by
  induction l generalizing a with
  | nil => rfl
  | cons x l ih =>
    simp only [copyFold, List.foldl_cons] at ih ⊢
    rw [ih _ (fun i hi => hj i (List.mem_cons_of_mem _ hi))]
    have hx : od + x ≠ j := hj x (List.mem_cons_self ..)
    simp only [Array.set!_eq_setIfInBounds, getElem!_def, Array.getElem?_setIfInBounds]
    simp [hx]

/-- The array that `Ptr.memcpy dst src n` leaves in the destination. -/
theorem memcpy_loop (ad src : Array UInt8) (od os n : Nat) :
    (Id.run do
      let mut out := ad
      for i in [0:n] do
        out := out.set! (od + i) src[os + i]!
      return out) = copyFold src od os (List.range' 0 n) ad := by
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp [copyFold]
  rfl

theorem space_get_heap (h : Heap) (b : Nat) : Space.get h (BRef.heap b) = h.bytes b := rfl

/-- `memcpy` into heap block `bd` from another object: block `bd` gets `copyFold`, nothing else changes. -/
theorem memcpy_heap {h : Heap} {bd od : Nat} {rs : BRef} {os n : Nat} {ad src : Array UInt8}
    (hd : h.bytes bd = some ad) (hs : Space.get h rs = some src) (hne : rs ≠ .heap bd)
    (h1 : od + n ≤ ad.size) (h2 : os + n ≤ src.size) :
    Ptr.memcpy (.ref (.heap bd) od) (.ref rs os) n h =
      .ok ((), { h with bytes := upd h.bytes bd (some (copyFold src od os (List.range' 0 n) ad)) }) := by
  have hne' : ¬ (BRef.heap bd = rs) := fun e => hne e.symm
  simp only [Ptr.memcpy, space_get_heap, hd, hs, h1, h2, and_self, hne', false_and, ↓reduceIte]
  simp only [Space.ro, Heap.isRo, Bool.false_eq_true, ↓reduceIte, Space.modify, Heap.modifyBytes,
    Tbl.modify_opt h.bytes bd _ ad hd]
  rw [← memcpy_loop]

/-- A change of the bytes of block `bd` that keeps its size and every byte outside `[od, od + n)` is in the frame that
names the write `(.ref (.heap bd) od, n)`. -/
theorem frame_bytes {h : Heap} {bd od n : Nat} {a a' : Array UInt8} (hd : h.bytes bd = some a)
    (hsz : a'.size = a.size) (hpt : ∀ j, (j < od ∨ od + n ≤ j) → a'[j]! = a[j]!) :
    Frame h { h with bytes := upd h.bytes bd (some a') } [] [] [] [(.ref (.heap bd) od, n)] := by
  refine ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => ⟨rfl, rfl⟩, ?_, ?_, rfl, rfl, rfl, rfl, Nat.le_refl _⟩
  · intro b _ _ data hb
    by_cases e : b = bd
    · subst e
      rw [hd] at hb; cases hb
      refine ⟨a', upd_same _ _ _, hsz, fun j _ hw => hpt j ?_⟩
      exact hw _ (List.mem_singleton_self _) od rfl
    · exact ⟨data, by simp only [upd_ne _ _ _ _ e]; exact hb, rfl, fun _ _ _ => rfl⟩
  · intro b _ _ hn
    by_cases e : b = bd
    · subst e; rw [hd] at hn; cases hn
    · simp only [upd_ne _ _ _ _ e]; exact hn

/-- The invariant reads block `b` only through its bytes: a store into another block keeps it. -/
theorem inv_bytes_ne {h : Heap} {s : StreamPtr} {bd : Nat} {a' : Array UInt8} (hv : Inv h s)
    (hne : ∀ b, StateBlock h s b → b ≠ bd) : Inv { h with bytes := upd h.bytes bd (some a') } s := by
  obtain ⟨i, z, b, st, al, rfl, hz, hb, hst, hal, c⟩ := hv
  have e : b ≠ bd := hne b ⟨z, ⟨i, rfl, hz⟩, hb⟩
  have hbb : (upd h.bytes bd (some a')) b = h.bytes b := upd_ne _ _ _ _ e
  refine ⟨i, z, b, st, al, rfl, hz, hb, ?_, ?_, Core.of_heap hbb rfl c⟩
  · simp only [Heap.istate, hbb]; exact hst
  · simp only [Heap.iallocsOf, hbb]; exact hal

/-- `p + k` inside a heap block. -/
theorem add_heap {h : Heap} {b off k : Nat} {a : Array UInt8} (hb : h.bytes b = some a) (hk : off + k ≤ a.size) :
    Ptr.add (Ptr.ref (BRef.heap b) off) (Int.ofNat k) h = .ok (.ref (.heap b) (off + k), h) := by
  have e : ((off : Int) + Int.ofNat k).toNat = off + k := by simp only [Int.ofNat_eq_natCast]; omega
  have hc : off ≤ a.size ∧ 0 ≤ (off : Int) + Int.ofNat k ∧ (off : Int) + Int.ofNat k ≤ (a.size : Int) := by
    simp only [Int.ofNat_eq_natCast]; omega
  simp only [Ptr.add, space_get_heap, hb, hc, and_self, ↓reduceIte, e]

/-- The window facts of the invariant, in `Nat`. -/
theorem window_nat {h : Heap} {s : StreamPtr} {z : ZStream} {b : Nat} {st : InflateState} {al : InflateAllocs}
    (c : Core h s z b (view st) al) :
    ∃ woff data, st.window = .val (.ref (.heap b) woff) ∧ h.bytes b = some data ∧ woff + 32832 ≤ data.size ∧
      st.wsize.toNat ≤ 32768 ∧ st.whave.toNat ≤ st.wsize.toNat ∧ st.wnext.toNat ≤ st.whave.toNat := by
  obtain ⟨woff, data, hw, _, hd, hsz⟩ := c.window
  have hbuf : (view st).wbufsize.toNat = 32832 := by rw [c.wbufsize]; rfl
  refine ⟨woff, data, hw, hd, hbuf ▸ hsz, ?_, c.whave, c.wnext_le⟩
  have := c.wsize_le
  exact this

/-! ## `inflateGetDictionary` -/

theorem getDict_noState {h : Heap} {s : StreamPtr} (hn : InflateControl.NoState h s) (d : BPtr) (hasLen : Bool) :
    C.run (inflateGetDictionary s d hasLen) h = .ok ((Z_STREAM_ERROR, none), h) := by
  simp [C.run, inflateGetDictionary, bind_app,
    show inflateStateCheck s h = .ok (true, h) from InflateControl.stateCheck_noState hn]

/-- `inflateGetDictionary` on an invariant stream: no fault, only the dictionary buffer changes, the invariant
holds after. -/
theorem getDict_inv {h : Heap} {s : StreamPtr} {d : BPtr} (hasLen : Bool) (hv : Inv h s)
    (hd : NullOrWrite h d 32768) (hnb : ∀ b, StateBlock h s b → NotInBlock b d) :
    ∃ r h', C.run (inflateGetDictionary s d hasLen) h = .ok (r, h') ∧ Inv h' s ∧
      Frame h h' [] [] [] [(d, 32768)] := by
  obtain ⟨i, z, b, st, al, rfl, L, hal, c⟩ := InflateInv.live hv
  obtain ⟨woff, data, hwin, hdata, hwsz, hws, hwh, hwn⟩ := window_nat c
  by_cases hc : st.whave = 0 ∨ d = .null
  · refine ⟨(Z_OK, if hasLen then some st.whave else none), h, ?_, hv, InflateInit.frame_refl h _ _ _ _⟩
    rcases hc with hc | hc <;>
    simp [C.run, inflateGetDictionary, bind_app, L.check, L.stateOf, ldState_app L.istate, hc]
  · have hc' : ¬ st.whave = 0 ∧ ¬ d = .null := by simpa [not_or] using hc
    rcases hd with hd | ⟨bd, off, ad, rfl, had, hoff⟩
    · exact absurd hd hc'.2
    have hne : bd ≠ b := by
      intro e; subst e; exact hnb bd ⟨z, ⟨i, rfl, L.hz⟩, L.hb⟩ off rfl
    have hne' : BRef.heap b ≠ BRef.heap bd := fun e => hne (BRef.heap.inj e).symm
    have hk : (st.whave - st.wnext).toNat = st.whave.toNat - st.wnext.toNat :=
      UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr hwn)
    obtain ⟨K, hK⟩ : ∃ K, K = st.whave.toNat - st.wnext.toNat := ⟨_, rfl⟩
    rw [← hK] at hk
    let a1 := copyFold data off (woff + st.wnext.toNat) (List.range' 0 K) ad
    let a2 := copyFold data (off + K) woff (List.range' 0 st.wnext.toNat) a1
    have hs1 : a1.size = ad.size := copyFold_size ..
    have hs2 : a2.size = ad.size := by rw [copyFold_size]; exact hs1
    have e1 := add_heap (off := woff) (k := st.wnext.toNat) hdata (by omega)
    have e2 := memcpy_heap (n := K) (od := off) (os := woff + st.wnext.toNat) had (by rw [space_get_heap]; exact hdata) hne' (by omega)
      (by omega)
    let h1 : Heap := { h with bytes := upd h.bytes bd (some a1) }
    have hb1 : h1.bytes bd = some a1 := upd_same _ _ _
    have hbb : h1.bytes b = some data := by simp only [h1, upd_ne _ _ _ _ (Ne.symm hne)]; exact hdata
    have e3 := add_heap (h := h1) (off := off) (k := K) hb1 (by rw [hs1]; omega)
    have e4 := memcpy_heap (n := st.wnext.toNat) (od := off + K) (os := woff) hb1
      (by rw [space_get_heap]; exact hbb) hne' (by rw [hs1]; omega) (by omega)
    have hw0 : (st.whave != 0) = true := by simpa using hc'.1
    have hd0 : (Ptr.ref (BRef.heap bd) off != Ptr.null) = true := by simp
    refine ⟨(Z_OK, if hasLen then some st.whave else none), { h with bytes := upd h.bytes bd (some a2) }, ?_, ?_, ?_⟩
    · simp only [C.run, inflateGetDictionary, bind_app, L.check, L.stateOf, ldState_app L.istate, hw0, hd0,
        Bool.and_self, Bool.false_eq_true, ↓reduceIte, hwin, Ival.get, pure_app, hk]
      rw [e1]; simp only []
      rw [e2]; simp only []
      rw [e3]; simp only []
      rw [e4]
      simp only [h1, upd_upd, a2]
    · exact inv_bytes_ne hv (fun b' hb' e => by
        obtain ⟨z', ⟨i', hi', hz'⟩, hb''⟩ := hb'
        obtain rfl := Option.some.inj hi'
        rw [L.hz] at hz'; obtain rfl := Option.some.inj hz'
        rw [L.hb] at hb''; obtain rfl := Option.some.inj hb''
        exact hne e.symm)
    · refine frame_bytes had hs2 (fun j hj => ?_)
      have hK32 : K + st.wnext.toNat ≤ 32768 := by omega
      simp only [a2]
      rw [copyFold_get _ _ _ _ _ _ (fun x hx => by
        simp only [List.mem_range'] at hx; omega)]
      exact copyFold_get _ _ _ _ _ _ (fun x hx => by simp only [List.mem_range'] at hx; omega)

end ZlibNgF.Proof.InflateDict
