import ZlibNgF.Proof.«deflate.c.reset»
import ZlibNgF.Proof.«inflate.c.dict»

/-!
# `deflateGetDictionary` (`ZlibNgF`)

On a stream with the structural invariant, `deflateGetDictionary` copies the last `min(strstart + lookahead,
w_size)` window bytes into the caller's buffer: the source lies in the window (`strstart + lookahead <= window_size`),
the count is at most `w_size <= 32768`, and the buffer is outside the library's block, so only the buffer changes and
the invariant is kept. On a stream that the state check rejects it returns `Z_STREAM_ERROR` and changes nothing.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.DeflateDict
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInv
open ZlibNgF.Proof.InflateDict (copyFold copyFold_size copyFold_get memcpy_heap frame_bytes space_get_heap)

/-- `p + k` inside a heap block, for any `Int` offset. -/
theorem add_heap_int {h : Heap} {b off : Nat} {k : Int} {a : Array UInt8} (hb : h.bytes b = some a)
    (hoff : off ≤ a.size) (h0 : 0 ≤ (off : Int) + k) (h1 : (off : Int) + k ≤ a.size) :
    Ptr.add (Ptr.ref (BRef.heap b) off) k h = .ok (.ref (.heap b) ((off : Int) + k).toNat, h) := by
  simp only [Ptr.add, space_get_heap, hb, hoff, h0, h1, and_self, ↓reduceIte]

/-- `W_BUF_SIZE` of a window size of at most 32768 is at most 65536. -/
theorem wbuf_le (w : UInt32) (hw : w.toNat ≤ 32768) : (W_BUF_SIZE w).toNat ≤ 65536 := by
  rw [DeflateInit.wbuf_toNat w hw]; unfold DeflateAlloc.dWS; split <;> omega

/-- The invariant reads block `b` only through its bytes: a store into another block keeps it. -/
theorem dinv_bytes_ne {h : Heap} {s : StreamPtr} {bd : Nat} {a' : Array UInt8} (hv : DInv h s)
    (hne : ∀ b, StateBlock h s b → b ≠ bd) : DInv { h with bytes := upd h.bytes bd (some a') } s := by
  obtain ⟨i, z, b, st, al, rfl, hz, hb, hst, hal, c⟩ := hv
  have e : b ≠ bd := hne b ⟨z, ⟨i, rfl, hz⟩, hb⟩
  have hbb : (upd h.bytes bd (some a')) b = h.bytes b := upd_ne _ _ _ _ e
  refine ⟨i, z, b, st, al, rfl, hz, hb, ?_, ?_, DCore.of_heap hbb c⟩
  · simp only [Heap.dstate, hbb]; exact hst
  · simp only [Heap.dallocsOf, hbb]; exact hal

theorem getDict_noState {h : Heap} {s : StreamPtr} (hn : DNoState h s) (d : BPtr) (hasLen : Bool) :
    C.run (deflateGetDictionary s d hasLen) h = .ok ((Z_STREAM_ERROR, none), h) := by
  simp [C.run, deflateGetDictionary, bind_app, stateCheck_noState hn]

/-- `deflateGetDictionary` on an invariant stream: no fault, only the dictionary buffer changes, the invariant
holds after. -/
theorem getDict_inv {h : Heap} {s : StreamPtr} {d : BPtr} (hasLen : Bool) (hv : DInv h s)
    (hd : NullOrWrite h d 32768) (hnb : ∀ b, StateBlock h s b → NotInBlock b d) :
    ∃ r h', C.run (deflateGetDictionary s d hasLen) h = .ok (r, h') ∧ DInv h' s ∧
      DFrame h h' [] [] [] [(d, 32768)] ∧
      (h' = h ∨ ∃ bd off ad a1, d = .ref (.heap bd) off ∧ h.bytes bd = some ad ∧
        h' = { h with bytes := upd h.bytes bd (some a1) } ∧ a1.size = ad.size ∧
        ∀ j, (j < off ∨ off + 32768 ≤ j) → a1[j]! = ad[j]!) := by
  obtain ⟨i, z, b, st, al, rfl, L, hal, c⟩ := live hv
  obtain ⟨w1, w2, wsz, -, -, -, -⟩ := c.sizes
  obtain ⟨data, wo, po, ho, pbo, hdata, hwin, -, -, -, h1, h2, h3, h4, -, -⟩ := c.lay
  simp only [dview] at w1 w2 wsz hwin h1 h2 h3 h4
  have hlook : st.strstart.toNat + st.lookahead.toNat ≤ st.window_size.toNat := c.look
  have hwsz : st.window_size = W_BUF_SIZE st.w_size := wsz
  have hw65 : st.window_size.toNat ≤ 65536 := by rw [hwsz]; exact wbuf_le _ w2
  have hsum : (st.strstart + st.lookahead).toNat = st.strstart.toNat + st.lookahead.toNat := by
    rw [UInt32.toNat_add]; omega
  obtain ⟨len, hlen⟩ : ∃ len : UInt32, len = (if st.strstart + st.lookahead > st.w_size then st.w_size
      else st.strstart + st.lookahead) := ⟨_, rfl⟩
  have hl1 : len.toNat ≤ st.strstart.toNat + st.lookahead.toNat := by
    rw [hlen]; split
    · rename_i hc; simp only [gt_iff_lt, UInt32.lt_iff_toNat_lt, hsum] at hc; omega
    · omega
  have hl2 : len.toNat ≤ st.w_size.toNat := by
    rw [hlen]; split
    · exact Nat.le_refl _
    · rename_i hc; simp only [gt_iff_lt, UInt32.lt_iff_toNat_lt, hsum] at hc; omega
  have hfr0 : DFrame h h [] [] [] [(d, 32768)] := ⟨InflateInit.frame_refl h _ _ _ _, fun _ _ _ => ⟨rfl, rfl⟩⟩
  by_cases hc : d = .null ∨ len = 0
  · refine ⟨(Z_OK, if hasLen then some len else none), h, ?_, hv, hfr0, Or.inl rfl⟩
    rcases hc with hc | hc <;>
    simp [C.run, deflateGetDictionary, bind_app, L.check, L.stateOf, ldDState_app L.dstate, hc, ← hlen]
  · have hc' : ¬ d = .null ∧ ¬ len = 0 := by simpa [not_or] using hc
    rcases hd with hd | ⟨bd, off, ad, rfl, had, hoff⟩
    · exact absurd hd hc'.1
    have hne : bd ≠ b := by
      intro e; subst e; exact hnb bd ⟨z, ⟨i, rfl, L.hz⟩, L.hb⟩ off rfl
    have hne' : BRef.heap b ≠ BRef.heap bd := fun e => hne (BRef.heap.inj e).symm
    let src := wo + st.strstart.toNat + st.lookahead.toNat - len.toNat
    let a1 := copyFold data off src (List.range' 0 len.toNat) ad
    have hs1 : a1.size = ad.size := copyFold_size ..
    have e1 := add_heap_int (off := wo) (k := (st.strstart.toNat : Int)) hdata (by omega) (by omega) (by omega)
    have e2 := add_heap_int (off := wo + st.strstart.toNat) (k := (st.lookahead.toNat : Int)) hdata (by omega)
      (by omega) (by omega)
    have e3 := add_heap_int (off := wo + st.strstart.toNat + st.lookahead.toNat) (k := -(len.toNat : Int)) hdata
      (by omega) (by omega) (by omega)
    have e4 := memcpy_heap (n := len.toNat) (od := off) (os := src) had (by rw [space_get_heap]; exact hdata) hne'
      (by omega) (by omega)
    have hl0 : (len != 0) = true := by simpa using hc'.2
    have hd0 : (Ptr.ref (BRef.heap bd) off != Ptr.null) = true := by simp
    have hpt : ∀ j, (j < off ∨ off + 32768 ≤ j) → a1[j]! = ad[j]! := fun j hj =>
      copyFold_get _ _ _ _ _ _ (fun x hx => by simp only [List.mem_range'] at hx; omega)
    refine ⟨(Z_OK, if hasLen then some len else none), { h with bytes := upd h.bytes bd (some a1) }, ?_, ?_, ?_,
      Or.inr ⟨bd, off, ad, a1, rfl, had, rfl, hs1, hpt⟩⟩
    · simp only [C.run, deflateGetDictionary, bind_app, L.check, L.stateOf, ldDState_app L.dstate,
        Bool.false_eq_true, ↓reduceIte, ← hlen, hl0, hd0, Bool.and_self, hwin, Ival.get, pure_app]
      rw [e1]; simp only []
      rw [show ((wo : Int) + (st.strstart.toNat : Int)).toNat = wo + st.strstart.toNat by omega, e2]
      simp only []
      rw [show ((wo + st.strstart.toNat : Nat) + (st.lookahead.toNat : Int)).toNat =
        wo + st.strstart.toNat + st.lookahead.toNat by omega, e3]
      simp only []
      rw [show ((wo + st.strstart.toNat + st.lookahead.toNat : Nat) + -(len.toNat : Int)).toNat = src by omega, e4]
    · exact dinv_bytes_ne hv (fun b' hb' e => by
        obtain ⟨z', ⟨i', hi', hz'⟩, hb''⟩ := hb'
        obtain rfl := Option.some.inj hi'
        rw [L.hz] at hz'; obtain rfl := Option.some.inj hz'
        rw [L.hb] at hb''; obtain rfl := Option.some.inj hb''
        exact hne e.symm)
    · exact ⟨frame_bytes had hs1 hpt, fun _ _ _ => ⟨rfl, rfl⟩⟩

end ZlibNgF.Proof.DeflateDict
