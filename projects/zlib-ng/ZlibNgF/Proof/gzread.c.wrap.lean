import ZlibNgF.Proof.«gzread.c.getc»
import ZlibNgF.Proof.«gzread.c.idlespec»

/-!
# `gzread` and `gzfread` on a read handle (`ZlibNgF`)

Both test the mode and the pending error, refuse a request that does not fit (`gz_error` with a literal), and
otherwise call `gz_read` with the caller's buffer. Given the specification of `gz_read` (`GzReadSpec`) and that
`gz_read` keeps `LookIdle` (`GzReadIdle`), each returns on a read handle with `LookIdle`, leaving a read handle with
`LookIdle` and a step of the call whose only write outside the file is the caller's buffer; so each keeps the read
invariant (`read_keepsRI`, `fread_keepsRI`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace ZlibNgF.Proof.GzMode
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Gz ZlibNgF.Proof.GzInv ZlibNgF.Proof.GzSat ZlibNgF.Proof.GzDecomp
open ZlibNg.Inflate (Z_OK Z_BUF_ERROR Z_STREAM_ERROR)

theorem lit_int : gzLits.findIdx? (· == "request does not fit in an int") = some 5 := by
  simp [gzLits, List.findIdx?_cons]

theorem lit_size_t : gzLits.findIdx? (· == "request does not fit in a size_t") = some 6 := by
  simp [gzLits, List.findIdx?_cons]

/-- What `gzread` and `gzfread` leave on a read handle: a read handle with `LookIdle`, and a step of the call whose
only write outside the file is `wr`. -/
def RPost {α : Type} (w : World) (h : Heap) (b : Nat) (wr : List (BPtr × Nat)) : α → World → Heap → Prop :=
  fun _ W H => GzInvR W H (some b) ∧ LookIdle W H (some b) ∧ GStep w h W H b wr

/-- `gz_error(state, e, lit)` with a literal of the table on a read handle with `LookIdle`, then `return v`. -/
theorem errlit_idle {α : Type} {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvR w h (some b))
    (hi : LookIdle w h (some b)) (hs : w.gz h b = some s) (e : Int32) (lit : String) (i : Nat)
    (hl : gzLits.findIdx? (· == lit) = some i) (hn : NoNul lit) (wr : List (BPtr × Nat)) (v : α) :
    GSat w h (do gz_error (some b) e (← gzLit lit); pure v) (RPost w h b wr) := by
  refine GSat.bind (GSat.mono (errlit_strm hv hs e lit i hl hn) fun p W2 H2 q =>
    GSat.bind (GSat.mono q fun _ W3 H3 q3 => ?_))
  obtain ⟨s', hs', he, hv', -, g', hst⟩ := q3
  exact GSat.pure ⟨hv', idle_same hi hs hs' (by rw [he.1]; rfl) (by rw [he.1]; rfl) (by rw [he.1]; rfl)
    (by rw [hst]), GzDecomp.GStep.widen g' wr⟩

/-- `gz_read` into a buffer of the caller, then any reads of the state and a pure result. -/
theorem gz_read_call {β : Type} (RS : GzReadSpec) (RI : GzReadIdle) {w : World} {h : Heap} {b : Nat}
    (hv : GzInvR w h (some b)) (hi : LookIdle w h (some b)) (buf : BPtr) (len : UInt64)
    (hout : GzOut w h (some b) buf len.toNat) (k : UInt64 → G β)
    (hk : ∀ r W H s', GzInvR W H (some b) → W.gz H b = some s' → ∃ v, k r W H = .ok ((v, W), H)) :
    GSat w h (gz_read (some b) buf len >>= k) (RPost w h b [(buf, len.toNat)]) := by
  refine GSat.bind (GSat.mono (GSat.withRun (RS w h b buf len hv hout)) fun r W H q => ?_)
  obtain ⟨⟨-, hvW, gW, -⟩, run⟩ := q
  have hiW := RI w h b buf len r W H hv hi hout run
  obtain ⟨b0, s', e0, hs', -, -⟩ := hvW.1
  cases e0
  obtain ⟨v, ev⟩ := hk r W H s' hvW hs'
  exact ⟨v, W, H, ev, hvW, hiW, gW⟩

/-- **`gzread`** on a read handle with `LookIdle`. -/
theorem gzread_call (RS : GzReadSpec) (RI : GzReadIdle) {w : World} {h : Heap} {b : Nat}
    (hv : GzInvR w h (some b)) (hi : LookIdle w h (some b)) (buf : BPtr) (len : UInt32)
    (hout : len.toInt32 ≥ 0 → GzOut w h (some b) buf len.toNat) :
    GSat w h (gzread (some b) buf len) (RPost w h b [(buf, len.toNat)]) := by
  obtain ⟨b0, s, e0, hs, -, -⟩ := hv.1
  cases e0
  unfold gzread
  apply GSat.ite
  · intro hc; simp at hc
  intro _
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  apply GSat.ite
  · intro _; exact GSat.pure ⟨hv, hi, GStep.refl w h b _⟩
  intro _
  apply GSat.ite
  · intro _
    exact errlit_idle hv hi hs Z_STREAM_ERROR _ 5 lit_int (by decide) _ _
  intro hlen
  have hge : len.toInt32 ≥ 0 := by simpa using hlen
  have ho := hout hge
  have e1 : (len.toUInt64).toNat = len.toNat := by simp
  rw [← e1]
  refine gz_read_call RS RI hv hi buf len.toUInt64 (by rw [e1]; exact ho) _ ?_
  intro r W H s' _ hs'
  simp only [gbind_app, rdG_app' hs']
  split <;> exact ⟨_, rfl⟩

theorem mul_no_overflow {size nitems : UInt64} (hz : size ≠ 0) (hc : ¬ 0xFFFFFFFFFFFFFFFF / size < nitems) :
    size.toNat * nitems.toNat < 2 ^ 64 ∧ (nitems * size).toNat = size.toNat * nitems.toNat := by
  have hz' : 0 < size.toNat := by
    have : size.toNat ≠ 0 := fun e => hz (UInt64.toNat_inj.mp (by simpa using e))
    omega
  have hle : nitems.toNat ≤ (2 ^ 64 - 1) / size.toNat := by
    have := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp hc)
    simpa [UInt64.toNat_div] using this
  have hm : size.toNat * nitems.toNat ≤ 2 ^ 64 - 1 := by
    have := Nat.mul_le_mul_left size.toNat hle
    exact Nat.le_trans this (Nat.mul_div_le _ _)
  refine ⟨by omega, ?_⟩
  rw [UInt64.toNat_mul, Nat.mul_comm]
  exact Nat.mod_eq_of_lt (by omega)

/-- **`gzfread`** on a read handle with `LookIdle`. -/
theorem gzfread_call (RS : GzReadSpec) (RI : GzReadIdle) {w : World} {h : Heap} {b : Nat}
    (hv : GzInvR w h (some b)) (hi : LookIdle w h (some b)) (buf : BPtr) (size nitems : UInt64)
    (hout : size.toNat * nitems.toNat < 2 ^ 64 → GzOut w h (some b) buf (size.toNat * nitems.toNat)) :
    GSat w h (gzfread buf size nitems (some b)) (RPost w h b [(buf, size.toNat * nitems.toNat)]) := by
  obtain ⟨b0, s, e0, hs, -, -⟩ := hv.1
  cases e0
  unfold gzfread
  apply GSat.ite
  · intro _; exact GSat.pure ⟨hv, hi, GStep.refl w h b _⟩
  intro hz
  have hz' : size ≠ 0 := by simpa using hz
  apply GSat.ite
  · intro hc; simp at hc
  intro _
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  apply GSat.ite
  · intro _; exact GSat.pure ⟨hv, hi, GStep.refl w h b _⟩
  intro _
  apply GSat.ite
  · intro _
    exact errlit_idle hv hi hs Z_STREAM_ERROR _ 6 lit_size_t (by decide) _ _
  intro hc
  have hc' : ¬ 0xFFFFFFFFFFFFFFFF / size < nitems := by simpa [hz'] using hc
  obtain ⟨hlt, e1⟩ := mul_no_overflow hz' hc'
  apply GSat.ite
  · intro _
    rw [← e1]
    exact gz_read_call RS RI hv hi buf _ (by rw [e1]; exact hout hlt) _ fun r W H _ _ _ => ⟨_, rfl⟩
  · intro _; exact GSat.pure ⟨hv, hi, GStep.refl w h b _⟩

theorem read_keepsRI (RS : GzReadSpec) (RI : GzReadIdle) : KeepsRI SRead := by
  intro w h w' h' f hv hi ⟨buf, len, r, hb, e⟩
  obtain ⟨b, s, rfl, -, -, -⟩ := hv.1
  obtain ⟨r2, W, H, e2, q⟩ := (gzread_call RS RI hv hi buf len hb).run
  obtain ⟨-, rfl, rfl⟩ := gdet e2 e
  exact ⟨q.1, q.2.1⟩

theorem fread_keepsRI (RS : GzReadSpec) (RI : GzReadIdle) : KeepsRI SFread := by
  intro w h w' h' f hv hi ⟨buf, size, nitems, r, hb, e⟩
  obtain ⟨b, s, rfl, -, -, -⟩ := hv.1
  obtain ⟨r2, W, H, e2, q⟩ := (gzfread_call RS RI hv hi buf size nitems hb).run
  obtain ⟨-, rfl, rfl⟩ := gdet e2 e
  exact ⟨q.1, q.2.1⟩

end ZlibNgF.Proof.GzMode
