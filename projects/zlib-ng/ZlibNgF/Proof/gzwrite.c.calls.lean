import ZlibNgF.Proof.«gzwrite.c.direct»

/-!
# The public write calls (`ZlibNgF`)

On a write handle, `gzwrite`, `gzfwrite`, `gzputs` and `gzflush` keep the invariant `GzInvWS` and are a step of the
file (`CallPost`), given `GzCompSpec` and `DeflateGz`: the argument checks (`gz_error` with a literal of the table),
the pending seek (`gz_zero_spec`), then `gz_write_spec` or `gz_comp`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace ZlibNgF.Proof.GzWrite
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Gz ZlibNgF.Proof.GzInv ZlibNgF.Proof.GzSat ZlibNgF.Proof.GzMode
open ZlibNgF.Proof.GzWriteNeeds

/-- What a public write call leaves on the file `b`: the invariant, and a step of the file. -/
def CallPost {α : Type} (w : World) (h : Heap) (b : Nat) (_r : α) (W : World) (H : Heap) : Prop :=
  GzInvWS W H (some b) ∧ GStep w h W H b []

theorem CallPost.refl {α : Type} {w : World} {h : Heap} {b : Nat} (hv : GzInvWS w h (some b)) (r : α) :
    CallPost w h b r w h := ⟨hv, GStep.refl w h b []⟩

theorem lit_reqlen : gzLits.findIdx? (· == "requested length does not fit in int") = some 8 := by
  simp [gzLits, List.findIdx?_cons]

theorem lit_reqlen_get : gzLits[8]? = some "requested length does not fit in int" := by decide

theorem nonul_reqlen : NoNul "requested length does not fit in int" := by decide

theorem lit_sizet : gzLits.findIdx? (· == "request does not fit in a size_t") = some 6 := by
  simp [gzLits, List.findIdx?_cons]

theorem lit_sizet_get : gzLits[6]? = some "request does not fit in a size_t" := by decide

theorem nonul_sizet : NoNul "request does not fit in a size_t" := by decide

theorem lit_strlen : gzLits.findIdx? (· == "string length does not fit in int") = some 9 := by
  simp [gzLits, List.findIdx?_cons]

theorem lit_strlen_get : gzLits[9]? = some "string length does not fit in int" := by decide

theorem nonul_strlen : NoNul "string length does not fit in int" := by decide

/-- `gz_error` with a literal of the table, then a result: `CallPost`. -/
theorem err_call (lit : String) (i : Nat) (hi : gzLits.findIdx? (· == lit) = some i) (hl : gzLits[i]? = some lit)
    (hn : NoNul lit) {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvWS w h (some b))
    (hs : w.gz h b = some s) (e : Int32) {α : Type} (r : α) :
    GSat w h (do gz_error (some b) e (← gzLit lit); pure r) (CallPost w h b) := by
  refine GSat.mono (gz_error_litW lit i hi hl hn hv hs e r) fun _ W H q => ?_
  obtain ⟨-, s', hs', -, hv', -, g'⟩ := q
  exact ⟨hv', g'⟩

/-- `gz_write` as a public call: `CallPost`. -/
theorem write_call (C : GzCompSpec) (G : DeflateGz) {w : World} {h : Heap} {b : Nat} {s : GzState}
    (hv : GzInvWS w h (some b)) (hs : w.gz h b = some s) (buf : BPtr) (len : UInt64)
    (hin : GzIn w h (some b) buf len.toNat) {α : Type} (k : UInt64 → α) :
    GSat w h (do let r ← gz_write (some b) buf len; pure (k r)) (CallPost w h b) := by
  refine GSat.bind (GSat.mono (gz_write_spec C G hv hs buf len hin) fun r W H q => ?_)
  obtain ⟨-, -, hv', g', -⟩ := q
  exact GSat.pure ⟨hv', g'⟩

/-- **`gzwrite`** on a write handle. -/
theorem gzwrite_spec (C : GzCompSpec) (G : DeflateGz) {w : World} {h : Heap} {b : Nat} {s : GzState}
    (hv : GzInvWS w h (some b)) (hs : w.gz h b = some s) (buf : BPtr) (len : UInt32)
    (hin : len.toInt32 ≥ 0 → GzIn w h (some b) buf len.toNat) :
    GSat w h (gzwrite (some b) buf len) (CallPost w h b) := by
  unfold gzwrite
  refine GSat.ite (fun hc => by simp at hc) (fun _ => ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  refine GSat.ite (fun _ => GSat.pure (CallPost.refl hv _)) (fun _ => ?_)
  refine GSat.ite (fun _ => err_call _ 8 lit_reqlen lit_reqlen_get nonul_reqlen hv hs _ _) (fun hl => ?_)
  have hge : len.toInt32 ≥ 0 := Int32.not_lt.mp hl
  exact write_call C G hv hs buf len.toUInt64 (by rw [UInt32.toNat_toUInt64]; exact hin hge) _

/-- No overflow when `nitems * size / size == nitems`. -/
theorem mul_fits (a c : UInt64) (hc : c ≠ 0) (he : a * c / c = a) : a.toNat * c.toNat < 2 ^ 64 := by
  have hc' : 0 < c.toNat := by
    rcases Nat.eq_zero_or_pos c.toNat with e | e
    · exact absurd (UInt64.toNat_inj.mp (by simpa using e)) hc
    · exact e
  have e1 := congrArg UInt64.toNat he
  rw [UInt64.toNat_div, UInt64.toNat_mul] at e1
  have e2 := Nat.div_mul_le_self ((a.toNat * c.toNat) % 2 ^ 64) c.toNat
  rw [e1] at e2
  have e3 := Nat.mod_lt (a.toNat * c.toNat) (by decide : 0 < 2 ^ 64)
  omega

/-- **`gzfwrite`** on a write handle. -/
theorem gzfwrite_spec (C : GzCompSpec) (G : DeflateGz) {w : World} {h : Heap} {b : Nat} {s : GzState}
    (hv : GzInvWS w h (some b)) (hs : w.gz h b = some s) (buf : BPtr) (size nitems : UInt64)
    (hin : size.toNat * nitems.toNat < 2 ^ 64 → GzIn w h (some b) buf (size.toNat * nitems.toNat)) :
    GSat w h (gzfwrite buf size nitems (some b)) (CallPost w h b) := by
  unfold gzfwrite
  refine GSat.ite (fun _ => GSat.pure (CallPost.refl hv _)) (fun hz => ?_)
  have hz' : size ≠ 0 := by simpa using hz
  refine GSat.ite (fun hc => by simp at hc) (fun _ => ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  refine GSat.ite (fun _ => GSat.pure (CallPost.refl hv _)) (fun _ => ?_)
  refine GSat.ite (fun _ => err_call _ 6 lit_sizet lit_sizet_get nonul_sizet hv hs _ _) (fun hd => ?_)
  have hd' : nitems * size / size = nitems := by simpa using hd
  have hf := mul_fits nitems size hz' hd'
  have hlen : (nitems * size).toNat = size.toNat * nitems.toNat := by
    rw [UInt64.toNat_mul, Nat.mod_eq_of_lt hf, Nat.mul_comm]
  refine GSat.ite (fun _ => ?_) (fun _ => GSat.pure (CallPost.refl hv _))
  exact write_call C G hv hs buf _ (by rw [hlen]; exact hin (by rw [Nat.mul_comm]; exact hf)) _

/-- **`gzputs`** on a write handle, with a C string outside the file. -/
theorem gzputs_spec (C : GzCompSpec) (G : DeflateGz) {w : World} {h : Heap} {b : Nat} {s : GzState}
    (hv : GzInvWS w h (some b)) (hs : w.gz h b = some s) (p : BPtr) (hp : CStr h p) (ho : OutsideGz w h (some b) p) :
    GSat w h (gzputs (some b) p) (CallPost w h b) := by
  obtain ⟨n, hn⟩ := hp
  unfold gzputs
  refine GSat.ite (fun hc => by simp at hc) (fun _ => ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  refine GSat.ite (fun _ => GSat.pure (CallPost.refl hv _)) (fun _ => ?_)
  refine GSat.bind (GSat.of_eq (a := UInt64.ofNat n) (w' := w) (h' := h) (by rw [lm_app, GzOpen.strlenB_of hn]) ?_)
  refine GSat.ite (fun _ => err_call _ 9 lit_strlen lit_strlen_get nonul_strlen hv hs _ _) (fun _ => ?_)
  have hin : GzIn w h (some b) p (UInt64.ofNat n).toNat := by
    obtain ⟨r, off, d, ep, hd, hle, -⟩ := hn
    refine Or.inr ⟨⟨r, off, d, ep, hd, ?_⟩, ho⟩
    have : (UInt64.ofNat n).toNat ≤ n := by rw [UInt64.toNat_ofNat']; exact Nat.mod_le _ _
    omega
  exact write_call C G hv hs p _ hin _

/-- **`gzflush`** on a write handle. -/
theorem gzflush_spec (C : GzCompSpec) (G : DeflateGz) {w : World} {h : Heap} {b : Nat} {s : GzState}
    (hv : GzInvWS w h (some b)) (hs : w.gz h b = some s) (fl : Int32) :
    GSat w h (gzflush (some b) fl) (CallPost w h b) := by
  unfold gzflush
  refine GSat.ite (fun hc => by simp at hc) (fun _ => ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  refine GSat.ite (fun _ => GSat.pure (CallPost.refl hv _)) (fun _ => ?_)
  refine GSat.ite (fun _ => GSat.pure (CallPost.refl hv _)) (fun _ => ?_)
  -- the flush from a handle with no pending seek
  have tail : ∀ {W : World} {H : Heap} {s1 : GzState}, GzInvWS W H (some b) → W.gz H b = some s1 →
      GStep w h W H b [] → GSat W H (do let _ ← gz_comp (some b) fl; rdG (some b) (·.err)) (CallPost w h b) := by
    intro W H s1 hv1 hs1 g1
    refine GSat.bind (GSat.mono (comp_inv C G hv1 hs1 fl) fun rc W2 H2 q => ?_)
    obtain ⟨s2, z2, hs2, -, hv2, g2, -⟩ := q
    exact GSat.of_eq (rdG_app' hs2 _) ⟨hv2, g1.trans g2 ⟨s, hs⟩ ⟨s1, hs1⟩⟩
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  refine GSat.ite (fun hk => ?_) (fun _ => tail hv hs (GStep.refl w h b []))
  refine GSat.bind (GSat.mono (gz_zero_spec C G hv hs (by simpa using hk)) fun rz W2 H2 q => ?_)
  obtain ⟨s2, hs2, hv2, g2, -, -, -⟩ := q
  exact GSat.ite (fun _ => GSat.of_eq (rdG_app' hs2 _) ⟨hv2, g2⟩) (fun _ => tail hv2 hs2 g2)

end ZlibNgF.Proof.GzWrite
