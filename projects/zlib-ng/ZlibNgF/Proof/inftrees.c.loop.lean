import ZlibNgF.Proof.«inftrees.c.cont»

/-!
# `zng_inflate_table`: small run lemmas for the table-filling loop (`ZlibNgF`)
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.Inftrees
open C ZlibNg.Inftrees ZlibNg.InflateP ZlibNgF.Math.BitReverse ZlibNgF.Math.InftreesCount

theorem bind_have {α β γ : Type} {h : Heap} {Q : γ → Heap → Prop} {m : M α} {v : α → β}
    {f : α → β → M γ} (hm : Wp m h (fun a h' => Wp (f a (v a)) h' Q)) :
    Wp (m >>= fun a => have x := v a; f a x) h Q := Wp.bind hm

theorem st_at_ok {a : Array UInt16} {i : Nat} (hi : i < a.size) : (U16Src.st a).at i = pure a[i] := by
  simp [U16Src.at, aget_ok hi]

end ZlibNgF.Proof.Inftrees
