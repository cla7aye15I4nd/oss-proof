import ZlibNgF.Proof.«gzwrite.c.compthm»
import ZlibNgF.Proof.«public-deflate»

/-!
# `gz_comp` meets its specification (`ZlibNgF`)

`gz_comp_spec`: `GzCompSpec`, from `gz_comp_spec_of` and the proved obligations of the deflate side
(`DeflatePublic.dpending`).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.GzWrite

/-- **`gz_comp` meets its specification** (`GzCompSpec`). -/
theorem gz_comp_spec : GzCompSpec := gz_comp_spec_of DeflatePublic.dpending

end ZlibNgF.Proof.GzWrite
