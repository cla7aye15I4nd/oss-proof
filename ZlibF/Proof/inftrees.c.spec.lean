import ZlibF.Zlib.«inftrees.c»
import ZlibF.Spec.Functional.Format.Huffman

/-!
# inftrees.c: what the theorems about `inflate_table` say

`capOf` is the room the caller gives the table (`inftrees.h`: `ENOUGH_LENS`, `ENOUGH_DISTS`; 128 entries for
`CODES`, where the code-length code has at most 7 bits). `Result` is what every exit of `inflate_table` does to
the heap and to the returned values.
-/

namespace Zlib.Inftrees.Spec
open C

/-- The first `n` code lengths of `lens` (the array `la` read from offset `ol`), as the specification sees them. -/
def lensList (la : Array UInt16) (ol n : Nat) : List Nat := (List.range n).map (fun k => (la.getD (ol + k) 0).toNat)

/-- The kind of code that `inflate_table` builds for each table type: `CODES` is the code-length code, `LENS` the
literal/length code, `DISTS` the distance code. -/
def kindOf (type : UInt32) : ZlibF.Spec.CodeKind :=
  if type = CODES then .codeLength else if type = LENS then .litLen else .dist

end Zlib.Inftrees.Spec
