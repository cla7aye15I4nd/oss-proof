import ZlibNgF.Math.OverlayHeader

/-!
# Counting facts of the tree header model (heap-free)

The token list of `scanTokens` (the loop of `scan_tree` / `send_tree`) has at most one token per code length it
covers, so `scan_tree`'s `bl_tree` frequencies stay far below `2^16`.
-/

namespace ZlibNgF.Math.Huff
set_option autoImplicit false

theorem groupTokens_length (prevlen : Int) (count minc curlen : Nat) (h1 : 1 ≤ count) (hm : 3 ≤ minc) :
    (groupTokens prevlen count minc curlen).length ≤ count := by
  unfold groupTokens
  split
  · simp
  · split
    · split <;> simp <;> omega
    · split <;> simp <;> omega

theorem scanTokens_length (len : Nat → Nat) (m : Nat) :
    ∀ k n (prevlen : Int) (count maxc minc nextlen : Nat), 3 ≤ minc →
      (scanTokens len m k n prevlen count maxc minc nextlen).length ≤ count + k
  | 0, _, _, _, _, _, _, _ => by simp [scanTokens]
  | k + 1, n, prevlen, count, maxc, minc, nextlen, hm => by
    simp only [scanTokens]
    split
    · have := scanTokens_length len m k (n + 1) prevlen (count + 1) maxc minc (nextLen len m n) hm
      omega
    · rw [List.length_append]
      have g := groupTokens_length prevlen (count + 1) minc nextlen (by omega) hm
      have r := scanTokens_length len m k (n + 1) nextlen 0
        (if nextLen len m n = 0 then 138 else if nextlen = nextLen len m n then 6 else 7)
        (if nextLen len m n = 0 then 3 else if nextlen = nextLen len m n then 3 else 4) (nextLen len m n)
        (by split <;> (try split) <;> omega)
      omega

theorem treeTokens_length (len : Nat → Nat) (m : Nat) : (treeTokens len m).length ≤ m := by
  have := scanTokens_length len m m 0 (-1) 0 (if len 0 = 0 then 138 else 7) (if len 0 = 0 then 3 else 4) (len 0)
    (by split <;> omega)
  unfold treeTokens; omega

end ZlibNgF.Math.Huff
