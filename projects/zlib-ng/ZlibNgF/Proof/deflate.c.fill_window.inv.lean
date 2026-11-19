import ZlibNgF.Proof.«deflate_p.h.readbuf»
import ZlibNgF.Proof.«deflate.c.facts»
import ZlibNgF.Math.WinMask

/-!
# The window invariant `WInv` of a deflate stream (`ZlibNgF`)

The clauses of the window layer that the structural invariant `DInv` (`Proof/deflate.c.invariant.lean`) does not
state yet, on the state record (`WCore`):

* `w_size` is a power of two (`1 << windowBits`), so `W_MASK` rounds down to a multiple of it;
* `fill_end + MIN_LOOKAHEAD` is a multiple of `w_size` and at most `window_size` (`lm_init` sets
  `fill_end = 2 * w_size - MIN_LOOKAHEAD`; `fill_window` adds `w_size` and subtracts a multiple of it): the slide of
  `fill_window` then moves at least half the data, so its `memcpy` does not overlap, and the reads stay in the window;
* `insert <= strstart` (`str = strstart - insert` does not wrap);
* `block_start <= strstart` and `strstart - block_start <= 2^30` (the slide subtracts the same amount from both, so
  the `int` subtraction of `block_start` does not overflow).

`WInv h s`: the state record of `s` satisfies `WCore`. The loop rules `sat_cwhileH` / `sat_cdoWhileH` take a measure
on the heap. `FWS st st'`: `st'` is `st` with only the fields that `fill_window` writes changed.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.WinInv
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateFacts
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)

/-- The window clauses of a `deflate_state`. -/
structure WCore (st : DeflateState) : Prop where
  wpow : ∃ k, 9 ≤ k ∧ k ≤ 15 ∧ st.w_size.toNat = 2 ^ k
  fe_mod : (st.fill_end.toNat + 262) % st.w_size.toNat = 0
  fe_hi : st.fill_end.toNat + 262 ≤ st.window_size.toNat
  ins : st.insert.toNat ≤ st.strstart.toNat
  bs_hi : st.block_start.toInt ≤ st.strstart.toNat
  bs_lo : (st.strstart.toNat : Int) - st.block_start.toInt ≤ 2 ^ 30

/-- The window invariant of stream `s`. -/
def WInv (h : Heap) (s : StreamPtr) : Prop := ∃ b st, DStateIs h s b st ∧ WCore st

/-- `st'` is `st` with only the fields that `fill_window` writes changed. -/
def FWS (st st' : DeflateState) : Prop :=
  ∃ (fe ms pl ss : UInt32) (bs : Int32) (ins sl la ih hw : UInt32),
    st' = { st with
      fill_end := fe
      match_start := ms
      prev_length := pl
      strstart := ss
      block_start := bs
      insert := ins
      slide_len := sl
      lookahead := la
      ins_h := ih
      high_water := hw }

theorem FWS.refl (st : DeflateState) : FWS st st :=
  ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩

theorem FWS.trans {a b c : DeflateState} (h1 : FWS a b) (h2 : FWS b c) : FWS a c := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩ := h1
  obtain ⟨fe, ms, pl, ss, bs, ins, sl, la, ih, hw, rfl⟩ := h2
  exact ⟨fe, ms, pl, ss, bs, ins, sl, la, ih, hw, rfl⟩

/-- `z'` is `z` with only the input fields and the check value changed, and no more input. -/
def ZR (z z' : ZStream) : Prop :=
  z'.avail_in.toNat ≤ z.avail_in.toNat ∧ ∃ (ni : BPtr) (ai : UInt32) (ti ad : UInt64),
    z' = { z with next_in := ni, avail_in := ai, total_in := ti, adler := ad }

theorem ZR.refl (z : ZStream) : ZR z z := ⟨Nat.le_refl _, _, _, _, _, rfl⟩

theorem ZR.trans {a b c : ZStream} (h1 : ZR a b) (h2 : ZR b c) : ZR a c := by
  obtain ⟨l1, _, _, _, _, rfl⟩ := h1
  obtain ⟨l2, ni, ai, ti, ad, rfl⟩ := h2
  exact ⟨Nat.le_trans l2 l1, ni, ai, ti, ad, rfl⟩

/-- `while (cond) body` over a changing heap, with a measure on the loop state and the heap. -/
theorem sat_cwhileH {σ : Type} {cond : σ → M (Bool × σ)} {body : σ → M σ} (I : σ → Heap → Prop)
    (μ : σ → Heap → Nat) (Q : σ → Heap → Prop)
    (hstep : ∀ s H, I s H → Sat H (cond s) (fun cs H1 =>
      (cs.1 = true → Sat H1 (body cs.2) (fun s2 H2 => I s2 H2 ∧ μ s2 H2 < μ s H)) ∧ (cs.1 = false → Q cs.2 H1)))
    {s : σ} {H : Heap} (hI : I s H) (hμ : μ s H < fuel) : Sat H (cwhile cond body s) Q := by
  unfold cwhile
  suffices ∀ n s H, I s H → μ s H < n → Sat H (cwhile.go cond body n s) Q from this _ s H hI hμ
  intro n
  induction n with
  | zero => intro s _ _ hlt; omega
  | succ n ih =>
    intro s H hI hlt
    obtain ⟨⟨c, s1⟩, H1, ec, ht, hf⟩ := hstep s H hI
    cases c with
    | false => exact ⟨s1, H1, by simp [cwhile.go, bind_app, ec], hf rfl⟩
    | true =>
      obtain ⟨s2, H2, eb, hI2, hμ2⟩ := ht rfl
      obtain ⟨s', H', eg, q⟩ := ih s2 H2 hI2 (by omega)
      exact ⟨s', H', by simp [cwhile.go, bind_app, ec, eb, eg], q⟩

/-- `do body while (cond)` over a changing heap, with a measure on the loop state and the heap. -/
theorem sat_cdoWhileH {σ : Type} {body : σ → M σ} {cond : σ → M (Bool × σ)} (I : σ → Heap → Prop)
    (μ : σ → Heap → Nat) (Q : σ → Heap → Prop)
    (hstep : ∀ s H, I s H → Sat H (body s) (fun s1 H1 => Sat H1 (cond s1) (fun cs H2 =>
      (cs.1 = true → I cs.2 H2 ∧ μ cs.2 H2 < μ s H) ∧ (cs.1 = false → Q cs.2 H2))))
    {s : σ} {H : Heap} (hI : I s H) (hμ : μ s H < fuel) : Sat H (cdoWhile body cond s) Q := by
  unfold cdoWhile
  suffices ∀ n s H, I s H → μ s H < n → Sat H (cdoWhile.go body cond n s) Q from this _ s H hI hμ
  intro n
  induction n with
  | zero => intro s _ _ hlt; omega
  | succ n ih =>
    intro s H hI hlt
    obtain ⟨s1, H1, eb, ⟨c, s2⟩, H2, ec, ht, hf⟩ := hstep s H hI
    cases c with
    | false => exact ⟨s2, H2, by simp [cdoWhile.go, bind_app, eb, ec], hf rfl⟩
    | true =>
      obtain ⟨hI2, hμ2⟩ := ht rfl
      simp only at hI2 hμ2
      obtain ⟨s', H', eg, q⟩ := ih s2 H2 hI2 (by omega)
      exact ⟨s', H', by simp [cdoWhile.go, bind_app, eb, ec, eg], q⟩

end ZlibNgF.Proof.WinInv
