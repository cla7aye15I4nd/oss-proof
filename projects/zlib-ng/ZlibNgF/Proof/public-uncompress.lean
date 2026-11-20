import ZlibNgF.Proof.«public-inflate»
import ZlibNgF.Proof.«public-inflate-init»
import ZlibNgF.Proof.«public-inflate-control»
import ZlibNgF.Proof.«inflate.c.keep»

/-!
# The safety of `uncompress2_z`, `uncompress2`, `uncompress_z` and `uncompress` (`ZlibNgF`)

`uncompress2_z` makes a local `z_stream` and `buf[1]`, calls `inflateInit`, runs `inflate` in a `do … while` loop
that hands the caller's lengths to the stream in chunks of at most `UINT_MAX` bytes, and ends the stream. The loop
invariant (`J`): the local stream holds the invariant of `Inv` with no registered header, its input position is inside
the source with `avail_in` plus the remaining `len` bytes before the end, and its output position is inside the
destination (or `buf`) with `avail_out` plus the remaining `left` bytes before the end. The measure is
`len + avail_in + left + avail_out`: refilling the stream keeps it, and `inflate` returns `Z_OK` only after it consumed
input or wrote output (`InflateTop.Progress`), so every trip that continues the loop lowers it. It starts at
`*sourceLen` plus `*destLen` (or 1), below `2^64` by `ObjBound`.
-/

set_option autoImplicit false
namespace ZlibNgF.Proof.Uncompress
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Inflate ZlibNg.Uncompr
open ZlibNgF.Proof.InflateInv (Inv)
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.mono Sat.of_eq)
open ZlibNgF.Proof.InflateLoop (Frame.trans Frame.mono Frame.widen InAt)

/-! ## Loops and frames -/

/-- `do body while (cond)` over a changing heap, with a measure that reads the heap. -/
theorem sat_cdoWhile_heap {σ : Type} {body : σ → M σ} {cond : σ → M (Bool × σ)} (I : σ → Heap → Prop)
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
    obtain ⟨s1, H1, eb, ⟨⟨c, s2⟩, H2, ec, ht, hf⟩⟩ := hstep s H hI
    cases c with
    | false => exact ⟨s2, H2, by simp [cdoWhile.go, bind_app, eb, ec], hf rfl⟩
    | true =>
      obtain ⟨hI2, hμ2⟩ := ht rfl
      simp only at hI2 hμ2
      obtain ⟨s', H', eg, q⟩ := ih s2 H2 hI2 (by omega)
      exact ⟨s', H', by simp [cdoWhile.go, bind_app, eb, ec, eg], q⟩

/-- A change of the stream records only. -/
theorem frame_streams (H : Heap) (X : Tbl (Option ZStream)) (i : Nat) (hX : ∀ j, j ≠ i → X j = H.streams j)
    (B G : List Nat) (W : List (BPtr × Nat)) : Frame H { H with streams := X } [i] B G W :=
  ⟨fun j hj => hX j (by simpa using hj), fun _ _ => rfl, fun _ _ _ => ⟨rfl, rfl⟩,
    fun _ _ _ d hd => ⟨d, hd, rfl, fun _ _ _ => rfl⟩, fun _ _ _ hd => hd, rfl, rfl, rfl, rfl, Nat.le_refl _⟩

/-- The end of the call: the local stream is gone again, and the two fresh blocks and a write range in a fresh block are
not part of the frame. -/
theorem frame_fin {h H : Heap} {i nb sb : Nat} {D dest : BPtr} {L0 n : Nat}
    (f : Frame h H [i] [nb, sb] [] [(D, L0)]) (hi : H.streams i = h.streams i) (hnb : h.nextBlk ≤ nb)
    (hsb : h.nextBlk ≤ sb) (hD : (D = dest ∧ L0 = n) ∨ ∃ c o, D = .ref (.heap c) o ∧ h.nextBlk ≤ c) :
    Frame h H [] [] [] [(dest, n)] := by
  obtain ⟨s1, g1, i1, b1, n1, c1, r1, x1, a1, k1⟩ := f
  refine ⟨fun j _ => ?_, g1, fun b hb _ => i1 b hb (by simp; omega), fun b hb _ d hd => ?_,
    fun b hb _ hn => n1 b hb (by simp; omega) hn, c1, r1, x1, a1, k1⟩
  · by_cases e : j = i
    · subst e; exact hi
    · exact s1 j (by simpa using e)
  · obtain ⟨d', e1, e2, e3⟩ := b1 b hb (by simp; omega) d hd
    refine ⟨d', e1, e2, fun j hj hw => e3 j hj ?_⟩
    intro w hw' off hoff
    simp only [List.mem_singleton] at hw'
    subst hw'
    rcases hD with ⟨rfl, rfl⟩ | ⟨c, o, rfl, hc⟩
    · exact hw _ (List.mem_singleton_self _) off hoff
    · injection hoff with hoff; injection hoff with hoff; omega

/-! ## Single steps -/

theorem rdZ_app {α : Type} {H : Heap} {i : Nat} {z : ZStream} (hz : H.streams i = some z) (f : ZStream → α) :
    rdZ (some i) f H = .ok (f z, H) := by
  simp [rdZ, bind_app, ldStream, hz]

theorem wrZ_app {H : Heap} {i : Nat} {z : ZStream} (hz : H.streams i = some z) (f : ZStream → ZStream) :
    wrZ (some i) f H = .ok ((), { H with streams := upd H.streams i (some (f z)) }) := by
  simp [wrZ, bind_app, ldStream, stStream, hz]

theorem dropStream_app {H : Heap} {i : Nat} {z : ZStream} (hz : H.streams i = some z) :
    dropStream (some i) H = .ok ((), { H with streams := upd H.streams i none }) := by
  simp [dropStream, hz]

theorem dropLocal_app {H : Heap} {b : Nat} {d : Array UInt8} (hd : H.bytes b = some d) :
    dropLocal (.ref (.heap b) 0) H = .ok ((), { H with bytes := upd H.bytes b none }) := by
  simp [dropLocal, hd]

/-- A change of the four buffer fields of an invariant stream keeps the invariant (a caller step). -/
theorem inv_setZ {H : Heap} {i : Nat} {z z' : ZStream} (hv : Inv H (some i)) (hz : H.streams i = some z)
    (e : z' = { z with
      next_in := z'.next_in
      avail_in := z'.avail_in
      next_out := z'.next_out
      avail_out := z'.avail_out }) :
    Inv { H with streams := upd H.streams i (some z') } (some i) := by
  obtain ⟨i', z0, b, st, al, e0, hz0, hb, -⟩ := id hv
  cases e0
  rw [hz] at hz0; cases hz0
  exact InflateReach.caller_inv hv ⟨i, z, z', b, rfl, hz, by simp, hb, e, rfl, rfl, rfl,
    fun k g _ hg => ⟨g, hg⟩, rfl, Nat.le_refl _⟩

/-- `Space.get` of an object outside the frame keeps its size. -/
theorem get_frame {H H' : Heap} {S B G : List Nat} {W : List (BPtr × Nat)} (f : Frame H H' S B G W) {r : BRef}
    (hr : ∀ c, r = .heap c → c < H.nextBlk ∧ c ∉ B) {d : Array UInt8} (hd : Space.get H r = some d) :
    ∃ d', Space.get H' r = some d' ∧ d'.size = d.size := by
  cases r with
  | heap c =>
    obtain ⟨h1, h2⟩ := hr c rfl
    obtain ⟨d', e1, e2, -⟩ := f.2.2.2.1 c h1 h2 d hd
    exact ⟨d', e1, e2⟩
  | const c =>
    refine ⟨d, ?_, rfl⟩
    show H'.consts c = some d
    rw [f.2.2.2.2.2.1]; exact hd
  | str k => exact ⟨d, hd, rfl⟩

/-! ## The loop invariant -/

/-- What one call fixes: the heap at the start of the loop, the local stream, the blocks of `buf` and of the state, the
source and its length, and the destination (`dest`, or `buf` when `*destLen` is 0) with its length. -/
structure Cx where
  h0 : Heap
  i : Nat
  nb : Nat
  sb : Nat
  src : BPtr
  sl : UInt64
  bo : Nat
  oo : Nat
  L0 : Nat

/-- The facts of the call that do not change. -/
structure Cx.OK (C : Cx) : Prop where
  bo_sb : C.bo ≠ C.sb
  nb_sb : C.nb ≠ C.sb
  bo_lt : C.bo < C.h0.nextBlk
  nb_lt : C.nb < C.h0.nextBlk
  src : ∀ r o, C.src = .ref r o → r ≠ .heap C.sb ∧ ∀ c, r = .heap c → c < C.h0.nextBlk ∧ c ≠ C.nb
  disj : Disjoint (.ref (.heap C.bo) C.oo) C.L0 C.src C.sl.toNat
  crc : C.h0.crcTable = ZlibNg.Crc32Tbl.crc_table

/-- The input of the local stream: inside the source, with `avail_in` and the remaining `len` bytes before its end. -/
def InJ (src : BPtr) (sl : UInt64) (H : Heap) (next : BPtr) (avail : UInt32) (len : UInt64) : Prop :=
  match src with
  | .null => next = .null ∧ avail = 0 ∧ len = 0
  | .ref r o => (∃ d, Space.get H r = some d ∧ o + sl.toNat ≤ d.size) ∧
      ∃ q, next = .ref r q ∧ o ≤ q ∧ q + avail.toNat + len.toNat ≤ o + sl.toNat

/-- The loop invariant, with the remaining lengths `left` and `len`. -/
def J (C : Cx) (left len : UInt64) (H : Heap) : Prop :=
  ∃ z st, H.streams C.i = some z ∧ z.state = some C.sb ∧ H.istate C.sb = some st ∧ st.head = .val none ∧
    Inv H (some C.i) ∧ Frame C.h0 H [C.i] [C.nb, C.sb] [] [(.ref (.heap C.bo) C.oo, C.L0)] ∧
    (∃ d, H.bytes C.nb = some d) ∧ (∃ d, H.bytes C.bo = some d ∧ C.oo + C.L0 ≤ d.size) ∧
    (∃ p, z.next_out = .ref (.heap C.bo) p ∧ C.oo ≤ p ∧ p + z.avail_out.toNat + left.toNat ≤ C.oo + C.L0) ∧
    InJ C.src C.sl H z.next_in z.avail_in len

/-- The measure of the loop. -/
def μ (C : Cx) (s : Int32 × UInt64 × UInt64) (H : Heap) : Nat :=
  s.2.1.toNat + s.2.2.toNat + match H.streams C.i with
    | some z => z.avail_in.toNat + z.avail_out.toNat
    | none => 0

/-- Where the loop ends: the stream with the invariant, ready for `inflateEnd`, `buf` alive. -/
def Qe (C : Cx) (_ : Int32 × UInt64 × UInt64) (H : Heap) : Prop :=
  Inv H (some C.i) ∧ Frame C.h0 H [C.i] [C.nb, C.sb] [] [(.ref (.heap C.bo) C.oo, C.L0)] ∧
    (∃ d, H.bytes C.nb = some d) ∧ ∃ z, H.streams C.i = some z ∧ z.state = some C.sb

theorem pairwise_two {a b : BPtr × Nat} (h1 : Disjoint a.1 a.2 b.1 b.2) (h2 : Disjoint b.1 b.2 a.1 a.2) :
    PairwiseDisjoint [a, b] := by
  intro i j x y hij hx hy
  match i, j, hx, hy with
  | 0, 1, hx, hy => cases hx; cases hy; exact h1
  | 1, 0, hx, hy => cases hx; cases hy; exact h2
  | 0, 0, _, _ => exact absurd rfl hij
  | 1, 1, _, _ => exact absurd rfl hij
  | 0, k + 2, _, hy => simp at hy
  | 1, k + 2, _, hy => simp at hy
  | k + 2, _, hx, _ => simp at hx

theorem disjoint_symm {p q : BPtr} {n m : Nat} (h : Disjoint p n q m) : Disjoint q m p n := by
  cases p with
  | null => cases q <;> trivial
  | ref r o =>
    cases q with
    | null => trivial
    | ref s o' =>
      simp only [Disjoint] at h ⊢
      rcases h with h | h | h
      · exact Or.inl (Ne.symm h)
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)

/-- The buffers of the invariant are valid for `inflate`. -/
theorem J.io {C : Cx} (ok : C.OK) {left len : UInt64} {H : Heap} (hj : J C left len H) : StreamIO H (some C.i) := by
  obtain ⟨z, st, hz, hb, hst, hhd, -, -, -, ⟨d, hd, hds⟩, ⟨p, hpo, hp1, hp2⟩, hin⟩ := hj
  have hreg : RegisteredHeader H (some C.i) none := ⟨C.sb, st, ⟨z, ⟨C.i, rfl, hz⟩, hb⟩, hst, hhd⟩
  have hHR : headerRanges H none = [] := rfl
  have hout : NullOrWrite H z.next_out z.avail_out.toNat := Or.inr ⟨C.bo, p, d, hpo, hd, by omega⟩
  have dj := ok.disj
  have hsrcok := ok.src
  unfold InJ at hin
  rcases hsrc : C.src with _ | ⟨r, o⟩
  · rw [hsrc] at hin
    obtain ⟨hn, -, -⟩ := hin
    refine ⟨z, C.sb, none, ⟨C.i, rfl, hz⟩, hb, hreg, Or.inl rfl, Or.inl hn, hout, ?_, ?_⟩
    · rw [hHR]
      have hd : Disjoint z.next_out z.avail_out.toNat z.next_in z.avail_in.toNat := by
        rw [hpo, hn]; trivial
      exact pairwise_two (disjoint_symm hd) hd
    · rw [hHR]
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · intro off e; rw [hn] at e; cases e
      · intro off e
        rw [hpo] at e
        injection e with e; injection e with e
        exact ok.bo_sb e
  rw [hsrc] at hin dj
  obtain ⟨⟨d', hd', hds'⟩, q, hq, hq1, hq2⟩ := hin
  refine ⟨z, C.sb, none, ⟨C.i, rfl, hz⟩, hb, hreg, Or.inl rfl, Or.inr ⟨r, q, d', hq, hd', by omega⟩, hout, ?_, ?_⟩
  · rw [hHR]
    have hd : Disjoint z.next_out z.avail_out.toNat z.next_in z.avail_in.toNat := by
      rw [hpo, hq]
      simp only [Disjoint] at dj ⊢
      rcases dj with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr (by omega))
    exact pairwise_two (disjoint_symm hd) hd
  · rw [hHR]
    intro r' hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · intro off e
      rw [hq] at e
      injection e with e
      exact (hsrcok r o hsrc).1 e
    · intro off e
      rw [hpo] at e
      injection e with e; injection e with e
      exact ok.bo_sb e

/-- What a trip of the loop ends with, below the measure `m`. -/
def Post (C : Cx) (m : Nat) (s : Int32 × UInt64 × UInt64) (H : Heap) : Prop :=
  (s.1 = Z_OK → J C s.2.1 s.2.2 H ∧ μ C s H < m) ∧ Qe C s H

/-- The call of `inflate` at the end of a trip. -/
theorem step_inflate {C : Cx} (ok : C.OK) {left len : UInt64} {H : Heap} (hj : J C left len H) (e0 : Int32)
    {m : Nat} (hm : μ C (e0, left, len) H ≤ m) :
    Sat H (do let err ← inflate (some C.i) 0; pure (err, left, len)) (Post C m) := by
  have hio := hj.io ok
  obtain ⟨z, st, hz, hb, hst, hhd, hv, fJ, ⟨dn, hdn⟩, ⟨d, hd, hds⟩, ⟨p, hpo, hp1, hp2⟩, hin⟩ := hj
  have hcrc : H.crcTable = ZlibNg.Crc32Tbl.crc_table := fJ.2.2.2.2.2.2.1.trans ok.crc
  obtain ⟨r, H3, e, hv3, f3, hp3, hk3⟩ := InflateTop.inflate_ok 0 hv hio hcrc
  refine Sat.bind ⟨r, H3, e, Sat.pure ?_⟩
  have hnext : C.h0.nextBlk ≤ H.nextBlk := fJ.2.2.2.2.2.2.2.2.2
  rw [InflateReach.stateIds_of hz hb, InflateTop.headerIds_eq hz hb hst hhd,
    InflateTop.outputRanges_eq hz hb hst hhd] at f3
  have hHR : headerRanges H none = [] := rfl
  rw [hHR, hpo] at f3
  have f3' : Frame H H3 [C.i] [C.nb, C.sb] [] [(.ref (.heap C.bo) C.oo, C.L0)] :=
    Frame.mono (Frame.widen f3 (List.mem_singleton_self _) hp1 (by omega)) (fun _ m => m)
      (fun x m => by simp at m ⊢; exact Or.inr m) (fun _ m => m) (fun _ m => m)
  have fN := Frame.trans fJ f3'
  have hnb3 : ∃ d, H3.bytes C.nb = some d := by
    obtain ⟨d', e1, -, -⟩ := f3.2.2.2.1 C.nb (by have := ok.nb_lt; omega) (by simpa using ok.nb_sb) dn hdn
    exact ⟨d', e1⟩
  obtain ⟨z3, hz3, hb3⟩ := hk3 z hz
  refine ⟨fun hr => ?_, hv3, fN, hnb3, z3, hz3, hb3.trans hb⟩
  obtain ⟨z', S', e1, e2, e3, e4, ⟨hle, hat⟩, ⟨ho1, bo', oo', p', ho2, ho3, ho4, ho5⟩, hprog⟩ :=
    hp3 hr z C.sb st hz hb hst
  rw [hpo] at ho2
  injection ho2 with ho2 ho2'
  injection ho2 with ho2
  subst ho2; subst ho2'
  have hd3 : ∃ d', H3.bytes C.bo = some d' ∧ C.oo + C.L0 ≤ d'.size := by
    obtain ⟨d', e1, e2, -⟩ := f3.2.2.2.1 C.bo (by have := ok.bo_lt; omega) (by simpa using ok.bo_sb) d hd
    exact ⟨d', e1, by omega⟩
  have hai : z'.avail_in.toNat ≤ z.avail_in.toNat := hle
  have hao : z'.avail_out.toNat ≤ z.avail_out.toNat := ho1
  refine ⟨⟨z', S', e1, e2, e3, by rw [e4, hhd], hv3, fN, hnb3, hd3, ⟨p', ho5, by omega, by dsimp only; omega⟩, ?_⟩, ?_⟩
  · unfold InJ at hin ⊢
    revert hin hat
    rcases hsrc : C.src with _ | ⟨rr, o⟩
    · intro hin hat
      obtain ⟨hn, ha, hl⟩ := hin
      rw [hn] at hat
      exact ⟨hat.1, hat.2, hl⟩
    · intro hin hat
      obtain ⟨⟨dd, hdd, hdds⟩, q, hq, hq1, hq2⟩ := hin
      rw [hq] at hat
      obtain ⟨dd', e5, e6⟩ := get_frame f3 (fun c hc => by
        obtain ⟨-, h2⟩ := ok.src rr o hsrc
        obtain ⟨h3, -⟩ := h2 c hc
        refine ⟨by omega, ?_⟩
        simp only [List.mem_singleton]
        intro e; subst e; exact (ok.src rr o hsrc).1 hc) hdd
      refine ⟨⟨dd', e5, by omega⟩, q + (z.avail_in - z'.avail_in).toNat, hat, by omega, ?_⟩
      rw [UInt32.toNat_sub_of_le _ _ hle]
      dsimp only
      omega
  · have hm' : left.toNat + len.toNat + (z.avail_in.toNat + z.avail_out.toNat) ≤ m := by
      simpa only [μ, hz] using hm
    show left.toNat + len.toNat + (match H3.streams C.i with
      | some z => z.avail_in.toNat + z.avail_out.toNat
      | none => 0) < m
    rw [e1]
    dsimp only
    have : z'.avail_in.toNat + z'.avail_out.toNat < z.avail_in.toNat + z.avail_out.toNat := by
      rcases hprog with h | h
      · have : z'.avail_in.toNat < z.avail_in.toNat := h
        omega
      · have : z'.avail_out.toNat < z.avail_out.toNat := h
        omega
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left this _) hm'

/-! ## Refilling the stream -/

/-- The chunk `x > max ? max : (unsigned)x` that a trip hands to the stream. -/
def chunk (x : UInt64) : UInt32 := if x > (-1 : Int32).toUInt32.toUInt64 then (-1 : Int32).toUInt32 else x.toUInt32

theorem chunk_toNat (x : UInt64) : (chunk x).toNat ≤ x.toNat ∧ (x - (chunk x).toUInt64).toNat = x.toNat - (chunk x).toNat := by
  have hm : ((-1 : Int32).toUInt32.toUInt64).toNat = 4294967295 := by decide
  have hm' : ((-1 : Int32).toUInt32).toNat = 4294967295 := by decide
  have hle : (chunk x).toNat ≤ x.toNat := by
    unfold chunk
    split
    · rename_i h
      have h' : ((-1 : Int32).toUInt32.toUInt64).toNat < x.toNat := UInt64.lt_iff_toNat_lt.mp h
      omega
    · rw [UInt64.toNat_toUInt32]; exact Nat.mod_le _ _
  refine ⟨hle, ?_⟩
  rw [UInt64.toNat_sub_of_le]
  · rw [UInt32.toNat_toUInt64]
  · rw [UInt64.le_iff_toNat_le, UInt32.toNat_toUInt64]; exact hle

theorem chunk_zero : chunk 0 = 0 := by decide

theorem space_get_streams (H : Heap) (X : Tbl (Option ZStream)) (r : BRef) :
    Space.get { H with streams := X } r = Space.get H r := by
  cases r <;> rfl

/-- `avail_out` empty: the stream gets the chunk `a` of `left`. -/
theorem J.setOut {C : Cx} {left len : UInt64} {H : Heap} (hj : J C left len H) {z : ZStream}
    (hz : H.streams C.i = some z) (h0 : z.avail_out = 0) (a : UInt32) (left' : UInt64)
    (ha : a.toNat + left'.toNat = left.toNat) :
    J C left' len { H with streams := upd H.streams C.i (some { z with avail_out := a }) } ∧
      ∀ e, μ C (e, left', len) { H with streams := upd H.streams C.i (some { z with avail_out := a }) } =
        μ C (e, left, len) H := by
  obtain ⟨z0, st, hz0, hb, hst, hhd, hv, fJ, hn, hd, ⟨p, hpo, hp1, hp2⟩, hin⟩ := hj
  rw [hz] at hz0; cases hz0
  refine ⟨⟨{ z with avail_out := a }, st, by simp, hb, hst, hhd, inv_setZ hv hz rfl,
    Frame.trans fJ (frame_streams H _ C.i (fun j hj => upd_ne _ _ _ _ hj) _ _ _), hn, hd,
    ⟨p, hpo, hp1, ?_⟩, ?_⟩, fun e => ?_⟩
  · rw [h0] at hp2; show p + a.toNat + left'.toNat ≤ _; simp at hp2; omega
  · unfold InJ at hin ⊢
    revert hin
    rcases C.src with _ | ⟨r, o⟩
    · exact id
    · intro hin; exact hin
  · simp only [μ, upd_same, hz]
    rw [h0]
    show left'.toNat + len.toNat + (z.avail_in.toNat + a.toNat) =
      left.toNat + len.toNat + (z.avail_in.toNat + (0 : UInt32).toNat)
    have : (0 : UInt32).toNat = 0 := rfl
    omega

/-- `avail_in` empty: the stream gets the chunk `a` of `len`. -/
theorem J.setIn {C : Cx} {left len : UInt64} {H : Heap} (hj : J C left len H) {z : ZStream}
    (hz : H.streams C.i = some z) (h0 : z.avail_in = 0) (a : UInt32) (len' : UInt64)
    (ha : a.toNat + len'.toNat = len.toNat) (hnull : C.src = .null → a = 0 ∧ len' = 0) :
    J C left len' { H with streams := upd H.streams C.i (some { z with avail_in := a }) } ∧
      ∀ e, μ C (e, left, len') { H with streams := upd H.streams C.i (some { z with avail_in := a }) } =
        μ C (e, left, len) H := by
  obtain ⟨z0, st, hz0, hb, hst, hhd, hv, fJ, hn, hd, hout, hin⟩ := hj
  rw [hz] at hz0; cases hz0
  refine ⟨⟨{ z with avail_in := a }, st, by simp, hb, hst, hhd, inv_setZ hv hz rfl,
    Frame.trans fJ (frame_streams H _ C.i (fun j hj => upd_ne _ _ _ _ hj) _ _ _), hn, hd, hout, ?_⟩, fun e => ?_⟩
  · unfold InJ at hin ⊢
    revert hin
    revert hnull
    rcases C.src with _ | ⟨r, o⟩
    · intro hnull hin
      obtain ⟨e1, e2⟩ := hnull rfl
      exact ⟨hin.1, e1, e2⟩
    · intro _ hin
      obtain ⟨hg, q, hq, hq1, hq2⟩ := hin
      rw [h0] at hq2
      refine ⟨hg, q, hq, hq1, ?_⟩
      show q + a.toNat + len'.toNat ≤ _
      simp at hq2; omega
  · simp only [μ, upd_same, hz]
    rw [h0]
    show left.toNat + len'.toNat + (a.toNat + z.avail_out.toNat) =
      left.toNat + len.toNat + ((0 : UInt32).toNat + z.avail_out.toNat)
    have : (0 : UInt32).toNat = 0 := rfl
    omega

/-- The last call of a trip and the test of `while (err == Z_OK)`. -/
theorem trip_end {C : Cx} (ok : C.OK) {L N : UInt64} {H : Heap} (hj : J C L N H) (e0 : Int32) {m : Nat}
    (hm : μ C (e0, L, N) H ≤ m) :
    Sat H (do let err ← inflate (some C.i) 0; pure (err, L, N)) (fun s1 H1 =>
      Sat H1 (pure (s1.1 == Z_OK, s1.1, s1.2.1, s1.2.2)) (fun cs H2 =>
        (cs.1 = true → J C cs.2.2.1 cs.2.2.2 H2 ∧ μ C cs.2 H2 < m) ∧ (cs.1 = false → Qe C cs.2 H2))) := by
  refine Sat.mono (step_inflate ok hj e0 hm) ?_
  rintro ⟨e, l, n⟩ H1 ⟨h1, h2⟩
  refine Sat.pure ⟨fun he => ?_, fun _ => h2⟩
  have : e = Z_OK := by simpa using he
  exact h1 this

/-- The `do … while` loop of `uncompress2_z`, from the invariant. -/
theorem loop_ok {C : Cx} (ok : C.OK) {L N : UInt64} {H : Heap} (hj : J C L N H) (hμ : μ C (Z_OK, L, N) H < fuel) :
    Sat H (cdoWhile
      (fun ((_, left, len) : Int32 × UInt64 × UInt64) => do
        let mut left := left
        let mut len := len
        if (← rdZ (some C.i) (·.avail_out)) == 0 then
          let a := if left > (-1 : Int32).toUInt32.toUInt64 then (-1 : Int32).toUInt32 else left.toUInt32
          wrZ (some C.i) fun z => { z with avail_out := a }
          left := left - a.toUInt64
        if (← rdZ (some C.i) (·.avail_in)) == 0 then
          let a := if len > (-1 : Int32).toUInt32.toUInt64 then (-1 : Int32).toUInt32 else len.toUInt32
          wrZ (some C.i) fun z => { z with avail_in := a }
          len := len - a.toUInt64
        let err ← inflate (some C.i) 0
        pure (err, left, len))
      (fun ((err, left, len) : Int32 × UInt64 × UInt64) => pure (err == Z_OK, (err, left, len)))
      (Z_OK, L, N)) (Qe C) := by
  refine sat_cdoWhile_heap (fun s H => J C s.2.1 s.2.2 H) (μ C) (Qe C) ?_ hj hμ
  rintro ⟨e0, left, len⟩ H hj
  dsimp only at hj ⊢
  obtain ⟨z, -, hz, -⟩ := id hj
  have hcl := chunk_toNat left
  have hcn := chunk_toNat len
  -- the second half of a trip: refill `avail_in` if empty, then `inflate`
  have tail : ∀ (L' : UInt64) (H' : Heap) (z' : ZStream), J C L' len H' → H'.streams C.i = some z' →
      μ C (e0, L', len) H' = μ C (e0, left, len) H →
      Sat H' (do
        let a ← rdZ (some C.i) (·.avail_in)
        if (a == 0) = true then do
          wrZ (some C.i) fun z => { z with avail_in := chunk len }
          let err ← inflate (some C.i) 0
          pure (err, L', len - (chunk len).toUInt64)
        else do
          let err ← inflate (some C.i) 0
          pure (err, L', len)) (fun s1 H1 =>
        Sat H1 (pure (s1.1 == Z_OK, s1.1, s1.2.1, s1.2.2)) (fun cs H2 =>
          (cs.1 = true → J C cs.2.2.1 cs.2.2.2 H2 ∧ μ C cs.2 H2 < μ C (e0, left, len) H) ∧
            (cs.1 = false → Qe C cs.2 H2))) := by
    intro L' H' z' hj' hz' hμ'
    refine Sat.bind (Sat.of_eq (rdZ_app hz' _) ?_)
    split
    · rename_i h0
      have h0' : z'.avail_in = 0 := by simpa using h0
      have hnull : C.src = .null → chunk len = 0 ∧ len - (chunk len).toUInt64 = 0 := by
        intro hs
        obtain ⟨z1, st1, h1, h2, h3, h4, h5, h6, h7, h8, h9, hin⟩ := hj'
        unfold InJ at hin
        rw [hs] at hin
        rw [hin.2.2]
        exact ⟨chunk_zero, by rw [chunk_zero]; rfl⟩
      obtain ⟨hj2, hμ2⟩ := J.setIn hj' hz' h0' (chunk len) (len - (chunk len).toUInt64) (by omega) hnull
      refine Sat.bind (Sat.of_eq (wrZ_app hz' _) ?_)
      exact trip_end ok hj2 e0 (Nat.le_of_eq ((hμ2 e0).trans hμ'))
    · exact trip_end ok hj' e0 (Nat.le_of_eq hμ')
  refine Sat.bind (Sat.of_eq (rdZ_app hz _) ?_)
  split
  · rename_i h0
    have h0' : z.avail_out = 0 := by simpa using h0
    obtain ⟨hj1, hμ1⟩ := J.setOut hj hz h0' (chunk left) (left - (chunk left).toUInt64) (by omega)
    refine Sat.bind (Sat.of_eq (wrZ_app hz _) ?_)
    exact tail _ _ _ hj1 (upd_same _ _ _) (hμ1 e0)
  · exact tail _ _ _ hj hz rfl

/-! ## The call -/

/-- A frame from facts on the blocks that existed before. -/
theorem frame_lt {h h' : Heap} {S B G : List Nat} {W : List (BPtr × Nat)}
    (hs : ∀ i, i ∉ S → h'.streams i = h.streams i) (hg : h'.gzheaders = h.gzheaders)
    (hb : ∀ b, b < h.nextBlk → b ∉ B → h'.istates b = h.istates b ∧ h'.iallocs b = h.iallocs b ∧
      h'.bytes b = h.bytes b)
    (hc : h'.consts = h.consts) (hcrc : h'.crcTable = h.crcTable) (hx : h'.x2nTable = h.x2nTable)
    (hbase : h'.baseAddr = h.baseAddr) (hn : h.nextBlk ≤ h'.nextBlk) : Frame h h' S B G W :=
  ⟨hs, fun k _ => by rw [hg], fun b h1 h2 => ⟨(hb b h1 h2).1, (hb b h1 h2).2.1⟩,
    fun b h1 h2 d hd => ⟨d, by rw [(hb b h1 h2).2.2]; exact hd, rfl, fun _ _ _ => rfl⟩,
    fun b h1 h2 hn' => by rw [(hb b h1 h2).2.2]; exact hn', hc, hcrc, hx, hbase, hn⟩

/-- The end of the stream: `inflateEnd`, the end of the local stream and of `buf`. -/
theorem end_ok {C : Cx} (ok : C.OK) {s : Int32 × UInt64 × UInt64} {H : Heap} (hq : Qe C s H) {α : Type} (k : ZStream → α) :
    Sat H (do
      let _ ← inflateEnd (some C.i)
      let z ← ldStream (some C.i)
      dropStream (some C.i)
      dropLocal (.ref (.heap C.nb) 0)
      pure (k z)) (fun _ H' => Frame C.h0 H' [C.i] [C.nb, C.sb] [] [(.ref (.heap C.bo) C.oo, C.L0)] ∧
        H'.streams C.i = none) := by
  obtain ⟨hv, fq, ⟨dn, hdn⟩, z, hz, hb⟩ := hq
  obtain ⟨i, z', b, e, hz', hb', he⟩ := InflateControl.inflateEnd_inv hv
  cases e
  rw [hz] at hz'; cases hz'
  rw [hb] at hb'; cases hb'
  refine Sat.bind (Sat.of_eq he ?_)
  refine Sat.bind (Sat.of_eq (InflateInv.ldStream_app (upd_same _ _ _)) ?_)
  refine Sat.bind (Sat.of_eq (dropStream_app (upd_same _ _ _)) ?_)
  have hdn' : (upd H.bytes C.sb none) C.nb = some dn := by rw [upd_ne _ _ _ _ ok.nb_sb]; exact hdn
  refine Sat.bind (Sat.of_eq (dropLocal_app hdn') ?_)
  refine Sat.pure ⟨Frame.trans fq (frame_lt (fun j hj => ?_) rfl (fun c _ hc => ?_) rfl rfl rfl rfl (Nat.le_refl _)),
    by simp⟩
  · have hj' : j ≠ C.i := by simpa using hj
    simp [upd_ne _ _ _ _ hj']
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hc
    simp [upd_ne _ _ _ _ hc.1, upd_ne _ _ _ _ hc.2]

theorem strLit_app (H : Heap) : strLitRef "1.3.2.zlib-ng" H = .ok (.ref (.str 0) 0, H) := by
  have hf : strTable.findIdx? (· == "1.3.2.zlib-ng") = some 0 :=
    Array.findIdx?_eq_some_iff_getElem.mpr ⟨by decide, by decide, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
  simp only [strLitRef, hf]

theorem init_app (i : Nat) :
    inflateInit_ (some i) (.ref (.str 0) 0) SIZEOF_Z_STREAM.toInt32 = inflateInit2 (some i) DEF_WBITS := by
  funext H
  have hc : CHECK_VER_STSIZE (.ref (.str 0) 0) SIZEOF_Z_STREAM.toInt32 H = .ok (false, H) := rfl
  simp only [inflateInit_, bind_app, hc, Bool.false_eq_true, ↓reduceIte]

theorem get_size_none {β : Type} (t : Tbl (Option β)) : t t.arr.size = none := by
  refine Classical.byContradiction fun hc => ?_
  exact absurd (Tbl.lt_size_of_get_ne t _ hc) (Nat.lt_irrefl _)

/-- The heap after `unsigned char buf[1]`. -/
def lbHeap (h : Heap) : Heap :=
  { h with
    bytes := upd h.bytes h.nextBlk (some (Array.ofFn (n := 1) fun i => Junk.of (h.garbage (2 ^ 41 + h.nextBlk) i.val)))
    nextBlk := h.nextBlk + 1 }

theorem localBlock_app (h : Heap) : localBlock 1 h = .ok (.ref (.heap h.nextBlk) 0, lbHeap h) := rfl

theorem uncompress2_z_some (h : Heap) (dest source : BPtr) (dl sl : UInt64) (hcg : CrcGlobals h)
    (hfr : FreshBlocks h) (hob : ObjBound h) (hdst : NullOrWrite h dest dl.toNat) (hsrc : NullOrRead h source sl.toNat)
    (hdisj : Disjoint dest dl.toNat source sl.toNat) :
    Sat h (uncompress2_z dest (some dl) source (some sl)) (fun _ h' => Frame h h' [] [] [] [(dest, dl.toNat)]) := by
  unfold uncompress2_z
  dsimp (config := { zeta := false }) only
  refine Sat.bind (Sat.of_eq (localBlock_app h) ?_)
  extract_lets fin len0 dl0 dest0 left0 jp left1 dl1 dest1
  have hnb_none : ∀ c, h.nextBlk ≤ c → h.bytes c = none := fun c hc => (hfr c hc).2.2
  have hlb : ∀ c, c ≠ h.nextBlk → (lbHeap h).bytes c = h.bytes c := fun c hc => upd_ne _ _ _ _ hc
  have hjp : ∀ (L dlx : UInt64) (D : BPtr),
      ((source = .null ∧ sl = 0) ∨ ∃ r o d, source = .ref r o ∧ Space.get h r = some d ∧ o + sl.toNat ≤ d.size ∧
        d.size < 2 ^ 63 ∧ ∀ c, r = .heap c → c < h.nextBlk) →
      (∃ bo oo d, D = .ref (.heap bo) oo ∧ (lbHeap h).bytes bo = some d ∧ oo + L.toNat ≤ d.size ∧ bo ≤ h.nextBlk ∧
        L.toNat ≤ 2 ^ 63 ∧ Disjoint D L.toNat source sl.toNat ∧ ((D = dest ∧ L.toNat = dl.toNat) ∨ bo = h.nextBlk)) →
      Sat (lbHeap h) (jp () L dlx D) (fun _ h' => Frame h h' [] [] [] [(dest, dl.toNat)]) := by
    intro L dlx D hS hD
    simp only [jp]
    -- the local stream
    refine Sat.bind (Sat.of_eq (show newStream {} (lbHeap h) = _ from rfl) ?_)
    refine Sat.bind (Sat.of_eq (wrZ_app (upd_same _ _ _) _) ?_)
    refine Sat.bind (Sat.of_eq (wrZ_app (upd_same _ _ _) _) ?_)
    refine Sat.bind (Sat.of_eq (wrZ_app (upd_same _ _ _) _) ?_)
    refine Sat.bind (Sat.of_eq (wrZ_app (upd_same _ _ _) _) ?_)
    refine Sat.bind (Sat.of_eq (wrZ_app (upd_same _ _ _) _) ?_)
    simp only [InflateInv.upd_upd]
    refine Sat.bind (Sat.of_eq (strLit_app _) ?_)
    rw [init_app]
    have hi0 : h.streams h.streams.arr.size = none := get_size_none _
    generalize hi0' : (lbHeap h).streams.arr.size = i0
    have hi0n : h.streams i0 = none := by rw [← hi0']; exact hi0
    generalize hH3 : ({ lbHeap h with streams := upd (lbHeap h).streams i0 (some { next_in := source }) } : Heap) = H3
    have hz3 : H3.streams i0 = some { next_in := source } := by rw [← hH3]; simp
    have hn3 : H3.nextBlk = h.nextBlk + 1 := by rw [← hH3]; rfl
    have his3 : H3.istates = h.istates ∧ H3.iallocs = h.iallocs := by rw [← hH3]; exact ⟨rfl, rfl⟩
    have f3 : ∀ W, Frame h H3 [i0] [h.nextBlk, h.nextBlk + 1] [] W := by
      intro W
      rw [← hH3]
      refine frame_lt (fun j hj => ?_) rfl (fun c hc _ => ⟨rfl, rfl, hlb c (by omega)⟩) rfl rfl rfl rfl
        (by show h.nextBlk ≤ h.nextBlk + 1; omega)
      have : j ≠ i0 := by simpa using hj
      simp [upd_ne _ _ _ _ this]; rfl
    obtain ⟨r, H4, e4, fr4, hinv4, -, hhead4, z4', hz4'⟩ := InflateAlloc.init2_ok hz3 (Or.inl rfl) (Or.inl rfl)
      (by rw [hn3, his3.1]; exact (hfr (h.nextBlk + 1) (by omega)).1)
      (by rw [hn3, his3.2]; exact (hfr (h.nextBlk + 1) (by omega)).2.1) DEF_WBITS
    refine Sat.bind (Sat.of_eq e4 ?_)
    have f4 : ∀ W, Frame h H4 [i0] [h.nextBlk, h.nextBlk + 1] [] W := fun W =>
      Frame.trans (f3 W) (Frame.mono fr4.frame (fun _ m => m) (fun _ m => nomatch m) (fun _ m => m) (fun _ m => nomatch m))
    have hb4 : H4.bytes h.nextBlk = (lbHeap h).bytes h.nextBlk := by
      rw [(fr4.old h.nextBlk (by omega)).2.2, ← hH3]
    split
    · -- `inflateInit` failed
      refine Sat.bind (Sat.of_eq (dropStream_app hz4') ?_)
      simp only [fin]
      refine Sat.bind (Sat.of_eq (dropLocal_app (d := Array.ofFn (n := 1) fun i =>
        Junk.of (h.garbage (2 ^ 41 + h.nextBlk) i.val)) (by rw [hb4]; simp [lbHeap])) ?_)
      refine Sat.pure ?_
      refine frame_fin (i := i0) (D := .ref (.heap h.nextBlk) 0) (L0 := 1) (sb := h.nextBlk + 1) (nb := h.nextBlk) ?_ ?_
        (Nat.le_refl _) (by omega) (Or.inr ⟨_, _, rfl, Nat.le_refl _⟩)
      · refine Frame.trans (f4 _) (frame_lt (fun j hj => ?_) rfl (fun c _ hc => ?_) rfl rfl rfl rfl (Nat.le_refl _))
        · have : j ≠ i0 := by simpa using hj
          simp [upd_ne _ _ _ _ this]
        · have : c ≠ h.nextBlk := by simp at hc; exact hc.1
          simp [upd_ne _ _ _ _ this]
      · simp [hi0n]
    · rename_i hr0
      have hr : r = Z_OK := by simpa using hr0
      obtain ⟨z4, st4, hz4, hb4s, hst4, hhd4, hni4, hai4⟩ := hhead4 hr
      have hv4 := hinv4 hr
      refine Sat.bind (Sat.of_eq (wrZ_app hz4 _) ?_)
      refine Sat.bind (Sat.of_eq (wrZ_app (upd_same _ _ _) _) ?_)
      simp only [InflateInv.upd_upd]
      generalize hH5 : ({ H4 with
        streams := upd H4.streams i0 (some { z4 with
          next_out := D
          avail_out := 0 }) } : Heap) = H5
      obtain ⟨bo, oo, d, rfl, hbo, hbos, hbole, hL, hdj, hdc⟩ := hD
      let C : Cx := ⟨H5, i0, h.nextBlk, h.nextBlk + 1, source, sl, bo, oo, L.toNat⟩
      have hn4 : h.nextBlk + 1 ≤ H4.nextBlk := hn3 ▸ fr4.next
      have hn5 : H5.nextBlk = H4.nextBlk := by rw [← hH5]
      have hb5 : H5.bytes = H4.bytes := by rw [← hH5]
      have hk5 : H5.consts = H4.consts := by rw [← hH5]
      have hcrc5 : H5.crcTable = h.crcTable := by
        rw [← hH5]; show H4.crcTable = _; rw [fr4.crc, ← hH3]; rfl
      have hz5 : H5.streams i0 = some { z4 with next_out := .ref (.heap bo) oo, avail_out := 0 } := by
        rw [← hH5]; simp
      have ok : C.OK := by
        refine ⟨by show bo ≠ h.nextBlk + 1; omega, by show h.nextBlk ≠ h.nextBlk + 1; omega,
          by show bo < H5.nextBlk; omega, by show h.nextBlk < H5.nextBlk; omega, ?_, hdj, hcrc5.trans hcg.1⟩
        intro r o hro
        have hro : source = .ref r o := hro
        show r ≠ BRef.heap (h.nextBlk + 1) ∧ ∀ c, r = BRef.heap c → c < H5.nextBlk ∧ c ≠ h.nextBlk
        rcases hS with ⟨hs0, -⟩ | ⟨r', o', d', hs0, -, -, -, hc⟩
        · rw [hs0] at hro; cases hro
        · rw [hs0] at hro; injection hro with e1 e2; subst e1; subst e2
          refine ⟨fun e => by have := hc _ e; omega, fun c hc' => ⟨by have := hc c hc'; omega, by
            have := hc c hc'; omega⟩⟩
      have hj : J C L sl H5 := by
        rw [hn3] at hb4s hst4
        have hi5 : H5.istate (h.nextBlk + 1) = H4.istate (h.nextBlk + 1) := by rw [← hH5]; rfl
        have h0 : (0 : UInt32).toNat = 0 := rfl
        refine ⟨_, st4, hz5, hb4s, by rw [hi5]; exact hst4, hhd4, ?_, ?_, ?_, ?_,
          ⟨oo, rfl, Nat.le_refl _, by show oo + (0 : UInt32).toNat + L.toNat ≤ oo + L.toNat; omega⟩, ?_⟩
        · rw [← hH5]
          exact inv_setZ hv4 hz4 rfl
        · exact InflateTop.frame_refl _ _ _ _ _
        · show ∃ d, H5.bytes h.nextBlk = some d
          rw [hb5, (fr4.old h.nextBlk (by omega)).2.2, ← hH3]
          exact ⟨_, upd_same _ _ _⟩
        · show ∃ d, H5.bytes bo = some d ∧ oo + L.toNat ≤ d.size
          rw [hb5, (fr4.old bo (by omega)).2.2, ← hH3]
          exact ⟨d, hbo, hbos⟩
        · show InJ source sl H5 z4.next_in z4.avail_in sl
          rw [hni4, hai4]
          rcases hS with ⟨rfl, rfl⟩ | ⟨r, o, d', rfl, hgd, hgs, -, hc⟩
          · exact ⟨rfl, rfl, rfl⟩
          · obtain ⟨d'', e1, e2⟩ := get_frame (f4 []) (fun c e => ⟨hc c e, by
              have := hc c e; simp; omega⟩) hgd
            refine ⟨⟨d'', ?_, by omega⟩, o, rfl, Nat.le_refl _, by
              show o + (0 : UInt32).toNat + sl.toNat ≤ o + sl.toNat; omega⟩
            rw [← hH5, space_get_streams]; exact e1
      have hμ : μ C (Z_OK, L, sl) H5 < fuel := by
        have hsl : sl.toNat < 2 ^ 63 := by
          rcases hS with ⟨-, rfl⟩ | ⟨r, o, d', -, -, hgs, hds, -⟩
          · show (0 : UInt64).toNat < _; decide
          · omega
        show L.toNat + sl.toNat + (match H5.streams i0 with
          | some z => z.avail_in.toNat + z.avail_out.toNat
          | none => 0) < 2 ^ 64
        rw [hz5]
        show L.toNat + sl.toNat + (z4.avail_in.toNat + (0 : UInt32).toNat) < 2 ^ 64
        rw [hai4]
        show L.toNat + sl.toNat + ((0 : UInt32).toNat + (0 : UInt32).toNat) < 2 ^ 64
        have : (0 : UInt32).toNat = 0 := rfl
        omega
      refine Sat.bind (Sat.mono (loop_ok ok hj hμ) ?_)
      intro s6 H6 hq
      have f5 : Frame h H5 [i0] [h.nextBlk, h.nextBlk + 1] [] [(.ref (.heap bo) oo, L.toNat)] := by
        refine Frame.trans (f4 _) ?_
        rw [← hH5]
        exact frame_streams H4 _ i0 (fun j hj => upd_ne _ _ _ _ hj) _ _ _
      have fin_ok : ∀ (H' : Heap), Frame C.h0 H' [C.i] [C.nb, C.sb] [] [(.ref (.heap C.bo) C.oo, C.L0)] →
          H'.streams C.i = none → Frame h H' [] [] [] [(dest, dl.toNat)] := by
        intro H' f' hn'
        refine frame_fin (i := i0) (Frame.trans f5 f') (by rw [hi0n]; exact hn') (Nat.le_refl _) (by omega) ?_
        rcases hdc with ⟨e1, e2⟩ | e
        · exact Or.inl ⟨e1, e2⟩
        · exact Or.inr ⟨bo, oo, rfl, by omega⟩
      obtain ⟨-, -, -, z6, hz6, -⟩ := id hq
      refine Sat.bind (Sat.of_eq (InflateInv.ldStream_app hz6) ?_)
      simp only [fin]
      split
      · exact Sat.mono (end_ok ok hq _) (fun _ H' ⟨f', hn'⟩ => fin_ok H' f' hn')
      · split
        · exact Sat.mono (end_ok ok hq _) (fun _ H' ⟨f', hn'⟩ => fin_ok H' f' hn')
        · exact Sat.mono (end_ok ok hq _) (fun _ H' ⟨f', hn'⟩ => fin_ok H' f' hn')
  have hbuf : (lbHeap h).bytes h.nextBlk =
      some (Array.ofFn (n := 1) fun i => Junk.of (h.garbage (2 ^ 41 + h.nextBlk) i.val)) := upd_same _ _ _
  split
  · -- `Z_STREAM_ERROR` on a NULL buffer with a nonzero length
    simp only [fin]
    refine Sat.bind (Sat.of_eq (dropLocal_app hbuf) ?_)
    refine Sat.pure (frame_lt (fun _ _ => rfl) rfl (fun c hc _ => ⟨rfl, rfl, ?_⟩) rfl rfl rfl rfl
      (by show h.nextBlk ≤ h.nextBlk + 1; omega))
    show upd (lbHeap h).bytes h.nextBlk none c = h.bytes c
    rw [upd_ne _ _ _ _ (by omega), hlb c (by omega)]
  rename_i hc
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, not_or, not_and] at hc
  obtain ⟨hcs, hcd⟩ := hc
  have hS : (source = .null ∧ sl = 0) ∨ ∃ r o d, source = .ref r o ∧ Space.get h r = some d ∧
      o + sl.toNat ≤ d.size ∧ d.size < 2 ^ 63 ∧ ∀ c, r = .heap c → c < h.nextBlk := by
    rcases hsrc with e | ⟨r, o, d, e, hg, hle⟩
    · left
      refine ⟨e, ?_⟩
      by_cases h0 : sl > 0
      · exact absurd e (hcs h0)
      · simp only [gt_iff_lt, UInt64.lt_iff_toNat_lt] at h0
        have : (0 : UInt64).toNat = 0 := rfl
        exact UInt64.toNat_inj.mp (by show sl.toNat = 0; omega)
    · right
      refine ⟨r, o, d, e, hg, hle, hob r d hg, fun c hrc => ?_⟩
      subst hrc
      refine Classical.byContradiction fun hlt => ?_
      have : h.bytes c = none := hnb_none c (by omega)
      have hg' : h.bytes c = some d := hg
      rw [this] at hg'; cases hg'
  split
  · rename_i hdl
    have hdl0 : dl ≠ 0 := by simpa using hdl
    have hdl1 : dl > 0 := by
      rw [gt_iff_lt, UInt64.lt_iff_toNat_lt]
      have : dl.toNat ≠ 0 := fun e => hdl0 (UInt64.toNat_inj.mp (by rw [e]; rfl))
      show 0 < dl.toNat; omega
    rcases hdst with e | ⟨b, off, d, e, hd, hle⟩
    · exact absurd e (hcd hdl1)
    have hb : b < h.nextBlk := by
      refine Classical.byContradiction fun hlt => ?_
      rw [hnb_none b (by omega)] at hd; cases hd
    have hds : d.size < 2 ^ 63 := hob (.heap b) d hd
    exact hjp dl 0 dest hS ⟨b, off, d, e, by rw [hlb b (by omega)]; exact hd, hle, by omega, by omega, hdisj,
      Or.inl ⟨e ▸ rfl, rfl⟩⟩
  · refine hjp 1 dl _ hS ⟨h.nextBlk, 0, _, rfl, hbuf, by simp, Nat.le_refl _, by decide, ?_, Or.inr rfl⟩
    rcases hS with ⟨rfl, -⟩ | ⟨r, o, d, rfl, -, -, -, hc⟩
    · trivial
    · refine Or.inl fun e => ?_
      have := hc h.nextBlk e.symm
      omega

/-- A `NULL` length cell: `Z_STREAM_ERROR`, and only `buf` came and went. -/
theorem fin_frame (h : Heap) (W : List (BPtr × Nat)) :
    Frame h { lbHeap h with bytes := upd (lbHeap h).bytes h.nextBlk none } [] [] [] W := by
  refine frame_lt (fun _ _ => rfl) rfl (fun c hc _ => ⟨rfl, rfl, ?_⟩) rfl rfl rfl rfl
    (by show h.nextBlk ≤ h.nextBlk + 1; omega)
  show upd (lbHeap h).bytes h.nextBlk none c = h.bytes c
  rw [upd_ne _ _ _ _ (by omega)]
  exact upd_ne _ _ _ _ (by omega)

theorem uncompress2_z_safety : Goal.uncompress2_z_safety := by
  intro h dest source destLen sourceLen hcg hfr hob hdst hsrc hdisj
  refine InflateKeep.iframe_up (InflateKeep.K.ZlibNg.Uncompr.uncompress2_z _ _ _ _) ?_
  have hbuf : (lbHeap h).bytes h.nextBlk =
      some (Array.ofFn (n := 1) fun i => Junk.of (h.garbage (2 ^ 41 + h.nextBlk) i.val)) := upd_same _ _ _
  rcases sourceLen with _ | sl
  · refine ⟨(Z_STREAM_ERROR, destLen, none), _, ?_, fin_frame h _⟩
    simp only [C.run, uncompress2_z, bind_app, localBlock_app, dropLocal_app hbuf]
    rfl
  rcases destLen with _ | dl
  · refine ⟨(Z_STREAM_ERROR, none, some sl), _, ?_, fin_frame h _⟩
    simp only [C.run, uncompress2_z, bind_app, localBlock_app, dropLocal_app hbuf]
    rfl
  obtain ⟨r, h', e, f⟩ := uncompress2_z_some h dest source dl sl hcg hfr hob hdst hsrc hdisj
  exact ⟨r, h', e, f⟩

theorem uncompress2_safety : Goal.uncompress2_safety := by
  intro h dest source destLen sourceLen hcg hfr hob hdst hsrc hdisj
  obtain ⟨r, h', e, f⟩ := uncompress2_z_safety h dest source (some (destLen.getD 0)) (some (sourceLen.getD 0)) hcg
    hfr hob hdst hsrc hdisj
  exact ⟨_, h', by simp only [C.run, uncompress2, bind_app]; rw [show uncompress2_z _ _ _ _ h = _ from e]; rfl, f⟩

theorem uncompress_z_safety : Goal.uncompress_z_safety := by
  intro h dest source destLen sourceLen hcg hfr hob hdst hsrc hdisj
  obtain ⟨r, h', e, f⟩ := uncompress2_z_safety h dest source destLen (some sourceLen) hcg hfr hob hdst hsrc hdisj
  exact ⟨_, h', by simp only [C.run, uncompress_z, bind_app]; rw [show uncompress2_z _ _ _ _ h = _ from e]; rfl, f⟩

theorem uncompress_safety : Goal.uncompress_safety := by
  intro h dest source destLen sourceLen hcg hfr hob hdst hsrc hdisj
  obtain ⟨r, h', e, f⟩ := uncompress2_safety h dest source destLen (some sourceLen) hcg hfr hob hdst hsrc hdisj
  exact ⟨_, h', by simp only [C.run, uncompress, bind_app]; rw [show uncompress2 _ _ _ _ h = _ from e]; rfl, f⟩

end ZlibNgF.Proof.Uncompress
