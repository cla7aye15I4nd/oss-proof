import ZlibNgF.Proof.«inflate.c.codelens-mode»
import ZlibNgF.Proof.«inflate.c.callees»

/-!
# The decoding modes of `inflate` (`ZlibNgF`)

`LEN_`, `LEN`, `LENEXT`, `DIST`, `DISTEXT`, `MATCH`. `LEN` either hands the stream to `inflate_fast_c` /
`inflate_fast_safe_c` (`fastFacts`, after `RESTORE()`, then `LOAD()`), or decodes one symbol with `decodeSym`: a
root lookup and at most one link into a sub-table of the `CodeTable` (a link takes the root bits, so the
second-level `BITS(last.bits + last.op)` shifts by less than 32). `MATCH` copies from the window (the distance
back past the output written in this call is at most `whave`) or, with `chunkmemset_safe_c` (`copyFacts`), from the
output already written in this call (`offset ≤ out - left`). The `DISTEXT` store of the distance is followed on the
heap together with the change to `MATCH`, as the invariant asks `offset < 65536` only while in `DISTEXT`.
-/

set_option autoImplicit false
namespace ZlibNgF.Proof.InflateLoop
open C ZlibNgF.Spec ZlibNg.Inflate
open ZlibNgF.Proof.InflateInv (Inv Core view ModeOK DecodeMode)
open ZlibNgF.Proof.InflateX
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.mono Sat.of_eq St Touch)
open ZlibNgF.Proof.InflateTab (TabAt CodeTable EntryOK linkTest)
open ZlibNg.InflateP (CODE_BITS CODE_EXTRA)
open ZlibNgF.Proof.InflateDict (copyFold copyFold_size add_heap)

/-- `p[k]` inside the region of a table. -/
theorem tab_index' {H : Heap} {r : CodeRef} {o : Nat} {a : Array Code} (hg : Space.get H r = some a) {k : Nat}
    (hk : o + k < a.size) : Ptr.index (.ref r o : CodePtr) (Int.ofNat k) H = .ok (a[o + k]!, H) := by
  have hc : o ≤ a.size ∧ 0 ≤ (o : Int) + Int.ofNat k ∧ (o : Int) + Int.ofNat k ≤ (a.size : Int) := by
    simp only [Int.ofNat_eq_natCast]; omega
  have e1 : ((o : Int) + Int.ofNat k).toNat = o + k := by simp only [Int.ofNat_eq_natCast]; omega
  simp only [Ptr.index, Ptr.add, Ptr.load, bind_app, hg, hc, and_self, ↓reduceIte, e1, hk, ↓reduceDIte,
    getElem!_pos a (o + k) hk]

/-- `BITS(n)` is below `2 ^ n` for `n < 32`. -/
theorem bits_lt32 (x : UInt64) (n : UInt32) (hn : n.toNat < 32) :
    (x &&& ((1 : UInt32) <<< n - 1).toUInt64).toNat < 2 ^ n.toNat := by
  have hk : n.toNat % 32 = n.toNat := Nat.mod_eq_of_lt hn
  have hp : 2 ^ n.toNat < 2 ^ 32 := Nat.pow_lt_pow_right (by decide) hn
  have h1 : ((1 : UInt32) <<< n).toNat = 2 ^ n.toNat := by
    rw [UInt32.toNat_shiftLeft, hk]
    show 1 <<< n.toNat % 2 ^ 32 = _
    rw [Nat.shiftLeft_eq, Nat.one_mul]; exact Nat.mod_eq_of_lt hp
  have h0 : 1 ≤ 2 ^ n.toNat := Nat.one_le_two_pow
  have h2 : ((1 : UInt32) <<< n - 1).toNat = 2 ^ n.toNat - 1 := by
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, h1]; exact h0), h1]; rfl
  have h3 : ((1 : UInt32) <<< n - 1).toUInt64.toNat = 2 ^ n.toNat - 1 := by rw [UInt32.toNat_toUInt64, h2]
  rw [UInt64.toNat_and, h3]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by omega)

theorem andf0_16 : ∀ x : UInt8, x &&& 0xf0 = 0 → x &&& 16 = 0 := by decide
theorem andf0_15 : ∀ x : UInt8, x &&& 0xf0 = 0 → x &&& 15 = x := by decide
theorem andf0_lt' : ∀ x : UInt8, x &&& 0xf0 = 0 → x.toNat < 16 := by decide

theorem link_f0 {dist : Bool} {e : Code} (h : linkTest dist e = true) : e.op &&& 0xf0 = 0 := by
  unfold linkTest at h
  cases dist <;> simp_all

theorem cb_link {e : Code} (h : e.op &&& 0xf0 = 0) : CODE_BITS e = e.bits.toUInt32 := by
  unfold CODE_BITS
  have : (e.op &&& 16 != 0) = false := by simpa using andf0_16 _ h
  rw [this]; rfl

/-- The first-level lookup loop of `decodeSym`. -/
theorem dec1_ok {E : Env} (eo : EnvOK E) {l : IL} {H : Heap} {z : ZStream} {S : InflateState}
    (li : LI E l H z S) {r : CodeRef} {o e : Nat} {a : Array Code} (hg : Space.get H r = some a) {nb : UInt32}
    {dist : Bool} (t : CodeTable a o e nb.toNat 28 dist) :
    SatX H l (xloopBrk (do
        let b ← BITS nb
        let here : Code ← Ptr.index (.ref r o : CodePtr) (Int.ofNat b.toNat)
        modify fun l => { l with here := here }
        if CODE_BITS here <= (← get).bits.toUInt32 then return true
        PULLBYTE
        return false))
      (fun res l' H' => H' = H ∧ LI E l' H z S ∧ l'.left = l.left ∧
        8 * l'.have_.toNat + l'.bits.toNat = 8 * l.have_.toNat + l.bits.toNat ∧
        match res with
        | .ok () => (∃ j, o ≤ j ∧ j < o + 2 ^ nb.toNat ∧ l'.here = a[j]!) ∧
            (CODE_BITS l'.here).toNat ≤ l'.bits.toNat
        | .error e => e = .leave) := by
  have hn15 : nb.toNat ≤ 15 := t.n_le
  unfold xloopBrk
  refine xwhileBrk_rank (fun l' H' => H' = H ∧ LI E l' H z S ∧ l'.left = l.left ∧
      8 * l'.have_.toNat + l'.bits.toNat = 8 * l.have_.toNat + l.bits.toNat) (fun l' _ => l'.have_.toNat) _ ?_
    ⟨rfl, li, rfl, rfl⟩ (by have := l.have_.toNat_lt; unfold fuel; omega)
  rintro l1 H1 ⟨hH1, li1, hl1, hb1⟩
  rw [hH1]
  refine SatX.pure ?_
  dsimp only
  refine SatX.bind (bits_ok nb (by rw [UInt32.lt_iff_toNat_lt]; show _ < 32; omega) ?_)
  have hk := bits_lt l1.hold nb hn15
  refine SatX.bind (SatX.lift_eq (tab_index hg t hk) ?_)
  generalize (l1.hold &&& ((1 : UInt32) <<< nb - 1).toUInt64).toNat = k at hk ⊢
  refine SatX.bind (SatX.modify ?_)
  have hj2 : o + k < e := by have := t.root; omega
  have hent := t.ent _ (Nat.le_add_right _ _) hj2
  have li2 : LI E { l1 with here := a[o + k]! } H z S := li1.locals rfl rfl rfl rfl rfl rfl
  refine SatX.bind (SatX.get ?_)
  dsimp only
  split
  · rename_i hle
    refine SatX.pure ⟨rfl, li2, hl1, hb1, ⟨o + k, Nat.le_add_right _ _, by omega, rfl⟩, ?_⟩
    have := UInt32.le_iff_toNat_le.mp hle; rw [UInt8.toNat_toUInt32] at this; exact this
  · rename_i hgt
    have hgt' : l1.bits.toNat < (CODE_BITS a[o + k]!).toNat := by
      have := UInt32.lt_iff_toNat_lt.mp (UInt32.not_le.mp hgt); rw [UInt8.toNat_toUInt32] at this; exact this
    have h28 := hent.bits_le
    have hcb := hent.cb_le
    refine SatX.bind (SatX.mono (pullbyte_ok eo li2 (by show l1.bits.toNat + 8 ≤ 39; omega)) ?_)
    rintro res l3 H3 ⟨hH3, hres⟩
    rw [hH3]
    match res, hres with
    | .error e, ⟨he, hl3⟩ => rw [he, hl3]; exact ⟨rfl, li2, hl1, hb1, rfl⟩
    | .ok (), ⟨li3, p3, hb3, hh3⟩ =>
      refine SatX.pure ⟨⟨rfl, li3, ?_, ?_⟩, ?_⟩
      · rw [p3.1]; exact hl1
      · rw [p3.2]; exact hb1
      · show l3.have_.toNat < l1.have_.toNat
        have : l3.have_.toNat + 1 = l1.have_.toNat := hh3
        omega

/-- The second-level lookup loop of `decodeSym`, after the link `a[j]` of `lb` (the root) bits. -/
theorem dec2_ok {E : Env} (eo : EnvOK E) {l : IL} {H : Heap} {z : ZStream} {S : InflateState}
    (li : LI E l H z S) {r : CodeRef} {o e : Nat} {a : Array Code} (hg : Space.get H r = some a) {n : Nat}
    {dist : Bool} (t : CodeTable a o e n 28 dist) {j : Nat} (hj1 : o ≤ j) (hj2 : j < e)
    (hl : linkTest dist a[j]! = true) (lb : UInt32) (hlb : lb.toNat = n) :
    SatX H l (xloopBrk (do
        let b ← BITS (lb + (a[j]!.op &&& 15).toUInt32)
        let idx := a[j]!.val.toUInt64 + (b >>> lb.toUInt64)
        let here : Code ← Ptr.index (.ref r o : CodePtr) (Int.ofNat idx.toNat)
        modify fun l => { l with here := here }
        if lb + CODE_BITS here <= (← get).bits.toUInt32 then return true
        PULLBYTE
        return false))
      (fun res l' H' => H' = H ∧ LI E l' H z S ∧ l'.left = l.left ∧
        8 * l'.have_.toNat + l'.bits.toNat = 8 * l.have_.toNat + l.bits.toNat ∧
        match res with
        | .ok () => EntryOK l'.here 28 dist ∧ n + (CODE_BITS l'.here).toNat ≤ l'.bits.toNat
        | .error e => e = .leave) := by
  have hn15 : n ≤ 15 := t.n_le
  have hf0 := link_f0 hl
  have hop16 : a[j]!.op.toNat < 16 := andf0_lt' _ hf0
  have hop : (a[j]!.op &&& 15).toUInt32.toNat = a[j]!.op.toNat := by rw [andf0_15 _ hf0]; exact UInt8.toNat_toUInt32 _
  have hn2 : (lb + (a[j]!.op &&& 15).toUInt32).toNat = n + a[j]!.op.toNat := by
    rw [UInt32.toNat_add, hop, hlb]; exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨hreg, hsub⟩ := t.link j hj1 hj2 hl
  have hfits := t.fits
  unfold xloopBrk
  refine xwhileBrk_rank (fun l' H' => H' = H ∧ LI E l' H z S ∧ l'.left = l.left ∧
      8 * l'.have_.toNat + l'.bits.toNat = 8 * l.have_.toNat + l.bits.toNat) (fun l' _ => l'.have_.toNat) _ ?_
    ⟨rfl, li, rfl, rfl⟩ (by have := l.have_.toNat_lt; unfold fuel; omega)
  rintro l1 H1 ⟨hH1, li1, hl1, hb1⟩
  rw [hH1]
  refine SatX.pure ?_
  dsimp only
  refine SatX.bind (bits_ok _ (by rw [UInt32.lt_iff_toNat_lt, hn2]; show _ < 32; omega) ?_)
  have hk := bits_lt32 l1.hold (lb + (a[j]!.op &&& 15).toUInt32) (by rw [hn2]; omega)
  rw [hn2] at hk
  generalize (l1.hold &&& ((1 : UInt32) <<< (lb + (a[j]!.op &&& 15).toUInt32) - 1).toUInt64) = v at hk ⊢
  have hsh : (v >>> lb.toUInt64).toNat < 2 ^ a[j]!.op.toNat := by
    rw [UInt64.toNat_shiftRight, UInt32.toNat_toUInt64, hlb, Nat.mod_eq_of_lt (by omega : n < 64),
      Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, Nat.add_comm]
    exact hk
  have hvl := a[j]!.val.toNat_lt
  have hidx : (a[j]!.val.toUInt64 + (v >>> lb.toUInt64)).toNat = a[j]!.val.toNat + (v >>> lb.toUInt64).toNat := by
    rw [UInt64.toNat_add, UInt16.toNat_toUInt64]
    have : 2 ^ a[j]!.op.toNat ≤ 2 ^ 16 := Nat.pow_le_pow_right (by decide) (by omega)
    exact Nat.mod_eq_of_lt (by show _ < 18446744073709551616; omega)
  generalize (v >>> lb.toUInt64).toNat = kk at hsh hidx
  have hin : o + (a[j]!.val.toNat + kk) < a.size := by omega
  refine SatX.bind (SatX.lift_eq (by rw [hidx]; exact tab_index' hg hin) ?_)
  refine SatX.bind (SatX.modify ?_)
  obtain ⟨hs28, -, -⟩ := hsub kk hsh
  have hjb := t.link_bits j hj1 hj2 hl
  have hent := t.ent (o + (a[j]!.val.toNat + kk)) (by omega) (by omega)
  rw [show o + (a[j]!.val.toNat + kk) = o + a[j]!.val.toNat + kk by omega] at hent ⊢
  have li2 : LI E { l1 with here := a[o + a[j]!.val.toNat + kk]! } H z S := li1.locals rfl rfl rfl rfl rfl rfl
  have hcbn : (lb + CODE_BITS a[o + a[j]!.val.toNat + kk]!).toNat = n + (CODE_BITS a[o + a[j]!.val.toNat + kk]!).toNat := by
    have := hent.cb_le; have := hent.bits_le
    rw [UInt32.toNat_add, hlb]; exact Nat.mod_eq_of_lt (by omega)
  refine SatX.bind (SatX.get ?_)
  dsimp only
  split
  · rename_i hle
    refine SatX.pure ⟨rfl, li2, hl1, hb1, hent, ?_⟩
    have := UInt32.le_iff_toNat_le.mp hle; rw [UInt8.toNat_toUInt32, hcbn] at this; exact this
  · rename_i hgt
    have hgt' : l1.bits.toNat < n + (CODE_BITS a[o + a[j]!.val.toNat + kk]!).toNat := by
      have := UInt32.lt_iff_toNat_lt.mp (UInt32.not_le.mp hgt); rw [UInt8.toNat_toUInt32, hcbn] at this; exact this
    have hcb := hent.cb_le
    refine SatX.bind (SatX.mono (pullbyte_ok eo li2 (by show l1.bits.toNat + 8 ≤ 39; omega)) ?_)
    rintro res l3 H3 ⟨hH3, hres⟩
    rw [hH3]
    match res, hres with
    | .error e, ⟨he, hl3⟩ => rw [he, hl3]; exact ⟨rfl, li2, hl1, hb1, rfl⟩
    | .ok (), ⟨li3, p3, hb3, hh3⟩ =>
      refine SatX.pure ⟨⟨rfl, li3, ?_, ?_⟩, ?_⟩
      · rw [p3.1]; exact hl1
      · rw [p3.2]; exact hb1
      · show l3.have_.toNat < l1.have_.toNat
        have : l3.have_.toNat + 1 = l1.have_.toNat := hh3
        omega


/-- `decodeSym`: the table lookup of `LEN` / `DIST`, with at most one link. -/
theorem decodeSym_ok {E : Env} (eo : EnvOK E) {l : IL} {H : Heap} {z : ZStream} {S : InflateState}
    (li : LI E l H z S) {r : CodeRef} {o e : Nat} {a : Array Code} (hg : Space.get H r = some a) {nb : UInt32}
    {dist : Bool} (t : CodeTable a o e nb.toNat 28 dist) :
    SatX H l (decodeSym E.c (.ref r o) nb (linkTest dist))
      (fun res l' H' => ∃ S', LI E l' H' z S' ∧ S' = { S with back := S'.back } ∧ l'.left = l.left ∧
        8 * l'.have_.toNat + l'.bits.toNat ≤ 8 * l.have_.toNat + l.bits.toNat ∧
        match res with
        | .ok () => EntryOK l'.here 28 dist ∧ (CODE_BITS l'.here).toNat ≤ l'.bits.toNat
        | .error e => e = .leave) := by
  unfold decodeSym
  refine SatX.bind (SatX.mono (dec1_ok eo li hg t) ?_)
  rintro res l1 H1 ⟨rfl, li1, hl1, hb1, hres⟩
  match res, hres with
  | .error e, he => exact ⟨S, li1, rfl, hl1, by omega, he⟩
  | .ok (), ⟨⟨j, hj1, hj2, hhere⟩, hcb⟩ =>
  refine SatX.bind (SatX.get ?_)
  dsimp only
  have hent := t.ent j hj1 (by have := t.root; omega)
  rw [hhere] at hcb ⊢
  split
  · rename_i hl
    have hlb := t.link_bits j hj1 (by have := t.root; omega) hl
    rw [cb_link (link_f0 hl)]
    refine SatX.bind (SatX.modify ?_)
    have li2 : LI E { l1 with last := a[j]! } H1 z S := li1.locals rfl rfl rfl rfl rfl rfl
    refine SatX.bind (SatX.mono (dec2_ok eo li2 hg t hj1 (by have := t.root; omega) hl a[j]!.bits.toUInt32
      (by rw [UInt8.toNat_toUInt32]; exact hlb)) ?_)
    rintro res l3 H3 ⟨rfl, li3, hl3, hb3, hres⟩
    dsimp only at hl3 hb3
    match res, hres with
    | .error e, he => exact ⟨S, li3, rfl, by rw [hl3]; exact hl1, by omega, he⟩
    | .ok (), ⟨hent3, hcb3⟩ =>
    have hbn : a[j]!.bits.toUInt32.toNat = a[j]!.bits.toNat := UInt8.toNat_toUInt32 _
    have h28 := hent.bits_le
    refine SatX.bind (dropbits_ok _ (by rw [UInt32.lt_iff_toNat_lt, hbn]; show _ < 64; omega) ?_)
    have hd := drop_toNat (b := l3.bits) (n := a[j]!.bits.toUInt32) (by rw [hbn]; omega) (by rw [hbn]; omega)
    rw [hbn] at hd
    have li4 := li3.drop a[j]!.bits.toUInt32 (by rw [hbn]; omega) (by rw [hbn]; omega)
    refine SatX.lift (Sat.mono (li4.wrS (fun s => { s with back := s.back + a[j]!.bits.toUInt32.toInt32 })
      (fun _ _ c => c) rfl) ?_)
    intro _ H5 li5
    refine ⟨_, li5, rfl, by rw [hl3]; exact hl1, ?_, hent3, ?_⟩
    · show 8 * l3.have_.toNat + (l3.bits - a[j]!.bits.toUInt32.toUInt8).toNat ≤ _
      rw [hd]; omega
    · show (CODE_BITS l3.here).toNat ≤ (l3.bits - a[j]!.bits.toUInt32.toUInt8).toNat
      rw [hd]; omega
  · exact SatX.pure ⟨S, li1, rfl, hl1, by omega, hhere ▸ hent, by rw [hhere]; exact hcb⟩

theorem rank_MATCH : rank MATCH = 6 := by decide

/-- The end of `MATCH`: `left -= copy; state->length -= copy; if (state->length == 0) state->mode = LEN;`. -/
def mtail (c : Ctx) (copy : UInt32) : X Unit := do
  modify fun l => { l with left := l.left - copy }
  wrS c.st fun s => { s with length := s.length - copy }
  if (← rdS c.st (·.length)) == 0 then setMode c.st LEN else pure ()

theorem mtail_ok {E : Env} {m : Nat} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (c : UInt32)
    (li : LI E { l with left := l.left - c } H z S) (hm : S.mode = MATCH) (hc : c ≤ S.length)
    (hc1 : 1 ≤ c.toNat ∨ S.length = 0) (hcl : c ≤ l.left)
    (hμ : 32 * (8 * l.have_.toNat + l.bits.toNat + l.left.toNat) + 6 ≤ m) :
    SatX H l (mtail E.c c) (Post E m) := by
  unfold mtail
  refine SatX.bind (SatX.modify ?_)
  refine SatX.bind (SatX.lift (Sat.mono (li.wrS (fun s => { s with length := s.length - c })
    (fun _ _ c => { c with }) rfl) ?_))
  intro _ H1 li1
  refine SatX.bind (SatX.lift_eq (li1.rdS (·.length)) ?_)
  have hcl' : c.toNat ≤ l.left.toNat := hcl
  have hsl : (l.left - c).toNat = l.left.toNat - c.toNat := UInt32.toNat_sub_of_le _ _ hcl
  dsimp only
  split
  · refine SatX.lift (Sat.mono (li1.setLen (by rw [hm]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))) ?_)
    intro _ H2 li2
    refine post_ok li2 ?_
    unfold μ; dsimp only; rw [rank_LEN, hsl]; omega
  · rename_i hne
    refine SatX.pure (post_ok li1 ?_)
    have hne' : S.length - c ≠ 0 := by simpa using hne
    have h1 : 1 ≤ c.toNat := by
      rcases hc1 with h | h
      · exact h
      · exfalso; apply hne'
        have : c.toNat = 0 := by have : c.toNat ≤ S.length.toNat := hc; rw [h] at this; exact Nat.le_zero.mp this
        have hc0 : c = 0 := UInt32.toNat_inj.mp this
        rw [h, hc0]; rfl
    unfold μ; dsimp only; rw [hm, rank_MATCH, hsl]; omega


theorem min3_facts (c len left : UInt32) :
    (if (if c > len then len else c) > left then left else (if c > len then len else c)) ≤ c ∧
    (if (if c > len then len else c) > left then left else (if c > len then len else c)) ≤ len ∧
    (if (if c > len then len else c) > left then left else (if c > len then len else c)) ≤ left ∧
    (1 ≤ c.toNat → 1 ≤ left.toNat →
      1 ≤ (if (if c > len then len else c) > left then left else (if c > len then len else c)).toNat ∨ len = 0) := by
  by_cases hz : len = 0
  · subst hz
    simp only [UInt32.le_iff_toNat_le, gt_iff_lt, UInt32.lt_iff_toNat_lt]
    split <;> split <;> simp_all <;> omega
  have hz' : len.toNat ≠ 0 := fun e => hz (UInt32.toNat_inj.mp e)
  simp only [UInt32.le_iff_toNat_le, gt_iff_lt, UInt32.lt_iff_toNat_lt, hz, or_false]
  split <;> split <;> simp_all <;> omega

theorem run_MATCH (E : Env) (eo : EnvOK E) : ModeRun E inflate_MATCH (·.mode = MATCH) := by
  intro l H z S li hm m hμ
  have hμ' : 32 * (8 * l.have_.toNat + l.bits.toNat + l.left.toNat) + 6 ≤ m := by
    unfold μ at hμ; rwa [hm, rank_MATCH] at hμ
  unfold inflate_MATCH
  refine SatX.bind (SatX.get ?_)
  dsimp (config := { zeta := false }) only
  split
  · exact SatX.bind (SatX.throw ⟨z, S, li⟩)
  rename_i hl0
  have hl : l.left ≠ 0 := by simpa using hl0
  have hl1 : 1 ≤ l.left.toNat := by
    rcases Nat.eq_zero_or_pos l.left.toNat with e | e
    · exact absurd (UInt32.toNat_inj.mp (by rw [e]; rfl)) hl
    · exact e
  refine SatX.bind (SatX.lift_eq li.ldState ?_)
  dsimp (config := { zeta := false }) only
  extract_lets jp k1 jp2 k2 k3
  have ek1 : k1 = S.offset - (l.out - l.left) := rfl
  have ek2 : k2 = k1 - S.wnext := rfl
  have ek3 : k3 = (if S.length > l.left then l.left else S.length) := rfl
  clear_value k1 k2 k3
  subst ek2; subst ek1; subst ek3
  have hjp : ∀ (u : PUnit) (c : UInt32) (l' : IL) (H' : Heap) (z' : ZStream) (S' : InflateState),
      LI E { l' with left := l'.left - c } H' z' S' → S'.mode = MATCH → S'.length = S.length → c ≤ S.length →
      (1 ≤ c.toNat ∨ S.length = 0) → c ≤ l'.left → l'.have_ = l.have_ → l'.bits = l.bits → l'.left = l.left →
      SatX H' l' (jp u c) (Post E m) := by
    intro u c l' H' z' S' li' hm' hlen hc hc1 hcl h1 h2 h3
    simp only [jp]
    refine mtail_ok c li' hm' (by rw [hlen]; exact hc) (by rw [hlen]; exact hc1) hcl (by rw [h1, h2, h3]; exact hμ')
  clear_value jp
  obtain ⟨al, -, cr⟩ := li.core
  obtain ⟨hoff, -⟩ := cr.modes.offset (Or.inr hm)
  obtain ⟨p, hput, hp1, hp2⟩ := li.outPos
  obtain ⟨dout, hdo, hdos⟩ := li.outBytes eo
  obtain ⟨-, -, -, hbne, hw, -⟩ := eo.outW
  obtain ⟨hlo, ob, hob1, hob2, hput'⟩ := li.outAt
  have hlo' : l.left.toNat ≤ l.out.toNat := hlo
  have hD : (l.out - l.left).toNat = l.out.toNat - l.left.toNat := UInt32.toNat_sub_of_le _ _ hlo
  rw [hput] at hput'
  have hpob : p = ob + (l.out - l.left).toNat := by injection hput'
  split
  · rename_i hgt
    have hgt' : l.out.toNat - l.left.toNat < S.offset.toNat := by rw [← hD]; exact UInt32.lt_iff_toNat_lt.mp hgt
    have hc1 : (S.offset - (l.out - l.left)).toNat = S.offset.toNat - (l.out.toNat - l.left.toNat) := by
      rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_of_lt hgt), hD]
    split
    · exact bad_ok li (by omega) "invalid distance too far back" (strIdx 20 (by decide) (by decide) (by decide))
    rename_i hwh
    have hwh' : S.offset.toNat - (l.out.toNat - l.left.toNat) ≤ S.whave.toNat := by
      rw [← hc1]; exact UInt32.le_iff_toNat_le.mp (UInt32.not_lt.mp hwh)
    obtain ⟨woff, dw, hwv, -, hdw, hdws⟩ := cr.window
    have hwin : S.window = .val (.ref (.heap E.b) woff) := hwv
    have hwb : (view S).wbufsize.toNat = 32832 := by rw [cr.wbufsize]; rfl
    have hwz : S.wsize.toNat ≤ 32768 := UInt32.le_iff_toNat_le.mp cr.wsize
    have hwh : S.whave.toNat ≤ S.wsize.toNat := UInt32.le_iff_toNat_le.mp cr.whave
    have hwn : S.wnext.toNat ≤ S.whave.toNat := UInt32.le_iff_toNat_le.mp cr.wnext_le
    have hdws' : woff + 32832 ≤ dw.size := by rw [← hwb]; exact hdws
    rw [hwin]
    refine SatX.bind (SatX.lift_eq (a := (.ref (.heap E.b) woff : BPtr)) rfl ?_)
    dsimp only
    have hjp2 : ∀ (c : UInt32) (q : Nat), 1 ≤ c.toNat → q + c.toNat ≤ dw.size →
        SatX H l (jp2 () c (.ref (.heap E.b) q)) (Post E m) := by
      intro c q hc1 hq
      simp only [jp2]
      clear jp2
      obtain ⟨m1, m2, m3, m4⟩ := min3_facts c S.length l.left
      generalize (if (if c > S.length then S.length else c) > l.left then l.left else
        (if c > S.length then S.length else c)) = c3 at m1 m2 m3 m4 ⊢
      have m1' : c3.toNat ≤ c.toNat := m1
      have m3' : c3.toNat ≤ l.left.toNat := m3
      rw [hput]
      refine SatX.bind (SatX.lift (Sat.of_eq (memcpy_heap' hdo hdw (fun e => (hbne (by injection e with e; exact e.symm)).elim)
        (by omega) (by omega)) ?_))
      have li2 := li.wrBytes (od := p) (n := c3.toNat) (o0 := E.oo) (n0 := E.O0.toNat)
        (a' := copyFold dw p q (List.range' 0 c3.toNat) dout) hdo hbne
        (copyFold_size _ _ _ _ _) (copyFold_out _ _ _ _ _) hw hp1 (by omega)
      refine SatX.bind (SatX.lift_eq (add_heap (upd_same _ _ _) (by rw [copyFold_size]; omega)) ?_)
      refine SatX.bind (SatX.modify ?_)
      refine hjp _ c3 _ _ z S ?_ hm rfl m2 (m4 hc1 hl1) m3 rfl rfl rfl
      exact li2.produce hput c3 m3 _ rfl rfl rfl rfl rfl rfl
    clear_value jp2
    split
    · rename_i hwn2
      have hwn2' : S.wnext.toNat < S.offset.toNat - (l.out.toNat - l.left.toNat) := by
        rw [← hc1]; exact UInt32.lt_iff_toNat_lt.mp hwn2
      have hc2 : (S.offset - (l.out - l.left) - S.wnext).toNat =
          S.offset.toNat - (l.out.toNat - l.left.toNat) - S.wnext.toNat := by
        rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_of_lt hwn2), hc1]
      have hc3 : (S.wsize - (S.offset - (l.out - l.left) - S.wnext)).toNat =
          S.wsize.toNat - (S.offset.toNat - (l.out.toNat - l.left.toNat) - S.wnext.toNat) := by
        rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, hc2]; omega), hc2]
      refine SatX.bind (SatX.lift_eq (add_heap hdw (by rw [hc3]; omega)) ?_)
      exact hjp2 _ _ (by rw [hc2]; omega) (by rw [hc3, hc2]; omega)
    · rename_i hwn2
      have hwn2' : S.offset.toNat - (l.out.toNat - l.left.toNat) ≤ S.wnext.toNat := by
        rw [← hc1]; exact UInt32.le_iff_toNat_le.mp (UInt32.not_lt.mp hwn2)
      have hc3 : (S.wnext - (S.offset - (l.out - l.left))).toNat =
          S.wnext.toNat - (S.offset.toNat - (l.out.toNat - l.left.toNat)) := by
        rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, hc1]; omega), hc1]
      refine SatX.bind (SatX.lift_eq (add_heap hdw (by rw [hc3]; omega)) ?_)
      exact hjp2 _ _ (by rw [hc1]; omega) (by rw [hc3, hc1]; omega)
  · rename_i hle
    have hle' : S.offset.toNat ≤ l.out.toNat - l.left.toNat := by
      rw [← hD]; exact UInt32.le_iff_toNat_le.mp (UInt32.not_lt.mp hle)
    have hcf : ∀ c : UInt32, c = (if S.length > l.left then l.left else S.length) →
        c ≤ S.length ∧ c ≤ l.left ∧ (1 ≤ c.toNat ∨ S.length = 0) := by
      intro c hc; subst hc
      simp only [UInt32.le_iff_toNat_le, gt_iff_lt, UInt32.lt_iff_toNat_lt]
      by_cases hz : S.length = 0
      · simp only [hz, or_true, and_true]; split <;> simp_all
      have hz' : S.length.toNat ≠ 0 := fun e => hz (UInt32.toNat_inj.mp e)
      simp only [hz, or_false]
      split <;> simp_all <;> omega
    obtain ⟨m1, m2, m3⟩ := hcf _ rfl
    generalize (if S.length > l.left then l.left else S.length) = c at m1 m2 m3 ⊢
    rw [hput]
    refine SatX.bind (SatX.lift_eq (InflateWindow.add_neg (r := .heap E.bo) hdo (by rw [hpob]; omega) (by omega)) ?_)
    have m2' : c.toNat ≤ l.left.toNat := m2
    obtain ⟨d', e, hs', hout⟩ := ZlibNgF.Proof.InffastFacts.copyFacts.memset H E.bo p S.offset.toNat dout
      c.toUInt64 l.left.toUInt64 hdo hoff (by have := S.offset.toNat_lt; omega) (by rw [hpob]; omega)
      (by rw [UInt32.toNat_toUInt64]; omega) (by rw [UInt64.le_iff_toNat_le, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64]; exact m2')
      (by rw [UInt64.le_iff_toNat_le, UInt32.toNat_toUInt64]; exact hl1)
    unfold C.run at e
    refine SatX.bind (SatX.lift (Sat.of_eq e ?_))
    have li2 := li.wrBytes (od := p) (n := l.left.toUInt64.toNat) (o0 := E.oo) (n0 := E.O0.toNat)
      (a' := d') hdo hbne hs' hout hw hp1 (by rw [UInt32.toNat_toUInt64]; omega)
    refine SatX.bind (SatX.modify ?_)
    refine hjp _ c _ _ z S ?_ hm rfl m1 m3 m2 rfl rfl rfl
    have := li2.produce hput c m2 { l with put := .ref (.heap E.bo) (p + c.toNat), copy := c, left := l.left - c }
      rfl rfl rfl rfl rfl rfl
    rw [UInt32.toNat_toUInt64]
    exact this


/-! ## Mode changes among the decoding modes -/

theorem decodeMode_bounds {M : UInt32} (h : DecodeMode M) : HEAD ≤ M ∧ M ≤ SYNC := by
  rcases h with e | e | e | e | e | e | e <;> rw [e] <;> decide

/-- `state->mode = M` from a decoding mode to a decoding mode keeps the mode clauses when `extra` and `offset` are in
range for `M`. -/
theorem modeOK_dec (b : Nat) (S : InflateState) (hm : ModeOK b (view S).m) (hd : DecodeMode S.mode) (M : UInt32)
    (hM : DecodeMode M) (hx : M = LENEXT ∨ M = DISTEXT → S.extra ≤ 31)
    (ho : M = DISTEXT ∨ M = MATCH → 1 ≤ S.offset.toNat ∧ (M = DISTEXT → S.offset.toNat < 65536)) :
    ModeOK b (view { S with mode := M }).m where
  lenlens := fun e => by
    have e' : M = LENLENS := e
    rcases hM with h | h | h | h | h | h | h <;> rw [h] at e' <;> exact absurd e' (by decide)
  codelens := fun e => by
    have e' : M = CODELENS := e
    rcases hM with h | h | h | h | h | h | h <;> rw [h] at e' <;> exact absurd e' (by decide)
  decode := fun _ => hm.decode hd
  extra := hx
  offset := ho

theorem LI.setDec {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (li : LI E l H z S)
    (hd : DecodeMode S.mode) (M : UInt32) (hM : DecodeMode M) (hx : M = LENEXT ∨ M = DISTEXT → S.extra ≤ 31)
    (ho : M = DISTEXT ∨ M = MATCH → 1 ≤ S.offset.toNat ∧ (M = DISTEXT → S.offset.toNat < 65536)) :
    Sat H (setMode (some E.b) M) (fun _ H' => LI E l H' z { S with mode := M }) :=
  li.wrS (fun s => { s with mode := M }) (fun _ _ c => { c with
    mode_lo := (decodeMode_bounds hM).1
    mode_hi := (decodeMode_bounds hM).2
    modes := modeOK_dec _ S c.modes hd M hM hx ho }) rfl

theorem rank_DISTEXT : rank DISTEXT = 7 := by decide
theorem rank_DIST : rank DIST = 8 := by decide
theorem rank_LENEXT : rank LENEXT = 9 := by decide

/-- The state entering `MATCH` from `DISTEXT`, with the extra bits added to the distance. -/
theorem modeOK_match (b : Nat) (S : InflateState) (hm : ModeOK b (view S).m) (hd : DecodeMode S.mode) (o' : UInt32)
    (bk : Int32) (h1 : 1 ≤ o'.toNat) : ModeOK b (view { S with offset := o', back := bk, mode := MATCH }).m where
  lenlens := fun e => absurd (show MATCH = LENLENS from e) (by decide)
  codelens := fun e => absurd (show MATCH = CODELENS from e) (by decide)
  decode := fun _ => hm.decode hd
  extra := fun e => by
    rcases e with e | e
    · exact absurd (show MATCH = LENEXT from e) (by decide)
    · exact absurd (show MATCH = DISTEXT from e) (by decide)
  offset := fun _ => ⟨h1, fun e => absurd (show MATCH = DISTEXT from e) (by decide)⟩

theorem run_DISTEXT (E : Env) (eo : EnvOK E) (hX : ModeRun E inflate_MATCH (·.mode = MATCH)) :
    ModeRun E inflate_DISTEXT (·.mode = DISTEXT) := by
  intro l H z S li hm m hμ
  have hμ' : 32 * (8 * l.have_.toNat + l.bits.toNat + l.left.toNat) + 7 ≤ m := by
    unfold μ at hμ; rwa [hm, rank_DISTEXT] at hμ
  have hdm : DecodeMode S.mode := by rw [hm]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  obtain ⟨al, -, cr⟩ := li.core
  have hx : S.extra ≤ 31 := cr.modes.extra (Or.inr hm)
  have hx' : S.extra.toNat ≤ 31 := hx
  obtain ⟨ho1, ho2⟩ := cr.modes.offset (Or.inl hm)
  have ho2' : S.offset.toNat < 65536 := ho2 hm
  have ho1' : 1 ≤ S.offset.toNat := ho1
  unfold inflate_DISTEXT
  refine SatX.bind (SatX.lift_eq (li.rdS (·.extra)) ?_)
  dsimp (config := { zeta := false }) only
  extract_lets jp
  have hjp : ∀ (u : PUnit) (l' : IL) (H' : Heap) (o' : UInt32) (bk : Int32),
      LI E l' H z S → H'.istate E.b = some { S with offset := o', back := bk } →
      (∀ X, withS H' E.b X = withS H E.b X) → 1 ≤ o'.toNat → l'.left = l.left →
      8 * l'.have_.toNat + l'.bits.toNat ≤ 8 * l.have_.toNat + l.bits.toNat →
      SatX H' l' (jp u) (Post E m) := by
    intro u l' H' o' bk li' hs' hw h1 hl hb
    simp only [jp]
    refine SatX.bind (SatX.lift (Sat.of_eq (wrS_app hs' _) ?_))
    rw [hw]
    refine hX _ _ _ _ (li'.withS { S with offset := o', back := bk, mode := MATCH } (fun _ _ c => { c with
      mode_lo := by show HEAD ≤ MATCH; decide
      mode_hi := by show MATCH ≤ SYNC; decide
      modes := modeOK_match _ S c.modes hdm o' bk h1 }) rfl) rfl m ?_
    unfold μ; dsimp only; rw [rank_MATCH, hl]; omega
  clear_value jp
  split
  · rename_i hx0
    refine needbits_then eo li _ (by omega) ?_
    intro l1 li1 hb1 hl1 hT1
    have hbn : S.extra.toNat < 32 := by omega
    refine SatX.bind (bits_ok _ (UInt32.lt_iff_toNat_lt.mpr hbn) ?_)
    have hbl := bits_lt32 l1.hold S.extra hbn
    generalize (l1.hold &&& ((1 : UInt32) <<< S.extra - 1).toUInt64) = v at hbl ⊢
    refine SatX.bind (SatX.lift (Sat.of_eq (wrS_app li1.hs _) ?_))
    refine SatX.bind (dropbits_ok _ (by rw [UInt32.lt_iff_toNat_lt]; show _ < 64; omega) ?_)
    have hd := drop_toNat (b := l1.bits) (n := S.extra) (by omega) hb1
    have li2 := li1.drop S.extra (by omega) hb1
    refine SatX.bind (SatX.lift (Sat.of_eq (wrS_withS li1.hs _ _) ?_))
    have hp : 2 ^ S.extra.toNat ≤ 2 ^ 31 := Nat.pow_le_pow_right (by decide) hx'
    have hv32 : v.toUInt32.toNat = v.toNat := by rw [UInt64.toNat_toUInt32]; exact Nat.mod_eq_of_lt (by omega)
    have hon : (S.offset + v.toUInt32).toNat = S.offset.toNat + v.toNat := by
      rw [UInt32.toNat_add, hv32]; exact Nat.mod_eq_of_lt (by omega)
    refine hjp _ _ _ (S.offset + v.toUInt32) (S.back + S.extra.toInt32) li2 (istate_withS li1.hs _)
      (fun X => withS_withS _ _ _ _) (by rw [hon]; omega) (by rw [← hl1]) ?_
    show 8 * l1.have_.toNat + (l1.bits - S.extra.toUInt8).toNat ≤ _
    rw [hd]; omega
  · have hs0 : H.istate E.b = some { S with offset := S.offset, back := S.back } := li.hs
    exact hjp _ _ _ S.offset S.back li hs0 (fun _ => rfl) ho1' rfl (Nat.le_refl _)

/-! ## `DIST` -/

theorem i32_small : ∀ k : _root_.Fin 29, (Int32.ofInt ((k : Nat) : Int)).toUInt32 ≤ 28 := by decide

theorem code_extra_le {e : Code} {dist : Bool} (h : EntryOK e 28 dist) : CODE_EXTRA e ≤ 28 := by
  unfold CODE_EXTRA
  split
  · rename_i h16
    have hcb := h.cb_le
    have hb := h.bits_le
    unfold CODE_BITS at hcb
    simp only [h16, ↓reduceIte, UInt8.toNat_toUInt32] at hcb
    have e1 : ((e.bits.toNat : Int) - ((e.op &&& 15).toNat : Int)) =
        ((e.bits.toNat - (e.op &&& 15).toNat : Nat) : Int) := by omega
    rw [e1]
    exact i32_small ⟨_, by omega⟩
  · decide

/-- Stores of `offset` and `extra` in a mode that does not read them. -/
theorem modeOK_ox (b : Nat) (S : InflateState) (hm : ModeOK b (view S).m)
    (hq : S.mode ≠ LENEXT ∧ S.mode ≠ DISTEXT ∧ S.mode ≠ MATCH) (o x : UInt32) :
    ModeOK b (view { S with offset := o, extra := x }).m where
  lenlens := hm.lenlens
  codelens := hm.codelens
  decode := hm.decode
  extra := fun e => by rcases e with e | e; exact absurd e hq.1; exact absurd e hq.2.1
  offset := fun e => by rcases e with e | e; exact absurd e hq.2.1; exact absurd e hq.2.2

theorem linkTest_dist : (fun h : Code => (h.op &&& 0xf0) == 0) = linkTest true := by funext e; rfl
theorem linkTest_len : (fun h : Code => h.op != 0 && (h.op &&& 0xf0) == 0) = linkTest false := by funext e; rfl

theorem run_DIST (E : Env) (eo : EnvOK E) (hX : ModeRun E inflate_DISTEXT (·.mode = DISTEXT)) :
    ModeRun E inflate_DIST (·.mode = DIST) := by
  intro l H z S li hm m hμ
  have hμ' : 32 * (8 * l.have_.toNat + l.bits.toNat + l.left.toNat) + 8 ≤ m := by
    unfold μ at hμ; rwa [hm, rank_DIST] at hμ
  have hdm : DecodeMode S.mode := by rw [hm]; exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨al, -, cr⟩ := li.core
  obtain ⟨-, htab⟩ := cr.modes.decode hdm
  obtain ⟨r, o, e, a, hp, hg, t⟩ := tab_get li.hs htab
  unfold inflate_DIST
  refine SatX.bind (SatX.lift_eq (li.rdS (·.distcode)) ?_)
  dsimp only
  have hp' : S.distcode = .val (.ref r o) := hp
  rw [hp']
  refine SatX.bind (SatX.lift_eq (a := (.ref r o : CodePtr)) rfl ?_)
  refine SatX.bind (SatX.lift_eq (li.rdS (·.distbits)) ?_)
  dsimp only
  rw [linkTest_dist]
  refine SatX.bind (SatX.mono (decodeSym_ok eo li hg t) ?_)
  rintro res l1 H1 ⟨S1, li1, hS1, hl1, hb1, hres⟩
  match res, hres with
  | .error e, he => rw [he]; exact ⟨z, S1, li1⟩
  | .ok (), ⟨hent, hcb⟩ =>
  refine SatX.bind (SatX.get ?_)
  dsimp only
  refine SatX.bind (SatX.modify ?_)
  have hc1 := hent.cb_pos
  have hc2 := hent.cb_le
  have hc3 := hent.bits_le
  refine SatX.bind (dropbits_ok _ (by rw [UInt32.lt_iff_toNat_lt]; show _ < 64; omega) ?_)
  have hd := drop_toNat (b := l1.bits) (n := CODE_BITS l1.here) (by omega) hcb
  have li2 := (li1.locals (l' := { l1 with code_bits := CODE_BITS l1.here }) rfl rfl rfl rfl rfl rfl).drop
    (CODE_BITS l1.here) (by omega) hcb
  have hm1 : S1.mode = DIST := by rw [hS1]; exact hm
  refine SatX.bind (SatX.lift (Sat.mono (li2.wrS (fun s => { s with back := s.back + (CODE_BITS l1.here).toInt32 })
    (fun _ _ c => c) rfl) ?_))
  intro _ H3 li3
  have hμ3 : 32 * (8 * l1.have_.toNat + (l1.bits - (CODE_BITS l1.here).toUInt8).toNat + l1.left.toNat) + 8 ≤
      m - 32 := by rw [hd, hl1]; omega
  dsimp (config := { zeta := false }) only
  split
  · exact bad_ok li3 (by
      show 32 * (8 * l1.have_.toNat + (l1.bits - (CODE_BITS l1.here).toUInt8).toNat + l1.left.toNat) < m
      omega) "invalid distance code" (strIdx 19 (by decide) (by decide) (by decide))
  rename_i h64
  have h64' : l1.here.op &&& 64 = 0 := by simpa using h64
  have hv1 : 1 ≤ l1.here.val.toNat := hent.dval rfl (Or.inl h64')
  have hq : ∀ S' : InflateState, S'.mode = DIST → S'.mode ≠ LENEXT ∧ S'.mode ≠ DISTEXT ∧ S'.mode ≠ MATCH := by
    intro S' h; rw [h]; exact ⟨by decide, by decide, by decide⟩
  refine SatX.bind (SatX.lift (Sat.mono (li3.wrS (fun s => { s with offset := l1.here.val.toUInt32 })
    (fun _ _ c => { c with modes := modeOK_ox _ _ c.modes (hq _ hm1) _ _ }) rfl) ?_))
  intro _ H4 li4
  refine SatX.bind (SatX.lift (Sat.mono (li4.wrS (fun s => { s with extra := CODE_EXTRA l1.here })
    (fun _ _ c => { c with modes := modeOK_ox _ _ c.modes (hq _ hm1) _ _ }) rfl) ?_))
  intro _ H5 li5
  have hx := code_extra_le hent
  refine SatX.bind (SatX.lift (Sat.mono (li5.setDec (by rw [hm1, ← hm]; exact hdm) DISTEXT
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (fun _ => UInt32.le_trans hx (by decide))
    (fun _ => ⟨by show 1 ≤ l1.here.val.toUInt32.toNat; rw [UInt16.toNat_toUInt32]; exact hv1,
      fun _ => by show l1.here.val.toUInt32.toNat < 65536; rw [UInt16.toNat_toUInt32]; exact l1.here.val.toNat_lt⟩)) ?_))
  intro _ H6 li6
  refine hX _ _ _ _ li6 rfl m ?_
  show 32 * (8 * l1.have_.toNat + (l1.bits - (CODE_BITS l1.here).toUInt8).toNat + l1.left.toNat) + rank DISTEXT ≤ m
  rw [rank_DISTEXT]; omega

/-! ## `LENEXT` -/

theorem run_LENEXT (E : Env) (eo : EnvOK E) (hX : ModeRun E inflate_DIST (·.mode = DIST)) :
    ModeRun E inflate_LENEXT (·.mode = LENEXT) := by
  intro l H z S li hm m hμ
  have hμ' : 32 * (8 * l.have_.toNat + l.bits.toNat + l.left.toNat) + 9 ≤ m := by
    unfold μ at hμ; rwa [hm, rank_LENEXT] at hμ
  obtain ⟨al, -, cr⟩ := li.core
  have hx : S.extra ≤ 31 := cr.modes.extra (Or.inl hm)
  have hx' : S.extra.toNat ≤ 31 := hx
  unfold inflate_LENEXT
  refine SatX.bind (SatX.lift_eq (li.rdS (·.extra)) ?_)
  dsimp (config := { zeta := false }) only
  extract_lets jp
  have hjp : ∀ (u : PUnit) (l' : IL) (H' : Heap) (z' : ZStream) (S' : InflateState),
      LI E l' H' z' S' → S'.mode = LENEXT → l'.left = l.left →
      8 * l'.have_.toNat + l'.bits.toNat ≤ 8 * l.have_.toNat + l.bits.toNat →
      SatX H' l' (jp u) (Post E m) := by
    intro u l' H' z' S' li' hm' hl hb
    simp only [jp]
    refine SatX.bind (SatX.lift (Sat.mono (li'.wrS (fun s => { s with was := s.length }) (fun _ _ c => c) rfl) ?_))
    intro _ H2 li2
    refine SatX.bind (SatX.lift (Sat.mono (li2.setDec (by rw [hm']; exact Or.inr (Or.inr (Or.inl rfl))) DIST
      (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      (fun e => by rcases e with e | e <;> exact absurd e (by decide))
      (fun e => by rcases e with e | e <;> exact absurd e (by decide))) ?_))
    intro _ H3 li3
    refine hX _ _ _ _ li3 rfl m ?_
    unfold μ; dsimp only; rw [rank_DIST, hl]; omega
  clear_value jp
  split
  · refine needbits_then eo li _ (by omega) ?_
    intro l1 li1 hb1 hl1 hT1
    have hbn : S.extra.toNat < 32 := by omega
    refine SatX.bind (bits_ok _ (UInt32.lt_iff_toNat_lt.mpr hbn) ?_)
    refine SatX.bind (SatX.lift (Sat.mono (li1.wrS (fun s => { s with length := s.length +
      (l1.hold &&& ((1 : UInt32) <<< S.extra - 1).toUInt64).toUInt32 }) (fun _ _ c => { c with }) rfl) ?_))
    intro _ H2 li2
    refine SatX.bind (dropbits_ok _ (by rw [UInt32.lt_iff_toNat_lt]; show _ < 64; omega) ?_)
    have hd := drop_toNat (b := l1.bits) (n := S.extra) (by omega) hb1
    have li3 := li2.drop S.extra (by omega) hb1
    refine SatX.bind (SatX.lift (Sat.mono (li3.wrS (fun s => { s with back := s.back + S.extra.toInt32 })
      (fun _ _ c => c) rfl) ?_))
    intro u H4 li4
    refine hjp u _ _ _ _ li4 hm (by rw [← hl1]) ?_
    show 8 * l1.have_.toNat + (l1.bits - S.extra.toUInt8).toNat ≤ _
    rw [hd]; omega
  · exact hjp _ _ _ _ _ li hm rfl (Nat.le_refl _)

/-! ## `LEN`: the fast decoder -/

/-- `RESTORE()` with the records it stores. -/
theorem LI.restoreX {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (li : LI E l H z S) :
    SatX H l (RESTORE E.c) (fun r l' H' => r = .ok ⟨⟩ ∧ l' = l ∧
      LI E l H' { z with next_out := l.put, avail_out := l.left, next_in := l.next, avail_in := l.have_ }
        { S with hold := l.hold, bits := l.bits.toUInt32 }) := by
  unfold RESTORE
  refine SatX.bind (SatX.get ?_)
  refine SatX.bind (SatX.lift (Sat.mono (li.wrZ (fun z => { z with
    next_out := l.put
    avail_out := l.left
    next_in := l.next
    avail_in := l.have_ }) rfl rfl rfl) ?_))
  intro _ H1 li1
  have hb : l.bits.toUInt32 ≤ 39 := by
    have := li.bits; rw [UInt8.le_iff_toNat_le] at this
    rw [UInt32.le_iff_toNat_le, UInt8.toNat_toUInt32]; exact this
  exact SatX.lift (Sat.mono (li1.wrS (fun s => { s with hold := l.hold, bits := l.bits.toUInt32 })
    (fun _ _ c => { c with bits := hb }) rfl) (fun _ H2 li2 => ⟨rfl, rfl, li2⟩))

/-- The input of a state with `have != 0`. -/
theorem LI.inFacts {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (eo : EnvOK E)
    (li : LI E l H z S) (hh : l.have_ ≠ 0) :
    ∃ r o0 d, E.inp = .ref r o0 ∧ l.next = .ref r (o0 + (E.A0.toNat - l.have_.toNat)) ∧ Space.get H r = some d ∧
      o0 + E.A0.toNat ≤ d.size ∧ l.have_.toNat ≤ E.A0.toNat := by
  obtain ⟨hle, hat⟩ := li.inAt
  have hle' : l.have_.toNat ≤ E.A0.toNat := hle
  obtain ⟨r, o, d, hnx, hg, hsz⟩ := li.inBytes eo hh
  cases hi : E.inp with
  | null => rw [hi] at hat; exact absurd hat.2 hh
  | ref r0 o0 =>
    rw [hi] at hat
    rw [hnx] at hat
    injection hat with e1 e2
    subst e1
    rw [UInt32.toNat_sub_of_le _ _ hle] at e2
    subst e2
    exact ⟨r, o0, d, rfl, by rw [hnx], hg, by omega, hle'⟩

open ZlibNgF.Proof.InflateInv (MView) in
/-- The mode clauses after `inflate_fast`: `LEN`, `TYPE`, `BAD`, or `MATCH` with a nonzero distance. -/
theorem modeOK_fast (b : Nat) (S : InflateState) (hm : ModeOK b (view S).m) (hd : S.mode = LEN) (m' : UInt32)
    (hold : UInt64) (bits len was off : UInt32)
    (hmode : m' = LEN ∨ m' = TYPE ∨ m' = BAD ∨ (m' = MATCH ∧ 1 ≤ off.toNat)) :
    ModeOK b (view { S with mode := m', hold := hold, bits := bits, length := len, was := was, offset := off }).m := by
  have hdm : DecodeMode S.mode := by rw [hd]; exact Or.inr (Or.inl rfl)
  rcases hmode with e | e | e | ⟨e, ho⟩
  · subst e
    exact { lenlens := fun e => absurd (show LEN = LENLENS from e) (by decide)
            codelens := fun e => absurd (show LEN = CODELENS from e) (by decide)
            decode := fun _ => hm.decode hdm
            extra := fun e => by
              rcases e with e | e
              · exact absurd (show LEN = LENEXT from e) (by decide)
              · exact absurd (show LEN = DISTEXT from e) (by decide)
            offset := fun e => by
              rcases e with e | e
              · exact absurd (show LEN = DISTEXT from e) (by decide)
              · exact absurd (show LEN = MATCH from e) (by decide) }
  · subst e; exact ModeOK.quiet _ _ (Or.inl (show TYPE < LENLENS by decide))
  · subst e; exact ModeOK.quiet _ _ (Or.inr (show LIT < BAD by decide))
  · subst e
    exact { lenlens := fun e => absurd (show MATCH = LENLENS from e) (by decide)
            codelens := fun e => absurd (show MATCH = CODELENS from e) (by decide)
            decode := fun _ => hm.decode hdm
            extra := fun e => by
              rcases e with e | e
              · exact absurd (show MATCH = LENEXT from e) (by decide)
              · exact absurd (show MATCH = DISTEXT from e) (by decide)
            offset := fun _ => ⟨ho, fun e => absurd (show MATCH = DISTEXT from e) (by decide)⟩ }

/-- The clauses read the heap only through block `b` and the `gz_header` records (pointwise). -/
theorem Core.of_heap' {h h' : Heap} {s : StreamPtr} {z : ZStream} {b : Nat} {v : InflateInv.View}
    {al : InflateAllocs} (hb : h'.bytes b = h.bytes b) (hg : ∀ k, h'.gzheaders k = h.gzheaders k)
    (c : Core h s z b v al) : Core h' s z b v al :=
  { c with
    toShape := c.toShape.of_heap hb
    head := by
      rcases c.head with e | ⟨k, g, e1, e2⟩
      · exact Or.inl e
      · exact Or.inr ⟨k, g, e1, by rw [hg]; exact e2⟩ }

/-- `LI` after `inflate_fast` and `LOAD()`. -/
theorem LI.afterFast {E : Env} (eo : EnvOK E) {l : IL} {H2 h' : Heap} {z : ZStream} {S : InflateState}
    (li : LI E l H2 { z with next_out := l.put, avail_out := l.left, next_in := l.next, avail_in := l.have_ }
      { S with hold := l.hold, bits := l.bits.toUInt32 })
    (hm : S.mode = LEN) {o0 ob : Nat} {ri : BRef} (hinp : E.inp = .ref ri o0)
    (hhA : l.have_.toNat ≤ E.A0.toNat)
    (hob1 : E.oo ≤ ob) (hob2 : ob + l.out.toNat ≤ E.oo + E.O0.toNat)
    (hput : l.put = .ref (.heap E.bo) (ob + (l.out - l.left).toNat)) (hlo : l.left ≤ l.out)
    {ai ao m' bits len was off : UInt32} {hold : UInt64} {msg : BPtr}
    (hai : ai ≤ l.have_) (hao : ao ≤ l.left)
    (hz' : h'.streams E.i = some { z with
        next_out := Ptr.ref (BRef.heap E.bo) (ob + (l.out - ao).toNat)
        avail_out := ao
        next_in := Ptr.ref ri (o0 + (E.A0.toNat - l.have_.toNat) + (l.have_ - ai).toNat)
        avail_in := ai
        msg := msg })
    (hs' : h'.istates E.b = some { S with
        hold := hold
        bits := bits
        mode := m'
        length := len
        was := was
        offset := off })
    (hmode : m' = LEN ∨ m' = TYPE ∨ m' = BAD ∨ (m' = MATCH ∧ 1 ≤ off.toNat)) (hbits : bits < 8)
    (hbb : h'.bytes E.b = H2.bytes E.b) (hia : h'.iallocs E.b = H2.iallocs E.b)
    (hoth : ∀ c, c ≠ E.bo → h'.bytes c = H2.bytes c)
    (hbo : ∀ d, H2.bytes E.bo = some d → ∃ d', h'.bytes E.bo = some d' ∧ d'.size = d.size)
    (hfr : Frame H2 h' [E.i] [E.b] [] [(l.put, l.left.toNat)]) :
    LI E { l with
        put := Ptr.ref (BRef.heap E.bo) (ob + (l.out - ao).toNat)
        left := ao
        next := Ptr.ref ri (o0 + (E.A0.toNat - l.have_.toNat) + (l.have_ - ai).toNat)
        have_ := ai
        hold := hold
        bits := bits.toUInt8 } h'
      { z with
        next_out := Ptr.ref (BRef.heap E.bo) (ob + (l.out - ao).toNat)
        avail_out := ao
        next_in := Ptr.ref ri (o0 + (E.A0.toNat - l.have_.toNat) + (l.have_ - ai).toNat)
        avail_in := ai
        msg := msg }
      { S with
        hold := hold
        bits := bits
        mode := m'
        length := len
        was := was
        offset := off } := by
  have hg : ∀ k, h'.gzheaders k = H2.gzheaders k := fun k => hfr.2.1 k (List.not_mem_nil)
  obtain ⟨d, hd⟩ : ∃ d, H2.bytes E.b = some d := by
    have := li.hs; unfold Heap.istate at this; split at this <;> simp_all
  have hist : h'.istate E.b = some { S with
        hold := hold
        bits := bits
        mode := m'
        length := len
        was := was
        offset := off } := by
    unfold Heap.istate; rw [hbb, hd]; exact hs'
  have hai' : ai.toNat ≤ l.have_.toNat := hai
  have hao' : ao.toNat ≤ l.left.toNat := hao
  have hlo' : l.left.toNat ≤ l.out.toNat := hlo
  have hb8 : bits.toNat < 8 := hbits
  refine ⟨?_, ?_, ?_, hz', li.hb, hist, li.head, ?_, ?_, ?_, ?_⟩
  · obtain ⟨i', z0, b0, st0, al, e, hz0, hb0, hst0, hal, c⟩ := li.inv
    obtain rfl : E.i = i' := Option.some.inj e
    rw [li.hz] at hz0; cases hz0
    rw [li.hb] at hb0; cases hb0
    rw [li.hs] at hst0; cases hst0
    have c1 := Core.of_heap' (h' := h') (by rw [hbb]) hg c
    refine ⟨E.i, _, E.b, _, al, rfl, hz', li.hb, hist, by unfold Heap.iallocsOf at hal ⊢; rw [hbb, hia]; exact hal,
      { c1 with
        mode_lo := ?_
        mode_hi := ?_
        bits := ?_
        modes := modeOK_fast _ _ c.modes hm m' hold bits len was off hmode }⟩
    · show HEAD ≤ m'; rcases hmode with e | e | e | ⟨e, -⟩ <;> rw [e] <;> decide
    · show m' ≤ SYNC; rcases hmode with e | e | e | ⟨e, -⟩ <;> rw [e] <;> decide
    · show bits ≤ 39; rw [UInt32.le_iff_toNat_le]; show _ ≤ 39; omega
  · obtain ⟨-, -, -, -, hw, -⟩ := eo.outW
    rw [hput] at hfr
    exact Frame.trans li.frame (Frame.mono (Frame.widen hfr hw (by omega) (by
      rw [UInt32.toNat_sub_of_le _ _ hlo]; omega)) (fun _ m => m) (fun _ m => m) (fun _ m => nomatch m) (fun _ m => m))
  · refine li.sz.trans ⟨fun c _ d' hd' => ?_, hfr.2.2.2.2.2.1⟩
    by_cases e : c = E.bo
    · subst e; exact hbo d' hd'
    · exact ⟨d', by rw [hoth c e]; exact hd', rfl⟩
  · have hd := li.hdr
    unfold HdrOK at hd ⊢
    revert hd
    cases E.hp with
    | none => exact fun _ => trivial
    | some k => intro hd; dsimp only at hd ⊢; rw [hg]; exact hd
  · refine ⟨UInt32.le_trans hai li.inAt.1, ?_⟩
    rw [hinp]
    dsimp only
    rw [UInt32.toNat_sub_of_le _ _ hai, UInt32.toNat_sub_of_le _ _ (UInt32.le_trans hai li.inAt.1)]
    congr 1; omega
  · refine ⟨UInt32.le_trans hao hlo, ob, hob1, hob2, rfl⟩
  · show bits.toUInt8 ≤ 39
    rw [UInt8.le_iff_toNat_le, UInt32.toNat_toUInt8, Nat.mod_eq_of_lt (by omega)]; show _ ≤ 39; omega

/-- The measure after `inflate_fast`: it consumed a bit or produced a byte, or went to `BAD`. -/
theorem fast_mu {m : Nat} {N N' : Nat} (m' : UInt32) (h : N' + (if m' = BAD then 0 else 1) ≤ N)
    (hm : 32 * N + 3 ≤ m) : 32 * N' + rank m' < m := by
  by_cases e : m' = BAD
  · simp only [e, ↓reduceIte] at h; rw [e, rank_BAD]; omega
  · simp only [e, ↓reduceIte] at h; have := rank_le m'; omega

theorem run_LEN (E : Env) (eo : EnvOK E) (hX : ModeRun E inflate_LENEXT (·.mode = LENEXT)) :
    ModeRun E inflate_LEN (·.mode = LEN) := by
  intro l H z S li hm m hμ
  have hμ' : 32 * (8 * l.have_.toNat + l.bits.toNat + l.left.toNat) + 3 ≤ m := by
    unfold μ at hμ; rwa [hm, rank_LEN] at hμ
  have hdm : DecodeMode S.mode := by rw [hm]; exact Or.inr (Or.inl rfl)
  unfold inflate_LEN
  refine SatX.bind (SatX.get ?_)
  dsimp (config := { zeta := false }) only
  split
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨h15, h3⟩, h8⟩ := hc
    have h15' : 15 ≤ l.have_.toNat := UInt32.le_iff_toNat_le.mp h15
    have h3' : 3 ≤ l.left.toNat := UInt32.le_iff_toNat_le.mp h3
    have h8' : l.bits.toNat < 8 := UInt8.lt_iff_toNat_lt.mp h8
    refine SatX.bind (SatX.mono li.restoreX ?_)
    rintro r l1 H2 ⟨hr, hl1, li2⟩
    subst hr
    rw [hl1]
    dsimp (config := { zeta := false }) only
    obtain ⟨ri, o0, d, hinp, hni, hgd, hsz, hhA⟩ := li2.inFacts eo (fun e => by rw [e] at h15'; exact absurd h15' (by decide))
    obtain ⟨hlo, ob, hob1, hob2, hput⟩ := li2.outAt
    have hlo' : l.left.toNat ≤ l.out.toNat := hlo
    obtain ⟨dout, hdo, hdos⟩ := li2.outBytes eo
    obtain ⟨-, -, -, hbne, hw, hdj⟩ := eo.outW
    extract_lets jpi jp
    have hjp : ∀ (u : PUnit) (h' : Heap) (ai ao m' bits len was off : UInt32) (hold : UInt64) (msg : BPtr),
        ai ≤ l.have_ → ao ≤ l.left →
        h'.streams E.i = some { z with
          next_out := Ptr.ref (BRef.heap E.bo) (ob + (l.out - ao).toNat)
          avail_out := ao
          next_in := Ptr.ref ri (o0 + (E.A0.toNat - l.have_.toNat) + (l.have_ - ai).toNat)
          avail_in := ai
          msg := msg } →
        h'.istates E.b = some { S with
          hold := hold
          bits := bits
          mode := m'
          length := len
          was := was
          offset := off } →
        (m' = LEN ∨ m' = TYPE ∨ m' = BAD ∨ (m' = MATCH ∧ 1 ≤ off.toNat)) → bits < 8 →
        8 * ai.toNat + bits.toNat + ao.toNat + (if m' = BAD then 0 else 1) ≤
          8 * l.have_.toNat + l.bits.toNat + l.left.toNat →
        h'.bytes E.b = H2.bytes E.b → h'.iallocs E.b = H2.iallocs E.b →
        (∀ c, c ≠ E.bo → h'.bytes c = H2.bytes c) →
        (∀ d, H2.bytes E.bo = some d → ∃ d', h'.bytes E.bo = some d' ∧ d'.size = d.size) →
        Frame H2 h' [E.i] [E.b] [] [(l.put, l.left.toNat)] →
        SatX h' l (jp u) (Post E m) := by
      intro u h' ai ao m' bits len was off hold msg hai hao hz' hs' hmode hbits hmeas hbb hia hoth hbo hfr
      have li3 := LI.afterFast eo li2 hm hinp hhA hob1 hob2 hput hlo hai hao hz' hs' hmode hbits hbb hia hoth hbo hfr
      simp only [jp, jpi]
      refine SatX.bind ?_
      unfold LOAD
      refine SatX.bind (SatX.lift_eq li3.ldStream ?_)
      refine SatX.bind (SatX.lift_eq li3.ldState ?_)
      refine SatX.modify ?_
      dsimp only
      refine SatX.bind (SatX.lift_eq (li3.rdS (·.mode)) ?_)
      have hb8 : (bits.toUInt8).toNat = bits.toNat := by
        rw [UInt32.toNat_toUInt8]; exact Nat.mod_eq_of_lt (by have : bits.toNat < 8 := hbits; omega)
      have hμ3 := fast_mu (N := 8 * l.have_.toNat + l.bits.toNat + l.left.toNat)
        (N' := 8 * ai.toNat + bits.toNat + ao.toNat) m' (by omega) hμ'
      dsimp only
      split
      · refine SatX.bind (SatX.lift (Sat.mono (li3.wrS (fun s => { s with back := -1 }) (fun _ _ c => c) rfl) ?_))
        intro _ H4 li4
        refine SatX.pure (post_ok li4 ?_)
        unfold μ; dsimp only; rw [hb8]; exact hμ3
      · refine SatX.pure (post_ok li3 ?_)
        unfold μ; dsimp only; rw [hb8]; exact hμ3
    clear_value jp jpi
    have hzst : H2.istate E.b = some { S with hold := l.hold, bits := l.bits.toUInt32 } := li2.hs
    have hbl : l.bits.toUInt32 < 8 := by
      rw [UInt32.lt_iff_toNat_lt, UInt8.toNat_toUInt32]; exact h8'
    have hrd : ReadSlice H2 l.next l.have_.toNat := ⟨ri, _, d, hni, hgd, by omega⟩
    have hwr : WriteSlice H2 (.ref (.heap E.bo) ob) l.out.toNat := ⟨E.bo, ob, dout, rfl, hdo, by omega⟩
    have hdisj : Disjoint l.next l.have_.toNat (.ref (.heap E.bo) ob) l.out.toNat := by
      rw [hinp] at hdj
      rw [hni]
      rcases hdj with h1 | h1 | h1
      · exact Or.inl h1
      · right; left; omega
      · right; right; omega
    have hnib : NotInBlock E.b l.next := by
      intro off e
      rw [hni] at e
      injection e with e1
      subst e1
      exact eo.inNB o0 hinp
    split
    · rename_i hge
      have hge' : 260 ≤ l.left.toNat := UInt32.le_iff_toNat_le.mp hge
      obtain ⟨h', ai, ao, m', hold, bits, len, was, off, msg, e, hai, hao, hz', hs', hmode, hbits, hmeas, hbb, hia,
        hoth, hbo, hfr⟩ := ZlibNgF.Proof.InffastFacts.fastFacts.fast false H2 E.i E.b _ _ l.out ri _ E.bo ob li2.inv
          li2.hz li2.hb hzst hm hbl h15 hge hlo hni hrd hput hwr hdisj hnib hbne
      simp only [Bool.false_eq_true, ↓reduceIte] at e
      refine SatX.bind (SatX.lift (Sat.of_eq e ?_))
      refine hjp _ h' ai ao m' bits len was off hold msg hai hao hz' hs' ?_ hbits ?_ hbb hia hoth hbo hfr
      · rcases hmode with h | h | h | ⟨h, -⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · cases h
      · have : (l.bits.toUInt32).toNat = l.bits.toNat := UInt8.toNat_toUInt32 _
        dsimp only at hmeas; omega
    · rename_i hlt
      have hlt' : l.left.toNat < 260 := by
        have := UInt32.not_le.mp hlt; exact UInt32.lt_iff_toNat_lt.mp this
      obtain ⟨h', ai, ao, m', hold, bits, len, was, off, msg, e, hai, hao, hz', hs', hmode, hbits, hmeas, hbb, hia,
        hoth, hbo, hfr⟩ := ZlibNgF.Proof.InffastFacts.fastFacts.fast true H2 E.i E.b _ _ l.out ri _ E.bo ob li2.inv
          li2.hz li2.hb hzst hm hbl h15 ⟨h3, UInt32.lt_iff_toNat_lt.mpr hlt'⟩ hlo hni hrd hput hwr hdisj hnib hbne
      simp only [↓reduceIte] at e
      refine SatX.bind (SatX.lift (Sat.of_eq e ?_))
      refine hjp _ h' ai ao m' bits len was off hold msg hai hao hz' hs' ?_ hbits ?_ hbb hia hoth hbo hfr
      · rcases hmode with h | h | h | ⟨-, h, h'⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr ⟨h, h'⟩))
      · have : (l.bits.toUInt32).toNat = l.bits.toNat := UInt8.toNat_toUInt32 _
        dsimp only at hmeas; omega
  · refine SatX.bind (SatX.lift (Sat.mono (li.wrS (fun s => { s with back := 0 }) (fun _ _ c => c) rfl) ?_))
    intro _ H1 li1
    obtain ⟨al, -, cr⟩ := li1.core
    obtain ⟨htab, -⟩ := cr.modes.decode hdm
    obtain ⟨r, o, e, a, hp, hg, t⟩ := tab_get li1.hs htab
    refine SatX.bind (SatX.lift_eq (li1.rdS (·.lencode)) ?_)
    dsimp only
    have hp' : S.lencode = .val (.ref r o) := hp
    rw [hp']
    refine SatX.bind (SatX.lift_eq (a := (.ref r o : CodePtr)) rfl ?_)
    refine SatX.bind (SatX.lift_eq (li1.rdS (·.lenbits)) ?_)
    dsimp only
    rw [linkTest_len]
    refine SatX.bind (SatX.mono (decodeSym_ok eo li1 hg t) ?_)
    rintro res l1 H2 ⟨S1, li2, hS1, hl1, hb1, hres⟩
    match res, hres with
    | .error e, he => rw [he]; exact ⟨_, S1, li2⟩
    | .ok (), ⟨hent, hcb⟩ =>
    refine SatX.bind (SatX.get ?_)
    dsimp only
    refine SatX.bind (SatX.modify ?_)
    have hc1 := hent.cb_pos
    have hc2 := hent.cb_le
    have hc3 := hent.bits_le
    refine SatX.bind (dropbits_ok _ (by rw [UInt32.lt_iff_toNat_lt]; show _ < 64; omega) ?_)
    have hd := drop_toNat (b := l1.bits) (n := CODE_BITS l1.here) (by omega) hcb
    have li3 := (li2.locals (l' := { l1 with code_bits := CODE_BITS l1.here }) rfl rfl rfl rfl rfl rfl).drop
      (CODE_BITS l1.here) (by omega) hcb
    have hm1 : S1.mode = LEN := by rw [hS1]; exact hm
    refine SatX.bind (SatX.lift (Sat.mono (li3.wrS (fun s => { s with back := s.back + (CODE_BITS l1.here).toInt32 })
      (fun _ _ c => c) rfl) ?_))
    intro _ H4 li4
    refine SatX.bind (SatX.lift (Sat.mono (li4.wrS (fun s => { s with length := l1.here.val.toUInt32 })
      (fun _ _ c => { c with }) rfl) ?_))
    intro _ H5 li5
    have hN : 32 * (8 * l1.have_.toNat + (l1.bits - (CODE_BITS l1.here).toUInt8).toNat + l1.left.toNat) + 32 ≤
        32 * (8 * l.have_.toNat + l.bits.toNat + l.left.toNat) := by rw [hd, hl1]; omega
    dsimp (config := { zeta := false }) only
    split
    · refine SatX.bind (SatX.lift (Sat.mono (li5.setDec (by rw [hm1]; exact Or.inr (Or.inl rfl)) LIT
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
        (fun e => by rcases e with e | e <;> exact absurd e (by decide))
        (fun e => by rcases e with e | e <;> exact absurd e (by decide))) ?_))
      intro _ H6 li6
      refine SatX.pure (post_ok li6 ?_)
      show 32 * (8 * l1.have_.toNat + (l1.bits - (CODE_BITS l1.here).toUInt8).toNat + l1.left.toNat) + rank LIT < m
      rw [rank_LIT]; omega
    split
    · refine SatX.bind (SatX.lift (Sat.mono (li5.wrS (fun s => { s with back := -1 }) (fun _ _ c => c) rfl) ?_))
      intro _ H6 li6
      refine SatX.bind (SatX.lift (Sat.mono (li6.setQuiet TYPE (by decide) (by decide) (Or.inl (by decide))) ?_))
      intro _ H7 li7
      refine SatX.pure (post_ok li7 ?_)
      show 32 * (8 * l1.have_.toNat + (l1.bits - (CODE_BITS l1.here).toUInt8).toNat + l1.left.toNat) + rank TYPE < m
      rw [rank_TYPE]; omega
    split
    · exact bad_ok li5 (by
        show 32 * (8 * l1.have_.toNat + (l1.bits - (CODE_BITS l1.here).toUInt8).toNat + l1.left.toNat) < m
        omega) "invalid literal/length code" (strIdx 22 (by decide) (by decide) (by decide))
    have hq : ∀ S' : InflateState, S'.mode = LEN → S'.mode ≠ LENEXT ∧ S'.mode ≠ DISTEXT ∧ S'.mode ≠ MATCH := by
      intro S' h; rw [h]; exact ⟨by decide, by decide, by decide⟩
    refine SatX.bind (SatX.lift (Sat.mono (li5.wrS (fun s => { s with extra := CODE_EXTRA l1.here })
      (fun _ _ c => { c with modes := modeOK_ox _ _ c.modes (hq _ hm1) _ _ }) rfl) ?_))
    intro _ H6 li6
    have hx := code_extra_le hent
    refine SatX.bind (SatX.lift (Sat.mono (li6.setDec (by rw [hm1]; exact Or.inr (Or.inl rfl)) LENEXT
      (Or.inr (Or.inr (Or.inl rfl))) (fun _ => UInt32.le_trans hx (by decide))
      (fun e => by rcases e with e | e <;> exact absurd e (by decide))) ?_))
    intro _ H7 li7
    refine hX _ _ _ _ li7 rfl m ?_
    show 32 * (8 * l1.have_.toNat + (l1.bits - (CODE_BITS l1.here).toUInt8).toNat + l1.left.toNat) + rank LENEXT ≤ m
    rw [rank_LENEXT]; omega

theorem run_LEN_ (E : Env) (hX : ModeRun E inflate_LEN (·.mode = LEN)) :
    ModeRun E inflate_LEN_ (·.mode = LEN_) := by
  intro l H z S li hm m hμ
  have hμ' : 32 * (8 * l.have_.toNat + l.bits.toNat + l.left.toNat) + 4 ≤ m := by
    unfold μ at hμ; rwa [hm, rank_LEN_] at hμ
  unfold inflate_LEN_
  refine SatX.bind (SatX.lift (Sat.mono (li.setLen (by rw [hm]; exact Or.inl rfl)) ?_))
  intro _ H1 li1
  refine hX _ _ _ _ li1 rfl m ?_
  unfold μ; dsimp only; rw [rank_LEN]; omega

end ZlibNgF.Proof.InflateLoop