import ZlibNgF.Proof.«infback.c.fast»

/-!
# `inflateBack()`: the symbol decoder `decodeSym` (`ZlibNgF`)

`decodeSym` looks a symbol up in a decoding table, pulling a byte (`PULLBYTE`, which may call `in()`) while the entry
needs more bits than are held, and follows at most one link to a sub-table. Every entry it reads lies in the table
(`CodeTable`). It ends with the code bits of the entry held; when the decoder had to pull a byte, the prefix property
of the table level (`Lvl`) says that the code it found is longer than the bits held before that byte, so after the
code is dropped fewer than 8 bits are held (for an entry that does not lead to `BAD`).

`J`: the bits `b` held are fewer than 8, or some index `y` whose entry needs more than `b - 8` bits agrees with the
bit buffer on its low `min (b - 8) n` bits (the lookup before the last byte was pulled).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InfbackLoop
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Infback ZlibNg.InflateP
open ZlibNgF.Proof.InflateX
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.mono Sat.of_eq)
open ZlibNgF.Proof.InfbackPull
open ZlibNgF.Proof.InflateLoop (withS bits_ok dropbits_ok tab_index tab_index' bits_lt bits_lt32 link_f0 cb_link
  andf0_lt' andf0_15)
open ZlibNgF.Proof.InflateTab (CodeTable EntryOK linkTest)

/-! ## The prefix argument -/

/-- See the module comment. -/
def J (c : Nat → Nat) (n b h : Nat) : Prop :=
  b < 8 ∨ ∃ y, y < 2 ^ n ∧ b - 8 < c y ∧ y % 2 ^ (min (b - 8) n) = h % 2 ^ (min (b - 8) n)

/-- The prefix property of a level as a property of the code-bits function `c` and the liveness `live`. -/
def RepF (c : Nat → Nat) (live : Nat → Prop) (n : Nat) : Prop :=
  ∀ x x', x < 2 ^ n → x' < 2 ^ n → live x' → c x' ≤ n ∧ (x % 2 ^ (c x') = x' % 2 ^ (c x') → c x = c x')

theorem lvl_repF {a : Array Code} {s k : Nat} (h : Lvl a s k) :
    RepF (fun y => (CODE_BITS a[s + y]!).toNat) (fun y => Live a[s + y]!) k := by
  intro x x' hx hx' hl
  obtain ⟨h1, h2⟩ := h x x' hx hx' hl
  exact ⟨h1, fun e => congrArg UInt32.toNat (h2 e)⟩

/-- At the end of a lookup loop: a live entry found with `b` bits held needs more than `b - 8` bits. -/
theorem rep_exit {c : Nat → Nat} {live : Nat → Prop} {n b h : Nat} (rep : RepF c live n) (j : J c n b h)
    (hl : live (h % 2 ^ n)) : b < c (h % 2 ^ n) + 8 := by
  rcases j with j | ⟨y, hy, hc, hm⟩
  · omega
  · refine Nat.lt_of_not_le fun hn => ?_
    have hx : h % 2 ^ n < 2 ^ n := Nat.mod_lt _ (Nat.two_pow_pos n)
    obtain ⟨hL, hrep⟩ := rep y (h % 2 ^ n) hy hx hl
    have hLm : c (h % 2 ^ n) ≤ min (b - 8) n := Nat.le_min.mpr ⟨by omega, hL⟩
    have d : 2 ^ c (h % 2 ^ n) ∣ 2 ^ (min (b - 8) n) := Nat.pow_dvd_pow 2 hLm
    have d2 : 2 ^ c (h % 2 ^ n) ∣ 2 ^ n := Nat.pow_dvd_pow 2 hL
    have := hrep (by rw [← Nat.mod_mod_of_dvd y d, hm, Nat.mod_mod_of_dvd h d, Nat.mod_mod_of_dvd h d2])
    omega

/-- A pull after a lookup whose entry needs more than the `b` bits held. -/
theorem rep_pull {c : Nat → Nat} {n b h h' : Nat} (hc : b < c (h % 2 ^ n)) (hh : h' % 2 ^ b = h % 2 ^ b) :
    J c n (b + 8) h' := by
  right
  refine ⟨h % 2 ^ n, Nat.mod_lt _ (Nat.two_pow_pos n), by omega, ?_⟩
  have e : b + 8 - 8 = b := by omega
  rw [e]
  have d1 : 2 ^ (min b n) ∣ 2 ^ n := Nat.pow_dvd_pow 2 (Nat.min_le_right _ _)
  have d2 : 2 ^ (min b n) ∣ 2 ^ b := Nat.pow_dvd_pow 2 (Nat.min_le_left _ _)
  rw [Nat.mod_mod_of_dvd h d1, ← Nat.mod_mod_of_dvd h' d2, hh, Nat.mod_mod_of_dvd h d2]

/-- The sub-table index: bits `n .. n + k` of the bit buffer. -/
theorem sub_idx (h n k : Nat) : h % 2 ^ (n + k) / 2 ^ n = h / 2 ^ n % 2 ^ k := by
  rw [Nat.pow_add]; exact Nat.mod_mul_right_div_self h _ _

/-- A pull keeps the bits above the link's `n` bits that were held. -/
theorem sub_pull {h h' n b : Nat} (hn : n ≤ b) (hh : h' % 2 ^ b = h % 2 ^ b) :
    h' / 2 ^ n % 2 ^ (b - n) = h / 2 ^ n % 2 ^ (b - n) := by
  rw [← sub_idx, ← sub_idx, Nat.add_sub_cancel' hn, hh]

/-! ## Tables of the state -/

/-- A decoding table of the state, with the array it lives in on every heap of the call. -/
theorem RTab.get {E : BEnv} {S : InflateState} {p : Ival CodePtr}
    {n : UInt32} {m : Nat} {dist : Bool} (t : RTab E.b S.codes p n m dist) :
    ∃ r o e a, p = .val (.ref r o) ∧ CodeTable a o e n.toNat m dist ∧ Rep a o n.toNat dist ∧
      ∀ H' z', BShape E H' z' S → Space.get H' r = some a := by
  rcases t with ⟨o, e, hp, ct, rp⟩ | ⟨hp, ⟨e, ct⟩, rp⟩ | ⟨hp, ⟨e, ct⟩, rp⟩
  · refine ⟨.codes E.b, o, e, S.codes, hp, ct, rp, fun H' z' sh' => ?_⟩
    show (H'.istate E.b).map (·.codes) = _
    rw [sh'.istate]; rfl
  · exact ⟨.lenfix, 0, e, lenfix, hp, ct, rp, fun _ _ _ => rfl⟩
  · exact ⟨.distfix, 0, e, distfix, hp, ct, rp, fun _ _ _ => rfl⟩

/-! ## The lookup loops -/

/-- A state of a lookup loop started from `l0` with `t0` bytes to come: the shape and the input, `put`, `left` and
`last` kept, the input bits conserved. -/
def DL (E : BEnv) (z : ZStream) (S : InflateState) (l0 : IL) (t0 : Nat) (l : IL) (H : Heap) : Prop :=
  ∃ t, BM E l H t z S ∧ l.put = l0.put ∧ l.left = l0.left ∧ l.last = l0.last ∧
    8 * (l.have_.toNat + t) + l.bits.toNat = 8 * (l0.have_.toNat + t0) + l0.bits.toNat

theorem DL.refl {E : BEnv} {z : ZStream} {S : InflateState} {l : IL} {H : Heap} {t : Nat} (bm : BM E l H t z S) :
    DL E z S l t l H := ⟨t, bm, rfl, rfl, rfl, rfl⟩

/-- `DL` after a `PULLBYTE` that read a byte. -/
theorem DL.pull {E : BEnv} {z : ZStream} {S : InflateState} {l0 : IL} {t0 : Nat} {l l' : IL} {H H' : Heap}
    {t t' : Nat} (bm : BM E l H t z S) (hp : l.put = l0.put) (hl : l.left = l0.left) (hla : l.last = l0.last)
    (hm : 8 * (l.have_.toNat + t) + l.bits.toNat = 8 * (l0.have_.toNat + t0) + l0.bits.toNat)
    (hk : BackKeep H H' E.i E.b E.w) (hin : InB E.I H' l' t')
    (hm' : 8 * (l'.have_.toNat + t') + l'.bits.toNat = 8 * (l.have_.toNat + t) + l.bits.toNat)
    (hb : l'.bits.toNat = l.bits.toNat + 8) (pb : Pb l l') : DL E z S l0 t0 l' H' := by
  refine ⟨t', ⟨bm.sh.keep hk, hin, ?_, by rw [pb]; exact bm.put, by rw [pb]; exact bm.left, bm.whave⟩,
    by rw [pb]; exact hp, by rw [pb]; exact hl, by rw [pb]; exact hla, by omega⟩
  have := bm.tot; omega

theorem ival_get {α : Type} (a : α) (H : Heap) : (Ival.val a).get H = .ok (a, H) := rfl

/-- The first-level lookup loop of `decodeSym`. -/
theorem bdec1 {E : BEnv} (cb : E.CB) {l : IL} {H : Heap} {t : Nat} {z : ZStream} {S : InflateState}
    (bm : BM E l H t z S) {tab : InflateState → Ival CodePtr} {nbits : InflateState → UInt32} {r : CodeRef}
    {o e : Nat} {a : Array Code} {dist : Bool} (hp : tab S = .val (.ref r o))
    (hga : ∀ H' z', BShape E H' z' S → Space.get H' r = some a) (ct : CodeTable a o e (nbits S).toNat 28 dist)
    (rep : Lvl a o (nbits S).toNat) (hb8 : l.bits.toNat < 8) :
    SatX H l (xloopBrk (do
      let t ← (← rdS E.c.st tab).get
      let b ← BITS (← rdS E.c.st nbits)
      let here : Code ← Ptr.index t (Int.ofNat b.toNat)
      modify fun l => { l with here := here }
      if CODE_BITS (← get).here <= (← get).bits.toUInt32 then return true
      PULLBYTE E.c
      return false))
      (fun res l' H' => match res with
        | .ok () => DL E z S l t l' H' ∧ (∃ j, j < 2 ^ (nbits S).toNat ∧ l'.here = a[o + j]!) ∧
            (CODE_BITS l'.here).toNat ≤ l'.bits.toNat ∧
            (Live l'.here → l'.bits.toNat < (CODE_BITS l'.here).toNat + 8) ∧ l'.bits.toNat ≤ 35
        | .error .leave => BLv E l' H'
        | .error (.ret _) => False) := by
  have hn15 : (nbits S).toNat ≤ 15 := ct.n_le
  have hrep := lvl_repF rep
  unfold xloopBrk
  refine xwhileBrk_rank (fun l' H' => DL E z S l t l' H' ∧
      J (fun y => (CODE_BITS a[o + y]!).toNat) (nbits S).toNat l'.bits.toNat l'.hold.toNat ∧ l'.bits.toNat ≤ 35)
    (fun l' _ => 64 - l'.bits.toNat) _ ?_ ⟨DL.refl bm, Or.inl hb8, by omega⟩ (by unfold fuel; omega)
  rintro l1 H1 ⟨⟨t1, bm1, hp1, hl1, hla1, hm1⟩, hj1, hb1⟩
  refine SatX.pure ?_
  dsimp only
  refine SatX.bind (liftEq (bm1.sh.rdS tab) ?_)
  rw [hp]
  refine SatX.bind (liftEq (ival_get _ _) ?_)
  refine SatX.bind (liftEq (bm1.sh.rdS nbits) ?_)
  refine SatX.bind (bits_ok _ (by rw [UInt32.lt_iff_toNat_lt]; show _ < 32; omega) ?_)
  have hk := bits_lt l1.hold (nbits S) hn15
  refine SatX.bind (liftEq (tab_index (hga H1 z bm1.sh) ct hk) ?_)
  have hkv : (l1.hold &&& ((1 : UInt32) <<< nbits S - 1).toUInt64).toNat = l1.hold.toNat % 2 ^ (nbits S).toNat := by
    have h1 : ((1 : UInt32) <<< nbits S).toNat = 2 ^ (nbits S).toNat := by
      rw [UInt32.toNat_shiftLeft, Nat.mod_eq_of_lt (by omega : (nbits S).toNat < 32)]
      show 1 <<< (nbits S).toNat % 2 ^ 32 = _
      rw [Nat.shiftLeft_eq, Nat.one_mul]; exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))
    have h2 : ((1 : UInt32) <<< nbits S - 1).toUInt64.toNat = 2 ^ (nbits S).toNat - 1 := by
      rw [UInt32.toNat_toUInt64, UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, h1]; exact Nat.one_le_two_pow), h1]
      rfl
    rw [UInt64.toNat_and, h2, Nat.and_two_pow_sub_one_eq_mod]
  generalize (l1.hold &&& ((1 : UInt32) <<< nbits S - 1).toUInt64).toNat = k at hk hkv ⊢
  subst hkv
  refine SatX.bind (SatX.modify ?_)
  have hj2 : o + l1.hold.toNat % 2 ^ (nbits S).toNat < e := by have := ct.root; omega
  have hent := ct.ent _ (Nat.le_add_right _ _) hj2
  have bm2 : BM E { l1 with here := a[o + l1.hold.toNat % 2 ^ (nbits S).toNat]! } H1 t1 z S :=
    bm1.locals rfl rfl rfl rfl
  refine SatX.bind (SatX.get ?_)
  refine SatX.bind (SatX.get ?_)
  dsimp only
  split
  · rename_i hle
    have hle' : (CODE_BITS a[o + l1.hold.toNat % 2 ^ (nbits S).toNat]!).toNat ≤ l1.bits.toNat := by
      have := UInt32.le_iff_toNat_le.mp hle; rw [UInt8.toNat_toUInt32] at this; exact this
    refine SatX.pure ⟨⟨t1, bm2, hp1, hl1, hla1, hm1⟩, ⟨_, Nat.mod_lt _ (Nat.two_pow_pos _), rfl⟩, hle',
      fun hv => rep_exit (live := fun y => Live a[o + y]!) hrep hj1 hv, hb1⟩
  · rename_i hgt
    have hgt' : l1.bits.toNat < (CODE_BITS a[o + l1.hold.toNat % 2 ^ (nbits S).toNat]!).toNat := by
      have := UInt32.lt_iff_toNat_lt.mp (UInt32.not_le.mp hgt); rw [UInt8.toNat_toUInt32] at this; exact this
    have h28 := hent.bits_le
    have hcb := hent.cb_le
    refine SatX.bind (pullbyte_ok cb E.c rfl rfl bm2.inB (by show l1.bits.toNat < 56; omega) ?_ ?_)
    · intro H' q hk hI h0
      exact ⟨t1, z, S, bm2.sh.keep hk, ⟨q, 0, hI, by rw [h0]; exact Nat.le_refl _, fun h => absurd rfl h⟩,
        bm2.put, bm2.left⟩
    · intro l3 H3 t3 hk hin3 hm3 hb3 pb3 _ hh3
      have hb3' : l3.bits.toNat = l1.bits.toNat + 8 := hb3
      refine SatX.pure ⟨⟨DL.pull bm2 hp1 hl1 hla1 hm1 hk hin3 hm3 hb3 pb3, ?_, by omega⟩, by omega⟩
      rw [hb3]
      exact rep_pull hgt' hh3

theorem bits_mod (x : UInt64) (q : UInt32) (hq : q.toNat < 32) :
    (x &&& ((1 : UInt32) <<< q - 1).toUInt64).toNat = x.toNat % 2 ^ q.toNat := by
  have h1 : ((1 : UInt32) <<< q).toNat = 2 ^ q.toNat := by
    rw [UInt32.toNat_shiftLeft, Nat.mod_eq_of_lt hq]
    show 1 <<< q.toNat % 2 ^ 32 = _
    rw [Nat.shiftLeft_eq, Nat.one_mul]; exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hq)
  have h2 : ((1 : UInt32) <<< q - 1).toUInt64.toNat = 2 ^ q.toNat - 1 := by
    rw [UInt32.toNat_toUInt64, UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, h1]; exact Nat.one_le_two_pow), h1]
    rfl
  rw [UInt64.toNat_and, h2, Nat.and_two_pow_sub_one_eq_mod]

theorem shr64_ok (b : UInt64) (s : UInt32) (hs : s.toNat < 64) (H : Heap) :
    shr64 b s H = .ok (b >>> s.toUInt64, H) := by
  have : s < 64 := by rw [UInt32.lt_iff_toNat_lt]; exact hs
  simp [shr64, this]

/-- The second-level lookup loop of `decodeSym`, after the link `a[o + j]` of `n` (the root) bits. -/
theorem bdec2 {E : BEnv} (cb : E.CB) {l : IL} {H : Heap} {t : Nat} {z : ZStream} {S : InflateState}
    (bm : BM E l H t z S) {tab : InflateState → Ival CodePtr} {r : CodeRef}
    {o e : Nat} {a : Array Code} {dist : Bool} {n : Nat} (hp : tab S = .val (.ref r o))
    (hga : ∀ H' z', BShape E H' z' S → Space.get H' r = some a) (ct : CodeTable a o e n 28 dist)
    {j : Nat} (hj : j < 2 ^ n) (hl : linkTest dist a[o + j]! = true)
    (rep : Lvl a (o + a[o + j]!.val.toNat) a[o + j]!.op.toNat) (hlast : l.last = a[o + j]!)
    (hb0 : n ≤ l.bits.toNat) (hb8 : l.bits.toNat < n + 8) :
    SatX H l (xloopBrk (do
      let t ← (← rdS E.c.st tab).get
      let last := (← get).last
      let b ← BITS (CODE_BITS a[o + j]! + (last.op &&& 15).toUInt32)
      let idx := last.val.toUInt64 + (← shr64 b (CODE_BITS a[o + j]!))
      let here : Code ← Ptr.index t (Int.ofNat idx.toNat)
      modify fun l => { l with here := here }
      if CODE_BITS a[o + j]! + CODE_BITS (← get).here <= (← get).bits.toUInt32 then return true
      PULLBYTE E.c
      return false))
      (fun res l' H' => match res with
        | .ok () => DL E z S l t l' H' ∧
            (∃ k, k < 2 ^ a[o + j]!.op.toNat ∧ l'.here = a[o + a[o + j]!.val.toNat + k]!) ∧
            n + (CODE_BITS l'.here).toNat ≤ l'.bits.toNat ∧
            (Live l'.here → l'.bits.toNat < n + (CODE_BITS l'.here).toNat + 8) ∧ l'.bits.toNat ≤ 35
        | .error .leave => BLv E l' H'
        | .error (.ret _) => False) := by
  have hn15 : n ≤ 15 := ct.n_le
  have hjr : o + j < e := by have := ct.root; omega
  have hf0 := link_f0 hl
  have hop16 : a[o + j]!.op.toNat < 16 := andf0_lt' _ hf0
  have hlb : (CODE_BITS a[o + j]!).toNat = n := by
    rw [cb_link hf0, UInt8.toNat_toUInt32]; exact ct.link_bits _ (Nat.le_add_right _ _) hjr hl
  have hop : (a[o + j]!.op &&& 15).toUInt32.toNat = a[o + j]!.op.toNat := by
    rw [andf0_15 _ hf0]; exact UInt8.toNat_toUInt32 _
  have hn2 : (CODE_BITS a[o + j]! + (a[o + j]!.op &&& 15).toUInt32).toNat = n + a[o + j]!.op.toNat := by
    rw [UInt32.toNat_add, hop, hlb]; exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨hreg, hsub⟩ := ct.link _ (Nat.le_add_right _ _) hjr hl
  have hfits := ct.fits
  have hrep := lvl_repF rep
  unfold xloopBrk
  refine xwhileBrk_rank (fun l' H' => DL E z S l t l' H' ∧
      J (fun y => (CODE_BITS a[o + a[o + j]!.val.toNat + y]!).toNat) a[o + j]!.op.toNat (l'.bits.toNat - n)
        (l'.hold.toNat / 2 ^ n) ∧ n ≤ l'.bits.toNat ∧ l'.bits.toNat ≤ 35)
    (fun l' _ => 64 - l'.bits.toNat) _ ?_ ⟨DL.refl bm, Or.inl (by omega), hb0, by omega⟩ (by unfold fuel; omega)
  rintro l1 H1 ⟨⟨t1, bm1, hp1, hl1, hla1, hm1⟩, hj1, hn1, hb1⟩
  refine SatX.pure ?_
  dsimp only
  refine SatX.bind (liftEq (bm1.sh.rdS tab) ?_)
  rw [hp]
  refine SatX.bind (liftEq (ival_get _ _) ?_)
  refine SatX.bind (SatX.get ?_)
  dsimp only
  rw [hla1, hlast]
  refine SatX.bind (bits_ok _ (by rw [UInt32.lt_iff_toNat_lt, hn2]; show _ < 32; omega) ?_)
  have hv := bits_mod l1.hold (CODE_BITS a[o + j]! + (a[o + j]!.op &&& 15).toUInt32) (by rw [hn2]; omega)
  rw [hn2] at hv
  generalize (l1.hold &&& ((1 : UInt32) <<< (CODE_BITS a[o + j]! + (a[o + j]!.op &&& 15).toUInt32) - 1).toUInt64)
    = v at hv ⊢
  refine SatX.bind (liftEq (shr64_ok v _ (by rw [hlb]; omega) _) ?_)
  have hsh : (v >>> (CODE_BITS a[o + j]!).toUInt64).toNat = l1.hold.toNat / 2 ^ n % 2 ^ a[o + j]!.op.toNat := by
    rw [UInt64.toNat_shiftRight, UInt32.toNat_toUInt64, hlb, Nat.mod_eq_of_lt (by omega : n < 64),
      Nat.shiftRight_eq_div_pow, hv, sub_idx]
  have hkk : l1.hold.toNat / 2 ^ n % 2 ^ a[o + j]!.op.toNat < 2 ^ a[o + j]!.op.toNat := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hvl := a[o + j]!.val.toNat_lt
  have hidx : (a[o + j]!.val.toUInt64 + (v >>> (CODE_BITS a[o + j]!).toUInt64)).toNat =
      a[o + j]!.val.toNat + l1.hold.toNat / 2 ^ n % 2 ^ a[o + j]!.op.toNat := by
    rw [UInt64.toNat_add, UInt16.toNat_toUInt64, hsh]
    have : 2 ^ a[o + j]!.op.toNat ≤ 2 ^ 16 := Nat.pow_le_pow_right (by decide) (by omega)
    exact Nat.mod_eq_of_lt (by show _ < 18446744073709551616; omega)
  generalize hkkd : l1.hold.toNat / 2 ^ n % 2 ^ a[o + j]!.op.toNat = kk at hkk hidx hsh
  have hin : o + (a[o + j]!.val.toNat + kk) < a.size := by omega
  refine SatX.bind (liftEq (by rw [hidx]; exact tab_index' (hga H1 z bm1.sh) hin) ?_)
  refine SatX.bind (SatX.modify ?_)
  obtain ⟨hs28, hsl, -⟩ := hsub kk hkk
  have hent := ct.ent (o + (a[o + j]!.val.toNat + kk)) (by omega) (by omega)
  rw [show o + (a[o + j]!.val.toNat + kk) = o + a[o + j]!.val.toNat + kk by omega] at hent ⊢
  have bm2 : BM E { l1 with here := a[o + a[o + j]!.val.toNat + kk]! } H1 t1 z S := bm1.locals rfl rfl rfl rfl
  have hcbn : (CODE_BITS a[o + j]! + CODE_BITS a[o + a[o + j]!.val.toNat + kk]!).toNat =
      n + (CODE_BITS a[o + a[o + j]!.val.toNat + kk]!).toNat := by
    have := hent.cb_le; have := hent.bits_le
    rw [UInt32.toNat_add, hlb]; exact Nat.mod_eq_of_lt (by omega)
  refine SatX.bind (SatX.get ?_)
  refine SatX.bind (SatX.get ?_)
  dsimp only
  split
  · rename_i hle
    have hle' : n + (CODE_BITS a[o + a[o + j]!.val.toNat + kk]!).toNat ≤ l1.bits.toNat := by
      have := UInt32.le_iff_toNat_le.mp hle; rw [UInt8.toNat_toUInt32, hcbn] at this; exact this
    refine SatX.pure ⟨⟨t1, bm2, hp1, hl1, hla1, hm1⟩, ⟨kk, hkk, rfl⟩, hle', fun hlv => ?_, hb1⟩
    have := rep_exit (live := fun y => Live a[o + a[o + j]!.val.toNat + y]!) hrep hj1 (by rw [hkkd]; exact hlv)
    rw [hkkd] at this
    show l1.bits.toNat < n + (CODE_BITS a[o + a[o + j]!.val.toNat + kk]!).toNat + 8
    omega
  · rename_i hgt
    have hgt' : l1.bits.toNat < n + (CODE_BITS a[o + a[o + j]!.val.toNat + kk]!).toNat := by
      have := UInt32.lt_iff_toNat_lt.mp (UInt32.not_le.mp hgt); rw [UInt8.toNat_toUInt32, hcbn] at this; exact this
    have hcb := hent.cb_le
    have hjb := ct.link_bits _ (Nat.le_add_right _ _) hjr hl
    refine SatX.bind (pullbyte_ok cb E.c rfl rfl bm2.inB (by show l1.bits.toNat < 56; omega) ?_ ?_)
    · intro H' q hk hI h0
      exact ⟨t1, z, S, bm2.sh.keep hk, ⟨q, 0, hI, by rw [h0]; exact Nat.le_refl _, fun h => absurd rfl h⟩,
        bm2.put, bm2.left⟩
    · intro l3 H3 t3 hk hin3 hm3 hb3 pb3 _ hh3
      have hb3' : l3.bits.toNat = l1.bits.toNat + 8 := hb3
      have hh3' : l3.hold.toNat % 2 ^ l1.bits.toNat = l1.hold.toNat % 2 ^ l1.bits.toNat := hh3
      refine SatX.pure ⟨⟨DL.pull bm2 hp1 hl1 hla1 hm1 hk hin3 hm3 hb3 pb3, ?_, by omega, by omega⟩, by omega⟩
      rw [hb3', show l1.bits.toNat + 8 - n = l1.bits.toNat - n + 8 by omega]
      refine rep_pull (c := fun y => (CODE_BITS a[o + a[o + j]!.val.toNat + y]!).toNat) ?_ (sub_pull hn1 hh3')
      rw [hkkd]; omega

/-- The outcome of `decodeSym` from `l` with `t` bytes to come (see the module comment). -/
def DPost (E : BEnv) (z : ZStream) (S : InflateState) (l : IL) (t : Nat) (dist : Bool) :
    Except Ex Unit → IL → Heap → Prop
  | .ok (), l', H' => ∃ t', BM E l' H' t' z S ∧ l'.put = l.put ∧ l'.left = l.left ∧
      8 * (l'.have_.toNat + t') + l'.bits.toNat ≤ 8 * (l.have_.toNat + t) + l.bits.toNat ∧
      EntryOK l'.here 28 dist ∧ linkTest dist l'.here = false ∧
      (dist = false → ∃ pre, ZlibNgF.Proof.InflateTab.LenOK pre l'.here) ∧
      (CODE_BITS l'.here).toNat ≤ l'.bits.toNat ∧
      (Live l'.here → l'.bits.toNat < (CODE_BITS l'.here).toNat + 8) ∧ l'.bits.toNat ≤ 35
  | .error .leave, l', H' => BLv E l' H'
  | .error (.ret _), _, _ => False

theorem live_link {dist : Bool} {e : Code} (h : linkTest dist e = true) : Live e := by
  left
  have := link_f0 h
  revert this
  generalize e.op = x
  revert x
  decide

/-- `decodeSym`: the table lookup of `LEN`, with at most one link. -/
theorem bdecode {E : BEnv} (cb : E.CB) {l : IL} {H : Heap} {t : Nat} {z : ZStream} {S : InflateState}
    (bm : BM E l H t z S) (hb8 : l.bits.toNat < 8) {tab : InflateState → Ival CodePtr}
    {nbits : InflateState → UInt32} {dist : Bool} (hrt : RTab E.b S.codes (tab S) (nbits S) 28 dist) :
    SatX H l (ZlibNg.Infback.decodeSym E.c tab nbits (linkTest dist)) (DPost E z S l t dist) := by
  obtain ⟨r, o, e, a, hp, ct, rp, hga⟩ := hrt.get (E := E)
  unfold ZlibNg.Infback.decodeSym
  refine SatX.bind (SatX.mono (bdec1 cb bm hp hga ct rp.1 hb8) ?_)
  rintro res l1 H1 p
  match res, p with
  | .error .leave, p => exact p
  | .ok (), ⟨⟨t1, bm1, hp1, hl1, hla1, hm1⟩, ⟨j, hj, hhere⟩, hcb, hlive, hb35⟩ =>
  refine SatX.bind (SatX.get ?_)
  dsimp only
  have hjr : o + j < e := by have := ct.root; omega
  have hent := ct.ent _ (Nat.le_add_right _ _) hjr
  rw [hhere] at hcb hlive ⊢
  split
  · rename_i hl
    have hlb : (CODE_BITS a[o + j]!).toNat = (nbits S).toNat := by
      rw [cb_link (link_f0 hl), UInt8.toNat_toUInt32]; exact ct.link_bits _ (Nat.le_add_right _ _) hjr hl
    refine SatX.bind (SatX.modify ?_)
    refine SatX.bind (SatX.get ?_)
    dsimp only
    rw [hhere]
    have h8 := hlive (live_link hl)
    refine SatX.bind (SatX.mono (bdec2 cb (bm1.locals (l' := { l1 with here := a[o + j]!, last := a[o + j]! })
      rfl rfl rfl rfl) hp hga ct hj hl (rp.2 j hj hl) rfl
      (by show _ ≤ l1.bits.toNat; omega) (by show l1.bits.toNat < _; omega)) ?_)
    rintro res l3 H3 p
    match res, p with
    | .error .leave, p => exact p
    | .ok (), ⟨⟨t3, bm3, hp3, hl3, _, hm3⟩, ⟨k, hk, hhere3⟩, hcb3, hlive3, hb3⟩ =>
    have hn15 := ct.n_le
    refine dropbits_ok _ (by rw [UInt32.lt_iff_toNat_lt, hlb]; show _ < 64; omega) ?_
    have hlb8 : (CODE_BITS a[o + j]!).toUInt8.toNat = (nbits S).toNat := by
      rw [UInt32.toNat_toUInt8, hlb]; exact Nat.mod_eq_of_lt (by omega)
    have hd : (l3.bits - (CODE_BITS a[o + j]!).toUInt8).toNat = l3.bits.toNat - (nbits S).toNat := by
      rw [UInt8.toNat_sub_of_le _ _ (UInt8.le_iff_toNat_le.mpr (by rw [hlb8]; omega)), hlb8]
    obtain ⟨hreg, hsub⟩ := ct.link _ (Nat.le_add_right _ _) hjr hl
    have hm3' : 8 * (l3.have_.toNat + t3) + l3.bits.toNat = 8 * (l1.have_.toNat + t1) + l1.bits.toNat := hm3
    have hent3 := ct.ent (o + a[o + j]!.val.toNat + k) (by omega) (by omega)
    refine ⟨t3, bm3.locals rfl rfl rfl rfl, hp3.trans hp1, hl3.trans hl1, ?_, by rw [hhere3]; exact hent3,
      by rw [hhere3]; exact (hsub k hk).2.1, fun hd => ⟨_, by rw [hhere3]; exact ((hsub k hk).2.2 hd)⟩, ?_, ?_, ?_⟩
    · show 8 * (l3.have_.toNat + t3) + (l3.bits - (CODE_BITS a[o + j]!).toUInt8).toNat ≤ _
      rw [hd]; omega
    · show (CODE_BITS l3.here).toNat ≤ (l3.bits - (CODE_BITS a[o + j]!).toUInt8).toNat
      rw [hd]; omega
    · intro hv
      show (l3.bits - (CODE_BITS a[o + j]!).toUInt8).toNat < (CODE_BITS l3.here).toNat + 8
      have := hlive3 hv; rw [hd]; omega
    · show (l3.bits - (CODE_BITS a[o + j]!).toUInt8).toNat ≤ 35
      rw [hd]; omega
  · rename_i hnl
    refine SatX.pure ⟨t1, bm1, hp1, hl1, by omega, by rw [hhere]; exact hent, by rw [hhere]; simpa using hnl,
      fun hd => ⟨0, by rw [hhere]; exact ct.lit hd _ (Nat.le_add_right _ _) (by omega)⟩, by rw [hhere]; exact hcb,
      by rw [hhere]; exact hlive, hb35⟩

end ZlibNgF.Proof.InfbackLoop
