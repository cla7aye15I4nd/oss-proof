import ZlibNgF.Proof.«inflate.c.table-modes»

/-!
# The mode `CODELENS` of `inflate` (`ZlibNgF`)

`CODELENS` decodes the code lengths of the literal/length and distance codes with the code length code (the table of
`LENLENS` at the start of `codes`, `TabAt … 25`), stores them in `lens` (`have` counts them; a repeat code stores up
to 138 copies), and builds the two decoding tables with `zng_inflate_table` (`table_run`): the literal/length table at
`codes[0]`, the distance table after it. It then falls into `LEN_`.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InflateLoop
open C ZlibNgF.Spec ZlibNg.Inflate
open ZlibNgF.Proof.InflateInv (Inv Core view ModeOK DecodeMode)
open ZlibNgF.Proof.InflateX
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.mono Sat.of_eq St Touch)
open ZlibNgF.Proof.InflateTab (TabAt CodeTable EntryOK)

/-! ## `PULLBYTE` and the decoding loop -/

/-- `PULLBYTE()` with room for 8 more bits: one input byte moves into the bit buffer, or the call leaves. -/
theorem pullbyte_ok {E : Env} (eo : EnvOK E) {l : IL} {H : Heap} {z : ZStream} {S : InflateState}
    (li : LI E l H z S) (hb : l.bits.toNat + 8 ≤ 39) :
    SatX H l PULLBYTE (fun r l' H' => H' = H ∧ match r with
      | .ok () => LI E l' H z S ∧ Pulled l l' ∧ l'.bits.toNat = l.bits.toNat + 8 ∧
          l'.have_.toNat + 1 = l.have_.toNat
      | .error e => e = .leave ∧ l' = l) := by
  unfold PULLBYTE
  refine SatX.bind (SatX.get ?_)
  dsimp only
  by_cases h0 : l.have_ = 0
  · simp only [h0, beq_self_eq_true, ↓reduceIte]
    exact SatX.bind (SatX.throw ⟨rfl, rfl, rfl⟩)
  · have h0' : (l.have_ == 0) = false := by simpa using h0
    simp only [h0', Bool.false_eq_true, ↓reduceIte]
    obtain ⟨r, o, d, hnx, hg, hsz⟩ := li.inBytes eo h0
    have hh1 : 1 ≤ l.have_.toNat := by
      rcases Nat.eq_zero_or_pos l.have_.toNat with e | e
      · exact absurd (UInt32.toNat_inj.mp (by rw [e]; rfl)) h0
      · exact e
    rw [hnx]
    have hlo : o < d.size := by omega
    refine SatX.bind (SatX.lift_eq (a := d[o]) (by simp [load8, Ptr.load, hg, hlo]) ?_)
    refine SatX.bind (SatX.lift_eq (add_in hg (k := 1) (by omega)) ?_)
    have hb64 : l.bits.toUInt32 < 64 := by
      rw [UInt32.lt_iff_toNat_lt, UInt8.toNat_toUInt32]; show _ < 64; omega
    refine SatX.bind (SatX.lift_eq (a := (d[o]).toUInt64 <<< l.bits.toUInt32.toUInt64)
      (by simp [shl64, hb64]) ?_)
    refine SatX.set ?_
    have hb8 : (l.bits + 8).toNat = l.bits.toNat + 8 := by
      rw [UInt8.toNat_add]; show (l.bits.toNat + 8) % 256 = _; omega
    have hsub : (l.have_ - 1).toNat = l.have_.toNat - 1 := by
      rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; show 1 ≤ _; omega)]; rfl
    have hc1 : (1 : UInt32) ≤ l.have_ := by rw [UInt32.le_iff_toNat_le]; exact hh1
    have li1 := li.consume hnx 1 hc1 { l with have_ := l.have_ - 1, next := .ref r (o + 1) }
      rfl rfl rfl rfl rfl rfl
    refine ⟨rfl, li1.setBits rfl rfl rfl rfl rfl ?_, ⟨rfl, ?_⟩, hb8, by rw [hsub]; omega⟩
    · show l.bits + 8 ≤ 39
      rw [UInt8.le_iff_toNat_le, hb8]; exact hb
    · show 8 * (l.have_ - 1).toNat + (l.bits + 8).toNat = _
      rw [hsub, hb8]; omega

/-- The loop of `CODELENS` that looks up the next code: `here = lcode[BITS(lenbits)]` until `here.bits` bits are
held, pulling a byte at a time. The heap does not change; it ends with an entry of the table and enough bits, or
leaves when the input runs out. -/
theorem decode_ok {E : Env} (eo : EnvOK E) {l : IL} {H : Heap} {z : ZStream} {S : InflateState}
    (li : LI E l H z S) {r : CodeRef} {o e : Nat} {a : Array Code} (hg : Space.get H r = some a) {lb : UInt32}
    (t : CodeTable a o e lb.toNat 25 false) :
    SatX H l (xloopBrk (do
        let b ← BITS lb
        let here : Code ← Ptr.index (.ref r o : CodePtr) (Int.ofNat b.toNat)
        modify fun l => { l with here := here }
        if here.bits <= (← get).bits then return true
        PULLBYTE
        return false))
      (fun res l' H' => H' = H ∧ LI E l' H z S ∧ l'.left = l.left ∧
        8 * l'.have_.toNat + l'.bits.toNat = 8 * l.have_.toNat + l.bits.toNat ∧
        match res with
        | .ok () => EntryOK l'.here 25 false ∧ l'.here.bits ≤ l'.bits
        | .error e => e = .leave) := by
  have hn15 : lb.toNat ≤ 15 := t.n_le
  unfold xloopBrk
  refine xwhileBrk_rank (fun l' H' => H' = H ∧ LI E l' H z S ∧ l'.left = l.left ∧
      8 * l'.have_.toNat + l'.bits.toNat = 8 * l.have_.toNat + l.bits.toNat) (fun l' _ => l'.have_.toNat) _ ?_
    ⟨rfl, li, rfl, rfl⟩ (by have := l.have_.toNat_lt; unfold fuel; omega)
  rintro l1 H1 ⟨hH1, li1, hl1, hb1⟩
  rw [hH1]
  refine SatX.pure ?_
  dsimp only
  refine SatX.bind (bits_ok lb (by rw [UInt32.lt_iff_toNat_lt]; show _ < 32; omega) ?_)
  have hk := bits_lt l1.hold lb hn15
  refine SatX.bind (SatX.lift_eq (tab_index hg t hk) ?_)
  refine SatX.bind (SatX.modify ?_)
  have hj1 : o ≤ o + (l1.hold &&& ((1 : UInt32) <<< lb - 1).toUInt64).toNat := Nat.le_add_right _ _
  have hj2 : o + (l1.hold &&& ((1 : UInt32) <<< lb - 1).toUInt64).toNat < e := by
    have := t.root; omega
  have hent := t.ent _ hj1 hj2
  have li2 : LI E { l1 with here := a[o + (l1.hold &&& ((1 : UInt32) <<< lb - 1).toUInt64).toNat]! } H z S :=
    li1.locals rfl rfl rfl rfl rfl rfl
  refine SatX.bind (SatX.get ?_)
  dsimp only
  split
  · rename_i hle
    exact SatX.pure ⟨rfl, li2, hl1, hb1, hent, hle⟩
  · rename_i hgt
    have hgt' : l1.bits.toNat < (a[o + (l1.hold &&& ((1 : UInt32) <<< lb - 1).toUInt64).toNat]!).bits.toNat := by
      have := UInt8.not_le.mp hgt; exact this
    have h25 := hent.bits_le
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

/-! ## Stores of code lengths -/

/-- A store of the counter and the lengths in `CODELENS` that keeps the lengths read at most 15. -/
theorem core_CLs {H : Heap} {i b : Nat} {z : ZStream} {al : InflateAllocs} {S : InflateState} (hv : UInt32)
    (L : Array UInt16) (c : Core H (some i) z b (view S) al) (hm : S.mode = CODELENS) (hL : L.size = S.lens.size)
    (hk : ∀ j, j < hv.toNat → L[j]! ≤ 15) :
    Core H (some i) z b (view { S with «have» := hv, lens := L }) al := by
  obtain ⟨a1, a2, -, a4, a5⟩ := c.modes.codelens hm
  exact { c with
    lens_size := by show L.size = 320; rw [hL]; exact c.lens_size
    modes := modeOK_CL b _ hm ⟨a1, a2, hk, a4, a5⟩ }

theorem have_succ' {v : UInt32} (h : v.toNat < 320) : (v + 1).toNat = v.toNat + 1 := by
  rw [UInt32.toNat_add]; show (v.toNat + 1) % 4294967296 = _; omega

/-- The lengths read so far stay at most 15 after `lens[have++] = v` with `v ≤ 15`. -/
theorem cl_keep {L : Array UInt16} {hv : UInt32} (hL : L.size = 320) (h320 : hv.toNat < 320)
    (hk : ∀ j, j < hv.toNat → L[j]! ≤ 15) (v : UInt16) (hvle : v ≤ 15) :
    ∀ j, j < (hv + 1).toNat → (L.set! hv.toNat v)[j]! ≤ 15 := by
  intro j hj
  rw [have_succ' h320] at hj
  by_cases e : j = hv.toNat
  · subst e; rw [set16_eq _ _ _ (by omega)]; exact hvle
  · rw [set16_ne _ _ _ _ e]; exact hk j (by omega)

/-- `lens[k]` of the state for `k < 320`. -/
theorem index_lens {H : Heap} {b : Nat} {S : InflateState} (hs : H.istate b = some S) (hL : S.lens.size = 320)
    {k : Nat} (hk : k < 320) :
    Ptr.index (.ref (.lens b) 0 : WPtr) (Int.ofNat k) H = .ok (S.lens[k]!, H) := by
  have hg : Space.get H (WRef.lens b) = some S.lens := by
    show Heap.getWords _ _ = _
    simp only [Heap.getWords, hs, Option.map_some]
  have hlt : k < S.lens.size := by omega
  have hc : 0 ≤ S.lens.size ∧ 0 ≤ ((0 : Nat) : Int) + Int.ofNat k ∧ ((0 : Nat) : Int) + Int.ofNat k ≤ (S.lens.size : Int) := by
    simp only [Int.ofNat_eq_natCast]; omega
  have e1 : (((0 : Nat) : Int) + Int.ofNat k).toNat = k := by simp only [Int.ofNat_eq_natCast]; omega
  simp only [Ptr.index, Ptr.add, Ptr.load, bind_app, hg, hc, and_self, ↓reduceIte, e1, hlt,
    ↓reduceDIte, getElem!_pos S.lens k hlt]

/-! ## The loop of `CODELENS` -/

/-- The state of `CODELENS` during its loop, from the locals `l0` at entry. -/
def CLs (E : Env) (l0 : IL) (z : ZStream) (l : IL) (H : Heap) : Prop :=
  ∃ S, LI E l H z S ∧ S.mode = CODELENS ∧ l.left = l0.left ∧
    8 * l.have_.toNat + l.bits.toNat ≤ 8 * l0.have_.toNat + l0.bits.toNat

/-- The state after the loop: all lengths read (mode `CODELENS`), or a bad repeat (mode `BAD`). -/
def CLd (E : Env) (l0 : IL) (_z : ZStream) (l : IL) (H : Heap) : Prop :=
  ∃ z' S, LI E l H z' S ∧ l.left = l0.left ∧
    8 * l.have_.toNat + l.bits.toNat ≤ 8 * l0.have_.toNat + l0.bits.toNat ∧
    ((S.mode = CODELENS ∧ S.nlen.toNat + S.ndist.toNat ≤ S.«have».toNat) ∨ S.mode = BAD)

def CLrank (E : Env) (_l : IL) (H : Heap) : Nat :=
  match H.istate E.b with | some S => 320 - S.«have».toNat | none => 0

/-- What one trip of the loop body of `CODELENS` ends with, from a state whose counter was `hv0`. -/
def CLbody (E : Env) (m : Nat) (l0 : IL) (z : ZStream) (hv0 : Nat) : Except Ex Bool → IL → Heap → Prop
  | .error e, l, H => Post E m (.error e) l H
  | .ok true, l, H => CLd E l0 z l H
  | .ok false, l, H => CLs E l0 z l H ∧ CLrank E l H < 320 - hv0

/-- The counts of a state in `CODELENS`. -/
theorem LI.clFacts {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (li : LI E l H z S)
    (hm : S.mode = CODELENS) :
    (257 ≤ S.nlen.toNat ∧ S.nlen.toNat ≤ 286) ∧ (1 ≤ S.ndist.toNat ∧ S.ndist.toNat ≤ 30) ∧
      (∀ j, j < S.«have».toNat → S.lens[j]! ≤ 15) ∧ TabAt E.b S.codes S.lencode S.lenbits 25 false ∧
      S.lencode = .val (.ref (.codes E.b) 0) := by
  obtain ⟨al, -, c⟩ := li.core
  obtain ⟨⟨a1, a2⟩, ⟨a3, a4⟩, a5, a6, a7⟩ := c.modes.codelens hm
  exact ⟨⟨a1, UInt32.le_iff_toNat_le.mp a2⟩, ⟨a3, UInt32.le_iff_toNat_le.mp a4⟩, a5, a6, a7⟩

/-- A bad repeat: `SET_BAD(msg); break;`. -/
theorem badBrk_ok {E : Env} {m : Nat} {l0 : IL} {z0 : ZStream} {hv0 : Nat} {l : IL} {H : Heap} {z : ZStream}
    {S : InflateState} (li : LI E l H z S) (hl : l.left = l0.left)
    (hb : 8 * l.have_.toNat + l.bits.toNat ≤ 8 * l0.have_.toNat + l0.bits.toNat) :
    SatX H l (do (MonadLiftT.monadLift (SET_BAD E.c "invalid bit length repeat") : X Unit); pure true)
      (CLbody E m l0 z0 hv0) := by
  refine SatX.bind (SatX.lift (Sat.mono (li.setBad _ (strIdx 15 (by decide) (by decide) (by decide))) ?_))
  rintro _ H1 ⟨z1, li1⟩
  exact SatX.pure ⟨z1, _, li1, hl, hb, Or.inr rfl⟩

/-- The end of a repeat code: the check against `nlen + ndist` and the `copy` stores of `len`. -/
def repTail (c : Ctx) (lens : WPtr) : X Bool := do
  let s ← ldState c.st
  if s.«have» + (← get).copy > s.nlen + s.ndist then
    SET_BAD c "invalid bit length repeat"
    return true
  xwhile (do return (← get).copy != 0) (do
    modify fun l => { l with copy := l.copy - 1 }
    let hv ← rdS c.st (·.«have»)
    wrS c.st fun s => { s with «have» := s.«have» + 1 }
    Ptr.store (← lens.add (Int.ofNat hv.toNat)) (← get).len.toUInt16)
  return false

theorem repTail_ok {E : Env} {m : Nat} {l0 : IL} {l : IL} {H : Heap} {z : ZStream} {S : InflateState}
    (li : LI E l H z S) (hm : S.mode = CODELENS) (hlt : S.«have».toNat < S.nlen.toNat + S.ndist.toNat)
    (hlen : l.len.toUInt16 ≤ 15) (hc1 : 1 ≤ l.copy.toNat) (hc2 : l.copy.toNat ≤ 138) (hl : l.left = l0.left)
    (hb : 8 * l.have_.toNat + l.bits.toNat ≤ 8 * l0.have_.toNat + l0.bits.toNat) :
    SatX H l (repTail E.c (.ref (.lens E.b) 0)) (CLbody E m l0 z S.«have».toNat) := by
  obtain ⟨⟨n1, n2⟩, ⟨d1, d2⟩, -, -, -⟩ := li.clFacts hm
  unfold repTail
  refine SatX.bind (SatX.lift_eq li.ldState ?_)
  refine SatX.bind (SatX.get ?_)
  dsimp only
  have hsum : (S.«have» + l.copy).toNat = S.«have».toNat + l.copy.toNat := by
    rw [UInt32.toNat_add]; exact Nat.mod_eq_of_lt (by show _ < 4294967296; omega)
  have hnd : (S.nlen + S.ndist).toNat = S.nlen.toNat + S.ndist.toNat := by
    rw [UInt32.toNat_add]; exact Nat.mod_eq_of_lt (by show _ < 4294967296; omega)
  split
  · exact badBrk_ok li hl hb
  rename_i hng
  have hle : S.«have».toNat + l.copy.toNat ≤ S.nlen.toNat + S.ndist.toNat := by
    have : ¬ (S.nlen + S.ndist).toNat < (S.«have» + l.copy).toNat := hng
    omega
  refine SatX.bind (SatX.mono (P := fun r l' H' => match r with
      | .ok () => CLs E l0 z l' H' ∧ CLrank E l' H' < 320 - S.«have».toNat
      | .error e => CLbody E m l0 z S.«have».toNat (.error e) l' H') ?_ ?_)
  · unfold xwhile
    refine xwhileBrk_rank (fun l' H' => ∃ S', LI E l' H' z S' ∧ S'.mode = CODELENS ∧ l'.left = l.left ∧
        l'.have_ = l.have_ ∧ l'.bits = l.bits ∧ l'.len = l.len ∧ S'.nlen = S.nlen ∧ S'.ndist = S.ndist ∧
        S'.«have».toNat + l'.copy.toNat = S.«have».toNat + l.copy.toNat)
      (fun l' _ => l'.copy.toNat) _ ?_ ⟨S, li, hm, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      (by have := l.copy.toNat_lt; unfold fuel; omega)
    rintro l1 H1 ⟨S1, li1, hm1, hl1, hh1, hb1, hn1, hnl1, hnd1, hs1⟩
    refine SatX.bind (SatX.get ?_)
    refine SatX.pure ?_
    dsimp only
    by_cases h0 : l1.copy = 0
    · simp only [h0, bne_self_eq_false]
      refine ⟨⟨S1, li1, hm1, by rw [hl1, hl], by rw [hh1, hb1]; exact hb⟩, ?_⟩
      unfold CLrank; rw [li1.hs]; dsimp only
      have : l1.copy.toNat = 0 := by rw [h0]; rfl
      omega
    · have h0' : (l1.copy != 0) = true := by simpa using h0
      rw [h0']
      have hc1' : 1 ≤ l1.copy.toNat := by
        rcases Nat.eq_zero_or_pos l1.copy.toNat with e | e
        · exact absurd (UInt32.toNat_inj.mp (by rw [e]; rfl)) h0
        · exact e
      have hcsub : (l1.copy - 1).toNat = l1.copy.toNat - 1 := by
        rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; show 1 ≤ _; omega)]; rfl
      refine SatX.bind (SatX.bind (SatX.modify ?_))
      have li2 : LI E { l1 with copy := l1.copy - 1 } H1 z S1 := li1.locals rfl rfl rfl rfl rfl rfl
      have hs2 := li2.hs
      have hsz := li2.lensSize
      have hfx := li2.clFacts hm1
      have h320 : S1.«have».toNat < 320 := by omega
      refine SatX.bind (SatX.lift_eq (li2.rdS (·.«have»)) ?_)
      refine SatX.bind (SatX.lift (Sat.of_eq (wrS_app hs2 _) ?_))
      refine SatX.bind (SatX.lift_eq (addLens_withS hs2 _ (k := S1.«have».toNat) (by show _ ≤ S1.lens.size; omega)) ?_)
      refine SatX.bind (SatX.get ?_)
      refine SatX.lift (Sat.of_eq (storeLens_withS hs2 _ (by show _ < S1.lens.size; omega) _) (SatX.pure ?_))
      refine ⟨⟨_, li2.withS _ (fun _ _ c => core_CLs (S := S1) (S1.«have» + 1) _ c hm1 (by simp)
          (cl_keep hsz h320 hfx.2.2.1 _ (by rw [hn1]; exact hlen))) rfl, hm1, hl1, hh1, hb1, hn1, hnl1, hnd1, ?_⟩, ?_⟩
      · show (S1.«have» + 1).toNat + (l1.copy - 1).toNat = _
        rw [have_succ' h320, hcsub]; omega
      · show (l1.copy - 1).toNat < l1.copy.toNat
        rw [hcsub]; omega
  · rintro r l2 H2 p
    match r, p with
    | .error e, p => exact p
    | .ok (), p => exact SatX.pure p

/-- The repeat codes 17 and 18: `NEEDBITS(here.bits + k); DROPBITS(here.bits); len = 0; copy = base + BITS(k);
DROPBITS(k);` and the end of a repeat code. -/
theorem repK_ok {E : Env} {m : Nat} {l0 : IL} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (eo : EnvOK E)
    (li : LI E l H z S) (hm : S.mode = CODELENS) (hlt : S.«have».toNat < S.nlen.toNat + S.ndist.toNat) (h : Code)
    (hh : h.bits.toNat ≤ 25) (hbits : h.bits ≤ l.bits) (k base : UInt32) (hk : k.toNat ≤ 7)
    (hb1 : 1 ≤ base.toNat) (hb2 : base.toNat + 2 ^ k.toNat ≤ 139) (hl : l.left = l0.left)
    (hb : 8 * l.have_.toNat + l.bits.toNat ≤ 8 * l0.have_.toNat + l0.bits.toNat) :
    SatX H l (do
      NEEDBITS (h.bits.toUInt32 + k)
      DROPBITS h.bits.toUInt32
      modify fun l => { l with len := 0 }
      let b ← BITS k
      modify fun l => { l with copy := base + b.toUInt32 }
      DROPBITS k
      repTail E.c (.ref (.lens E.b) 0)) (CLbody E m l0 z S.«have».toNat) := by
  have hhb : h.bits.toUInt32.toNat = h.bits.toNat := UInt8.toNat_toUInt32 _
  have hn : (h.bits.toUInt32 + k).toNat = h.bits.toNat + k.toNat := by
    rw [UInt32.toNat_add, hhb]; exact Nat.mod_eq_of_lt (by omega)
  have hbl : h.bits.toNat ≤ l.bits.toNat := UInt8.le_iff_toNat_le.mp hbits
  refine SatX.bind (SatX.mono (needbits_ok eo li _ (by rw [hn]; omega)) ?_)
  rintro r l3 H3 ⟨hH3, li3, p3, -, hr⟩
  rw [hH3]
  match r, hr with
  | .error e, ⟨he, _⟩ => rw [he]; exact ⟨z, S, li3⟩
  | .ok (), hr =>
  rw [hn] at hr
  have hl3 : l3.left = l.left := by rw [p3.1]
  have hb3 := p3.2
  refine SatX.bind (dropbits_ok _ (by rw [UInt32.lt_iff_toNat_lt, hhb]; show _ < 64; omega) ?_)
  have hd4 := drop_toNat (b := l3.bits) (n := h.bits.toUInt32) (by rw [hhb]; omega) (by rw [hhb]; omega)
  rw [hhb] at hd4
  have li4 := li3.drop h.bits.toUInt32 (by rw [hhb]; omega) (by rw [hhb]; omega)
  refine SatX.bind (SatX.modify ?_)
  refine SatX.bind (bits_ok k (by rw [UInt32.lt_iff_toNat_lt]; show _ < 32; omega) ?_)
  refine SatX.bind (SatX.modify ?_)
  refine SatX.bind (dropbits_ok k (by rw [UInt32.lt_iff_toNat_lt]; show _ < 64; omega) ?_)
  have hd5 := drop_toNat (b := l3.bits - h.bits.toUInt32.toUInt8) (n := k) (by omega) (by rw [hd4]; omega)
  have hbk := bits_lt (l3.hold >>> h.bits.toUInt32.toUInt64) k (by omega)
  have hpow : 2 ^ k.toNat ≤ 128 := Nat.le_trans (Nat.pow_le_pow_right (by decide) hk) (by decide)
  have hcp : (base + ((l3.hold >>> h.bits.toUInt32.toUInt64) &&& ((1 : UInt32) <<< k - 1).toUInt64).toUInt32).toNat =
      base.toNat + ((l3.hold >>> h.bits.toUInt32.toUInt64) &&& ((1 : UInt32) <<< k - 1).toUInt64).toNat := by
    rw [UInt32.toNat_add, UInt64.toNat_toUInt32, Nat.mod_eq_of_lt (a := UInt64.toNat _) (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  refine repTail_ok (li4.setBits rfl rfl rfl rfl rfl ?_) hm hlt (by show (0 : UInt32).toUInt16 ≤ 15; decide) ?_ ?_ ?_ ?_
  · rw [UInt8.le_iff_toNat_le]; show (l3.bits - h.bits.toUInt32.toUInt8 - k.toUInt8).toNat ≤ 39
    rw [hd5, hd4]; have := li3.bits; rw [UInt8.le_iff_toNat_le] at this; have : l3.bits.toNat ≤ 39 := this; omega
  · show 1 ≤ (base + _).toNat; rw [hcp]; omega
  · show (base + _).toNat ≤ 138; rw [hcp]; omega
  · show l3.left = l0.left; rw [hl3, hl]
  · show 8 * l3.have_.toNat + (l3.bits - h.bits.toUInt32.toUInt8 - k.toUInt8).toNat ≤ _
    rw [hd5, hd4]; omega

/-- The repeat code 16: the previous length, 3 to 6 times. -/
theorem rep16_ok {E : Env} {m : Nat} {l0 : IL} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (eo : EnvOK E)
    (li : LI E l H z S) (hm : S.mode = CODELENS) (hlt : S.«have».toNat < S.nlen.toNat + S.ndist.toNat) (h : Code)
    (hh : h.bits.toNat ≤ 25) (hbits : h.bits ≤ l.bits) (hl : l.left = l0.left)
    (hb : 8 * l.have_.toNat + l.bits.toNat ≤ 8 * l0.have_.toNat + l0.bits.toNat) :
    SatX H l (do
      NEEDBITS (h.bits.toUInt32 + 2)
      DROPBITS h.bits.toUInt32
      let hv ← rdS E.c.st (·.«have»)
      if hv == 0 then
        SET_BAD E.c "invalid bit length repeat"
        return true
      let len ← Ptr.index (.ref (.lens E.b) 0 : WPtr) (Int.ofNat (hv - 1).toNat)
      modify fun l => { l with len := len.toUInt32 }
      let b ← BITS 2
      modify fun l => { l with copy := 3 + b.toUInt32 }
      DROPBITS 2
      repTail E.c (.ref (.lens E.b) 0)) (CLbody E m l0 z S.«have».toNat) := by
  have hhb : h.bits.toUInt32.toNat = h.bits.toNat := UInt8.toNat_toUInt32 _
  have hn : (h.bits.toUInt32 + 2).toNat = h.bits.toNat + 2 := by
    have : (2 : UInt32).toNat = 2 := rfl
    rw [UInt32.toNat_add, hhb, this]; exact Nat.mod_eq_of_lt (by omega)
  have hbl : h.bits.toNat ≤ l.bits.toNat := UInt8.le_iff_toNat_le.mp hbits
  obtain ⟨⟨-, n2⟩, ⟨-, d2⟩, hlens, -, -⟩ := li.clFacts hm
  refine SatX.bind (SatX.mono (needbits_ok eo li _ (by rw [hn]; omega)) ?_)
  rintro r l3 H3 ⟨hH3, li3, p3, -, hr⟩
  rw [hH3]
  match r, hr with
  | .error e, ⟨he, _⟩ => rw [he]; exact ⟨z, S, li3⟩
  | .ok (), hr =>
  rw [hn] at hr
  have hl3 : l3.left = l.left := by rw [p3.1]
  have hb3 := p3.2
  refine SatX.bind (dropbits_ok _ (by rw [UInt32.lt_iff_toNat_lt, hhb]; show _ < 64; omega) ?_)
  have hd4 := drop_toNat (b := l3.bits) (n := h.bits.toUInt32) (by rw [hhb]; omega) (by rw [hhb]; omega)
  rw [hhb] at hd4
  have li4 := li3.drop h.bits.toUInt32 (by rw [hhb]; omega) (by rw [hhb]; omega)
  refine SatX.bind (SatX.lift_eq (li4.rdS (·.«have»)) ?_)
  dsimp only
  split
  · exact badBrk_ok li4 (by show l3.left = l0.left; rw [hl3, hl])
      (by show 8 * l3.have_.toNat + (l3.bits - h.bits.toUInt32.toUInt8).toNat ≤ _; rw [hd4]; omega)
  rename_i hv0
  have hv0' : S.«have» ≠ 0 := by simpa using hv0
  have hv1 : 1 ≤ S.«have».toNat := by
    rcases Nat.eq_zero_or_pos S.«have».toNat with e | e
    · exact absurd (UInt32.toNat_inj.mp (by rw [e]; rfl)) hv0'
    · exact e
  have hsub : (S.«have» - 1).toNat = S.«have».toNat - 1 := by
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; show 1 ≤ _; omega)]; rfl
  refine SatX.bind (SatX.lift_eq (index_lens li4.hs li4.lensSize (k := (S.«have» - 1).toNat) (by omega)) ?_)
  have hlen : S.lens[(S.«have» - 1).toNat]! ≤ 15 := hlens _ (by omega)
  refine SatX.bind (SatX.modify ?_)
  refine SatX.bind (bits_ok 2 (by decide) ?_)
  refine SatX.bind (SatX.modify ?_)
  refine SatX.bind (dropbits_ok 2 (by decide) ?_)
  have hd5 := drop_toNat (b := l3.bits - h.bits.toUInt32.toUInt8) (n := 2) (by decide) (by rw [hd4]; show 2 ≤ _; omega)
  have hbk := bits_lt (l3.hold >>> h.bits.toUInt32.toUInt64) 2 (by decide)
  have hcp : ((3 : UInt32) + ((l3.hold >>> h.bits.toUInt32.toUInt64) &&& ((1 : UInt32) <<< 2 - 1).toUInt64).toUInt32).toNat =
      3 + ((l3.hold >>> h.bits.toUInt32.toUInt64) &&& ((1 : UInt32) <<< 2 - 1).toUInt64).toNat := by
    have h4 : (2 : Nat) ^ (2 : UInt32).toNat = 4 := rfl
    rw [UInt32.toNat_add, UInt64.toNat_toUInt32, Nat.mod_eq_of_lt (a := UInt64.toNat _) (by omega)]
    exact Nat.mod_eq_of_lt (by show _ < 4294967296; have : (3 : UInt32).toNat = 3 := rfl; omega)
  have h4 : (2 : Nat) ^ (2 : UInt32).toNat = 4 := rfl
  refine repTail_ok (li4.setBits rfl rfl rfl rfl rfl ?_) hm hlt ?_ ?_ ?_ ?_ ?_
  · rw [UInt8.le_iff_toNat_le]; show (l3.bits - h.bits.toUInt32.toUInt8 - (2 : UInt32).toUInt8).toNat ≤ 39
    rw [hd5, hd4]; have := li3.bits; rw [UInt8.le_iff_toNat_le] at this; have : l3.bits.toNat ≤ 39 := this; omega
  · show (S.lens[(S.«have» - 1).toNat]!).toUInt32.toUInt16 ≤ 15
    rw [UInt16.le_iff_toNat_le] at hlen ⊢
    simpa using hlen
  · show 1 ≤ (3 + _ : UInt32).toNat; rw [hcp]; omega
  · show (3 + _ : UInt32).toNat ≤ 138; rw [hcp]; omega
  · show l3.left = l0.left; rw [hl3, hl]
  · show 8 * l3.have_.toNat + (l3.bits - h.bits.toUInt32.toUInt8 - (2 : UInt32).toUInt8).toNat ≤ _
    rw [hd5, hd4]; have : (2 : UInt32).toNat = 2 := rfl; omega

/-! ## Building the tables -/

theorem rank_LEN_ : rank LEN_ = 4 := by decide

/-- A state of `CODELENS` that a failed table build sends to `BAD`. -/
theorem core_CLbad {H : Heap} {i b : Nat} {z : ZStream} {al : InflateAllocs} {S : InflateState}
    (c : Core H (some i) z b (view S) al) {C' : Array Code} {W' : Array UInt16}
    (cs : C'.size = ENOUGH) (ws : W'.size = 288) {o : Nat} (ho : o ≤ ENOUGH) (lb : UInt32) (dc : Ival CodePtr)
    (db : UInt32) (hdc : ∃ o2, dc = .val (.ref (.codes b) o2) ∧ o2 ≤ ENOUGH) :
    Core H (some i) z b (view { S with
      next := .val (.ref (.codes b) o)
      lencode := .val (.ref (.codes b) 0)
      lenbits := lb
      distcode := dc
      distbits := db
      codes := C'
      work := W'
      mode := BAD }) al := by
  obtain ⟨o2, hd, ho2⟩ := hdc
  exact { c with
    mode_lo := by show HEAD ≤ BAD; decide
    mode_hi := by show BAD ≤ SYNC; decide
    codes_size := cs
    work_size := ws
    lencode := ⟨_, rfl, Or.inl ⟨0, rfl, by decide⟩⟩
    distcode := ⟨_, hd, Or.inl ⟨o2, rfl, ho2⟩⟩
    next := ⟨o, rfl, ho⟩
    tables := Or.inl ⟨rfl, o2, hd, ho2⟩
    modes := ModeOK.quiet _ _ (Or.inr (by show LIT < BAD; decide)) }

/-- The mode clauses of `LEN_` with the two built tables. -/
theorem modeOK_LEN_ (b : Nat) (v : InflateInv.MView) (hm : v.mode = LEN_)
    (t1 : TabAt b v.codes v.lencode v.lenbits 28 false) (t2 : TabAt b v.codes v.distcode v.distbits 28 true) :
    ModeOK b v where
  lenlens := fun e => absurd (hm.symm.trans e) (by decide)
  codelens := fun e => absurd (hm.symm.trans e) (by decide)
  decode := fun _ => ⟨t1, t2⟩
  extra := fun e => by rw [hm] at e; rcases e with e | e <;> exact absurd e (by decide)
  offset := fun e => by rw [hm] at e; rcases e with e | e <;> exact absurd e (by decide)

/-- The state entering `LEN_` after `CODELENS`. -/
theorem core_CLlen {H : Heap} {i b : Nat} {z : ZStream} {al : InflateAllocs} {S : InflateState}
    (c : Core H (some i) z b (view S) al) {C' : Array Code} {W' : Array UInt16}
    (cs : C'.size = ENOUGH) (ws : W'.size = 288) {o1 o2 e1 e2 : Nat} (ho1 : o1 ≤ ENOUGH) (ho2 : o2 ≤ ENOUGH)
    (lb db : UInt32) (t1 : CodeTable C' 0 e1 lb.toNat 28 false) (t2 : CodeTable C' o1 e2 db.toNat 28 true) :
    Core H (some i) z b (view { S with
      next := .val (.ref (.codes b) o2)
      lencode := .val (.ref (.codes b) 0)
      lenbits := lb
      distcode := .val (.ref (.codes b) o1)
      distbits := db
      codes := C'
      work := W'
      mode := LEN_ }) al :=
  { c with
    mode_lo := by show HEAD ≤ LEN_; decide
    mode_hi := by show LEN_ ≤ SYNC; decide
    codes_size := cs
    work_size := ws
    lencode := ⟨_, rfl, Or.inl ⟨0, rfl, by decide⟩⟩
    distcode := ⟨_, rfl, Or.inl ⟨o1, rfl, ho1⟩⟩
    next := ⟨o2, rfl, ho2⟩
    tables := Or.inl ⟨rfl, o1, rfl, ho1⟩
    modes := modeOK_LEN_ b _ rfl (Or.inl ⟨0, e1, rfl, t1⟩) (Or.inl ⟨o1, e2, rfl, t2⟩) }

/-- `SET_BAD(msg); return;` after stores into the state that the invariant follows only together with the mode
`BAD`. -/
theorem bad_withS {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (li : LI E l H z S) {m : Nat}
    (S' : InflateState)
    (keep : ∀ al z, Core H (some E.i) z E.b (view S) al → Core H (some E.i) z E.b (view { S' with mode := BAD }) al)
    (hh : S'.head = S.head) (hμ : 32 * (8 * l.have_.toNat + l.bits.toNat + l.left.toNat) < m) (msg : String)
    {i : Nat} (hi : strTable.findIdx? (· == msg) = some i) :
    SatX (withS H E.b S') l (do (MonadLiftT.monadLift (SET_BAD E.c msg) : X Unit); pure ()) (Post E m) := by
  have li1 := li.withS { S' with mode := BAD } keep hh
  have hs : Sat (withS H E.b S') (SET_BAD E.c msg) (fun _ H' => ∃ z', LI E l H' z' { S' with mode := BAD }) := by
    unfold SET_BAD
    refine Sat.bind (Sat.of_eq (wrS_withS li.hs S' _) ?_)
    refine Sat.bind (Sat.of_eq (show strLitRef msg (withS H E.b { S' with mode := BAD }) =
      .ok (.ref (.str i) 0, withS H E.b { S' with mode := BAD }) by simp [strLitRef, hi]) ?_)
    exact Sat.mono (li1.wrZ (fun z => { z with msg := .ref (.str i) 0 }) rfl rfl rfl) (fun _ H2 li2 => ⟨_, li2⟩)
  refine SatX.bind (SatX.lift (Sat.mono hs ?_))
  rintro _ H1 ⟨z1, li2⟩
  refine SatX.pure (post_ok li2 ?_)
  unfold μ; dsimp only; rw [rank_BAD]; omega

/-! ## `CODELENS` -/

theorem mOf_LENS : Inftrees.mOf ZlibNg.Inftrees.LENS = 28 := by decide
theorem mOf_DISTS : Inftrees.mOf ZlibNg.Inftrees.DISTS = 28 := by decide
theorem dOf_LENS : Inftrees.dOf ZlibNg.Inftrees.LENS = false := by decide
theorem dOf_DISTS : Inftrees.dOf ZlibNg.Inftrees.DISTS = true := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem run_CODELENS (E : Env) (eo : EnvOK E) (hL : ModeRun E inflate_LEN_ (·.mode = LEN_)) :
    ModeRun E inflate_CODELENS (·.mode = CODELENS) := by
  intro l H z S li hm m hμ
  have hμ' : 32 * (8 * l.have_.toNat + l.bits.toNat + l.left.toNat) + 16 ≤ m := by
    unfold μ at hμ; rwa [hm, rank_CODELENS] at hμ
  unfold inflate_CODELENS
  refine SatX.bind (SatX.mono (P := fun r l' H' => match r with
      | .ok () => CLd E l z l' H'
      | .error e => Post E m (.error e) l' H') ?_ ?_)
  · refine xwhileBrk_rank (CLs E l z) (CLrank E) _ ?_ ⟨S, li, hm, rfl, Nat.le_refl _⟩
      (by unfold CLrank; rw [li.hs]; dsimp only; unfold fuel; omega)
    rintro l1 H1 ⟨S1, li1, hm1, hl1, hb1⟩
    refine SatX.bind (SatX.lift_eq li1.ldState ?_)
    refine SatX.pure ?_
    obtain ⟨⟨n1, n2⟩, ⟨d1, d2⟩, hlens, htab, hlc⟩ := li1.clFacts hm1
    have hnd : (S1.nlen + S1.ndist).toNat = S1.nlen.toNat + S1.ndist.toNat := by
      rw [UInt32.toNat_add]; exact Nat.mod_eq_of_lt (by show _ < 4294967296; omega)
    by_cases hlt : S1.«have» < S1.nlen + S1.ndist
    · simp only [hlt, decide_true]
      have hlt' : S1.«have».toNat < S1.nlen.toNat + S1.ndist.toNat := by
        rw [← hnd]; exact UInt32.lt_iff_toNat_lt.mp hlt
      have h320 : S1.«have».toNat < 320 := by omega
      refine SatX.mono (P := CLbody E m l z S1.«have».toNat) ?_ ?_
      · refine SatX.bind (SatX.lift_eq (li1.rdS (·.lencode)) ?_)
        dsimp only
        rw [hlc]
        refine SatX.bind (SatX.lift_eq (a := (.ref (.codes E.b) 0 : CodePtr)) rfl ?_)
        refine SatX.bind (SatX.lift_eq (li1.rdS (·.lenbits)) ?_)
        obtain ⟨r0, o0, e0, a0, hp0, hg0, t0⟩ := tab_get li1.hs htab
        rw [hlc] at hp0
        cases hp0
        refine SatX.bind (SatX.mono (decode_ok eo li1 hg0 t0) ?_)
        rintro res l2 H2 ⟨hH2, li2, hl2, hb2, hres⟩
        rw [hH2]
        match res, hres with
        | .error e, he => rw [he]; exact ⟨z, S1, li2⟩
        | .ok (), ⟨hent, hbits⟩ =>
        refine SatX.bind (SatX.get ?_)
        refine SatX.bind (SatX.lift_eq (a := (.ref (.lens E.b) 0 : WPtr)) rfl ?_)
        dsimp only
        have hb25 := hent.bits_le
        have hl2' : l2.left = l.left := by rw [hl2, hl1]
        have hb2' : 8 * l2.have_.toNat + l2.bits.toNat ≤ 8 * l.have_.toNat + l.bits.toNat := by omega
        split
        · rename_i hv16
          have hhb : l2.here.bits.toUInt32.toNat = l2.here.bits.toNat := UInt8.toNat_toUInt32 _
          have hbl : l2.here.bits.toNat ≤ l2.bits.toNat := UInt8.le_iff_toNat_le.mp hbits
          refine SatX.bind (dropbits_ok _ (by rw [UInt32.lt_iff_toNat_lt, hhb]; show _ < 64; omega) ?_)
          have hd3 := drop_toNat (b := l2.bits) (n := l2.here.bits.toUInt32) (by rw [hhb]; omega) (by rw [hhb]; omega)
          rw [hhb] at hd3
          have li3 := li2.drop l2.here.bits.toUInt32 (by rw [hhb]; omega) (by rw [hhb]; omega)
          have hs1 := li3.hs
          have hsz := li3.lensSize
          refine SatX.bind (SatX.lift_eq (li3.rdS (·.«have»)) ?_)
          refine SatX.bind (SatX.lift (Sat.of_eq (wrS_app hs1 _) ?_))
          refine SatX.bind (SatX.lift_eq (addLens_withS hs1 _ (k := S1.«have».toNat) (by show _ ≤ S1.lens.size; omega)) ?_)
          refine SatX.bind (SatX.lift (Sat.of_eq (storeLens_withS hs1 _ (by show _ < S1.lens.size; omega) _) ?_))
          have hv15 : l2.here.val ≤ 15 := by
            rw [UInt16.le_iff_toNat_le]; have := UInt16.lt_iff_toNat_lt.mp hv16; show _ ≤ 15
            have : (16 : UInt16).toNat = 16 := rfl; omega
          refine SatX.pure ⟨⟨_, li3.withS _ (fun _ _ c => core_CLs (S := S1) (S1.«have» + 1) _ c hm1 (by simp)
            (cl_keep hsz h320 hlens _ hv15)) rfl, hm1, hl2', ?_⟩, ?_⟩
          · show 8 * l2.have_.toNat + (l2.bits - l2.here.bits.toUInt32.toUInt8).toNat ≤ _
            rw [hd3]; omega
          · unfold CLrank; rw [istate_withS hs1]
            show 320 - (S1.«have» + 1).toNat < 320 - S1.«have».toNat
            rw [have_succ' h320]; omega
        · split
          · exact rep16_ok eo li2 hm1 hlt' l2.here hb25 hbits hl2' hb2'
          · split
            · exact repK_ok eo li2 hm1 hlt' l2.here hb25 hbits 3 3 (by decide) (by decide) (by decide) hl2' hb2'
            · exact repK_ok eo li2 hm1 hlt' l2.here hb25 hbits 7 11 (by decide) (by decide) (by decide) hl2' hb2'
      · rintro r l2 H2 p
        match r, p with
        | .error e, p => exact p
        | .ok true, p => exact p
        | .ok false, ⟨p1, p2⟩ => exact ⟨p1, by unfold CLrank at p2 ⊢; rw [li1.hs]; exact p2⟩
    · simp only [hlt, decide_false]
      refine ⟨z, S1, li1, hl1, hb1, Or.inl ⟨hm1, ?_⟩⟩
      have := UInt32.not_lt.mp hlt; rw [UInt32.le_iff_toNat_le, hnd] at this; exact this
  rintro r l1 H1 p
  match r, p with
  | .error e, p => exact p
  | .ok (), ⟨z1, S1, li1, hl1, hb1, hd⟩ =>
  dsimp only
  have hμ1 : 32 * (8 * l1.have_.toNat + l1.bits.toNat + l1.left.toNat) + 16 ≤ m := by rw [hl1]; omega
  refine SatX.bind (SatX.lift_eq (li1.rdS (·.mode)) ?_)
  dsimp only
  split
  · rename_i hbad
    have hbad' : S1.mode = BAD := by simpa using hbad
    refine SatX.pure (post_ok li1 ?_)
    unfold μ; rw [hbad', rank_BAD]; omega
  rename_i hnb
  obtain ⟨hm1, hcnt⟩ : S1.mode = CODELENS ∧ S1.nlen.toNat + S1.ndist.toNat ≤ S1.«have».toNat := by
    rcases hd with h | h
    · exact h
    · exact absurd (by rw [h]; rfl) hnb
  obtain ⟨⟨n1, n2⟩, ⟨d1, d2⟩, hlens, -, hlc⟩ := li1.clFacts hm1
  have hs1 := li1.hs
  obtain ⟨al, -, c1⟩ := li1.core
  refine SatX.bind (SatX.lift_eq (a := (.ref (.lens E.b) 0 : WPtr)) rfl ?_)
  refine SatX.bind (SatX.lift_eq (index_lens hs1 c1.lens_size (k := 256) (by decide)) ?_)
  dsimp only
  have hb1' : 32 * (8 * l1.have_.toNat + l1.bits.toNat + l1.left.toNat) < m := by omega
  split
  · exact bad_ok li1 hb1' "invalid code -- missing end-of-block" (strIdx 17 (by decide) (by decide) (by decide))
  have hdc : ∃ o2, S1.distcode = .val (.ref (.codes E.b) o2) ∧ o2 ≤ ENOUGH := by
    rcases c1.tables with ⟨-, o2, h2, h3⟩ | ⟨h1, -⟩
    · exact ⟨o2, h2, h3⟩
    · have h1' : S1.lencode = .val (.ref .lenfix 0) := h1
      rw [hlc] at h1'; cases h1'
  refine SatX.bind (SatX.lift_eq (a := (.ref (.codes E.b) 0 : CodePtr)) rfl ?_)
  refine SatX.bind (SatX.lift (Sat.of_eq (wrS_app hs1 _) ?_))
  refine SatX.bind (SatX.lift (Sat.of_eq (wrS_withS hs1 _ _) ?_))
  refine SatX.bind (SatX.lift (Sat.of_eq (wrS_withS hs1 _ _) ?_))
  refine SatX.bind (SatX.lift_eq (ldState_withS hs1 _) ?_)
  refine SatX.bind (SatX.lift_eq (a := (.ref (.codes E.b) 0 : CodePtr)) rfl ?_)
  refine SatX.bind (SatX.lift_eq (a := (.ref (.work E.b) 0 : WPtr)) rfl ?_)
  let S4 : InflateState := { S1 with
    next := .val (.ref (.codes E.b) 0)
    lencode := .val (.ref (.codes E.b) 0)
    lenbits := MAX_LEN_ROOT_BITS }
  obtain ⟨ret, o', lb, codes', work', e, hcs, hws, -, -, hok, herr⟩ :=
    Inftrees.table_run (withS H1 E.b S4) E.b S4 ZlibNg.Inftrees.LENS 0 S1.nlen 0 10 (istate_withS hs1 _)
      c1.codes_size c1.lens_size c1.work_size (Or.inr (Or.inl ⟨rfl, rfl, n1, n2, rfl, rfl⟩))
      (fun j hj => by
        have := hlens (0 + j) (by omega)
        rw [UInt16.le_iff_toNat_le] at this
        show _ ≤ (if ZlibNg.Inftrees.LENS = ZlibNg.Inftrees.CODES then 7 else 15)
        rw [ite_eq_right_iff.mpr (fun h => absurd h (by decide))]; exact this)
  have e' : (ZlibNg.Inftrees.zng_inflate_table ZlibNg.Inftrees.LENS (.ref (.lens E.b) 0) S1.nlen
      (.ref (.codes E.b) 0) MAX_LEN_ROOT_BITS (.ref (.work E.b) 0) : M _) (withS H1 E.b S4) =
      .ok ((ret, .ref (.codes E.b) o', lb), withS H1 E.b { S4 with codes := codes', work := work' }) := by
    unfold C.run at e; rw [show MAX_LEN_ROOT_BITS = 10 from rfl, e]
    exact congrArg (fun H' => Except.ok (_, H')) (withS_withS H1 E.b S4 _)
  refine SatX.bind (SatX.lift (Sat.of_eq e' ?_))
  refine SatX.bind (SatX.lift (Sat.of_eq (wrS_withS hs1 _ _) ?_))
  have li1r : LI E { l1 with ret := ret } H1 z1 S1 := li1.locals rfl rfl rfl rfl rfl rfl
  refine SatX.bind (SatX.modify (SatX.ite (fun hne => ?_) (fun hne => ?_)))
  · have h0 : ret ≠ 0 := by simpa using hne
    obtain rfl := herr h0
    exact bad_withS li1r { S4 with
        codes := codes'
        work := work'
        next := .val (.ref (.codes E.b) 0)
        lenbits := lb } (fun _ _ c => core_CLbad c hcs hws (o := 0) (by decide) lb S1.distcode S1.distbits hdc) rfl
      hb1' "invalid literal/lengths set" (strIdx 23 (by decide) (by decide) (by decide))
  have h0 : ret = 0 := by simpa using hne
  obtain ⟨ho1, -, -, -, hct1⟩ := hok h0
  have ho1' : o' ≤ 1332 := by
    have e2 : (if ZlibNg.Inftrees.LENS = ZlibNg.Inftrees.DISTS then 592 else 1332) = 1332 := by decide
    omega
  rw [mOf_LENS, dOf_LENS] at hct1
  let S5 : InflateState := { S4 with
    codes := codes'
    work := work'
    next := .val (.ref (.codes E.b) o')
    lenbits := lb }
  refine SatX.bind (SatX.lift_eq (rdS_withS hs1 S5 (·.next)) ?_)
  refine SatX.bind (SatX.lift_eq (a := (.ref (.codes E.b) o' : CodePtr)) rfl ?_)
  refine SatX.bind (SatX.lift (Sat.of_eq (wrS_withS hs1 _ _) ?_))
  refine SatX.bind (SatX.lift (Sat.of_eq (wrS_withS hs1 _ _) ?_))
  refine SatX.bind (SatX.lift_eq (ldState_withS hs1 _) ?_)
  let S6 : InflateState := { S5 with
    distcode := .val (.ref (.codes E.b) o')
    distbits := 9 }
  have hsz6 : S6.lens.size = 320 := c1.lens_size
  refine SatX.bind (SatX.lift_eq (addLens_withS hs1 S6 (k := S1.nlen.toNat) (by rw [hsz6]; omega)) ?_)
  refine SatX.bind (SatX.lift_eq (a := (.ref (.codes E.b) o' : CodePtr)) rfl ?_)
  refine SatX.bind (SatX.lift_eq (a := (.ref (.work E.b) 0 : WPtr)) rfl ?_)
  obtain ⟨ret2, o'', db, codes'', work'', e2, hcs2, hws2, hkeep2, -, hok2, herr2⟩ :=
    Inftrees.table_run (withS H1 E.b S6) E.b S6 ZlibNg.Inftrees.DISTS S1.nlen.toNat S1.ndist o' 9
      (istate_withS hs1 _) hcs c1.lens_size hws
      (Or.inr (Or.inr ⟨rfl, n1, n2, d1, d2, ho1', rfl⟩))
      (fun j hj => by
        have := hlens (S1.nlen.toNat + j) (by omega)
        rw [UInt16.le_iff_toNat_le] at this
        show _ ≤ (if ZlibNg.Inftrees.DISTS = ZlibNg.Inftrees.CODES then 7 else 15)
        rw [ite_eq_right_iff.mpr (fun h => absurd h (by decide))]; exact this)
  have e2' : (ZlibNg.Inftrees.zng_inflate_table ZlibNg.Inftrees.DISTS (.ref (.lens E.b) S1.nlen.toNat) S1.ndist
      (.ref (.codes E.b) o') 9 (.ref (.work E.b) 0) : M _) (withS H1 E.b S6) =
      .ok ((ret2, .ref (.codes E.b) o'', db), withS H1 E.b { S6 with codes := codes'', work := work'' }) := by
    unfold C.run at e2; rw [e2]
    exact congrArg (fun H' => Except.ok (_, H')) (withS_withS H1 E.b S6 _)
  refine SatX.bind (SatX.lift (Sat.of_eq e2' ?_))
  refine SatX.bind (SatX.lift (Sat.of_eq (wrS_withS hs1 _ _) ?_))
  have li1r2 : LI E { { l1 with ret := ret } with ret := ret2 } H1 z1 S1 := li1.locals rfl rfl rfl rfl rfl rfl
  refine SatX.bind (SatX.modify (SatX.ite (fun hne2 => ?_) (fun hne2 => ?_)))
  · have h02 : ret2 ≠ 0 := by simpa using hne2
    have ho := herr2 h02
    exact bad_withS li1r2 { S6 with
        codes := codes''
        work := work''
        next := .val (.ref (.codes E.b) o'')
        distbits := db } (fun _ _ c => core_CLbad c hcs2 hws2 (o := o'') (by rw [ho]; show o' ≤ 1924; omega) lb
      (.val (.ref (.codes E.b) o')) db ⟨o', rfl, by show o' ≤ 1924; omega⟩) rfl
      hb1' "invalid distances set" (strIdx 21 (by decide) (by decide) (by decide))
  have h02 : ret2 = 0 := by simpa using hne2
  obtain ⟨ho2, -, -, -, hct2⟩ := hok2 h02
  rw [mOf_DISTS, dOf_DISTS] at hct2
  have ho2' : o'' ≤ ENOUGH := by
    have e2 : (if ZlibNg.Inftrees.DISTS = ZlibNg.Inftrees.DISTS then 592 else 1332) = 592 := by decide
    show o'' ≤ 1924; omega
  have hct1' : CodeTable codes'' 0 o' lb.toNat 28 false :=
    hct1.congr (by rw [hcs2]; show o' ≤ 1924; omega) (fun j _ h2 => hkeep2 j h2)
  refine SatX.bind (SatX.lift (Sat.of_eq (wrS_withS hs1 _ _) ?_))
  have liF := li1r2.withS { S6 with
      codes := codes''
      work := work''
      next := .val (.ref (.codes E.b) o'')
      distbits := db
      mode := LEN_ }
    (fun _ _ c => core_CLlen c hcs2 hws2 (by show o' ≤ 1924; omega) ho2' lb db hct1' hct2) rfl
  dsimp (config := { zeta := false }) only
  split
  · exact SatX.bind (SatX.throw ⟨_, _, liF⟩)
  · refine hL _ _ _ _ liF rfl m ?_
    unfold μ; dsimp only; rw [rank_LEN_]; omega

end ZlibNgF.Proof.InflateLoop
