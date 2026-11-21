import ZlibNgF.Proof.«deflate_stored.c.frame»

/-!
# The direct-copy loop of `deflate_stored` (`ZlibNgF`)

One trip of the `do` loop (`stored_trip`, `deflate_stored.c:37-97`) from `SF` with no pending bytes: the header of an
empty stored block (`zng_tr_stored_block(s, NULL, 0, last)`, its `LEN` / `NLEN` rewritten, all flushed since the
header fits in `avail_out`), the window bytes `[block_start, block_start + left)` copied to `next_out`, and `read_buf`
of the rest straight into `next_out`. `SF` and no pending bytes after; a trip that does not break lowers `avail_out`.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.StoredTrip
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateFacts ZlibNgF.Proof.DeflateFlush ZlibNgF.Proof.Strategy
open ZlibNgF.Proof.StoredIO ZlibNgF.Proof.StoredF
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNgF.Proof.InflateInv (upd_upd)
open ZlibNgF.Proof.InflateDict (copyFold copyFold_size copyFold_get)
open ZlibNgF.Proof.DeflateAlloc (pure_bind_M ite_t ite_f)
open ZlibNgF.Proof.WinInv (InTail)
open ZlibNg.DeflateStored
open ZlibNgF.Proof.DeflatePsi (psiS G span owed)

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8}

theorem strmOf_SH (hs : st.strm = .val (some i)) :
    strmOf (some b) (SH H i z b st d) = .ok (some i, SH H i z b st d) := by
  simp [strmOf, ldDState_SH, bind_app, hs, Ival.get]

theorem i32_lt8 (v : Int32) (h0 : 0 ≤ v.toInt) (h8 : v.toInt < 8) :
    v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 ∨ v = 6 ∨ v = 7 := by
  have : v.toInt = 0 ∨ v.toInt = 1 ∨ v.toInt = 2 ∨ v.toInt = 3 ∨ v.toInt = 4 ∨ v.toInt = 5 ∨ v.toInt = 6 ∨
    v.toInt = 7 := by omega
  rcases this with e | e | e | e | e | e | e | e
  · exact .inl (Int32.toInt_inj.mp (by rw [e]; rfl))
  · exact .inr (.inl (Int32.toInt_inj.mp (by rw [e]; rfl)))
  · exact .inr (.inr (.inl (Int32.toInt_inj.mp (by rw [e]; rfl))))
  · exact .inr (.inr (.inr (.inl (Int32.toInt_inj.mp (by rw [e]; rfl)))))
  · exact .inr (.inr (.inr (.inr (.inl (Int32.toInt_inj.mp (by rw [e]; rfl))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inl (Int32.toInt_inj.mp (by rw [e]; rfl)))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl (Int32.toInt_inj.mp (by rw [e]; rfl))))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (Int32.toInt_inj.mp (by rw [e]; rfl))))))))

/-- `(s->bi_valid + 42) >> 3` with fewer than 8 bits waiting. -/
theorem headerBytes_SH (h0 : 0 ≤ st.bi_valid.toInt) (h8 : st.bi_valid.toInt < 8) :
    ∃ v : UInt32, headerBytes (some b) (SH H i z b st d) = .ok (v, SH H i z b st d) ∧
      v.toNat = (st.bi_valid.toInt.toNat + 42) / 8 := by
  unfold headerBytes
  simp only [bind_app, rdD_SH]
  rcases i32_lt8 _ h0 h8 with e | e | e | e | e | e | e | e <;> rw [e] <;>
    exact ⟨_, rfl, by decide⟩

/-- `left = (int)s->strstart - s->block_start` with `0 <= block_start <= strstart <= 65536`. -/
theorem leftOf_SH (h0 : 0 ≤ st.block_start.toInt) (h1 : st.block_start.toInt ≤ st.strstart.toNat)
    (h2 : st.strstart.toNat ≤ 65536) :
    ∃ v : UInt32, leftOf (some b) (SH H i z b st d) = .ok (v, SH H i z b st d) ∧
      (v.toNat : Int) = st.strstart.toNat - st.block_start.toInt := by
  have e1 : st.strstart.toInt32.toInt = st.strstart.toNat := DeflateAlloc.u32_toInt32_toInt _ (by omega)
  unfold leftOf
  simp only [bind_app, ldDState_SH, chkI32, e1]
  rw [ite_t (by omega)]
  refine ⟨_, rfl, ?_⟩
  have hx : (Int32.ofInt (↑st.strstart.toNat - st.block_start.toInt)).toInt = ↑st.strstart.toNat - st.block_start.toInt :=
    Int32.toInt_ofInt_of_le (by omega) (by omega)
  have hnn : 0 ≤ Int32.ofInt (↑st.strstart.toNat - st.block_start.toInt) :=
    Int32.le_iff_toInt_le.mpr (by rw [hx]; show (0 : Int) ≤ _; omega)
  rw [Int32.toNat_toUInt32_of_le hnn]
  show ((Int32.ofInt (↑st.strstart.toNat - st.block_start.toInt)).toInt.toNat : Int) = _
  rw [hx]; omega

end

/-- The `avail_out` of stream `i`. -/
def avOut (H : Heap) (i : Nat) : Nat :=
  match H.streams i with
  | some z => z.avail_out.toNat
  | none => 0

theorem SH_setB_SH {H : Heap} {i : Nat} {z z' : ZStream} {b ob : Nat} {st st' : DeflateState}
    {d d' X Y : Array UInt8} (hob : ob ≠ b) :
    SH (setB (SH (setB H ob X) i z b st d) ob Y) i z' b st' d' = SH (setB H ob Y) i z' b st' d' := by
  simp only [SH, setB]
  rw [upd_comm _ (Ne.symm hob) (some d) (some Y)]
  simp only [upd_upd]

theorem OH_eq {H : Heap} {i : Nat} {z : ZStream} {b ob : Nat} {st : DeflateState} {d Y : Array UInt8}
    (hob : ob ≠ b) : OH H i z b st d ob Y = SH (setB H ob Y) i z b st d := by
  simp only [OH, SH, setB]
  rw [upd_comm _ (Ne.symm hob)]

section parts
open ZlibNg.DeflateP ZlibNg.Trees

/-- The tail of a trip (`deflate_stored.c:92-97`): `read_buf` straight into `next_out`. -/
def rd_part (st : StatePtr) (last : Int32) (len : UInt32) : M (Int32 × Bool) := do
  if len != 0 then
    let strm ← strmOf st
    let _ ← read_buf strm (← rdZ (← strmOf st) (·.next_out)) len
    let strm ← strmOf st
    let no ← (← rdZ strm (·.next_out)).add len.toNat
    wrZ strm fun z => { z with next_out := no }
    wrZ (← strmOf st) fun z => { z with avail_out := z.avail_out - len }
    wrZ (← strmOf st) fun z => { z with total_out := z.total_out + len.toUInt64 }
  return (last, false)

/-- The window part of a trip (`deflate_stored.c:79-87`), followed by `k len`. -/
def win_part {α : Type} (st : StatePtr) (window : BPtr) (left len : UInt32) (k : UInt32 → M α) : M α := do
  let len ← if left != 0 then do
      let left := MIN32 left len
      let strm ← strmOf st
      let bs ← rdD st (·.block_start)
      Ptr.memcpy (← rdZ strm (·.next_out)) (← window.add bs.toInt) left.toNat
      let strm ← strmOf st
      let no ← (← rdZ strm (·.next_out)).add left.toNat
      wrZ strm fun z => { z with next_out := no }
      wrZ (← strmOf st) fun z => { z with avail_out := z.avail_out - left }
      wrZ (← strmOf st) fun z => { z with total_out := z.total_out + left.toUInt64 }
      let bs ← chkI32 ((← rdD st (·.block_start)).toInt + left.toInt32.toInt)
      wrD st fun s => { s with block_start := bs }
      pure (len - left)
    else pure len
  k len

/-- The header part of a trip (`deflate_stored.c:64-72`), followed by `k`. -/
def hdr_part {α : Type} (st : StatePtr) (len : UInt32) (last : Int32) (k : M α) : M α := do
  zng_tr_stored_block st .null 0 last
  wrD st fun s => { s with pending := s.pending - 4 }
  put_short st len.toUInt16
  put_short st (~~~len).toUInt16
  flush_pending (← strmOf st)
  k

end parts

/-- The clauses of `DCore` after a change of the pending bytes and the bit buffer that keeps `pending` and
`pending_out` and leaves fewer than 8 bits. -/
theorem dcore_flush {H : Heap} {s : StreamPtr} {z : ZStream} {b : Nat} {st st' : DeflateState}
    {al : DeflateAllocs} (c : DCore H s z b (dview st) al)
    (he : st' = { st with
      pending := st'.pending
      pending_out := st'.pending_out
      bi_buf := st'.bi_buf
      bi_valid := st'.bi_valid
      bi_used := st'.bi_used })
    (hp : st'.pending = st.pending) (hq : st'.pending_out = st.pending_out) (h0 : 0 ≤ st'.bi_valid)
    (h8 : st'.bi_valid < 8) : DCore H s z b (dview st') al := by
  have hz : st'.bi_valid.toInt.toNat / 8 = 0 := by
    have a := Int32.le_iff_toInt_le.mp h0
    have a' := Int32.lt_iff_toInt_lt.mp h8
    rw [show (0 : Int32).toInt = 0 from rfl] at a
    rw [show (8 : Int32).toInt = 8 from rfl] at a'
    omega
  have h64 : st'.bi_valid < 64 := Int32.lt_iff_toInt_lt.mpr (by
    have a' := Int32.lt_iff_toInt_lt.mp h8
    rw [show (8 : Int32).toInt = 8 from rfl] at a'
    rw [show (64 : Int32).toInt = 64 from rfl]
    omega)
  have hz' : (dview st).bi_valid.toInt.toNat / 8 = st.bi_valid.toInt.toNat / 8 := rfl
  rw [he, hp, hq]
  exact { c with
    bits := ⟨h0, h64⟩
    lay := by
      obtain ⟨d, wo, po, ho, pbo, hd, hwo, hp', hh, hpb, h1, h2, h3, h4, hsb, poo, hpo, hle, hroom⟩ := c.lay
      refine ⟨d, wo, po, ho, pbo, hd, hwo, hp', hh, hpb, h1, h2, h3, h4, hsb, poo, hpo, hle, ?_⟩
      simp only [dview] at hroom ⊢
      omega
    psym := fun hn => by
      obtain ⟨p1, p2, a1, a2, q⟩ := c.psym hn
      refine ⟨p1, p2, a1, a2, ?_⟩
      simp only [dview] at q ⊢
      omega }

theorem min32_toNat (a b : UInt32) : (MIN32 a b).toNat = min a.toNat b.toNat := by
  unfold MIN32; split
  · rename_i h; have := UInt32.lt_iff_toNat_lt.mp h; omega
  · rename_i h; have := UInt32.not_lt.mp h; have := UInt32.le_iff_toNat_le.mp this; omega

/-- The window part of a trip: `min(left, len)` window bytes from `block_start` copied to `next_out`. -/
theorem win_ok {e e' : Nat} {h H : Heap} {i b wo : Nat} (F : SF e h i b H)
    (hp0 : ∀ st, H.dstate b = some st → st.pending = 0)
    (hw0 : ∀ st0, h.dstate b = some st0 → st0.window = .val (.ref (.heap b) wo)) (left len : UInt32)
    (hl : ∀ st, H.dstate b = some st → (left.toNat : Int) ≤ st.strstart.toNat - st.block_start.toInt)
    (ho : ∀ z, H.streams i = some z → min left.toNat len.toNat ≤ z.avail_out.toNat)
    (he : e ≤ 5 * min left.toNat len.toNat + e')
    {α : Type} (k : UInt32 → M α) (Q : α → Heap → Prop)
    (hk : ∀ len2 H', SF e' h i b H' → (∀ st, H'.dstate b = some st → st.pending = 0) →
      len2.toNat = len.toNat - min left.toNat len.toNat → avOut H' i + min left.toNat len.toNat = avOut H i →
      avIn H' i = avIn H i → Sat H' (k len2) Q) :
    Sat H (win_part (some b) (.ref (.heap b) wo) left len k) Q := by
  unfold win_part
  by_cases h0 : left = 0
  · subst h0
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, pure_bind_M]
    exact hk len H (F.mono (by simpa using he)) hp0 (by simp) (by simp) rfl
  have h0' : (left != 0) = true := by simpa using h0
  simp only [h0', ↓reduceIte]
  obtain ⟨z, st, d, ob, oo, X, pbo, S⟩ := F.facts hw0
  have e0 : SH (setB H ob X) i z b st d = H := by
    rw [setB_self S.hX]; exact ZlibNgF.Proof.DeflateReset.SH_self S.hz S.hsts S.hd
  have hav : avOut H i = z.avail_out.toNat := by simp [avOut, S.hz]
  have hai : avIn H i = z.avail_in.toNat := by simp [avIn, S.hz]
  have hp := hp0 st S.hst
  have hl' := hl st S.hst
  have ho' := ho z S.hz
  have hlf := min32_toNat left len
  generalize MIN32 left len = lf at hlf ⊢
  have hoo := S.hoo
  obtain ⟨hb0, hbs, hss⟩ := S.bs
  obtain ⟨hw1, hw2⟩ := S.lay
  have hws := S.ws.1
  rw [← e0]
  refine Sat.bind (Sat.of_eq (strmOf_SH S.strm) ?_)
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  refine Sat.bind (Sat.of_eq (rdZ_SH _) ?_)
  rw [S.hno, show st.block_start.toInt = ((st.block_start.toInt.toNat : Nat) : Int) by omega]
  refine Sat.bind (Sat.of_eq (add_SH (st.block_start.toInt.toNat) (by omega)) ?_)
  refine Sat.bind (Sat.of_eq (memcpy_out S.hob (by omega) (by omega)) ?_)
  have hX1 := copyFold_size d oo (wo + st.block_start.toInt.toNat) (List.range' 0 lf.toNat) X
  refine Sat.bind (Sat.of_eq (strmOf_SH S.strm) ?_)
  refine Sat.bind (Sat.of_eq (rdZ_SH _) ?_)
  rw [S.hno]
  refine Sat.bind (Sat.of_eq (add_out_SH S.hob (by omega)) ?_)
  refine Sat.bind (Sat.of_eq (wrZ_SH _) ?_)
  refine Sat.bind (Sat.of_eq (strmOf_SH S.strm) ?_)
  refine Sat.bind (Sat.of_eq (wrZ_SH _) ?_)
  refine Sat.bind (Sat.of_eq (strmOf_SH S.strm) ?_)
  refine Sat.bind (Sat.of_eq (wrZ_SH _) ?_)
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  have el : lf.toInt32.toInt = lf.toNat := DeflateAlloc.u32_toInt32_toInt _ (by omega)
  simp only [chkI32, el]
  rw [ite_t (by omega), pure_bind_M]
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
  rw [pure_bind_M]
  have hnb : (Int32.ofInt (st.block_start.toInt + ↑lf.toNat)).toInt = st.block_start.toInt + lf.toNat :=
    Int32.toInt_ofInt_of_le (by omega) (by omega)
  have hsub : (z.avail_out - lf).toNat = z.avail_out.toNat - lf.toNat :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega))
  have hsl : (len - lf).toNat = len.toNat - lf.toNat :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega))
  refine hk _ _ ?_ (fun st2 h2 => ?_) (by rw [hsl]; omega) (by rw [hav]; simp [avOut]; omega)
    (by rw [hai]; simp [avIn])
  · refine sf_next F S.hz S.hst S.hno S.hX (L := lf.toNat) hX1 (fun j hj => copyFold_get _ _ _ _ _ _
      (fun x hx => by simp only [List.mem_range'_1] at hx; omega)) (by omega) rfl (Or.inl ⟨rfl, rfl⟩)
      (Nat.le_refl _) rfl (by simp; omega) (fun al _ c => dcore_mv
        ({ c with
          bstart := by simp only [dview]; omega
          bs_lo := by simp only [dview]; omega } : DCore H (some i) z b (dview { st with
            block_start := Int32.ofInt (st.block_start.toInt + ↑lf.toNat) }) al)
        S.hd (SH_bytes _ _ _ _ _ _) rfl S.sym rfl rfl) ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => ⟨UInt32.le_refl _, rfl⟩⟩, rfl, rfl, rfl, rfl⟩
      ⟨Int32.le_iff_toInt_le.mpr
        (by show (0 : Int) ≤ (Int32.ofInt (st.block_start.toInt + ↑lf.toNat)).toInt; omega), S.sym, S.b8⟩
      fun f => ?_
    have q := psiS_parts (f := f) (st := st) (st' := { st with
      block_start := Int32.ofInt (st.block_start.toInt + ↑lf.toNat) }) rfl rfl rfl rfl rfl rfl
    have s1 := span_eq (st := st) hbs
    have s2 := span_eq (st := { st with block_start := Int32.ofInt (st.block_start.toInt + ↑lf.toNat) })
      (by simp only []; omega)
    simp only [] at s2 q
    have ho : owed { st with block_start := Int32.ofInt (st.block_start.toInt + ↑lf.toNat) } = owed st := rfl
    rw [Nat.sub_self, Nat.mul_zero]
    omega
  · rw [SH_dstate] at h2; cases h2; exact hp

/-- `read_buf` of `len` input bytes straight into `next_out` (`deflate_stored.c:92-97`). -/
theorem rd_ok {e e' : Nat} {h H : Heap} {i b wo : Nat} (F : SF e h i b H)
    (hp0 : ∀ st, H.dstate b = some st → st.pending = 0)
    (hw0 : ∀ st0, h.dstate b = some st0 → st0.window = .val (.ref (.heap b) wo)) (last : Int32) (len : UInt32)
    (hla : ∀ z, H.streams i = some z → len.toNat ≤ z.avail_in.toNat ∧ len.toNat ≤ z.avail_out.toNat)
    (he : e ≤ 5 * len.toNat + e') :
    Sat H (rd_part (some b) last len) (fun v H' => v = (last, false) ∧ SF e' h i b H' ∧
      (∀ st, H'.dstate b = some st → st.pending = 0) ∧ avOut H' i + len.toNat = avOut H i ∧
      avIn H' i + len.toNat = avIn H i) := by
  obtain ⟨z, st, d, ob, oo, X, pbo, S⟩ := F.facts hw0
  have e0 : SH (setB H ob X) i z b st d = H := by rw [setB_self S.hX]; exact ZlibNgF.Proof.DeflateReset.SH_self S.hz S.hsts S.hd
  have hav : avOut H i = z.avail_out.toNat := by simp [avOut, S.hz]
  have hai : avIn H i = z.avail_in.toNat := by simp [avIn, S.hz]
  rw [hav, hai]
  obtain ⟨l1, l2⟩ := hla z S.hz
  have hp := hp0 st S.hst
  rw [← e0]
  unfold rd_part
  by_cases h0 : len = 0
  · subst h0
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    exact Sat.pure ⟨rfl, by rw [e0]; exact F.mono (by simpa using he), by rw [e0]; exact hp0, by simp [avOut],
      by simp [avIn]⟩
  have h0' : (len != 0) = true := by simpa using h0
  have hl0 : len.toNat ≠ 0 := fun e => h0 (UInt32.toNat_inj.mp (by rw [e]; rfl))
  simp only [h0', ↓reduceIte]
  have hni0 : z.next_in ≠ .null := S.inset (fun e => by rw [e] at l1; simp at l1; omega)
  obtain ⟨r, os, src, hni, hg, hin⟩ := S.inr.resolve_left hni0
  have hr : r ≠ .heap b := fun e => S.inb os (by rw [hni, e])
  have hdj := S.dj
  rw [S.hno, hni] at hdj
  refine Sat.bind (Sat.of_eq (strmOf_SH S.strm) ?_)
  refine Sat.bind (Sat.of_eq (strmOf_SH S.strm) ?_)
  refine Sat.bind (Sat.of_eq (rdZ_SH _) ?_)
  simp only [S.hno]
  refine Sat.bind (Sat.mono (read_buf_out S.hob S.hb hni hr (by rw [setB_self S.hX]; exact hg) hin
    (fun _ => F.crc.1) len (by have := S.hoo; omega) (fun e => by
      subst e
      rcases hdj with hne | hh | hh
      · exact absurd rfl hne
      · left; omega
      · right; exact hh)) ?_)
  rintro n H1 ⟨hn, X', a, rfl, hX's, hX'o⟩
  have hnl : n.toNat = len.toNat := by omega
  refine Sat.bind (Sat.of_eq (strmOf_SH S.strm) ?_)
  refine Sat.bind (Sat.of_eq (rdZ_SH _) ?_)
  have hoo := S.hoo
  have hnoR : (ZlibNgF.Proof.ReadBuf.RBZ z n r os a).next_out = .ref (.heap ob) oo := by
    simp [ZlibNgF.Proof.ReadBuf.RBZ, S.hno]
  rw [hnoR]
  refine Sat.bind (Sat.of_eq (add_out_SH S.hob (oo := oo) (k := len.toNat) (by omega)) ?_)
  refine Sat.bind (Sat.of_eq (wrZ_SH _) ?_)
  refine Sat.bind (Sat.of_eq (strmOf_SH S.strm) ?_)
  refine Sat.bind (Sat.of_eq (wrZ_SH _) ?_)
  refine Sat.bind (Sat.of_eq (strmOf_SH S.strm) ?_)
  refine Sat.bind (Sat.of_eq (wrZ_SH _) ?_)
  have hsub : (z.avail_out - len).toNat = z.avail_out.toNat - len.toNat :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr l2)
  have hsubn : (z.avail_in - n).toNat = z.avail_in.toNat - len.toNat := by
    rw [UInt32.toNat_sub_of_le z.avail_in n (UInt32.le_iff_toNat_le.mpr (by omega)), hnl]
  refine Sat.pure ⟨rfl, ?_, fun st2 h2 => ?_, ?_, ?_⟩
  · refine sf_next F S.hz S.hst S.hno S.hX (L := len.toNat) hX's (fun j hj => hX'o j hj) l2 rfl
      (Or.inr ⟨r, os, hni, ?_⟩) (by simp [ZlibNgF.Proof.ReadBuf.RBZ]; omega) rfl
      (by simp [ZlibNgF.Proof.ReadBuf.RBZ]; omega)
      (fun al _ c => dcore_mv c S.hd (SH_bytes _ _ _ _ _ _) rfl S.sym rfl rfl) (SK.refl _)
      ⟨(F.st st S.hst).1, S.sym, S.b8⟩ fun f => ?_
    · simp only [ZlibNgF.Proof.ReadBuf.RBZ]
      rw [hsubn, hnl]; congr 2; omega
    · simp only [ZlibNgF.Proof.ReadBuf.RBZ]
      rw [hsubn, show z.avail_in.toNat - (z.avail_in.toNat - len.toNat) = len.toNat by omega]
      have := G_pay len.toNat
      omega
  · rw [SH_dstate] at h2; cases h2; exact hp
  · simp [avOut, ZlibNgF.Proof.ReadBuf.RBZ]; omega
  · simp [avIn, ZlibNgF.Proof.ReadBuf.RBZ]; omega

theorem sat_gen {α : Type} {H0 : Heap} {i : Nat} {z : ZStream} {b : Nat} {d : Array UInt8} {st : DeflateState}
    {m : M α} {Q : α → Heap → Prop} (P : DeflateState → Prop) (hP : P st)
    (h : ∀ st', P st' → Sat (SH H0 i z b st' d) m Q) : Sat (SH H0 i z b st d) m Q := h st hP

theorem copyFold_out (src X : Array UInt8) (oo os n : Nat) :
    ∀ j, (j < oo ∨ oo + n ≤ j) → (copyFold src oo os (List.range' 0 n) X)[j]! = X[j]! := fun _ hj =>
  copyFold_get _ _ _ _ _ _ (fun x hx => by simp only [List.mem_range'_1] at hx; omega)

/-- The header part of a trip: the empty stored block, its `LEN` / `NLEN` rewritten, all flushed (the header fits in
`avail_out`). -/
theorem hdr_ok {e : Nat} {h H : Heap} {i b wo : Nat} (F : SF e h i b H)
    (hp0 : ∀ st, H.dstate b = some st → st.pending = 0)
    (hw0 : ∀ st0, h.dstate b = some st0 → st0.window = .val (.ref (.heap b) wo)) (len : UInt32) (last : Int32)
    (hroom : ∀ z st, H.streams i = some z → H.dstate b = some st →
      (st.bi_valid.toInt.toNat + 42) / 8 ≤ z.avail_out.toNat)
    {α : Type} (k : M α) (Q : α → Heap → Prop)
    (hk : ∀ H', SF (e + 5) h i b H' → (∀ st, H'.dstate b = some st → st.pending = 0) →
      (∀ st, H.dstate b = some st → ∃ p, 4 ≤ p ∧ p ≤ (st.bi_valid.toInt.toNat + 42) / 8 ∧
        avOut H' i + p = avOut H i) → avIn H' i = avIn H i →
      (∀ st st', H.dstate b = some st → H'.dstate b = some st' → st'.strstart = st.strstart ∧
        st'.block_start = st.block_start) → Sat H' k Q) :
    Sat H (hdr_part (some b) len last k) Q := by
  obtain ⟨z, st, d, ob, oo, X, pbo, S⟩ := F.facts hw0
  have e0 : SH (setB H ob X) i z b st d = H := by
    rw [setB_self S.hX]; exact ZlibNgF.Proof.DeflateReset.SH_self S.hz S.hsts S.hd
  have hav : avOut H i = z.avail_out.toNat := by simp [avOut, S.hz]
  have hai : avIn H i = z.avail_in.toNat := by simp [avIn, S.hz]
  have hp := hp0 st S.hst
  have hr := hroom z st S.hz S.hst
  have hoo := S.hoo
  obtain ⟨hv0, hv8⟩ := S.bits
  obtain ⟨hw1, hw2⟩ := S.lay
  obtain ⟨l1, l2, -⟩ := S.lb
  have hp' : st.pending.toNat = 0 := by rw [hp]; rfl
  rw [← e0]
  unfold hdr_part
  refine Sat.bind (Sat.mono (ZlibNgF.Proof.TreesEmitP.stored_block_X_SH S.hpb hv0 (by omega) .null 0
    (.inl ⟨rfl, rfl⟩) (by simp; omega) (by simp; omega) last) ?_)
  rintro _ H1 ⟨np2, pend, bu, d1, rfl, hpe, hle, hb2, w1⟩
  simp only [UInt32.toNat_zero, Nat.add_zero] at hpe
  have hd1 : d1.size = d.size := w1.1
  have hpA : pend.toNat ≤ z.avail_out.toNat ∧ pend.toNat ≤ (st.bi_valid.toInt.toNat + 42) / 8 ∧ 4 ≤ pend.toNat ∧
      pend.toNat ≤ 6 := by omega
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
  have h4 : (pend - 4).toNat = np2.toNat := by
    rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
  refine Sat.bind (Sat.mono (ZlibNgF.Proof.DeflateBits.put_short_SH (pbo := pbo) ?_ _ ?_) ?_)
  · exact S.hpb
  · show pbo + (pend - 4).toNat + 2 ≤ d1.size; rw [h4]; omega
  rintro _ H2 ⟨d2, rfl, w2⟩
  have hd2 : d2.size = d.size := w2.1.trans hd1
  have h6 : (pend - 4 + 2).toNat = np2.toNat + 2 := by rw [UInt32.toNat_add, h4]; simp; omega
  refine Sat.bind (Sat.mono (ZlibNgF.Proof.DeflateBits.put_short_SH (pbo := pbo) ?_ _ ?_) ?_)
  · exact S.hpb
  · show pbo + (pend - 4 + 2).toNat + 2 ≤ d2.size; rw [h6]; omega
  rintro _ H3 ⟨d3, rfl, w3⟩
  have hd3 : d3.size = d.size := w3.1.trans hd2
  have h8 : (pend - 4 + 2 + 2).toNat = pend.toNat := by rw [UInt32.toNat_add, h6]; simp; omega
  refine sat_gen (fun st3 => st3 = { st with
      pending := st3.pending
      bi_used := st3.bi_used
      bi_buf := st3.bi_buf
      bi_valid := st3.bi_valid } ∧ st3.pending.toNat = pend.toNat ∧ st3.bi_valid = 0) ⟨rfl, h8, rfl⟩ ?_
  clear w1 w2 w3 hb2 hle h4 h6 h8
  rintro st3 ⟨he3, hp3, hbv3⟩
  refine Sat.bind (Sat.of_eq (strmOf_SH (by rw [he3]; exact S.strm)) ?_)
  have hpo : st.pending_out = .val (.ref (.heap b) pbo) := (S.pout hp).trans S.hpb
  refine Sat.bind (Sat.mono (flushO_SH (lb := st.lit_bufsize.toNat) (pbo := pbo) (poo := pbo) (ad := X) (oo := oo) (ob := ob) S.hb S.hob (by simp [setB]) S.hno hoo ?_ ?_
    (Nat.le_refl _) ?_ ?_ l2 ?_ ?_ ?_) ?_)
  · rw [he3]; exact S.hpb
  · rw [he3]; exact hpo
  · rw [hp3, hbv3]; simp; omega
  · rw [hd3]; omega
  · rw [hbv3]; decide
  · rw [hbv3]; decide
  · intro _; rw [he3]; exact hpo.trans S.hpb.symm
  rintro _ H4 ⟨⟨np, bb, bv, d4, L, z', st', rfl, w4, hbv0, hbv8, hnp, hL, hst', hpn, hpz, -, hz', hno', hav'⟩, hO⟩
  have hnp' : np.toNat = pend.toNat := by
    rw [hnp, hp3, hbv3]; rfl
  clear hnp
  have hLp : L = pend.toNat := by rw [hL, hnp']; exact Nat.min_eq_left hpA.1
  subst hLp
  have hO' := hO z' st' (by simp [OH]) (OH_dstate S.hob)
  have ho3 : owed st3 = pend.toNat := by unfold owed; rw [hp3, hbv3]; simp
  rw [OH_eq S.hob, setB_setB]
  obtain ⟨no, ao, tt, rfl⟩ : ∃ no ao tt, z' = { z with next_out := no, avail_out := ao, total_out := tt } :=
    ⟨_, _, _, hz'⟩
  simp only [] at hno' hav'
  have hP : st'.pending = st.pending := by
    rw [hp]; exact UInt32.toNat_inj.mp (by rw [hpn]; simp; omega)
  have hQ : st'.pending_out = st.pending_out := by rw [hpz (hP.trans hp), hpo, he3]; exact S.hpb
  have he : st' = { st with
      pending := st'.pending
      pending_out := st'.pending_out
      bi_buf := st'.bi_buf
      bi_valid := st'.bi_valid
      bi_used := st'.bi_used } := by rw [hst']; rw [he3]
  have hbv : st'.bi_valid = bv := by rw [hst']
  clear hst' hpz hpn hL hnp'
  have hX4 := copyFold_size d4 oo pbo (List.range' 0 pend.toNat) X
  refine hk _ ?_ (fun st2 h2 => ?_) (fun st2 h2 => ?_) (by rw [hai]; simp [avIn])
    (fun st2 st3 h2 h3 => ?_)
  · have hXo := copyFold_out d4 X oo pbo pend.toNat
    have hsy : (dview st').sym_next = 0 := by show st'.sym_next = 0; rw [he]; exact S.sym
    have hb0' : 0 ≤ st'.bi_valid := Int32.le_iff_toInt_le.mpr (by rw [hbv, show (0 : Int32).toInt = 0 from rfl]; exact hbv0)
    have hb8' : st'.bi_valid < 8 := Int32.lt_iff_toInt_lt.mpr (by rw [hbv, show (8 : Int32).toInt = 8 from rfl]; exact hbv8)
    have hd4 : d4.size = d.size := by rw [w4.1, hd3]
    have hAo : pend.toNat ≤ z.avail_out.toNat := hpA.1
    refine sf_next F S.hz S.hst S.hno S.hX (L := pend.toNat) hX4 hXo hAo rfl (Or.inl ⟨rfl, rfl⟩)
      (Nat.le_refl _) hno' hav' (fun al _ c => dcore_mv (dcore_flush c he hP hQ hb0' hb8')
        S.hd (SH_bytes _ _ _ _ _ _) hd4 hsy rfl rfl) ?_ ?_ fun f => ?_
    · rw [he]; exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => ⟨UInt32.le_refl _, rfl⟩⟩, rfl, rfl, rfl, rfl⟩
    · exact ⟨by rw [he]; exact (F.st st S.hst).1, by rw [he]; exact S.sym, hb8'⟩
    · have q := psiS_parts (f := f) (st := st) (st' := st') (by rw [he]) (by rw [he]) (by rw [he]) (by rw [he])
        (by rw [he]) (by rw [he])
      have hsp : span st' = span st := by rw [he]; rfl
      have h0 := owed_p0 hp
      simp only [] at hav' hO'
      rw [Nat.sub_self, Nat.mul_zero]
      omega
  · rw [SH_dstate] at h2; cases h2; rw [hP, hp]
  · rw [S.hst] at h2; cases h2
    refine ⟨pend.toNat, by omega, by omega, ?_⟩
    rw [hav]; simp [avOut]; omega
  · rw [S.hst] at h2; cases h2
    rw [SH_dstate] at h3; cases h3
    rw [he]; exact ⟨rfl, rfl⟩

theorem len1_le (left ai : UInt32) :
    (if ZlibNg.DeflateP.MAX_STORED.toUInt64 > left.toUInt64 + ai.toUInt64 then left + ai
      else ZlibNg.DeflateP.MAX_STORED).toNat ≤ left.toNat + ai.toNat := by
  split
  · rename_i h
    have h' := UInt64.lt_iff_toNat_lt.mp h
    simp only [UInt64.toNat_add, UInt32.toNat_toUInt64] at h'
    have : ZlibNg.DeflateP.MAX_STORED.toUInt64.toNat = 65535 := rfl
    rw [UInt32.toNat_add]; omega
  · rename_i h
    have h' := UInt64.not_lt.mp h
    have h'' := UInt64.le_iff_toNat_le.mp h'
    simp only [UInt64.toNat_add, UInt32.toNat_toUInt64] at h''
    have : ZlibNg.DeflateP.MAX_STORED.toUInt64.toNat = 65535 := rfl
    have : ZlibNg.DeflateP.MAX_STORED.toNat = 65535 := rfl
    omega

theorem len1_eq (left ai : UInt32) :
    (if ZlibNg.DeflateP.MAX_STORED.toUInt64 > left.toUInt64 + ai.toUInt64 then left + ai
      else ZlibNg.DeflateP.MAX_STORED).toNat = min (left.toNat + ai.toNat) 65535 := by
  split
  · rename_i h
    have h' := UInt64.lt_iff_toNat_lt.mp h
    simp only [UInt64.toNat_add, UInt32.toNat_toUInt64] at h'
    have : ZlibNg.DeflateP.MAX_STORED.toUInt64.toNat = 65535 := rfl
    have : ZlibNg.DeflateP.MAX_STORED.toNat = 65535 := rfl
    have := UInt32.toNat_lt left; have := UInt32.toNat_lt ai
    rw [UInt32.toNat_add]; omega
  · rename_i h
    have h' := UInt64.not_lt.mp h
    have h'' := UInt64.le_iff_toNat_le.mp h'
    simp only [UInt64.toNat_add, UInt32.toNat_toUInt64] at h''
    have : ZlibNg.DeflateP.MAX_STORED.toUInt64.toNat = 65535 := rfl
    have : ZlibNg.DeflateP.MAX_STORED.toNat = 65535 := rfl
    have := UInt32.toNat_lt left; have := UInt32.toNat_lt ai
    omega

/-- Where the copy loop stops by a `break` (`deflate_stored.c:44`, `:58`): no room for a header and a block of
`min_block` bytes in `avail_out`, or fewer than `min_block` bytes left in the window and the input. -/
def TExit (H : Heap) (i b : Nat) (mb : UInt32) : Prop :=
  ∀ z st, H.streams i = some z → H.dstate b = some st →
    z.avail_out.toNat < (st.bi_valid.toInt.toNat + 42) / 8 + mb.toNat ∨
      ((st.strstart.toNat : Int) - st.block_start.toInt) + z.avail_in.toNat < mb.toNat

/-- One trip of the copy loop from `SF` with no pending bytes: `SF` and no pending bytes after; a trip that does not
break lowers `avail_out`; `last` set only under `Z_FINISH`; a trip that breaks stops at `TExit`. -/
theorem trip_ok {h H : Heap} {i b wo : Nat} (flush : Int32) (min_block : UInt32) (last : Int32)
    (F : SF 0 h i b H) (hp0 : ∀ st, H.dstate b = some st → st.pending = 0)
    (hw0 : ∀ st0, h.dstate b = some st0 → st0.window = .val (.ref (.heap b) wo))
    (hmb : min_block.toNat ≤ 65535) (hmb1 : 1 ≤ min_block.toNat) (hL : last ≠ 0 → flush = Z_FINISH) :
    Sat H (stored_trip (some b) (.ref (.heap b) wo) flush min_block last) (fun v H' =>
      SF (if v.1 = 0 then 0 else 5) h i b H' ∧ (∀ st, H'.dstate b = some st → st.pending = 0) ∧ (v.2 = false → avOut H' i < avOut H i) ∧
        (v.1 ≠ 0 → flush = Z_FINISH) ∧ (v.2 = true → TExit H' i b min_block)) := by
  obtain ⟨z, st, d, ob, oo, X, pbo, S⟩ := F.facts hw0
  have e0 : SH (setB H ob X) i z b st d = H := by
    rw [setB_self S.hX]; exact ZlibNgF.Proof.DeflateReset.SH_self S.hz S.hsts S.hd
  have e1 : SH H i z b st d = H := ZlibNgF.Proof.DeflateReset.SH_self S.hz S.hsts S.hd
  have hav : avOut H i = z.avail_out.toNat := by simp [avOut, S.hz]
  have hai : avIn H i = z.avail_in.toNat := by simp [avIn, S.hz]
  obtain ⟨hv0, hv8⟩ := S.bits
  obtain ⟨hb0, hbs, hss⟩ := S.bs
  have hws := S.ws.1
  obtain ⟨hv, ehv, hvn⟩ := headerBytes_SH (H := H) (i := i) (z := z) (d := d) hv0 hv8
  obtain ⟨left, elf, hlf⟩ := leftOf_SH (H := H) (i := i) (z := z) (d := d) hb0 hbs (by omega)
  rw [e1] at ehv elf
  have esm : strmOf (some b) H = .ok (some i, H) := by rw [← e1]; exact strmOf_SH S.strm
  have erz : ∀ {β : Type} (f : ZStream → β), rdZ (some i) f H = .ok (f z, H) := fun f => by
    rw [← e1]; exact rdZ_SH f
  unfold stored_trip
  refine Sat.bind (Sat.of_eq ehv ?_)
  refine Sat.bind (Sat.of_eq esm ?_)
  refine Sat.bind (Sat.of_eq (erz _) ?_)
  by_cases hbr : z.avail_out < hv
  · simp only [hbr, ↓reduceIte]
    refine Sat.pure ⟨F.mono (Nat.zero_le _), hp0, (fun e => by cases e), hL, fun _ z1 st1 h1 h2 => ?_⟩
    rw [S.hz] at h1; cases h1; rw [S.hst] at h2; cases h2
    have := UInt32.lt_iff_toNat_lt.mp hbr
    left; omega
  simp only [hbr, ↓reduceIte]
  have hA : hv.toNat ≤ z.avail_out.toNat := UInt32.le_iff_toNat_le.mp (UInt32.not_lt.mp hbr)
  refine Sat.bind (Sat.of_eq esm ?_)
  refine Sat.bind (Sat.of_eq (erz _) ?_)
  refine Sat.bind (Sat.of_eq elf ?_)
  refine Sat.bind (Sat.of_eq esm ?_)
  refine Sat.bind (Sat.of_eq (erz _) ?_)
  have hl1 := len1_le left z.avail_in
  have hl1e := len1_eq left z.avail_in
  have hsub : (z.avail_out - hv).toNat = z.avail_out.toNat - hv.toNat := UInt32.toNat_sub_of_le _ _
    (UInt32.not_lt.mp hbr)
  generalize (if ZlibNg.DeflateP.MAX_STORED.toUInt64 > left.toUInt64 + z.avail_in.toUInt64 then left + z.avail_in
      else ZlibNg.DeflateP.MAX_STORED) = len1 at hl1 hl1e ⊢
  have hlen := min32_toNat len1 (z.avail_out - hv)
  generalize MIN32 len1 (z.avail_out - hv) = len at hlen ⊢
  split
  · rename_i hc
    have hc1 : len.toNat < min_block.toNat := by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc; exact UInt32.lt_iff_toNat_lt.mp hc.1
    refine Sat.pure ⟨F.mono (Nat.zero_le _), hp0, (fun e => by cases e), hL, fun _ z1 st1 h1 h2 => ?_⟩
    rw [S.hz] at h1; cases h1; rw [S.hst] at h2; cases h2
    omega
  rename_i hc
  -- an empty block is the last one
  have key : len.toNat = 0 →
      (if flush == Z_FINISH && len == left + z.avail_in then (1 : Int32) else 0) ≠ 0 := by
    intro h0
    have h0' : len = 0 := UInt32.toNat_inj.mp (by rw [h0]; rfl)
    have hmb0 : (0 : UInt32) < min_block := UInt32.lt_iff_toNat_lt.mpr (by simp; omega)
    rw [h0'] at hc ⊢
    simp only [hmb0, decide_true, beq_self_eq_true, Bool.true_and, Bool.or_eq_true, bne_iff_ne, ne_eq,
      beq_iff_eq, not_or, Decidable.not_not] at hc
    obtain ⟨⟨hf, -⟩, hl⟩ := hc
    have : (flush == Z_FINISH && (0 : UInt32) == left + z.avail_in) = true := by
      rw [hf, ← hl]; decide
    rw [ite_eq_left this]; decide
  generalize hln : (if flush == Z_FINISH && len == left + z.avail_in then (1 : Int32) else 0) = ln at key ⊢
  refine hdr_ok F hp0 hw0 _ _ (fun z2 st2 h2 h3 => ?_) _ _ ?_
  · rw [S.hz] at h2; cases h2; rw [S.hst] at h3; cases h3; omega
  intro H1 F1 hp1 hav1 hai1 hk1
  obtain ⟨p, hp4, hpv, hpA⟩ := hav1 st S.hst
  refine win_ok (e' := if min left.toNat len.toNat = 0 then 5 else 0) F1 hp1 hw0 left len (fun st2 h2 => ?_)
    (fun z2 h2 => ?_) (by split <;> omega) _ _ ?_
  · obtain ⟨e2, e3⟩ := hk1 st st2 S.hst h2
    rw [e2, e3]; omega
  · have : avOut H1 i = z2.avail_out.toNat := by simp [avOut, h2]
    omega
  intro len2 H2 F2 hp2 hl2 hav2 hai2
  refine Sat.mono (rd_ok (e' := if ln = 0 then 0 else 5) F2 hp2 hw0 _ len2 (fun z3 h3 => ?_) ?_) ?_
  · have e4 : avOut H2 i = z3.avail_out.toNat := by simp [avOut, h3]
    have e5 : avIn H2 i = z3.avail_in.toNat := by simp [avIn, h3]
    omega
  · by_cases hm : min left.toNat len.toNat = 0
    · rw [ite_eq_left hm]
      by_cases hn : ln = 0
      · have := mt key (fun h => h hn); omega
      · rw [ite_eq_right hn]; omega
    · rw [ite_eq_right hm]; omega
  rintro v H3 ⟨rfl, F3, hp3, hav3, -⟩
  refine ⟨F3, hp3, fun _ => by omega, fun hne => ?_, fun e => by cases e⟩
  simp only [] at hne
  rw [← hln] at hne
  split at hne
  · rename_i hc; simp only [Bool.and_eq_true, beq_iff_eq] at hc; exact hc.1
  · exact absurd rfl hne

end ZlibNgF.Proof.StoredTrip
