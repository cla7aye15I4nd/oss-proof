import ZlibF.Proof.«inflate.c.meaning-gzip-fields-extra»
import ZlibF.Proof.«inflate.c.head-gzip»

/-!
# inflate.c: `EXLEN` keeps the format meaning

With `FEXTRA`, `EXLEN` waits for the two bytes of `XLEN` (`NEEDBITS(16)`), stores the length in
`length`, adds the two bytes to the header CRC through the local `hbuf` when `FHCRC` is set
(`CRC2`), and falls through to `EXTRA`. Without `FEXTRA` it falls through at once. The `hbuf`
write keeps the unread input by `HbufInputApart`.
-/

namespace Zlib.Inflate.Proofs.MeaningGzipFields
open C Zlib.Inflate Zlib.Inflate.Proofs Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs.MeaningFields
set_option autoImplicit false

/-! ## The bytes of the bit buffer -/

theorem hold_byte0 {hold : UInt64} {x : UInt8} {k : Nat} (v : hold.toNat = x.toNat + 256 * k) :
    hold.toUInt8 = x := by
  apply UInt8.toNat_inj.mp
  have hx := x.toNat_lt
  rw [UInt64.toNat_toUInt8, v]
  omega

theorem hold_shift8 {hold : UInt64} {k : Nat} (v : hold.toNat = k) :
    (hold >>> 8).toUInt8.toNat = k / 2 ^ 8 % 256 := by
  rw [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow, v]
  rfl

theorem hold_shift16 {hold : UInt64} {k : Nat} (v : hold.toNat = k) :
    (hold >>> 16).toUInt8.toNat = k / 2 ^ 16 % 256 := by
  rw [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow, v]
  rfl

theorem hold_shift24 {hold : UInt64} {k : Nat} (v : hold.toNat = k) :
    (hold >>> 24).toUInt8.toNat = k / 2 ^ 24 % 256 := by
  rw [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow, v]
  rfl

theorem hold_two {hold : UInt64} {x y : UInt8} (v : hold.toNat = x.toNat + 256 * y.toNat) :
    hold.toUInt8 = x ∧ (hold >>> 8).toUInt8 = y := by
  refine ⟨hold_byte0 v, ?_⟩
  apply UInt8.toNat_inj.mp
  have hx := x.toNat_lt
  have hy := y.toNat_lt
  rw [hold_shift8 v]
  omega

theorem hold_four {hold : UInt64} {a b c d : UInt8} (v : hold.toNat = leValue [a, b, c, d]) :
    hold.toUInt8 = a ∧ (hold >>> 8).toUInt8 = b ∧ (hold >>> 16).toUInt8 = c ∧
      (hold >>> 24).toUInt8 = d := by
  simp only [leValue] at v
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  have hc := c.toNat_lt
  have hd := d.toNat_lt
  refine ⟨hold_byte0 (k := b.toNat + 256 * (c.toNat + 256 * (d.toNat + 256 * 0))) v, ?_, ?_, ?_⟩ <;>
    apply UInt8.toNat_inj.mp
  · rw [hold_shift8 v]; omega
  · rw [hold_shift16 v]; omega
  · rw [hold_shift24 v]; omega

theorem crc2Value_of {check : UInt64} {bytes : List UInt8} {hold : UInt64} {x y : UInt8}
    (cf : check = (crc32 bytes).toUInt64) (v : hold.toNat = x.toNat + 256 * y.toNat) :
    crc2Value check hold = (crc32 (bytes ++ [x, y])).toUInt64 := by
  obtain ⟨e0, e1⟩ := hold_two v
  unfold crc2Value
  rw [e0, e1, cf, toUInt32_of_crc, MeaningChecksum.crc_continue]

theorem statics_put {h : Heap} (statics : Zlib.Crc32.Proofs.StaticsOK h) (b : Nat) (a : Array UInt8) :
    Zlib.Crc32.Proofs.StaticsOK (Space.put h (BRef.blk b) a) := statics

/-- The local `hbuf`: a writable four-byte block. -/
structure Hbuf (c : Ctx) (h : Heap) (b : Nat) (a : Array UInt8) : Prop where
  at_ : c.hbuf = .ref (.blk b) 0
  bytes : h.bytes b = some a
  size : a.size = 4
  ro : h.ro b = false

theorem Hbuf.setI {c : Ctx} {h : Heap} {b : Nat} {a : Array UInt8} (hb : Hbuf c h b a) (zs : Nat)
    (s : InflateState) : Hbuf c (Zlib.Inflate.Spec.setI h zs s) b a :=
  ⟨hb.at_, hb.bytes, hb.size, hb.ro⟩

theorem Hbuf.put {c : Ctx} {h : Heap} {b : Nat} {a : Array UInt8} (hb : Hbuf c h b a) (a' : Array UInt8)
    (size : a'.size = 4) : Hbuf c (Space.put h (BRef.blk b) a') b a' := by
  refine ⟨hb.at_, ?_, size, hb.ro⟩
  show (Space.put h (BRef.blk b) a').bytes b = some a'
  simp only [Space.put, upd_same]

/-- The heap of a `CRC2`/`CRC4` write after a state write, as an input-keeping change. -/
theorem keep_crc {c : Ctx} {h : Heap} {b : Nat} {a a' : Array UInt8} {l : IL} (hb : Hbuf c h b a)
    (apart : HbufInputApart c l) (size : a'.size = 4) (zs : Nat) (s1 s2 : InflateState) :
    InputKept h (Zlib.Inflate.Spec.setI (Space.put (Zlib.Inflate.Spec.setI h zs s1) (BRef.blk b) a') zs s2) l :=
  ((InputKept.setI h zs s1 l).trans (InputKept.hbuf apart hb.at_ hb.bytes hb.ro (by rw [size, hb.size]))).trans
    (InputKept.setI _ zs s2 l)

/-! ## `EXLEN` -/

set_option maxHeartbeats 4000000 in
theorem exlen_step {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {r : ZStreamRef} {z : ZStream}
    {zs : Nat} {s : InflateState} {bytes rest : List UInt8} (E : Env c h r zs z s)
    (g : GzAt c f h l zs s bytes rest) (mode : s.mode = EXLEN)
    (statics : Zlib.Crc32.Proofs.StaticsOK h) {b : Nat} {a : Array UInt8} (hb : Hbuf c h b a)
    (apart : HbufInputApart c l) :
    ∃ result l' h', runX (inflate_EXLEN c) l h = .ok ((result, l'), h') ∧
      TripOutcome c f result h' l' := by
  have range : FLAGS ≤ s.mode ∧ s.mode ≤ HCRC := by rw [mode]; decide
  have lo : TIME ≤ s.mode := by rw [mode]; decide
  have hi : s.mode ≤ HCRC := by rw [mode]; decide
  obtain ⟨gzb, len4, flagsInt, crcF, _, posAll⟩ := g.hm.2.2.2.2.1 lo hi
  obtain ⟨bitsLe, noFeBits, six, sixLen, bytesEq⟩ := posAll.2.2.1 mode
  have head := g.head
  have w4 := g.wrap4
  have method : bytes.getD 2 0 = 8 := by rw [bytesEq]; simp
  have flagsEq : s.flags = flagsWord (bytes.getD 3 0) := flagsWord_eq flagsInt method
  have small : (bytes.getD 3 0).toNat < 32 := by
    have v := g.viable
    rw [bytesEq] at v
    exact small_of_viable v
  unfold inflate_EXLEN
  rw [runX_bind, runX_ldS E]
  simp only [flagsEq, flagsWord_extra]
  by_cases fe : (bytes.getD 3 0).toNat / 4 % 2 = 1
  · simp only [fe, decide_true, ↓reduceIte]
    have short0 : GzipShort bytes := by rw [bytesEq]; exact gzipShort_exlen sixLen fe
    obtain ⟨result, l', j, run, shape, next, count, bitsCount, enough, leaveFacts, kinds, bitsMax,
      loopAt⟩ := g.needbits range short0 16 (by decide) (ok := fun b => b ≤ 16)
        (fun m => by rw [mode] at m; exact absurd m (by decide))
        (fun hold bits b' okb _ _ fw p => by
          obtain ⟨_, _, rest'⟩ := p.2.2.1 mode
          have same := flagsWord_byte (flagsEq ▸ fw)
          exact gzpos_exlen mode ⟨okb, fun nf => absurd fe (by rw [← same]; omega), rest'⟩)
    have n16 : (16 : UInt32).toNat = 16 := rfl
    rw [runX_bind, run]
    rcases kinds with rfl | rfl
    · have atLeast := enough rfl
      rw [n16] at atLeast bitsMax
      have aligned := g.bits
      have bits16 : l'.bits.toNat = 16 := by
        have := bitsLe
        change l.bits.toNat ≤ 16 at this
        omega
      have inEq : l'.in_ = l.in_ := by rw [shape]
      have g' := g.pulled (loopAt (by omega)) range inEq count bitsCount
      have restLen : (rest ++ (f.inp.drop (loopRead l)).take j).length = 2 := by
        have := g'.bits
        omega
      obtain ⟨x, y, xy⟩ : ∃ x y, rest ++ (f.inp.drop (loopRead l)).take j = [x, y] := by
        generalize rest ++ (f.inp.drop (loopRead l)).take j = w at restLen
        match w, restLen with
        | [x, y], _ => exact ⟨x, y, rfl⟩
      rw [xy] at g'
      have holdVal : l'.hold.toNat = x.toNat + 256 * y.toNat := by
        rw [g'.hold]
        simp [leValue]
      have apart' : HbufInputApart c l' := apart.advance next count
      have hx := x.toNat_lt
      have hy := y.toNat_lt
      have xlen : l'.hold.toUInt32.toNat = x.toNat + 256 * y.toNat := by
        rw [UInt64.toNat_toUInt32, holdVal]
        omega
      let s1 : InflateState := { s with length := l'.hold.toUInt32 }
      have E1 := envSetI E s1
      simp only []
      rw [runX_bind, runX_get]
      simp only []
      rw [runX_bind, runX_wrS E]
      simp only []
      rw [runX_bind, runX_ldS E1]
      simp only [show s1.head = none from head, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      rw [runX_bind, runX_lift_ok (hcrcOn_env E1)]
      simp only []
      rw [show (s1.flags &&& 0x0200 != 0 && s1.wrap &&& 4 != 0) =
        decide ((bytes.getD 3 0).toNat / 2 % 2 = 1) by
          show (s.flags &&& 0x0200 != 0 && s.wrap &&& 4 != 0) = _
          rw [flagsEq, flagsWord_hcrc, w4, Bool.and_true]]
      -- the header position after the length field
      have lenForm : [x, y] = le16 (x.toNat + 256 * y.toNat) := le16_of_value (by omega) rfl
      obtain ⟨getSame, start⟩ := start_append (bytes := bytes) (u := [x, y]) bytesEq
      have form : bytes ++ [x, y] = [31, 139, 8, bytes.getD 3 0] ++ six ++
          le16 (([] : List UInt8).length + l'.hold.toUInt32.toNat) ++ [] := by
        rw [bytesEq, List.length_nil, Nat.zero_add, xlen, ← lenForm]
        simp only [List.append_nil]
        rfl
      have viable : GzipViable (bytes ++ [x, y]) := by
        rw [form]
        exact gzipViable_extra small fe sixLen (by simp) (by rw [List.length_nil, xlen]; omega)
      have position : ∀ s' : InflateState, s'.mode = EXTRA → s'.length = l'.hold.toUInt32 →
          GzipPosition (loopState s' { l' with hold := 0, bits := 0 }) ((bytes ++ [x, y]).getD 3 0)
            (bytes ++ [x, y]) := by
        intro s' m' len'
        rw [getSame]
        exact gzpos_extra m' ⟨rfl, six, sixLen, fun _ => ⟨[], by
          show ([] : List UInt8).length + s'.length.toNat < _; rw [len', List.length_nil, xlen]; omega,
          by show _ = _ ++ le16 (([] : List UInt8).length + s'.length.toNat) ++ []; rw [len']; exact form⟩,
          fun nf => absurd fe (by omega)⟩
      by_cases fh : (bytes.getD 3 0).toNat / 2 % 2 = 1
      · simp only [fh, decide_true, ↓reduceIte]
        rw [runX_bind, CRC2_run E1 l' hb.at_ hb.bytes hb.size hb.ro statics]
        simp only []
        let s2 : InflateState := { s1 with check := crc2Value s1.check l'.hold }
        have E2 : Env c (Zlib.Inflate.Spec.setI (Space.put (Zlib.Inflate.Spec.setI h zs s1) (BRef.blk b)
            (crc2Bytes a l'.hold)) zs s2) r zs z s2 :=
          ⟨E.strm, E.st, by rw [ZStreamRef.get_setI, byte_view_put_stream, ZStreamRef.get_setI]; exact E.hz,
            setI_istates_same _ _ _⟩
        rw [runX_bind, runX_INITBITS]
        simp only []
        rw [runX_bind, runX_setMode E2]
        simp only []
        let s3 : InflateState := { s2 with mode := EXTRA }
        have size' : (crc2Bytes a l'.hold).size = 4 := by rw [crc2Bytes_size, hb.size]
        have g3 : GzAt c f (Zlib.Inflate.Spec.setI (Zlib.Inflate.Spec.setI (Space.put (Zlib.Inflate.Spec.setI h zs s1)
            (BRef.blk b) (crc2Bytes a l'.hold)) zs s2) zs s3) { l' with hold := 0, bits := 0 } zs s3
            (bytes ++ [x, y]) [] := by
          refine g'.step range (by simp) ((keep_crc hb apart' size' zs s1 s2).trans (InputKept.setI _ _ _ l'))
            0 (Nat.zero_le _) (inputAdvance_zero l'.next).symm (by simp) ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl rfl
            (by simp) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (by show EXTRA ≠ SYNC; decide)
            viable (by show TIME ≤ EXTRA; decide) (by show EXTRA ≤ HCRC; decide) start
            (by show s.flags = _; rw [getSame, flagsEq])
            (fun _ => by
              show crc2Value s.check l'.hold = _
              exact crc2Value_of (crcF fh) holdVal) (position s3 rfl rfl)
        have E3 := envSetI E2 s3
        exact extra_step E3 g3 rfl (statics_setI (statics_setI (statics_put (statics_setI statics zs s1) b _) zs s2) zs s3)
      · simp only [fh, decide_false, Bool.false_eq_true, ↓reduceIte]
        rw [runX_bind, runX_INITBITS]
        simp only []
        rw [runX_bind, runX_setMode E1]
        simp only []
        let s3 : InflateState := { s1 with mode := EXTRA }
        have g3 : GzAt c f (Zlib.Inflate.Spec.setI (Zlib.Inflate.Spec.setI h zs s1) zs s3)
            { l' with hold := 0, bits := 0 } zs s3 (bytes ++ [x, y]) [] := by
          refine g'.step range (by simp) ((InputKept.setI _ _ _ l').trans (InputKept.setI _ _ _ l'))
            0 (Nat.zero_le _) (inputAdvance_zero l'.next).symm (by simp) ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl rfl
            (by simp) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (by show EXTRA ≠ SYNC; decide)
            viable (by show TIME ≤ EXTRA; decide) (by show EXTRA ≤ HCRC; decide) start
            (by show s.flags = _; rw [getSame, flagsEq])
            (fun fh' => absurd (by rw [getSame] at fh'; exact fh') fh) (position s3 rfl rfl)
        exact extra_step (envSetI E1 s3) g3 rfl (statics_setI (statics_setI statics zs s1) zs s3)
    · have below := (leaveFacts rfl).2
      rw [n16] at below
      exact ⟨_, _, _, rfl, Or.inr ⟨rfl, Or.inl (loopAt (by omega))⟩⟩
  · simp only [fe, decide_false, Bool.false_eq_true, ↓reduceIte]
    simp only [head, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    have l0 : l.bits = 0 := noFeBits (by omega)
    have restNil : rest = [] := by
      have := g.bits
      rw [l0] at this
      have z : rest.length = 0 := by simp at this; omega
      exact List.eq_nil_of_length_eq_zero z
    subst restNil
    have hold0 : l.hold = 0 := by
      apply UInt64.toNat_inj.mp
      rw [g.hold]
      rfl
    rw [runX_bind, runX_setMode E]
    simp only []
    let s3 : InflateState := { s with mode := EXTRA }
    obtain ⟨getSame, start⟩ := start_append (bytes := bytes) (u := []) bytesEq
    have g3 : GzAt c f (Zlib.Inflate.Spec.setI h zs s3) l zs s3 (bytes ++ []) [] := by
      refine g.step range (by simp) (InputKept.setI _ _ _ l) 0 (Nat.zero_le _)
        (inputAdvance_zero l.next).symm (by simp) ⟨rfl, rfl, rfl, rfl, rfl⟩ hold0 l0
        (by simp) (Kept.mode s EXTRA) (by show EXTRA ≠ SYNC; decide)
        (by rw [List.append_nil]; exact g.viable)
        (by show TIME ≤ EXTRA; decide) (by show EXTRA ≤ HCRC; decide) start
        (by show s.flags = _; rw [getSame, flagsEq])
        (fun fh => by
          show s.check = _
          rw [getSame] at fh
          have cf : s.check = (crc32 bytes).toUInt64 := crcF fh
          rw [cf, List.append_nil]) ?_
      rw [getSame]
      exact gzpos_extra rfl ⟨l0, six, sixLen, fun fe' => absurd fe' fe,
        fun _ => by rw [List.append_nil]; exact bytesEq⟩
    exact extra_step (envSetI E s3) g3 rfl (statics_setI statics zs s3)

#print axioms exlen_step

end Zlib.Inflate.Proofs.MeaningGzipFields
