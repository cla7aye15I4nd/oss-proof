import ZlibF.Proof.«inflate.c.meaning-gzip-fields-loop»

/-!
# inflate.c: positions inside a gzip header (`GzAt.step`, `GzAt.body`)

The flag bits that the field modes test, the per-mode clauses of `GzipPosition`, and the two
ways a field mode moves the loop meaning: to a later header position (`GzAt.step`: the held
bytes and `n` more input bytes join the header, the bit buffer is empty), and past the header
into the body (`GzAt.body`, from `HCRC`).
-/

namespace Zlib.Inflate.Proofs.MeaningGzipFields
open C Zlib.Inflate Zlib.Inflate.Proofs Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs.MeaningBits Zlib.Inflate.Proofs.MeaningFields
set_option autoImplicit false

/-! ## The flags word -/

/-- The flags word of a gzip header with method 8 and flag byte `flg`. -/
def flagsWord (flg : UInt8) : Int32 := Int32.ofNat (8 + 256 * flg.toNat)

theorem flagsWord_eq {x : Int32} {bytes : List UInt8} (e : x.toInt = gzipFlagsWord bytes)
    (method : bytes.getD 2 0 = 8) : x = flagsWord (bytes.getD 3 0) := by
  apply Int32.toInt_inj.mp
  have small := (bytes.getD 3 0).toNat_lt
  rw [e, flagsWord, Int32.toInt_ofNat_of_lt (by omega), gzipFlagsWord, method]
  simp

/-- The flags word names its flag byte. -/
theorem flagsWord_byte {x : UInt8} {b : List UInt8} (e : (flagsWord x).toInt = gzipFlagsWord b) :
    b.getD 3 0 = x := by
  have hx := x.toNat_lt
  have h2 := (b.getD 2 0).toNat_lt
  have h3 := (b.getD 3 0).toNat_lt
  rw [flagsWord, Int32.toInt_ofNat_of_lt (by omega), gzipFlagsWord] at e
  apply UInt8.toNat_inj.mp
  omega

theorem flag_bits : ∀ n : Nat, n < 256 →
    ((Int32.ofNat (8 + 256 * n) &&& 0x0200) != 0) = decide (n / 2 % 2 = 1) ∧
    ((Int32.ofNat (8 + 256 * n) &&& 0x0400) != 0) = decide (n / 4 % 2 = 1) ∧
    ((Int32.ofNat (8 + 256 * n) &&& 0x0800) != 0) = decide (n / 8 % 2 = 1) ∧
    ((Int32.ofNat (8 + 256 * n) &&& 0x1000) != 0) = decide (n / 16 % 2 = 1) := by
  decide +kernel

theorem flagsWord_hcrc (flg : UInt8) :
    ((flagsWord flg &&& 0x0200) != 0) = decide (flg.toNat / 2 % 2 = 1) :=
  (flag_bits flg.toNat flg.toNat_lt).1

theorem flagsWord_extra (flg : UInt8) :
    ((flagsWord flg &&& 0x0400) != 0) = decide (flg.toNat / 4 % 2 = 1) :=
  (flag_bits flg.toNat flg.toNat_lt).2.1

theorem flagsWord_name (flg : UInt8) :
    ((flagsWord flg &&& 0x0800) != 0) = decide (flg.toNat / 8 % 2 = 1) :=
  (flag_bits flg.toNat flg.toNat_lt).2.2.1

theorem flagsWord_comment (flg : UInt8) :
    ((flagsWord flg &&& 0x1000) != 0) = decide (flg.toNat / 16 % 2 = 1) :=
  (flag_bits flg.toNat flg.toNat_lt).2.2.2

/-- The checks of `case FLAGS:` on the 16-bit word `m + 256 * flg`. -/
theorem flags_checks : ∀ f : Nat, f < 256 → ∀ m : Nat, m < 256 →
    ((Int32.ofNat (m + 256 * f) &&& 0xff) != Z_DEFLATED) = decide (m ≠ 8) ∧
    ((Int32.ofNat (m + 256 * f) &&& 0xe000) != 0) = decide (32 ≤ f) := by
  decide +kernel

theorem gzipFlagsWord_cons {flg : UInt8} {t : List UInt8} :
    gzipFlagsWord ([31, 139, 8, flg] ++ t) = 8 + 256 * (flg.toNat : Int) := by
  simp [gzipFlagsWord]

/-! ## Modes -/


/-! ## The clauses of `GzipPosition` -/

theorem gzpos_time {s : InflateState} {flg : UInt8} {bytes : List UInt8} (mode : s.mode = TIME)
    (cl : bytes = [31, 139, 8, flg] ∧ s.bits.toNat ≤ 32) : GzipPosition s flg bytes := by
  refine ⟨fun _ => cl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro e <;> rw [mode] at e <;> exact absurd e (by decide)

theorem gzpos_os {s : InflateState} {flg : UInt8} {bytes : List UInt8} (mode : s.mode = OS)
    (cl : s.bits.toNat ≤ 16 ∧ ∃ four : List UInt8, four.length = 4 ∧ bytes = [31, 139, 8, flg] ++ four) :
    GzipPosition s flg bytes := by
  refine ⟨?_, fun _ => cl, ?_, ?_, ?_, ?_, ?_⟩ <;> intro e <;> rw [mode] at e <;> exact absurd e (by decide)

theorem gzpos_exlen {s : InflateState} {flg : UInt8} {bytes : List UInt8} (mode : s.mode = EXLEN)
    (cl : s.bits.toNat ≤ 16 ∧ (flg.toNat / 4 % 2 = 0 → s.bits = 0) ∧
      ∃ six : List UInt8, six.length = 6 ∧ bytes = [31, 139, 8, flg] ++ six) :
    GzipPosition s flg bytes := by
  refine ⟨?_, ?_, fun _ => cl, ?_, ?_, ?_, ?_⟩ <;> intro e <;> rw [mode] at e <;> exact absurd e (by decide)

theorem gzpos_extra {s : InflateState} {flg : UInt8} {bytes : List UInt8} (mode : s.mode = EXTRA)
    (cl : s.bits = 0 ∧ ∃ six : List UInt8, six.length = 6 ∧
      (flg.toNat / 4 % 2 = 1 → ∃ e : List UInt8, e.length + s.length.toNat < 2 ^ 16 ∧
        bytes = [31, 139, 8, flg] ++ six ++ le16 (e.length + s.length.toNat) ++ e) ∧
      (flg.toNat / 4 % 2 = 0 → bytes = [31, 139, 8, flg] ++ six)) :
    GzipPosition s flg bytes := by
  refine ⟨?_, ?_, ?_, fun _ => cl, ?_, ?_, ?_⟩ <;> intro e <;> rw [mode] at e <;> exact absurd e (by decide)

theorem gzpos_name {s : InflateState} {flg : UInt8} {bytes : List UInt8} (mode : s.mode = NAME)
    (cl : s.bits = 0 ∧ ∃ six ex part : List UInt8, six.length = 6 ∧ ex.length < 2 ^ 16 ∧
      (0 : UInt8) ∉ part ∧ (flg.toNat / 8 % 2 = 0 → part = []) ∧
      bytes = [31, 139, 8, flg] ++ six ++ gzipExtraPart flg ex ++ part) :
    GzipPosition s flg bytes := by
  refine ⟨?_, ?_, ?_, ?_, fun _ => cl, ?_, ?_⟩ <;> intro e <;> rw [mode] at e <;> exact absurd e (by decide)

theorem gzpos_comment {s : InflateState} {flg : UInt8} {bytes : List UInt8} (mode : s.mode = COMMENT)
    (cl : s.bits = 0 ∧ ∃ six ex nm part : List UInt8, six.length = 6 ∧ ex.length < 2 ^ 16 ∧
      (0 : UInt8) ∉ nm ∧ (0 : UInt8) ∉ part ∧ (flg.toNat / 16 % 2 = 0 → part = []) ∧
      bytes = [31, 139, 8, flg] ++ six ++ gzipExtraPart flg ex ++ gzipNamePart flg nm ++ part) :
    GzipPosition s flg bytes := by
  refine ⟨?_, ?_, ?_, ?_, ?_, fun _ => cl, ?_⟩ <;> intro e <;> rw [mode] at e <;> exact absurd e (by decide)

theorem gzpos_hcrc {s : InflateState} {flg : UInt8} {bytes : List UInt8} (mode : s.mode = HCRC)
    (cl : s.bits.toNat ≤ 16 ∧ (flg.toNat / 2 % 2 = 0 → s.bits = 0) ∧
      ∃ mt xfl os ex nm cm, GzipFields flg mt ex nm cm ∧ bytes = Gzip.header flg mt xfl os ex nm cm) :
    GzipPosition s flg bytes := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun _ => cl⟩ <;> intro e <;> rw [mode] at e <;> exact absurd e (by decide)

/-! ## The header facts of a field mode -/

theorem headerWidth_transfer {s s' : InflateState} {configured : Nat} {b b' : List UInt8}
    (w : HeaderWidth s configured b) (wb : s'.wbits = s.wbits) (gb : IsGzipHeader b)
    (gb' : IsGzipHeader b') : HeaderWidth s' configured b' := by
  obtain ⟨w1, w2, w3⟩ := w
  rw [← wb] at w1 w2 w3
  exact ⟨w1, w2, fun z => ⟨fun _ => (w3 z).1 gb, fun ng => absurd gb' ng⟩⟩

/-- In `FLAGS` .. `HCRC` the header begins with the gzip magic and has the width of a gzip header. -/
theorem GzAt.width {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {zs : Nat} {s : InflateState}
    {bytes rest : List UInt8} (g : GzAt c f h l zs s bytes rest) (range : FLAGS ≤ s.mode ∧ s.mode ≤ HCRC) :
    HeaderWidth (loopState s l) f.configured bytes ∧ IsGzipHeader bytes := by
  rcases flags_or_time range with m | ⟨lo, hi⟩
  · obtain ⟨b, _, _, w⟩ := g.hm.2.2.2.1 m
    exact ⟨w, by rw [b]; rfl⟩
  · obtain ⟨gb, _, _, _, w, _⟩ := g.hm.2.2.2.2.1 lo hi
    exact ⟨w, gb⟩

/-- The configuration fields a field mode keeps. -/
def Kept (s s' : InflateState) : Prop :=
  s'.wrap = s.wrap ∧ s'.reqwrap = s.reqwrap ∧ s'.head = s.head ∧ s'.reqbits = s.reqbits ∧
    s'.wbits = s.wbits ∧ s'.window = s.window ∧ s'.wsize = s.wsize ∧ s'.whave = s.whave ∧
    s'.havedict = s.havedict ∧ s'.last = s.last ∧ s'.total = s.total

theorem Kept.update (s : InflateState) (m : UInt32) (fl : Int32) (ck : UInt64) (len : UInt32) :
    Kept s { s with mode := m, flags := fl, check := ck, length := len } :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem InputKept.advance {h h' : Heap} {l l' : IL} {n : Nat} (keep : InputKept h h' l)
    (next : l'.next = inputAdvance l.next n) (count : l'.have_.toNat + n = l.have_.toNat) :
    InputKept h h' l' := by
  refine ⟨keep.1, keep.2.1, fun ne ref off p => ?_⟩
  have ne' : l.have_ ≠ 0 := by
    intro z
    apply ne
    apply UInt32.toNat_inj.mp
    rw [z] at count
    simp only [UInt32.toNat_zero] at count ⊢
    omega
  cases hn : l.next with
  | null =>
    rw [hn] at next
    rw [next] at p
    cases p
  | ref ref0 off0 =>
    rw [hn] at next
    rw [next] at p
    simp only [inputAdvance, Ptr.ref.injEq] at p
    rw [← p.1]
    exact keep.2.2 ne' ref0 off0 hn

/-- A field mode moves to a later header position: the held bytes `rest` and `n` more input bytes
join the header, and the bit buffer is empty. -/
theorem GzAt.step {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {zs : Nat} {s : InflateState}
    {bytes rest : List UInt8} (g : GzAt c f h l zs s bytes rest)
    (old : FLAGS ≤ s.mode ∧ s.mode ≤ HCRC)
    {h' : Heap} {l' : IL} {s' : InflateState} {bytes' : List UInt8}
    (hs' : h'.istates zs = some s') (keep : InputKept h h' l)
    (n : Nat) (le : n ≤ l.have_.toNat)
    (next : l'.next = inputAdvance l.next n) (count : l'.have_.toNat + n = l.have_.toNat)
    (regs : l'.ret = l.ret ∧ l'.in_ = l.in_ ∧ l'.out_ = l.out_ ∧ l'.left = l.left ∧ l'.put = l.put)
    (hold0 : l'.hold = 0) (bits0 : l'.bits = 0)
    (bytesEq : bytes' = bytes ++ rest ++ (f.inp.drop (loopRead l)).take n)
    (same : Kept s s') (notSync : s'.mode ≠ SYNC)
    (viable : GzipViable bytes')
    (lo : TIME ≤ s'.mode) (hi : s'.mode ≤ HCRC)
    (start : ∃ t, bytes' = [31, 139, 8, bytes'.getD 3 0] ++ t)
    (flags : s'.flags = flagsWord (bytes'.getD 3 0))
    (crc : (bytes'.getD 3 0).toNat / 2 % 2 = 1 → s'.check = (crc32 bytes').toUInt64)
    (pos : GzipPosition (loopState s' l') (bytes'.getD 3 0) bytes') :
    GzAt c f h' l' zs s' bytes' [] := by
  obtain ⟨retEq, inEq, outEq, leftEq, putEq⟩ := regs
  obtain ⟨sw, srw, shd, srb, swb, swin, swsize, swhave, shd2, slast, stotal⟩ := same
  have bsLen := g.binv.have_eq
  rw [List.length_drop] at bsLen
  have readEq : loopRead l' = loopRead l + n := by
    simp only [loopRead, inEq]
    have := g.haveLe
    omega
  have keep' : InputKept h h' l' := keep.advance next count
  have binvH := keep.binv g.binv
  have adv := BitInv.advance_bytes (regs := { l' with hold := l.hold, bits := l.bits }) binvH
    (by rw [List.length_drop]; omega) next count rfl rfl
  have binv' : BitInv h' l' (f.inp.drop (loopRead l')) := by
    rw [readEq, ← List.drop_drop]
    exact ⟨adv.have_eq, adv.next, by rw [hold0, bits0]; decide⟩
  obtain ⟨t, startEq⟩ := start
  have gzb' : IsGzipHeader bytes' := by rw [startEq]; rfl
  obtain ⟨width, gzb⟩ := g.width old
  have wrappedC := g.hm.2.2.2.2.2.1 g.wrapped
  obtain ⟨c1, c2, c3, c4, c5, _⟩ := g.config
  refine ⟨g.st, hs', by rw [retEq]; exact g.ret, ⟨?_, ?_, ?_, ?_, ?_, notSync⟩,
    by rw [inEq]; have := g.haveLe; omega, by rw [inEq]; exact g.inLen, binv',
    by rw [leftEq, outEq]; exact g.leftLe, by simp only [loopPending, leftEq, outEq]; exact g.pend,
    by rw [putEq]; exact g.put, keep.bytes0 g.outBytes,
    by rw [putEq, leftEq]; exact keep.writable g.writable, ?_,
    by rw [putEq, leftEq]; show Separate _ _ s'.window s'.wsize.toNat; rw [swin, swsize]; exact g.sepWin,
    g.logOut, ?_, by rw [bits0]; rfl, by rw [hold0]; rfl, viable, ⟨?_, ?_⟩, ?_, g.dict, g.gz⟩
  · show s'.wrap = _; rw [sw]; exact c1
  · show s'.reqwrap = s'.wrap; rw [srw, sw]; exact c2
  · show s'.head = none; rw [shd]; exact c3
  · show s'.reqbits.toNat = _; rw [srb]; exact c4
  · intro nz; show s'.wbits.toNat = _; rw [swb]; exact c5 nz
  · rw [putEq, leftEq]
    have := separate_advance g.sepIn le
    have haveEq : l'.have_.toNat = l.have_.toNat - n := by omega
    rw [next, haveEq]
    exact this
  · rw [readEq, List.take_add, ← List.append_assoc, g.input, bytesEq, List.append_nil]
  · exact UInt32.le_trans (by decide) lo
  · exact UInt32.le_trans hi (by decide)
  · refine ⟨fun raw => absurd raw g.wrapped, fun m => ?_, fun m => ?_, fun m => ?_, fun _ _ => ?_,
      fun _ => ?_, ?_, ?_, fun raw => absurd raw g.wrapped⟩
    · have : TIME ≤ HEAD := by have e : s'.mode = HEAD := m; rw [e] at lo; exact lo
      exact absurd this (by decide)
    · have : DICTID ≤ HCRC := by have e : s'.mode = DICTID := m; rw [e] at hi; exact hi
      exact absurd this (by decide)
    · have : TIME ≤ FLAGS := by have e : s'.mode = FLAGS := m; rw [e] at lo; exact lo
      exact absurd this (by decide)
    · refine ⟨gzb', by rw [startEq]; simp, ?_, crc, headerWidth_transfer width swb gzb gzb', pos⟩
      show s'.flags.toInt = _
      rw [flags, startEq, gzipFlagsWord_cons, flagsWord, Int32.toInt_ofNat_of_lt]
      · simp
      · have := (bytes'.getD 3 0).toNat_lt
        rw [startEq] at this ⊢
        simp only [List.getD_eq_getElem?_getD] at this ⊢
        simp at this ⊢
        omega
    · show s'.havedict = 0 ∧ s'.wsize = 0 ∧ s'.whave = 0
      rw [shd2, swsize, swhave]
      exact wrappedC
    · show s'.last = 0; rw [slast]; exact g.hm.2.2.2.2.2.2.1
    · show s'.total = 0; rw [stotal]; exact g.hm.2.2.2.2.2.2.2.1

#print axioms GzAt.step

/-- `HCRC` ends the header: the body begins at its first block boundary with an empty window,
`check = crc32 [] = 0` and the flags word of the header. -/
theorem GzAt.body {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {zs : Nat} {s : InflateState}
    {bytes rest : List UInt8} (g : GzAt c f h l zs s bytes rest)
    (old : FLAGS ≤ s.mode ∧ s.mode ≤ HCRC)
    {h' : Heap} {l' : IL} {s' : InflateState} {header : List UInt8}
    (hs' : h'.istates zs = some s') (keep : InputKept h h' l)
    (regs : l'.ret = l.ret ∧ l'.in_ = l.in_ ∧ l'.out_ = l.out_ ∧ l'.left = l.left ∧ l'.put = l.put ∧
      l'.next = l.next ∧ l'.have_ = l.have_)
    (hold0 : l'.hold = 0) (bits0 : l'.bits = 0)
    (headerEq : header = bytes ++ rest)
    (same : Kept s s') (mode' : s'.mode = TYPE) (gh : GzipHeader header)
    (flags : s'.flags = flagsWord (header.getD 3 0)) (check : s'.check = 0) :
    LoopMatches c f h' l' := by
  obtain ⟨retEq, inEq, outEq, leftEq, putEq, nextEq, haveEq⟩ := regs
  obtain ⟨sw, srw, shd, srb, swb, swin, swsize, swhave, _, slast, stotal⟩ := same
  have readEq : loopRead l' = loopRead l := by simp only [loopRead, inEq, haveEq]
  have keep' : InputKept h h' l' := keep.regs nextEq haveEq
  have binvH := keep.binv g.binv
  have binv' : BitInv h' l' (f.inp.drop (loopRead l')) := by
    rw [readEq]
    exact ⟨by rw [haveEq]; exact binvH.have_eq, by rw [nextEq]; exact binvH.next,
      by rw [hold0, bits0]; decide⟩
  obtain ⟨width, gzb⟩ := g.width old
  have gzh : IsGzipHeader header := gzipHeader_is_gzip gh
  have wrappedC := g.hm.2.2.2.2.2.1 g.wrapped
  obtain ⟨c1, c2, c3, c4, c5, _⟩ := g.config
  obtain ⟨flg, mt, xfl, os, ex, nm, cm, small, mtLength, exLimit, nmOk, cmOk, hdrEq⟩ := gh
  have method : header.getD 2 0 = 8 := by rw [hdrEq]; simp [Gzip.header]
  refine ⟨zs, s', [], bytesToBits header, [], .body header ⟨[], false, .boundary⟩, g.st, hs',
    by rw [retEq]; exact g.ret, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩,
    by rw [inEq, haveEq]; exact g.haveLe, by rw [inEq]; exact g.inLen, binv',
    by rw [leftEq, outEq]; exact g.leftLe, ⟨?_, fun _ _ _ => ?_⟩,
    by rw [putEq, g.put]; exact (inputAdvance_zero f.start).symm, keep.bytes0 g.outBytes,
    by rw [putEq, leftEq]; exact keep.writable g.writable,
    by rw [putEq, leftEq, nextEq, haveEq]; exact g.sepIn,
    by rw [putEq, leftEq]; show Separate _ _ s'.window s'.wsize.toNat; rw [swin, swsize]; exact g.sepWin,
    Or.inl rfl, ?_, ⟨by show 0 = l'.bits.toNat; rw [bits0]; rfl,
      by show l'.hold.toNat = 0; rw [hold0]; rfl⟩, ?_, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, Or.inl g.dict⟩, ?_⟩
  · show s'.wrap = _; rw [sw]; exact c1
  · show s'.reqwrap = s'.wrap; rw [srw, sw]; exact c2
  · show s'.head = none; rw [shd]; exact c3
  · show s'.reqbits.toNat = _; rw [srb]; exact c4
  · intro nz; show s'.wbits.toNat = _; rw [swb]; exact c5 nz
  · show s'.mode ≠ SYNC; rw [mode']; decide
  · show loopPending l' ≤ 0
    simp only [loopPending, leftEq, outEq]
    exact Nat.le_of_eq g.pend
  · show loopPending l' = 0
    simp only [loopPending, leftEq, outEq]
    exact g.pend
  · rw [readEq, g.input, headerEq, bytesToBits_append', List.append_nil]
  · refine ⟨[], bytesToBits [] , ?_, by simp [bytesToBits], .start⟩
    rcases g.gz with w | w <;> rw [w]
    · exact ⟨⟨flg, mt, xfl, os, ex, nm, cm, small, mtLength, exLimit, nmOk,
        cmOk, hdrEq⟩, rfl⟩
    · exact Or.inr ⟨⟨flg, mt, xfl, os, ex, nm, cm, small, mtLength, exLimit, nmOk,
        cmOk, hdrEq⟩, rfl⟩
  · exact ⟨Or.inl mode', rfl, by show s'.last = 0; rw [slast]; exact g.hm.2.2.2.2.2.2.1,
      by show l'.bits.toNat < 8; rw [bits0]; decide⟩
  · exact Or.inr ⟨by show s'.wsize = 0; rw [swsize]; exact wrappedC.2.1,
      by show s'.whave = 0; rw [swhave]; exact wrappedC.2.2, by rw [g.dict, g.logOut]; rfl⟩
  · refine ⟨?_, fun _ => ?_⟩
    · show s'.total = _
      have t0 : s.total = 0 := g.hm.2.2.2.2.2.2.2.1
      rw [stotal, t0, g.logOut]
      simp
    · show s'.check = _
      rw [check, g.logOut]
      simp only [List.nil_append, List.take_nil]
      split
      · decide
      · rename_i notGz
        exfalso
        rcases g.gz with w | w
        · exact notGz (Or.inl w)
        · exact notGz (Or.inr ⟨w, gzh⟩)
  · show FlagsMatch s' f.wrap header
    unfold FlagsMatch
    rw [if_neg g.wrapped, if_pos gzh, flags, flagsWord, Int32.toInt_ofNat_of_lt]
    · unfold gzipFlagsWord
      rw [method]
      simp
    · have := (header.getD 3 0).toNat_lt
      omega
  · exact headerWidth_transfer width swb gzb gzh
  · rw [g.logOut]; rfl

#print axioms GzAt.body

end Zlib.Inflate.Proofs.MeaningGzipFields
