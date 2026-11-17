import ZlibF.Proof.«inflate.c.meaning-head-zlib»
import ZlibF.Proof.«inflate.c.head-gzip-state»
import ZlibF.Proof.«inflate.c.meaning-wrap-steps»
import ZlibF.Proof.«inflate.c.bits-complete»

/-!
# inflate.c: `HEAD` with gzip or automatic detection keeps the format meaning (`TripHeadGzip`)

`case HEAD:` with `wrap = 6` (gzip) or `wrap = 7` (automatic detection) and no header record:

* `NEEDBITS(16)` leaves for more input: the parse stays at the empty header with fewer than 16
  held bits (`LoopMatches`).
* The gzip magic `31, 139`: `CRC2` writes the two bytes into the local `hbuf` and `check` becomes
  the CRC-32 of the magic; the decoder is in `FLAGS` at the header stage `[31, 139]`, with width 15
  when the configured width is 0. The unread input is not in `hbuf` (`HbufInputApart` of
  `CallSide`), so the input bytes are those before the write.
* Any other two bytes with gzip: `incorrect header check` (`wrap & 1` is clear), and no gzip
  stream starts with them (`layerDecodes_head`).
* Any other two bytes with automatic detection: the zlib checks, as for the zlib wrapper
  (`trip_head_zlib`); a rejection is doomed since the bytes are neither the magic nor an
  acceptable zlib header.
-/

namespace Zlib.Inflate.Proofs.MeaningHeadGzip
open C Zlib.Inflate Zlib.Inflate.Proofs Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs.MeaningHeadZlib
set_option autoImplicit false

/-! ## Entry -/

/-- The configuration facts `HEAD` reads, for every wrapper. -/
theorem head_entry {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {zs : Nat}
    {s : InflateState} (loop : LoopMatches c f h l) (st : c.st = some (.tab zs))
    (hs : h.istates zs = some s) (mode : s.mode = HEAD) :
    s.wrap = wrapCode f.wrap ∧ s.head = none ∧ (f.configured = 0 → s.wbits = 0) ∧
      (f.configured ≠ 0 → s.wbits.toNat = f.configured) := by
  obtain ⟨zs1, s1, _, _, _, stage, st1, hs1, _, config, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    stageM, wrapM, _⟩ := loop
  have same : zs = zs1 ∧ s = s1 := by
    rw [st] at st1
    cases st1
    exact ⟨rfl, Option.some.inj (hs.symm.trans hs1)⟩
  obtain ⟨rfl, rfl⟩ := same
  have high : (loopState s l).mode ≤ DICTID := by
    show s.mode ≤ DICTID
    rw [mode]
    decide
  obtain ⟨bytes, rfl⟩ := MeaningDictid.stage_of_header stageM high
  have width0 := (wrapM.1.2.1 mode).2.2
  exact ⟨config.1, config.2.2.1, width0, config.2.2.2.2.1⟩

/-! ## The gzip magic -/

/-- The write of `hbuf` and of the state record keeps every byte view but the one of `hbuf`. -/
theorem get_hbuf_put_ne (h : Heap) (b : Nat) (arr : Array UInt8) (zs : Nat) (st : InflateState)
    (ref : BRef) (other : ref ≠ BRef.blk b) :
    (Space.get (setI (Space.put h (BRef.blk b) arr) zs st) ref : Option (Array UInt8)) =
      Space.get h ref := by
  rw [byte_view_get_setI]
  cases ref with
  | blk w =>
    have ne : w ≠ b := fun e => other (by rw [e])
    simp only [Space.get, Space.put, upd_ne _ _ _ _ ne]
  | _ => rfl

/-- The unread input after `CRC2` and `INITBITS()`: the input is not in `hbuf`. -/
theorem bitInv_hbuf_put {c : Ctx} {h : Heap} {l : IL} {bs : List UInt8} {b : Nat}
    {arr : Array UInt8} {zs : Nat} {st : InflateState} (inv : BitInv h l bs)
    (apart : HbufInputApart c l) (hbufAt : c.hbuf = .ref (.blk b) 0) :
    BitInv (setI (Space.put h (BRef.blk b) arr) zs st) { l with hold := 0, bits := 0 } bs := by
  refine ⟨inv.have_eq, ?_, show (0 : UInt64).toNat < 2 ^ (0 : UInt32).toNat by decide⟩
  by_cases empty : bs = []
  · exact Or.inl empty
  rcases inv.next with nil | ⟨ref, a, off, ptr, get, fit, content⟩
  · exact Or.inl nil
  have nonzero : l.have_ ≠ 0 := by
    intro zero
    have count := inv.have_eq
    rw [zero] at count
    apply empty
    exact List.eq_nil_of_length_eq_zero (by simpa using count.symm)
  have other : ref ≠ BRef.blk b := apart nonzero b 0 ref off hbufAt ptr
  exact Or.inr ⟨ref, a, off, ptr, by rw [get_hbuf_put_ne h b arr zs st ref other]; exact get, fit,
    content⟩

/-- The two magic bytes are the word `0x8b1f`. -/
theorem magic_bytes {hold : UInt64} {cmf flg : UInt8}
    (wire : hold.toNat = cmf.toNat + 256 * flg.toNat) :
    hold = 0x8b1f ↔ cmf = 31 ∧ flg = 139 := by
  have cb := cmf.toNat_lt
  have fb := flg.toNat_lt
  constructor
  · intro magic
    have value : cmf.toNat + 256 * flg.toNat = 35615 := by rw [← wire, magic]; rfl
    exact ⟨UInt8.toNat_inj.mp (by show cmf.toNat = 31; omega),
      UInt8.toNat_inj.mp (by show flg.toNat = 139; omega)⟩
  · rintro ⟨rfl, rfl⟩
    apply UInt64.toNat_inj.mp
    rw [wire]
    rfl

/-- The gzip magic: the header stage `[31, 139]` in `FLAGS`, `check` the CRC-32 of the magic. -/
theorem gzip_head_magic {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {r : ZStreamRef}
    {z : ZStream} {zs : Nat} {s : InflateState} {b : Nat} {a : Array UInt8}
    (loop : LoopMatches c f h l) (E : Env c h r zs z s) (mode : s.mode = HEAD)
    (gzipLike : f.wrap = .gzip ∨ f.wrap = .auto) (inv : DefaultStateJ h r zs z s)
    (hbufAt : c.hbuf = .ref (.blk b) 0) (bytes : h.bytes b = some a) (writable : h.ro b = false)
    (apart : HbufInputApart c l)
    (input : f.logIn ++ f.inp.take (loopRead l) = [31, 139]) (magic : l.hold = 0x8b1f) :
    LoopMatches c f (setI (Space.put h (BRef.blk b) (crc2Bytes a l.hold)) zs (headGzipState s l.hold))
      { l with hold := 0, bits := 0 } := by
  obtain ⟨zs1, s1, callOut, consumed, held, stage, st1, hs1, retOk, config, haveLe, inLen, binv,
    leftLe, pend, putEq, outBytes, writableOut, sepIn, sepWin, sepOutIn, _bitsEq, _heldBits, _parsed,
    stageM, wrapM, outputEq⟩ := loop
  have same : zs = zs1 ∧ s = s1 := by
    have st := E.st
    rw [st] at st1
    cases st1
    exact ⟨rfl, Option.some.inj (E.hs.symm.trans hs1)⟩
  obtain ⟨rfl, rfl⟩ := same
  have high : (loopState s l).mode ≤ DICTID := by
    show s.mode ≤ DICTID
    rw [mode]
    decide
  obtain ⟨stageBytes, rfl⟩ := MeaningDictid.stage_of_header stageM high
  obtain ⟨⟨_, headC, _, _, _, wrappedC, last0, total0, _⟩, _, dictC⟩ := wrapM
  obtain ⟨bytesNil, _, width0⟩ := headC mode
  subst bytesNil
  have wrapped : f.wrap ≠ .raw := by rcases gzipLike with e | e <;> rw [e] <;> decide
  obtain ⟨havedict0, wsize0, whave0⟩ := wrappedC wrapped
  have dictNil : f.dict = [] := dictC.resolve_right wrapped
  have outNil : f.logOut ++ callOut = [] := outputEq.symm
  obtain ⟨logNil, callNil⟩ := List.append_eq_nil_iff.mp outNil
  subst callNil
  have pend0 : loopPending l = 0 := by
    have := pend.1
    simp only [List.length_nil] at this
    omega
  have wrapEq : s.wrap = wrapCode f.wrap := config.1
  have allowed : GzipAllowed s.wrap := by
    rcases gzipLike with e | e
    · exact Or.inr (Or.inr (Or.inl (by rw [wrapEq, e]; rfl)))
    · exact Or.inr (Or.inr (Or.inr (by rw [wrapEq, e]; rfl)))
  obtain ⟨_, sizes, readonly, _⟩ := headGzip_default_state inv mode allowed bytes writable l.hold
  have width := headGzipState_width inv.toDefaultDecodeJ l.hold
  have bytesNew : Bytes (setI (Space.put h (BRef.blk b) (crc2Bytes a l.hold)) zs
      (headGzipState s l.hold)) f.start ([] : List UInt8).length [] := by
    rcases outBytes with null | ⟨ref, i, arr, ptr, get, fits, _⟩
    · exact Or.inl null
    · obtain ⟨arr', get', size'⟩ := sizes.view get
      exact Or.inr ⟨ref, i, arr', ptr, get', by rw [size']; exact fits, by simp⟩
  have writableNew : Writable (setI (Space.put h (BRef.blk b) (crc2Bytes a l.hold)) zs
      (headGzipState s l.hold)) l.put l.left.toNat := by
    rcases writableOut with null | ⟨ref, i, arr, ptr, get, ro, fits⟩
    · exact Or.inl null
    · obtain ⟨arr', get', size'⟩ := sizes.view get
      exact Or.inr ⟨ref, i, arr', ptr, get', by rw [readonly]; exact ro, by rw [size']; exact fits⟩
  have configNew : ConfigMatches (loopState (headGzipState s l.hold) { l with hold := 0, bits := 0 })
      f.wrap f.configured := by
    obtain ⟨c1, c2, c3, c4, c5, _⟩ := config
    refine ⟨c1, c2, c3, c4, fun nz => ?_, show FLAGS ≠ SYNC by decide⟩
    have w : s.wbits.toNat = f.configured := c5 nz
    have sNZ : s.wbits ≠ 0 := by
      intro e
      rw [e] at w
      exact nz (w.symm.trans rfl)
    show (if s.wbits = 0 then (15 : UInt32) else s.wbits).toNat = f.configured
    rw [ite_eq_right sNZ]
    exact w
  have bitsNew : bytesToBits (f.logIn ++ f.inp.take (loopRead { l with hold := 0, bits := 0 })) =
      bytesToBits [31, 139] ++ [] := by
    show bytesToBits (f.logIn ++ f.inp.take (loopRead l)) = _
    rw [List.append_nil, input]
  have checkEq : crc2Value 0 l.hold = (ZlibF.Spec.crc32 [31, 139]).toUInt64 := by
    unfold crc2Value
    rw [magic]
    rfl
  have headerNew : HeaderMatches (loopState (headGzipState s l.hold) { l with hold := 0, bits := 0 })
      f.wrap f.configured [31, 139] := by
    refine ⟨fun raw => absurd raw wrapped, fun m => absurd (show FLAGS = HEAD from m) (by decide),
      fun m => absurd (show FLAGS = DICTID from m) (by decide),
      fun _ => ⟨rfl, show (0 : UInt32).toNat ≤ 16 by decide, checkEq, width.1, width.2, fun cz => ?_⟩,
      fun low _ => absurd (show TIME ≤ FLAGS from low) (by decide),
      fun _ => ⟨havedict0, wsize0, whave0⟩, last0, total0, fun raw => absurd raw wrapped⟩
    refine ⟨fun _ => ?_, fun ng => absurd (show IsGzipHeader [31, 139] by decide) ng⟩
    have zero : s.wbits = 0 := width0 cz
    show (if s.wbits = 0 then (15 : UInt32) else s.wbits).toNat = 15
    rw [ite_eq_left zero]
    rfl
  refine ⟨zs, headGzipState s l.hold, [], bytesToBits [31, 139], [], .header [31, 139], E.st,
    setI_istates_same _ _ _, retOk, configNew, haveLe, inLen, bitInv_hbuf_put binv apart hbufAt,
    leftLe, ⟨Nat.le_of_eq pend0, fun _ _ e => by cases e⟩, putEq, bytesNew, writableNew, sepIn,
    sepWin, sepOutIn, bitsNew, ⟨rfl, rfl⟩, wrapParsed_gzip_magic gzipLike,
    show HEAD ≤ FLAGS ∧ FLAGS ≤ DICTID by decide,
    ⟨headerNew, Or.inr ⟨wsize0, whave0, by rw [dictNil]; rfl⟩, Or.inl dictNil⟩,
    by rw [logNil]; rfl⟩

/-! ## Other two bytes -/

/-- Two header bytes that are not the magic, and are no acceptable zlib header where one is
allowed, start no stream of the configuration. -/
theorem head_doomed {f : LoopFrame} {l : IL} {cmf flg : UInt8} (wrapped : f.wrap ≠ .raw)
    (input : f.logIn ++ f.inp.take (loopRead l) = [cmf, flg])
    (notMagic : ¬ (cmf = 31 ∧ flg = 139))
    (invalid : (f.wrap = .zlib ∨ f.wrap = .auto) →
      ¬ (ZlibF.Spec.Zlib.HeaderOK cmf flg ∧ ZlibF.Spec.Api.ZlibFits f.configured [cmf, flg])) :
    LoopDoomed f l := by
  intro source decoded valid _ pre
  rw [input] at pre
  rcases layerDecodes_head valid pre wrapped with ⟨_, first, second⟩ | ⟨zlibLike, okFits⟩
  · exact notMagic ⟨first, second⟩
  · exact invalid zlibLike okFits

/-- A rejected header: `BAD`, with the configuration kept and the input read so far doomed. -/
theorem head_bad {c : Ctx} {f : LoopFrame} {h : Heap} {l regs : IL} {r : ZStreamRef}
    {z : ZStream} {zs : Nat} {s : InflateState} {i : Nat}
    (loop : LoopMatches c f h l) (st : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (doomed : LoopDoomed f l) (regsEq : regs = l ∨ regs = headWindowRegs l) :
    LoopBad c f (badHeap h r zs z s i) regs := by
  obtain ⟨zs1, s1, _, _, _, _, st1, hs1, _, config, haveLe, inLen, _⟩ := loop
  have same : zs = zs1 ∧ s = s1 := by
    rw [st] at st1
    cases st1
    exact ⟨rfl, Option.some.inj (hs.symm.trans hs1)⟩
  obtain ⟨rfl, rfl⟩ := same
  have get : (badHeap h r zs z s i).istates zs = some { s with mode := BAD } := by
    simp only [badHeap, setI_istates_same]
  obtain ⟨c1, c2, c3, c4, c5, _⟩ := config
  rcases regsEq with rfl | rfl
  · exact ⟨zs, { s with mode := BAD }, st, get, rfl,
      ⟨c1, c2, c3, c4, c5, show BAD ≠ SYNC by decide⟩, haveLe, inLen, doomed⟩
  · exact ⟨zs, { s with mode := BAD }, st, get, rfl,
      ⟨c1, c2, c3, c4, c5, show BAD ≠ SYNC by decide⟩, haveLe, inLen, doomed⟩

/-! ## Automatic detection: the zlib checks -/

/-- A header that satisfies the RFC predicate passes the first two literal checks of the C with
the automatic wrapper code. -/
theorem auto_head_checks_pass {s : InflateState} {l : IL} {cmf flg : UInt8}
    (wire : l.hold.toNat = cmf.toNat + 256 * flg.toNat) (wrap : s.wrap = 7)
    (ok : ZlibF.Spec.Zlib.HeaderOK cmf flg) :
    headHeaderRejected s l = false ∧ headMethodRejected l = false ∧
      (headWindowRegs l).len.toNat ≤ 15 := by
  have mask8 : ((1 : UInt32) <<< 8 - 1) = 255 := by decide +kernel
  have mask4 : ((1 : UInt32) <<< 4 - 1) = 15 := by decide +kernel
  have cmfBound : cmf.toNat < 256 := cmf.toNat_lt
  have flgBound : flg.toNat < 256 := flg.toNat_lt
  have low8 : (l.hold.toUInt32 &&& 255).toNat = cmf.toNat := by
    rw [UInt32.toNat_and, UInt64.toNat_toUInt32]
    change (l.hold.toNat % 4294967296) &&& (2 ^ 8 - 1) = cmf.toNat
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega
  have low4 : (l.hold.toUInt32 &&& 15).toNat = cmf.toNat % 16 := by
    rw [UInt32.toNat_and, UInt64.toNat_toUInt32]
    change (l.hold.toNat % 4294967296) &&& (2 ^ 4 - 1) = cmf.toNat % 16
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega
  have high8 : (l.hold >>> 8).toNat = flg.toNat := by
    rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    change l.hold.toNat / 256 = flg.toNat
    omega
  have shifted : ((l.hold.toUInt32 &&& 255) <<< 8).toUInt64.toNat = cmf.toNat * 256 := by
    rw [UInt32.toNat_toUInt64, UInt32.toNat_shiftLeft, low8, Nat.shiftLeft_eq]
    change cmf.toNat * 256 % 4294967296 = cmf.toNat * 256
    omega
  have word : (((l.hold.toUInt32 &&& 255) <<< 8).toUInt64 + (l.hold >>> 8)).toNat =
      cmf.toNat * 256 + flg.toNat := by
    rw [UInt64.toNat_add, shifted, high8]
    change (cmf.toNat * 256 + flg.toNat) % 18446744073709551616 = _
    exact Nat.mod_eq_of_lt (by omega)
  have modZero : (((l.hold.toUInt32 &&& 255) <<< 8).toUInt64 + (l.hold >>> 8)) % 31 = 0 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_mod, word]
    change (cmf.toNat * 256 + flg.toNat) % 31 = 0
    exact ok.2.2
  have method : (l.hold.toUInt32 &&& 15) = i2u Z_DEFLATED := by
    apply UInt32.toNat_inj.mp
    rw [low4]
    change cmf.toNat % 16 = 8
    exact ok.1
  refine ⟨?_, ?_, ?_⟩
  · unfold headHeaderRejected
    rw [mask8, modZero, wrap] <;> decide
  · unfold headMethodRejected
    rw [mask4, method] <;> simp
  · rw [zlib_head_window_length wire]
    have := ok.2.1
    omega

/-- An accepted zlib header under automatic detection: the body at its first block boundary, or
the header stage in `DICTID` when `FDICT` is set. -/
theorem auto_head_accepted {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {r : ZStreamRef}
    {z : ZStream} {zs : Nat} {s : InflateState} {cmf flg : UInt8}
    (loop : LoopMatches c f h l) (E : Env c h r zs z s) (mode : s.mode = HEAD)
    (auto : f.wrap = .auto) (window : HeadWindow s)
    (wire : l.hold.toNat = cmf.toNat + 256 * flg.toNat)
    (input : f.logIn ++ f.inp.take (loopRead l) = [cmf, flg])
    (ok : ZlibF.Spec.Zlib.HeaderOK cmf flg) (fits : ZlibF.Spec.Api.ZlibFits f.configured [cmf, flg]) :
    LoopMatches c f (setI (r.put h { z with adler := 1 }) zs (headDefaultState s l))
      { headWindowRegs l with hold := 0, bits := 0 } := by
  obtain ⟨zs1, s1, callOut, consumed, held, stage, st1, hs1, retOk, config, haveLe, inLen, binv,
    leftLe, pend, putEq, outBytes, writable, sepIn, sepWin, sepOutIn, bitsEq, heldBits, parsed,
    stageM, wrapM, outputEq⟩ := loop
  have same : zs = zs1 ∧ s = s1 := by
    have st := E.st
    rw [st] at st1
    cases st1
    exact ⟨rfl, Option.some.inj (E.hs.symm.trans hs1)⟩
  obtain ⟨rfl, rfl⟩ := same
  have high : (loopState s l).mode ≤ DICTID := by
    show s.mode ≤ DICTID
    rw [mode]
    decide
  obtain ⟨bytes, rfl⟩ := MeaningDictid.stage_of_header stageM high
  obtain ⟨⟨_, headC, _, _, _, wrappedC, last0, total0, _⟩, _, dictC⟩ := wrapM
  obtain ⟨bytesNil, _, width0⟩ := headC mode
  subst bytesNil
  have wrapped : f.wrap ≠ .raw := by rw [auto]; decide
  obtain ⟨havedict0, wsize0, whave0⟩ := wrappedC wrapped
  have dictNil : f.dict = [] := dictC.resolve_right wrapped
  have outNil : f.logOut ++ callOut = [] := outputEq.symm
  obtain ⟨logNil, callNil⟩ := List.append_eq_nil_iff.mp outNil
  subst callNil
  have pend0 : loopPending l = 0 := by
    have := pend.1
    simp only [List.length_nil] at this
    omega
  have notGzip := zlib_head_not_gzip ok
  have width := zlib_head_width (l := l) wire ok window width0
  have views := MeaningDictid.sameViews_put h r { z with adler := 1 } zs (headDefaultState s l)
  have binv2 := binv.byte_views (fun ref => (views ref).1)
  have bitsNew : bytesToBits (f.logIn ++ f.inp.take (loopRead l)) = bytesToBits [cmf, flg] ++ [] := by
    rw [List.append_nil, input]
  have modeEq := zlib_head_mode (l := l) wire
  by_cases plain : flg.toNat / 32 % 2 = 0
  · have modeT : headDefaultMode l = TYPE := by rw [modeEq, ite_eq_left plain]
    refine ⟨zs, headDefaultState s l, [], bytesToBits [cmf, flg], [],
      .body [cmf, flg] ⟨[], false, .boundary⟩, E.st, setI_istates_same _ _ _, retOk,
      zlib_head_config config, haveLe, inLen, ⟨binv2.have_eq, binv2.next, by simp⟩, leftLe,
      ⟨Nat.le_of_eq pend0, fun _ _ _ => pend0⟩, putEq, views.bytes outBytes,
      views.writable writable, sepIn, sepWin, sepOutIn, bitsNew, ⟨rfl, rfl⟩,
      wrapParsed_zlib_body (Or.inr auto) ok fits plain,
      ⟨⟨Or.inl modeT, rfl, last0, by show (0 : UInt32).toNat < 8; decide⟩,
        Or.inr ⟨wsize0, whave0, by rw [dictNil, logNil] <;> rfl⟩, ?_⟩,
      ⟨?_, width, Or.inl dictNil⟩, by rw [logNil] <;> rfl⟩
    · refine ⟨?_, fun _ => ?_⟩
      · rw [logNil]
        simp only [List.append_nil, List.take_nil, List.length_nil]
        exact total0
      · show (1 : UInt64) = _
        rw [logNil, auto]
        split
        · rename_i gz
          exfalso
          rcases gz with g | ⟨_, g⟩
          · cases g
          · exact notGzip g
        · simp only [List.append_nil, List.take_nil] <;> decide
    · show FlagsMatch _ f.wrap _
      rw [auto]
      unfold FlagsMatch
      rw [ite_eq_right (show ¬ (Api.Wrap.auto = Api.Wrap.raw) by decide), ite_eq_right notGzip] <;> rfl
  · have fdict : flg.toNat / 32 % 2 = 1 := by omega
    have modeD : headDefaultMode l = DICTID := by rw [modeEq, ite_eq_right plain]
    refine ⟨zs, headDefaultState s l, [], bytesToBits [cmf, flg], [], .header [cmf, flg], E.st,
      setI_istates_same _ _ _, retOk, zlib_head_config config, haveLe, inLen,
      ⟨binv2.have_eq, binv2.next, by simp⟩, leftLe,
      ⟨Nat.le_of_eq pend0, fun _ _ e => by cases e⟩, putEq, views.bytes outBytes,
      views.writable writable, sepIn, sepWin, sepOutIn, bitsNew, ⟨rfl, rfl⟩,
      wrapParsed_zlib_fdict (Or.inr auto) ok fits fdict, ?_,
      ⟨?_, Or.inr ⟨wsize0, whave0, by rw [dictNil] <;> rfl⟩, Or.inl dictNil⟩, by rw [logNil] <;> rfl⟩
    · show HEAD ≤ headDefaultMode l ∧ headDefaultMode l ≤ DICTID
      rw [modeD]
      decide
    · refine ⟨fun raw => absurd raw wrapped, fun m => ?_,
        fun _ => ⟨rfl, notGzip, rfl, by show (0 : UInt32).toNat ≤ 32; decide, width, fdict⟩,
        fun m => ?_, fun _ hi => ?_, fun _ => ⟨havedict0, wsize0, whave0⟩, last0, total0,
        fun raw => absurd raw wrapped⟩
      · have m' : headDefaultMode l = HEAD := m
        rw [modeD] at m'
        exact absurd m' (by decide)
      · have m' : headDefaultMode l = FLAGS := m
        rw [modeD] at m'
        exact absurd m' (by decide)
      · have hi' : headDefaultMode l ≤ HCRC := hi
        rw [modeD] at hi'
        exact absurd hi' (by decide)

end Zlib.Inflate.Proofs.MeaningHeadGzip

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs.MeaningHeadZlib Zlib.Inflate.Proofs.MeaningHeadGzip
set_option autoImplicit false

/-- `HEAD` with gzip or automatic detection, every configured window (0 and 8 to 15): the
short-input leave, the gzip magic to `FLAGS`, for automatic detection the accepted zlib header
(the body, or `DICTID` with `FDICT`), and each rejection as `LoopBad`. -/
theorem trip_head_gzip : TripHeadGzip := by
  intro c f r gzipLike h l side loop head
  obtain ⟨zs, z, s, strm, st, inv, _, loc, _, apart⟩ := side
  have E : Env c h r zs z s := ⟨strm, st, inv.good.live.hz, inv.good.live.hs⟩
  have mode : s.mode = HEAD := head zs s st E.hs
  have window : HeadWindow s := inv.toDefaultDecodeJ.headWindow
  obtain ⟨wrapEq, headNone, width0, widthCfg⟩ := head_entry loop st E.hs mode
  obtain ⟨aligned, small, _, _, _⟩ := zlib_head_loop_entry loop head
  have wrapped : f.wrap ≠ .raw := by rcases gzipLike with e | e <;> rw [e] <;> decide
  have nonzero : (s.wrap == 0) = false := by
    rw [wrapEq]
    rcases gzipLike with e | e <;> rw [e] <;> rfl
  have gzipBit : (s.wrap &&& 2) ≠ 0 := by
    rw [wrapEq]
    rcases gzipLike with e | e <;> rw [e] <;> decide
  obtain ⟨result, l', j, needRun, _, _, bitsCount, enough, leaveFacts, kinds, bitsMax, loopAt⟩ :=
    MeaningBits.LoopMatches.needbits_at loop (ok := fun n => n ≤ 16)
      (fun zs' s' _ _ st' hs' stageM' wrapM' hold bits okb => by
        have mode' : s'.mode = HEAD := head zs' s' st' hs'
        have high : (loopState s' l).mode ≤ DICTID := by
          show s'.mode ≤ DICTID
          rw [mode']
          decide
        obtain ⟨bytes, rfl⟩ := MeaningDictid.stage_of_header stageM' high
        exact zlib_head_bits stageM' wrapM' mode' wrapped hold bits okb) 16 (by decide)
  -- The input cursor after `NEEDBITS(16)` stays in the input block, so `hbuf` stays apart.
  have apart' : HbufInputApart c l' := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, binvL, _⟩ := loop
    obtain ⟨r2, l2, j2, run2, jle, binv2, _, _, _, _, _, _, _, _, next2⟩ :=
      NEEDBITS_run_cursor binvL 16 (by decide)
    have lEq : l2 = l' := (Prod.mk.inj (Prod.mk.inj (Except.ok.inj (run2.symm.trans needRun))).1).2
    subst lEq
    have count : l2.have_.toNat + j2 = l.have_.toNat := by
      have before := binvL.have_eq
      have after := binv2.have_eq
      rw [List.length_drop] at after
      omega
    exact apart.advance next2 count
  have n16 : (16 : UInt32).toNat = 16 := rfl
  rcases kinds with rfl | rfl
  · have atLeast := enough rfl
    rw [n16] at atLeast bitsMax
    have bits16 : l'.bits.toNat = 16 := by omega
    have loop' := loopAt (show l'.bits.toNat ≤ 16 by omega)
    obtain ⟨cmf, flg, input, wire, _, _⟩ := zlib_head_observation loop' head (by omega)
    have prefixRun : runX (inflate_dispatch c) l h = runX (headAfterBits c) l' h := by
      rw [inflate_dispatch_HEAD E l mode, inflate_HEAD_split, runX_bind, runX_rdS E]
      simp only [nonzero, Bool.false_eq_true, ↓reduceIte]
      rw [runX_bind, needRun]
    by_cases magic : l'.hold = 0x8b1f
    · obtain ⟨cmfEq, flgEq⟩ := (magic_bytes wire).mp magic
      subst cmfEq flgEq
      have local_ := loc (by rw [mode]; decide) (by rw [mode]; decide)
      obtain ⟨b, a, hbufAt, bytes, size, writable⟩ := local_.hbuf
      have statics : Zlib.Crc32.Proofs.StaticsOK h := by
        unfold Zlib.Crc32.Proofs.StaticsOK
        rw [inv.globals]
        exact ⟨rfl, rfl⟩
      have run := prefixRun.trans
        (headAfterBits_gzip E l' hbufAt bytes size writable statics gzipBit magic)
      exact ⟨_, _, _, run, Or.inl (Or.inl ⟨rfl, Or.inl
        (gzip_head_magic loop' E mode gzipLike inv hbufAt bytes writable apart' input magic)⟩)⟩
    · have notMagicB : ((s.wrap &&& 2) != 0 && l'.hold == 0x8b1f) = false := by simp [magic]
      have notMagic : ¬ (cmf = 31 ∧ flg = 139) := fun both => magic ((magic_bytes wire).mpr both)
      have run0 := prefixRun.trans (headAfterBits_zlib E l' notMagicB
        (by intro i e; rw [headNone] at e; cases e))
      rw [headNone] at run0
      change runX (inflate_dispatch c) l h = runX (headDefaultCheck c s l') l' h at run0
      rcases gzipLike with gz | auto
      · have bit : ((s.wrap &&& 1) == 0) = true := by rw [wrapEq, gz]; decide
        have hdr : headHeaderRejected s l' = true := by
          unfold headHeaderRejected
          rw [bit]
          rfl
        obtain ⟨i, badRun⟩ := headDefaultCheck_bad_header E l' hdr
        have doomed : LoopDoomed f l' := head_doomed wrapped input notMagic
          (fun zl => by rw [gz] at zl; rcases zl with g | g <;> cases g)
        exact ⟨_, _, _, run0.trans badRun, Or.inl (Or.inl ⟨rfl, Or.inr
          (head_bad loop' st E.hs doomed (Or.inl rfl))⟩)⟩
      · have wrap7 : s.wrap = 7 := by rw [wrapEq, auto]; rfl
        have lenEq := zlib_head_window_length (l := l') wire
        by_cases valid : ZlibF.Spec.Zlib.HeaderOK cmf flg ∧
            ZlibF.Spec.Api.ZlibFits f.configured [cmf, flg]
        · obtain ⟨hdr, meth, len15⟩ := auto_head_checks_pass (s := s) wire wrap7 valid.1
          have accRun : runX (headDefaultCheck c s l') l' h =
              .ok ((.ok (), { headWindowRegs l' with hold := 0, bits := 0 }),
                setI (r.put h { z with adler := 1 }) zs (headDefaultState s l')) := by
            by_cases z0 : s.wbits = 0
            · exact headDefaultCheck_accept_zero E l' hdr meth z0 len15
            · have range := window.resolve_right (fun e => z0 e.1)
              have cfgNZ : f.configured ≠ 0 := fun e => z0 (width0 e)
              have w := widthCfg cfgNZ
              have fitsLe := zlib_fits_le valid.2 cfgNZ
              exact headDefaultCheck_accept E l' hdr meth (by omega) range
          exact ⟨_, _, _, run0.trans accRun, Or.inl (Or.inl ⟨rfl, Or.inl
            (auto_head_accepted loop' E mode auto window wire input valid.1 valid.2)⟩)⟩
        · have doomed : LoopDoomed f l' := head_doomed wrapped input notMagic (fun _ => valid)
          obtain ⟨regs, i, badRun, regsEq⟩ : ∃ (regs : IL) (i : Nat),
              runX (headDefaultCheck c s l') l' h = .ok ((.ok (), regs), badHeap h r zs z s i) ∧
                (regs = l' ∨ regs = headWindowRegs l') := by
            by_cases hdr : headHeaderRejected s l' = true
            · obtain ⟨i, run⟩ := headDefaultCheck_bad_header E l' hdr
              exact ⟨_, i, run, Or.inl rfl⟩
            have hdrF : headHeaderRejected s l' = false := by simpa using hdr
            by_cases meth : headMethodRejected l' = true
            · obtain ⟨i, run⟩ := headDefaultCheck_bad_method E l' hdrF meth
              exact ⟨_, i, run, Or.inl rfl⟩
            have methF : headMethodRejected l' = false := by simpa using meth
            by_cases z0 : s.wbits = 0
            · by_cases big : 15 < (headWindowRegs l').len.toNat
              · obtain ⟨i, run⟩ := headDefaultCheck_bad_window_zero E l' hdrF methF big
                exact ⟨_, i, run, Or.inr rfl⟩
              · exfalso
                apply valid
                refine ⟨zlib_head_format wire hdrF methF (by omega), ?_⟩
                by_cases cz : f.configured = 0
                · exact Or.inl cz
                · have w := widthCfg cz
                  have zz : (0 : UInt32).toNat = 0 := rfl
                  rw [z0, zz] at w
                  exact absurd w.symm cz
            · by_cases wide : s.wbits.toNat < (headWindowRegs l').len.toNat
              · obtain ⟨i, run⟩ := headDefaultCheck_bad_window E l' hdrF methF z0 wide
                exact ⟨_, i, run, Or.inr rfl⟩
              · exfalso
                apply valid
                have range := window.resolve_right (fun e => z0 e.1)
                have cfgNZ : f.configured ≠ 0 := fun e => z0 (width0 e)
                have w := widthCfg cfgNZ
                refine ⟨zlib_head_format wire hdrF methF (by omega), Or.inr ⟨cmf, rfl, by omega⟩⟩
          exact ⟨_, _, _, run0.trans badRun, Or.inl (Or.inl ⟨rfl, Or.inr
            (head_bad loop' st E.hs doomed regsEq)⟩)⟩
  · have below := (leaveFacts rfl).2
    rw [n16] at below
    have leaveRun : runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, l'), h) := by
      rw [inflate_dispatch_HEAD E l mode, inflate_HEAD_split, runX_bind, runX_rdS E]
      simp only [nonzero, Bool.false_eq_true, ↓reduceIte]
      rw [runX_bind, needRun]
    exact ⟨_, _, _, leaveRun, Or.inl (Or.inr ⟨rfl, Or.inl (loopAt (show l'.bits.toNat ≤ 16 by omega))⟩)⟩

#print axioms trip_head_gzip

end Zlib.Inflate.Proofs
