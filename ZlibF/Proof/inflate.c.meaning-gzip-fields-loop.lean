import ZlibF.Proof.«inflate.c.meaning-trip»
import ZlibF.Proof.«inflate.c.meaning-dictid»
import ZlibF.Proof.«inflate.c.meaning-accept»
import ZlibF.Proof.«inflate.c.meaning-fields»
import ZlibF.Proof.«inflate.c.stored-views»
import ZlibF.Math.«inflate-meaning-wrap»
import ZlibF.Proof.«inflate.c.gzip-header-dispatch»

/-!
# inflate.c: the loop meaning inside a gzip header (`GzAt`)

Interface of the gzip header field rows (`inflate.c.meaning-gzip-fields*`). Inside a gzip header
the loop meaning `LoopMatches` has a simple shape: no output, the input read so far is the header
bytes `bytes` followed by the bytes `rest` held in the bit buffer, and the decoder state matches
`HeaderMatches`. `GzAt` names these facts; `GzAt.loop` and `GzAt.of_loop` go between the two.

The heap changes of the header modes are writes of the state and stream records and of the local
`hbuf`. They keep the sizes and the writability of every byte view and the bytes of the unread
input (`InputKept`); the `hbuf` writes need `HbufInputApart` of the trip.
-/

namespace Zlib.Inflate.Proofs.MeaningGzipFields
open C Zlib.Inflate Zlib.Inflate.Proofs Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs.MeaningBits Zlib.Inflate.Proofs.MeaningFields
set_option autoImplicit false

/-! ## Heap changes that keep the unread input -/

/-- The heap `h'` keeps the size and the writability of every byte view of `h`, and the bytes of
the view that holds the unread input of `l`. -/
def InputKept (h h' : Heap) (l : IL) : Prop :=
  ByteViewSizes h h' ∧ (∀ ref : BRef, Space.ro h' ref = Space.ro h ref) ∧
  (l.have_ ≠ 0 → ∀ (ref : BRef) (off : Nat), l.next = .ref ref off →
    (Space.get h' ref : Option (Array UInt8)) = Space.get h ref)

theorem InputKept.refl (h : Heap) (l : IL) : InputKept h h l :=
  ⟨ByteViewSizes.refl h, fun _ => rfl, fun _ _ _ _ => rfl⟩

theorem InputKept.trans {h1 h2 h3 : Heap} {l : IL} (a : InputKept h1 h2 l) (b : InputKept h2 h3 l) :
    InputKept h1 h3 l :=
  ⟨a.1.trans b.1, fun ref => (b.2.1 ref).trans (a.2.1 ref),
    fun ne ref off p => (b.2.2 ne ref off p).trans (a.2.2 ne ref off p)⟩

theorem InputKept.setI (h : Heap) (zs : Nat) (s : InflateState) (l : IL) :
    InputKept h (Zlib.Inflate.Spec.setI h zs s) l :=
  ⟨byte_view_sizes_setI h zs s, byte_view_ro_setI h zs s, fun _ ref _ _ => byte_view_get_setI h zs s ref⟩

theorem InputKept.stream (h : Heap) (r : ZStreamRef) (z : ZStream) (l : IL) :
    InputKept h (r.put h z) l :=
  ⟨byte_view_sizes_stream_put h r z, byte_view_ro_stream_put h r z,
    fun _ ref _ _ => byte_view_get_stream_put h r z ref⟩

/-- A write of the local `hbuf`, which is apart from the unread input. -/
theorem InputKept.hbuf {c : Ctx} {l : IL} {h : Heap} {b : Nat} {a a' : Array UInt8}
    (apart : HbufInputApart c l) (hb : c.hbuf = .ref (.blk b) 0) (get : h.bytes b = some a)
    (ro : h.ro b = false) (size : a'.size = a.size) :
    InputKept h (Space.put h (BRef.blk b) a') l := by
  refine ⟨byte_view_sizes_put (dest := BRef.blk b) (old := a) get ro a' size,
    byte_view_ro_write h (BRef.blk b) a', ?_⟩
  intro ne ref off p
  exact byte_view_get_put_ne h (apart ne b 0 ref off hb p) a'

/-- `InputKept` only looks at the input pointer and count. -/
theorem InputKept.regs {h h' : Heap} {l l' : IL} (keep : InputKept h h' l) (next : l'.next = l.next)
    (count : l'.have_ = l.have_) : InputKept h h' l' :=
  ⟨keep.1, keep.2.1, fun ne ref off p => keep.2.2 (count ▸ ne) ref off (next ▸ p)⟩

theorem InputKept.binv {h h' : Heap} {l : IL} {bs : List UInt8} (keep : InputKept h h' l)
    (inv : BitInv h l bs) : BitInv h' l bs := by
  refine ⟨inv.have_eq, ?_, inv.hold_lt⟩
  rcases inv.next with empty | ⟨ref, a, off, p, get, fit, content⟩
  · exact Or.inl empty
  · by_cases zero : l.have_ = 0
    · left
      have count := inv.have_eq
      rw [zero] at count
      exact List.eq_nil_of_length_eq_zero (by simpa using count.symm)
    · exact Or.inr ⟨ref, a, off, p, by rw [keep.2.2 zero ref off p]; exact get, fit, content⟩

theorem InputKept.bytes0 {h h' : Heap} {l : IL} (keep : InputKept h h' l) {p : BPtr}
    (view : Bytes h p 0 []) : Bytes h' p 0 [] := by
  rcases view with null | ⟨r, i, a, ptr, get, fits, _⟩
  · exact Or.inl null
  · obtain ⟨a', get', size⟩ := keep.1.view get
    exact Or.inr ⟨r, i, a', ptr, get', by omega, by simp⟩

theorem InputKept.writable {h h' : Heap} {l : IL} (keep : InputKept h h' l) {p : BPtr} {n : Nat}
    (w : Writable h p n) : Writable h' p n := by
  rcases w with null | ⟨r, i, a, ptr, get, ro, fits⟩
  · exact Or.inl null
  · obtain ⟨a', get', size⟩ := keep.1.view get
    exact Or.inr ⟨r, i, a', ptr, get', by rw [keep.2.1 r]; exact ro, by omega⟩

/-! ## The loop meaning inside a gzip header -/

/-- `LoopMatches` at the header stage `bytes` of a gzip or automatic configuration, with the bytes
`rest` held in the bit buffer. -/
structure GzAt (c : Ctx) (f : LoopFrame) (h : Heap) (l : IL) (zs : Nat) (s : InflateState)
    (bytes rest : List UInt8) : Prop where
  st : c.st = some (.tab zs)
  hs : h.istates zs = some s
  ret : l.ret = Z_OK
  config : ConfigMatches (loopState s l) f.wrap f.configured
  haveLe : l.have_.toNat ≤ l.in_.toNat
  inLen : l.in_.toNat = f.inp.length
  binv : BitInv h l (f.inp.drop (loopRead l))
  leftLe : l.left.toNat ≤ l.out_.toNat
  pend : loopPending l = 0
  put : l.put = f.start
  outBytes : Bytes h f.start 0 []
  writable : Writable h l.put l.left.toNat
  sepIn : Separate l.put l.left.toNat l.next l.have_.toNat
  sepWin : Separate l.put l.left.toNat s.window s.wsize.toNat
  logOut : f.logOut = []
  input : f.logIn ++ f.inp.take (loopRead l) = bytes ++ rest
  bits : l.bits.toNat = 8 * rest.length
  hold : l.hold.toNat = leValue rest
  viable : GzipViable bytes
  range : HEAD ≤ s.mode ∧ s.mode ≤ DICTID
  hm : HeaderMatches (loopState s l) f.wrap f.configured bytes
  dict : f.dict = []
  gz : f.wrap = .gzip ∨ f.wrap = .auto

theorem GzAt.wrapped {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {zs : Nat} {s : InflateState}
    {bytes rest : List UInt8} (g : GzAt c f h l zs s bytes rest) : f.wrap ≠ .raw := by
  rcases g.gz with e | e <;> rw [e] <;> decide

theorem GzAt.loop {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {zs : Nat} {s : InflateState}
    {bytes rest : List UInt8} (g : GzAt c f h l zs s bytes rest) (short : GzipShort bytes) :
    LoopMatches c f h l := by
  have wrappedC := g.hm.2.2.2.2.2.1 g.wrapped
  refine ⟨zs, s, [], bytesToBits bytes, bytesToBits rest, .header bytes, g.st, g.hs, g.ret, g.config,
    g.haveLe, g.inLen, g.binv, g.leftLe, ⟨by rw [g.pend]; simp, fun _ _ e => by cases e⟩,
    by rw [g.put]; exact (inputAdvance_zero f.start).symm, g.outBytes, g.writable, g.sepIn, g.sepWin,
    Or.inl rfl, by rw [g.input, bytesToBits_append'], ⟨?_, ?_⟩, wrapParsed_gzip_header g.gz g.viable short, g.range,
    ⟨g.hm, Or.inr ⟨wrappedC.2.1, wrappedC.2.2, by rw [g.dict]; rfl⟩, Or.inl g.dict⟩,
    by rw [g.logOut]; rfl⟩
  · rw [bytesToBits_length']
    show 8 * rest.length = l.bits.toNat
    rw [g.bits]
  · show l.hold.toNat = heldValue (bytesToBits rest)
    rw [heldValue_bytesToBits, g.hold]

theorem flags_or_time {m : UInt32} (range : FLAGS ≤ m ∧ m ≤ HCRC) : m = FLAGS ∨ (TIME ≤ m ∧ m ≤ HCRC) := by
  rcases gzip_header_mode_cases range with e | e | e | e | e | e | e | e <;>
    first | exact Or.inl e | (right; rw [e]; decide)

/-- A gzip beginning of a header stage begins a complete gzip header. -/
theorem viable_of_parsed {wrap : Api.Wrap} {configured : Nat} {dict bytes : List UInt8}
    (gz : wrap = .gzip ∨ wrap = .auto) (gzb : IsGzipHeader bytes)
    (parsed : WrapParsed wrap configured dict (bytesToBits bytes) (.header bytes)) : GzipViable bytes := by
  obtain ⟨_, more, bodyDict, wh, _⟩ := parsed
  have len : 2 ≤ bytes.length := by
    have := congrArg List.length gzb
    simp at this
    omega
  have gzm : IsGzipHeader (bytes ++ more) := by
    unfold IsGzipHeader at gzb ⊢
    rw [List.take_append_of_le_length len]
    exact gzb
  have gh : GzipHeader (bytes ++ more) := by
    rcases gz with rfl | rfl
    · exact wh.1
    · rcases wh with ⟨window, zh, _⟩ | ⟨gh, _⟩
      · exact absurd gzm (zlibHeader_not_gzip zh)
      · exact gh
  exact ⟨_, gzipHeader_iff.mp gh, List.prefix_append _ _⟩

/-- In the loop, a gzip configuration in a header field mode has the shape `GzAt`. -/
theorem GzAt.of_loop {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {zs : Nat} {s : InflateState}
    (loop : LoopMatches c f h l) (st : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (range : FLAGS ≤ s.mode ∧ s.mode ≤ HCRC) (gz : f.wrap = .gzip ∨ f.wrap = .auto) :
    ∃ bytes rest, GzAt c f h l zs s bytes rest := by
  have high : s.mode ≤ DICTID := UInt32.le_trans range.2 (by decide)
  obtain ⟨zs1, s1, callOut, consumed, held, stage, st1, hs1, retOk, config, haveLe, inLen, binv,
    leftLe, pend, putEq, outBytes, writable, sepIn, sepWin, _, bitsEq, heldBits, parsed,
    stageM, wrapM, outputEq⟩ := loop
  have same : zs1 = zs ∧ s1 = s := by
    rw [st] at st1
    cases st1
    exact ⟨rfl, Option.some.inj (hs1.symm.trans hs)⟩
  obtain ⟨rfl, rfl⟩ := same
  obtain ⟨bytes, rfl⟩ := MeaningDictid.stage_of_header stageM high
  have outNil : f.logOut ++ callOut = [] := outputEq.symm
  obtain ⟨logNil, callNil⟩ := List.append_eq_nil_iff.mp outNil
  subst callNil
  have pend0 : loopPending l = 0 := by
    have := pend.1
    simp only [List.length_nil] at this
    omega
  have consumedEq : consumed = bytesToBits bytes := parsed.1
  subst consumedEq
  have aligned : held.length % 8 = 0 := by
    have lengths := congrArg List.length bitsEq
    simp only [List.length_append, bytesToBits_length'] at lengths
    omega
  obtain ⟨m, inputEq, heldEq⟩ := bytesToBits_middle (input := f.logIn ++ f.inp.take (loopRead l))
    (a := bytes) (c := []) (X := held) (by simpa [bytesToBits] using bitsEq) aligned
  subst heldEq
  have wrapped : f.wrap ≠ .raw := by rcases gz with e | e <;> rw [e] <;> decide
  have gzb : IsGzipHeader bytes := by
    rcases flags_or_time range with mf | ⟨lo, hi⟩
    · rw [(wrapM.1.2.2.2.1 mf).1]; rfl
    · exact (wrapM.1.2.2.2.2.1 lo hi).1
  refine ⟨bytes, m, ⟨st, hs, retOk, config, haveLe, inLen, binv, leftLe, pend0,
    by rw [putEq]; exact inputAdvance_zero f.start, outBytes, writable, sepIn, sepWin, logNil,
    by simpa using inputEq, ?_, ?_, viable_of_parsed gz gzb parsed, stageM, wrapM.1, wrapM.2.2.resolve_right wrapped, gz⟩⟩
  · have := heldBits.1
    rw [bytesToBits_length'] at this
    exact this.symm
  · have := heldBits.2
    change l.hold.toNat = heldValue (bytesToBits m) at this
    rw [this, heldValue_bytesToBits]

/-! ## Facts of the configuration -/

theorem GzAt.wrapCode {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {zs : Nat} {s : InflateState}
    {bytes rest : List UInt8} (g : GzAt c f h l zs s bytes rest) : s.wrap = 6 ∨ s.wrap = 7 := by
  have e : s.wrap = Zlib.Inflate.Proofs.wrapCode f.wrap := g.config.1
  rcases g.gz with w | w <;> rw [w] at e
  · exact Or.inl e
  · exact Or.inr e

theorem GzAt.wrap4 {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {zs : Nat} {s : InflateState}
    {bytes rest : List UInt8} (g : GzAt c f h l zs s bytes rest) : (s.wrap &&& 4 != 0) = true := by
  rcases g.wrapCode with e | e <;> rw [e] <;> decide

theorem GzAt.head {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {zs : Nat} {s : InflateState}
    {bytes rest : List UInt8} (g : GzAt c f h l zs s bytes rest) : s.head = none :=
  g.config.2.2.1

/-! ## A gzip stream of a gzip or automatic configuration -/

/-- A stream of a gzip or automatic configuration that begins with the gzip magic is a gzip
member. -/
theorem layer_gzip_member {wrap : Api.Wrap} {configured : Nat} {dict source out P : List UInt8}
    (gz : wrap = .gzip ∨ wrap = .auto) (valid : Api.Layer.Decodes wrap configured dict source out)
    (magic : [31, 139] <+: P) (pre : P <+: source) : Gzip.Decodes source out := by
  rcases gz with rfl | rfl
  · exact valid
  · rcases valid with ⟨member, fits⟩ | member
    · exfalso
      rcases layerDecodes_head (wrap := .zlib) ⟨member, fits⟩ (magic.trans pre) (by decide) with
        ⟨g, _⟩ | ⟨_, ok, _⟩
      · rcases g with g | g <;> cases g
      · have := ok.1
        revert this
        decide
    · exact member

/-- The read input has no completion when no gzip member begins with it. -/
theorem gz_doomed {f : LoopFrame} {l : IL} {P : List UInt8} (gz : f.wrap = .gzip ∨ f.wrap = .auto)
    (input : f.logIn ++ f.inp.take (loopRead l) = P) (magic : [31, 139] <+: P)
    (none : ∀ source out, Gzip.Decodes source out → ¬ P <+: source) : LoopDoomed f l := by
  intro source decoded valid _ pre
  rw [input] at pre
  exact none source decoded (layer_gzip_member gz valid magic pre) pre

/-- `BAD` after a rejected header byte. -/
theorem GzAt.bad {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {zs : Nat} {s : InflateState}
    {bytes rest : List UInt8} (g : GzAt c f h l zs s bytes rest) {h' : Heap} {l' : IL}
    {s' : InflateState} (hs' : h'.istates zs = some s') (mode : s'.mode = BAD)
    (same : s'.wrap = s.wrap ∧ s'.reqwrap = s.reqwrap ∧ s'.head = s.head ∧ s'.reqbits = s.reqbits ∧
      s'.wbits = s.wbits)
    (regs : l'.in_ = l.in_ ∧ l'.have_ = l.have_) (doomed : LoopDoomed f l') :
    LoopBad c f h' l' := by
  obtain ⟨c1, c2, c3, c4, c5, _⟩ := g.config
  obtain ⟨w, rw', hd, rb, wb⟩ := same
  refine ⟨zs, s', g.st, hs', mode, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, doomed⟩
  · show s'.wrap = _; rw [w]; exact c1
  · show s'.reqwrap = s'.wrap; rw [rw', w]; exact c2
  · show s'.head = none; rw [hd]; exact c3
  · show s'.reqbits.toNat = _; rw [rb]; exact c4
  · intro nz; show s'.wbits.toNat = _; rw [wb]; exact c5 nz
  · show s'.mode ≠ SYNC; rw [mode]; decide
  · rw [regs.1, regs.2]; exact g.haveLe
  · rw [regs.1]; exact g.inLen

#print axioms GzAt.loop
#print axioms GzAt.of_loop
#print axioms gz_doomed

end Zlib.Inflate.Proofs.MeaningGzipFields
