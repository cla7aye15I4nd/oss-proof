import ZlibNgF.Proof.«inflate.c.decode-modes»
import ZlibNgF.Proof.«adler32_c.c.safety»

/-!
# The modes `CHECK`, `LENGTH` of `inflate`, and one trip of its loop (`ZlibNgF`)

`CHECK` adds the output of the call so far to the totals and, when the check is on, to the check value with
`inf_chksum` (`crc32_braid` or `adler32_c` over the bytes written since `out` was last reset), then compares the
trailer; `LENGTH` compares the gzip length trailer. Between `out = out - left` and `out = left` the locals do not
satisfy the loop invariant, so the stores in between are followed with the invariant of the locals before them.
`tripOK`: one trip of the loop from every mode (`trip_of_modes`).
-/

set_option autoImplicit false
namespace ZlibNgF.Proof.InflateLoop
open C ZlibNgF.Spec ZlibNg.Inflate
open ZlibNgF.Proof.InflateInv (Inv Core view ModeOK DecodeMode)
open ZlibNgF.Proof.InflateX
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.mono Sat.of_eq St Touch)

theorem rank_LENGTH : rank LENGTH = 1 := by decide
theorem rank_DONE : rank DONE = 0 := by decide

theorem run_LENGTH (E : Env) (eo : EnvOK E) : ModeRun E inflate_LENGTH (·.mode = LENGTH) := by
  intro l H z S li hm m hμ
  unfold inflate_LENGTH
  refine SatX.bind (SatX.lift_eq li.ldState ?_)
  have hμ' : 32 * (8 * l.have_.toNat + l.bits.toNat + l.left.toNat) + 1 ≤ m := by
    unfold μ at hμ; rwa [hm, rank_LENGTH] at hμ
  dsimp (config := { zeta := false }) only
  extract_lets jp
  have hjp : ∀ (u : PUnit) (l' : IL) (H' : Heap) (z' : ZStream) (S' : InflateState), LI E l' H' z' S' →
      S'.mode = LENGTH → SatX H' l' (jp u) (Post E m) := by
    intro u l' H' z' S' li' hS'
    simp only [jp]
    refine SatX.bind (SatX.lift (Sat.mono (li'.setQuiet DONE (by decide) (by decide) (Or.inr (by decide))) ?_))
    intro _ H1 li1
    unfold inflate_DONE
    refine SatX.bind (SatX.modify ?_)
    have li2 := li1.setRet Z_STREAM_END (by decide)
    exact SatX.throw ⟨⟨_, _, li2⟩, Why.ret (show Z_STREAM_END ≠ Z_OK by decide) (li2.frLEnd rfl)⟩
  clear_value jp
  split
  · refine needbits_then eo li 32 (by decide) ?_
    intro l1 li1 h32 hleft hT
    refine SatX.bind (SatX.lift_eq li1.ldState ?_)
    refine SatX.bind (SatX.get ?_)
    dsimp (config := { zeta := false }) only
    split
    · exact bad_ok li1 (by rw [hleft]; omega) "incorrect length check" (strIdx 14 (by decide) (by decide) (by decide))
    · refine SatX.bind (initbits_ok ?_)
      exact hjp _ _ _ _ _ (li1.setBits (l' := { l1 with hold := 0, bits := 0 }) rfl rfl rfl rfl rfl (show (0 : UInt8) ≤ 39 by decide)) hm
  · exact hjp _ _ _ _ _ li hm

/-- `out = left`: the output position is the start of the room left. -/
theorem LI.resetOut {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (li : LI E l H z S) (l' : IL)
    (h1 : l'.next = l.next) (h2 : l'.have_ = l.have_) (h3 : l'.put = l.put) (h4 : l'.out = l'.left)
    (h5 : l'.left = l.left) (h6 : l'.bits = l.bits) (hr : rank S.mode ≤ 2) (h7 : l'.in_ = l.in_ := by rfl)
    (h8 : l'.ret = l.ret := by rfl) : LI E l' H z S := by
  obtain ⟨p, hp, hp1, hp2⟩ := li.outPos
  refine ⟨li.inv, li.frame, li.sz, li.hz, li.hb, li.hs, li.head, li.hdr, by rw [h1, h2]; exact li.inAt, ?_,
    by rw [h6]; exact li.bits, by rw [h7]; exact li.inn, Or.inr hr, by rw [h8]; exact li.retB, li.sacc, li.msgK,
    li.fr.mono h2 fun ⟨a, b, c, d⟩ => ⟨h6 ▸ a, b, c, h8 ▸ d⟩⟩
  refine ⟨by rw [h4]; exact UInt32.le_refl _, p, hp1, by rw [h4, h5]; exact hp2, ?_⟩
  rw [h3, hp, h4, UInt32.sub_self]; rfl

/-- `inf_chksum(strm, src, len)` over `len` readable bytes: the check value of the state and `adler` change. -/
theorem LI.chksum {E : Env} (eo : EnvOK E) {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (li : LI E l H z S)
    {r : BRef} {o : Nat} {d : Array UInt8} (hg : Space.get H r = some d) (len : UInt32)
    (hle : o + len.toNat ≤ d.size) :
    Sat H (inf_chksum (some E.i) (.ref r o) len) (fun _ H' => ∃ v : UInt32,
      LI E l H' { z with adler := v.toUInt64 } { S with check := v.toUInt64 }) := by
  have hc : H.crcTable = ZlibNg.Crc32Tbl.crc_table := li.frame.2.2.2.2.2.2.1.trans eo.crc
  unfold inf_chksum
  have hso : ZlibNg.Inflate.stateOf (some E.i) H = .ok (some E.b, H) := by
    simp [ZlibNg.Inflate.stateOf, rdZ, bind_app, li.ldStream, li.hb]
  refine Sat.bind (Sat.of_eq hso ?_)
  refine Sat.bind (Sat.of_eq li.ldState ?_)
  have hlen : o + len.toUInt64.toNat ≤ d.size := by rw [UInt32.toNat_toUInt64]; exact hle
  extract_lets jp
  have hjp : ∀ v : UInt32, Sat H (jp v) (fun _ H' => ∃ v : UInt32,
      LI E l H' { z with adler := v.toUInt64 } { S with check := v.toUInt64 }) := by
    intro v
    simp only [jp]
    refine Sat.bind (Sat.mono (li.wrS (fun s => { s with check := v.toUInt64 }) (fun _ _ c => c) rfl) ?_)
    intro _ H1 li1
    exact Sat.mono (li1.wrZ (fun z => { z with adler := v.toUInt64 }) rfl rfl rfl) (fun _ _ li2 => ⟨v, li2⟩)
  clear_value jp
  split
  · obtain ⟨v, e, -⟩ := ZlibNgF.Proof.Crc32.crc32_braid_ok hc hg S.check.toUInt32 o len.toUInt64 hlen
    exact Sat.bind (Sat.of_eq e (hjp v))
  · obtain ⟨v, e, -⟩ := ZlibNgF.Proof.Adler32Safe.adler32_c_safe hg S.check.toUInt32 o len.toUInt64 hlen
    exact Sat.bind (Sat.of_eq e (hjp v))

theorem run_CHECK (E : Env) (eo : EnvOK E) (hX : ModeRun E inflate_LENGTH (·.mode = LENGTH)) :
    ModeRun E inflate_CHECK (·.mode = CHECK) := by
  intro l H z S li hm m hμ
  have hμ' : 32 * (8 * l.have_.toNat + l.bits.toNat + l.left.toNat) + 2 ≤ m := by
    unfold μ at hμ; rwa [hm, rank_CHECK] at hμ
  unfold inflate_CHECK
  refine SatX.bind (SatX.lift_eq (li.rdS (·.wrap)) ?_)
  dsimp (config := { zeta := false }) only
  extract_lets jp jp2
  have hjp : ∀ (u : PUnit) (l' : IL) (H' : Heap) (z' : ZStream) (S' : InflateState), LI E l' H' z' S' →
      S'.mode = CHECK → 32 * (8 * l'.have_.toNat + l'.bits.toNat + l'.left.toNat) + 1 ≤ m →
      SatX H' l' (jp u) (Post E m) := by
    intro u l' H' z' S' li' hS' hμ1
    simp only [jp]
    refine SatX.bind (SatX.lift (Sat.mono (li'.setQuiet LENGTH (by decide) (by decide) (Or.inr (by decide))) ?_))
    intro _ H1 li1
    exact hX _ _ _ _ li1 rfl m (by unfold μ; dsimp only; rw [rank_LENGTH]; exact hμ1)
  have hjp2 : ∀ (u : PUnit) (l1 : IL) (H' : Heap) (z' : ZStream) (S' : InflateState), LI E l1 H' z' S' →
      S'.mode = CHECK → 32 * (8 * l1.have_.toNat + l1.bits.toNat + l1.left.toNat) + 2 ≤ m →
      SatX H' { l1 with out := l1.out - l1.left } (jp2 u) (Post E m) := by
    intro u l1 H' z' S' li' hS' hμ1
    have hr' : rank S'.mode ≤ 2 := by rw [hS']; decide
    simp only [jp2]
    refine SatX.bind (SatX.modify ?_)
    have li2 := li'.resetOut { l1 with out := l1.left } rfl rfl rfl rfl rfl rfl hr'
    refine SatX.bind (SatX.lift_eq li2.ldState ?_)
    refine SatX.bind (SatX.get ?_)
    dsimp (config := { zeta := false }) only
    split <;> split
    all_goals first
      | exact bad_ok li2 (by show 32 * (8 * l1.have_.toNat + l1.bits.toNat + l1.left.toNat) < m; omega)
          "incorrect data check" (strIdx 12 (by decide) (by decide) (by decide))
      | refine SatX.bind (initbits_ok ?_)
        exact hjp ⟨⟩ _ _ _ _ (li2.setBits (l' := { { l1 with out := l1.left } with hold := 0, bits := 0 }) rfl rfl rfl
        rfl rfl (show (0 : UInt8) ≤ 39 by decide)) hS' (by show 32 * (8 * l1.have_.toNat + (0 : UInt8).toNat + l1.left.toNat) + 1 ≤ m; rw [show (0 : UInt8).toNat = 0 from rfl]; omega)
  clear_value jp jp2
  split
  · refine needbits_then eo li 32 (by decide) ?_
    intro l1 li1 h32 hleft hT
    refine SatX.bind (SatX.get ?_)
    dsimp (config := { zeta := false }) only
    extract_lets o1
    have ho1 : o1 = l1.out - l1.left := rfl
    clear_value o1
    subst ho1
    have hμ1 : 32 * (8 * l1.have_.toNat + l1.bits.toNat + l1.left.toNat) + 2 ≤ m := by rw [hleft]; omega
    refine SatX.bind (SatX.modify ?_)
    refine SatX.bind (SatX.lift (Sat.mono (li1.wrZ (fun z => { z with total_out := z.total_out +
      (l1.out - l1.left).toUInt64 }) rfl rfl rfl) ?_))
    intro _ H2 li2
    refine SatX.bind (SatX.lift (Sat.mono (li2.wrS (fun s => { s with total := s.total +
      (l1.out - l1.left).toUInt64 }) (fun _ _ c => c) rfl) ?_))
    intro _ H3 li3
    refine SatX.bind (SatX.lift_eq (li3.rdS (·.wrap)) ?_)
    dsimp (config := { zeta := false }) only
    split
    · split
      · obtain ⟨p, hput, hp1, hp2⟩ := li3.outPos
        obtain ⟨dout, hdo, hdos⟩ := li3.outBytes eo
        obtain ⟨hlo, ob, hob1, hob2, hput'⟩ := li3.outAt
        rw [hput] at hput'
        have hpob : p = ob + (l1.out - l1.left).toNat := by injection hput'
        refine SatX.bind (SatX.lift_eq (show Ptr.add l1.put (-Int.ofNat (l1.out - l1.left).toNat) H3 = _ by
          rw [hput]; exact InflateWindow.add_neg (r := .heap E.bo) hdo (by omega) (by omega)) ?_)
        refine SatX.bind (SatX.lift (Sat.mono (li3.chksum eo hdo _ (by omega)) ?_))
        rintro u H4 ⟨v, li4⟩
        exact hjp2 u _ _ _ _ li4 hm hμ1
      · exact hjp2 _ _ _ _ _ li3 hm hμ1
    · exact hjp2 _ _ _ _ _ li3 hm hμ1
  · exact hjp _ _ _ _ _ li hm (by omega)

/-! ## One trip of the loop -/

/-- The mode values of a state with the invariant. -/
theorem mode_cases (M : UInt32) (lo : HEAD ≤ M) (hi : M ≤ SYNC) :
    M = HEAD ∨ M = FLAGS ∨ M = TIME ∨ M = OS ∨ M = EXLEN ∨ M = EXTRA ∨ M = NAME ∨ M = COMMENT ∨ M = HCRC ∨
    M = DICTID ∨ M = DICT ∨ M = TYPE ∨ M = TYPEDO ∨ M = STORED ∨ M = COPY_ ∨ M = COPY ∨ M = TABLE ∨
    M = LENLENS ∨ M = CODELENS ∨ M = LEN_ ∨ M = LEN ∨ M = LENEXT ∨ M = DIST ∨ M = DISTEXT ∨ M = MATCH ∨
    M = LIT ∨ M = CHECK ∨ M = LENGTH ∨ M = DONE ∨ M = BAD ∨ M = 16210 ∨ M = SYNC := by
  have h1 : 16180 ≤ M.toNat := UInt32.le_iff_toNat_le.mp lo
  have h2 : M.toNat ≤ 16211 := UInt32.le_iff_toNat_le.mp hi
  have e : ∀ k : Nat, k < 4294967296 → M.toNat = k → M = UInt32.ofNat k := fun k hk e => by
    apply UInt32.toNat_inj.mp; rw [e, UInt32.toNat_ofNat_of_lt' hk]
  have : M.toNat = 16180 ∨ M.toNat = 16181 ∨ M.toNat = 16182 ∨ M.toNat = 16183 ∨ M.toNat = 16184 ∨
      M.toNat = 16185 ∨ M.toNat = 16186 ∨ M.toNat = 16187 ∨ M.toNat = 16188 ∨ M.toNat = 16189 ∨ M.toNat = 16190 ∨
      M.toNat = 16191 ∨ M.toNat = 16192 ∨ M.toNat = 16193 ∨ M.toNat = 16194 ∨ M.toNat = 16195 ∨ M.toNat = 16196 ∨
      M.toNat = 16197 ∨ M.toNat = 16198 ∨ M.toNat = 16199 ∨ M.toNat = 16200 ∨ M.toNat = 16201 ∨ M.toNat = 16202 ∨
      M.toNat = 16203 ∨ M.toNat = 16204 ∨ M.toNat = 16205 ∨ M.toNat = 16206 ∨ M.toNat = 16207 ∨ M.toNat = 16208 ∨
      M.toNat = 16209 ∨ M.toNat = 16210 ∨ M.toNat = 16211 := by omega
  rcases this with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h <;> have := e _ (by decide) h <;> subst this
  all_goals (repeat (first | exact Or.inl rfl | apply Or.inr))
  all_goals rfl

/-- A mode statement with an unconditional precondition gives the one of its mode. -/
theorem ModeRun.of_true {E : Env} {f : Ctx → X Unit} {M : UInt32} (h : ModeRun E f (fun _ => True)) :
    ModeRun E f (·.mode = M) := fun l H z S li _ m hμ => h l H z S li trivial m hμ

set_option maxRecDepth 20000 in
/-- **One trip of the loop of `inflate`**, from the statements of all its modes. -/
theorem tripOK (E : Env) (eo : EnvOK E) : TripOK E := by
  have rMATCH := run_MATCH E eo
  have rDISTEXT := run_DISTEXT E eo rMATCH
  have rDIST := run_DIST E eo rDISTEXT
  have rLENEXT := run_LENEXT E eo rDIST
  have rLEN := run_LEN E eo rLENEXT
  have rLEN_ := run_LEN_ E rLEN
  have rCODELENS := run_CODELENS E eo rLEN_
  have rLENLENS := run_LENLENS E eo rCODELENS
  have rTABLE := run_TABLE E eo rLENLENS
  have rCOPY := run_COPY E eo
  have rCOPY_ := run_COPY_ E rCOPY
  have rSTORED := run_STORED E eo rCOPY_
  have rTYPEDO' := run_TYPEDO E eo
  have rTYPEDO : ModeRun E inflate_TYPEDO (·.mode = TYPEDO) :=
    fun l H z S li hm m hμ => rTYPEDO' l H z S li (Or.inl hm) m hμ
  have rTYPE := run_TYPE E rTYPEDO'
  have rDICT := run_DICT E rTYPE
  have rDICTID := run_DICTID E eo rDICT
  have rHCRC := run_HCRC E eo
  have rCOMMENT := run_COMMENT E eo rHCRC
  have rNAME := run_NAME E eo rCOMMENT
  have rEXTRA := run_EXTRA E eo rNAME
  have rEXLEN := run_EXLEN E eo rEXTRA
  have rOS := run_OS E eo rEXLEN
  have rTIME := run_TIME E eo rOS
  have rFLAGS := run_FLAGS E eo rTIME
  have rHEAD := run_HEAD E eo
  have rLIT := run_LIT E eo
  have rLENGTH := run_LENGTH E eo
  have rCHECK := run_CHECK E eo rLENGTH
  have rDONE : ModeRun E inflate_DONE (·.mode = DONE) := run_DONE E
  have rBAD : ModeRun E inflate_BAD (·.mode = BAD) := run_BAD E
  refine trip_of_modes (fun M l H z S li hm m hμ => ?_)
  obtain ⟨al, -, c⟩ := li.core
  have lo : HEAD ≤ M := hm ▸ c.mode_lo
  have hi : M ≤ SYNC := hm ▸ c.mode_hi
  rcases mode_cases M lo hi with e | e | e | e | e | e | e | e | e | e | e | e | e | e | e | e | e | e | e | e | e |
    e | e | e | e | e | e | e | e | e | e | e <;> subst e
  · exact rHEAD l H z S li hm m hμ
  · exact rFLAGS l H z S li hm m hμ
  · exact rTIME l H z S li hm m hμ
  · exact rOS l H z S li hm m hμ
  · exact rEXLEN l H z S li hm m hμ
  · exact rEXTRA l H z S li hm m hμ
  · exact rNAME l H z S li hm m hμ
  · exact rCOMMENT l H z S li hm m hμ
  · exact rHCRC l H z S li hm m hμ
  · exact rDICTID l H z S li hm m hμ
  · exact rDICT l H z S li hm m hμ
  · exact rTYPE l H z S li hm m hμ
  · exact rTYPEDO l H z S li hm m hμ
  · exact rSTORED l H z S li hm m hμ
  · exact rCOPY_ l H z S li hm m hμ
  · exact rCOPY l H z S li hm m hμ
  · exact rTABLE l H z S li hm m hμ
  · exact rLENLENS l H z S li hm m hμ
  · exact rCODELENS l H z S li hm m hμ
  · exact rLEN_ l H z S li hm m hμ
  · exact rLEN l H z S li hm m hμ
  · exact rLENEXT l H z S li hm m hμ
  · exact rDIST l H z S li hm m hμ
  · exact rDISTEXT l H z S li hm m hμ
  · exact rMATCH l H z S li hm m hμ
  · exact rLIT l H z S li hm m hμ
  · exact rCHECK l H z S li hm m hμ
  · exact rLENGTH l H z S li hm m hμ
  · exact rDONE l H z S li hm m hμ
  · exact rBAD l H z S li hm m hμ
  · exact run_default E 16210 (Or.inr rfl) l H z S li hm m hμ
  · exact run_default E SYNC (Or.inl rfl) l H z S li hm m hμ

end ZlibNgF.Proof.InflateLoop