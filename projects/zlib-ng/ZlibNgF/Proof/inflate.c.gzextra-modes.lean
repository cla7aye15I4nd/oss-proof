import ZlibNgF.Proof.«inflate.c.gzhead-modes»
import ZlibNgF.Proof.«inflate.c.dict»

/-!
# The gzip header modes `EXTRA`, `NAME`, `COMMENT` of `inflate` (`ZlibNgF`)

These modes read the input and copy it into the buffers of the registered `gz_header` (`HBuf` of `EnvOK`: `NULL` or
writable bytes outside the state's block, a write range of the call, disjoint from the input). Each falls through to
the next (`EXTRA → NAME → COMMENT → HCRC`).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InflateLoop
open C ZlibNgF.Spec ZlibNg.Inflate
open ZlibNgF.Proof.InflateInv (Inv Core view)
open ZlibNgF.Proof.InflateX
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.mono Sat.of_eq St Touch)
open ZlibNgF.Proof.InflateDict (copyFold copyFold_size copyFold_get frame_bytes inv_bytes_ne space_get_heap add_heap)

theorem rank_NAME : rank NAME = 20 := by decide
theorem rank_COMMENT : rank COMMENT = 19 := by decide
theorem rank_HCRC : rank HCRC = 18 := by decide

/-! ## Writes into the caller's header buffers -/

/-- A write inside one of the call's write ranges is in the frame of the call. -/
theorem Frame.widen {h h' : Heap} {S B G : List Nat} {W : List (BPtr × Nat)} {bd od n o0 n0 : Nat}
    (f : Frame h h' S B G [(.ref (.heap bd) od, n)]) (hw : ((.ref (.heap bd) o0 : BPtr), n0) ∈ W)
    (h1 : o0 ≤ od) (h2 : od + n ≤ o0 + n0) : Frame h h' S B G W := by
  obtain ⟨s1, g1, i1, b1, n1, c1, r1, x1, a1, k1⟩ := f
  refine ⟨s1, g1, i1, fun c hc hn data hd => ?_, n1, c1, r1, x1, a1, k1⟩
  obtain ⟨d2, e2, s2, q2⟩ := b1 c hc hn data hd
  refine ⟨d2, e2, s2, fun j hj hW => q2 j hj ?_⟩
  intro w hw' off he
  rw [List.mem_singleton] at hw'
  subst hw'
  injection he with f1 f2
  injection f1 with f3
  subst f3; subst f2
  have := hW _ hw o0 rfl
  dsimp only at this ⊢
  omega

/-- A change of the bytes of a block other than the state's, inside a write range of the call, keeps `LI`. -/
theorem LI.wrBytes {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (li : LI E l H z S)
    {bd od n o0 n0 : Nat} {a a' : Array UInt8} (hd : H.bytes bd = some a) (hne : bd ≠ E.b)
    (hsz : a'.size = a.size) (hpt : ∀ j, (j < od ∨ od + n ≤ j) → a'[j]! = a[j]!)
    (hw : ((.ref (.heap bd) o0 : BPtr), n0) ∈ E.W) (h1 : o0 ≤ od) (h2 : od + n ≤ o0 + n0) :
    LI E l { H with bytes := upd H.bytes bd (some a') } z S := by
  have hbb : (upd H.bytes bd (some a')) E.b = H.bytes E.b := upd_ne _ _ _ _ (fun e => hne e.symm)
  refine ⟨inv_bytes_ne li.inv ?_, ?_, ?_, li.hz, li.hb, ?_, li.head, li.hdr, li.inAt, li.outAt, li.bits, li.inn,
    li.outO, li.retB, li.sacc, li.msgK⟩
  · rintro b' ⟨z', ⟨i', hi', hz'⟩, hb'⟩
    cases hi'
    rw [li.hz] at hz'; cases hz'; rw [li.hb] at hb'; cases hb'
    exact fun e => hne e.symm
  · exact Frame.trans li.frame (Frame.widen (Frame.mono (frame_bytes hd hsz hpt) (fun _ m => nomatch m)
      (fun _ m => nomatch m) (fun _ m => nomatch m) (fun _ m => m)) hw h1 h2)
  · refine li.sz.trans ⟨fun c _ d hd' => ?_, rfl⟩
    by_cases e : c = bd
    · subst e; rw [hd] at hd'; cases hd'
      exact ⟨a', upd_same _ _ _, hsz⟩
    · exact ⟨d, by simp only [upd_ne _ _ _ _ e]; exact hd', rfl⟩
  · have := li.hs
    simp only [Heap.istate] at this ⊢
    rw [hbb]; exact this

/-- `*p = v` into a heap block. -/
theorem store_heap {h : Heap} {bd o : Nat} {a : Array UInt8} (hd : h.bytes bd = some a) (ho : o < a.size)
    (v : UInt8) :
    Ptr.store (Ptr.ref (BRef.heap bd) o) v h = .ok ((), { h with bytes := upd h.bytes bd (some (a.set! o v)) }) := by
  simp only [Ptr.store, space_get_heap, hd, ho, ↓reduceIte]
  simp only [Space.ro, Heap.isRo, Bool.false_eq_true, ↓reduceIte, Space.modify, Heap.modifyBytes,
    Tbl.modify_opt h.bytes bd _ a hd]

theorem set_get (a : Array UInt8) (o j : Nat) (v : UInt8) (hj : j ≠ o) : (a.set! o v)[j]! = a[j]! := by
  simp only [Array.set!_eq_setIfInBounds, getElem!_def, Array.getElem?_setIfInBounds]
  simp [Ne.symm hj]

/-- `memcpy` into a heap block from a range that does not overlap the destination. -/
theorem memcpy_heap' {h : Heap} {bd od : Nat} {rs : BRef} {os n : Nat} {ad src : Array UInt8}
    (hd : h.bytes bd = some ad) (hs : Space.get h rs = some src)
    (hov : rs = .heap bd → od + n ≤ os ∨ os + n ≤ od)
    (h1 : od + n ≤ ad.size) (h2 : os + n ≤ src.size) :
    Ptr.memcpy (.ref (.heap bd) od) (.ref rs os) n h =
      .ok ((), { h with bytes := upd h.bytes bd (some (copyFold src od os (List.range' 0 n) ad)) }) := by
  have hno : ¬ (BRef.heap bd = rs ∧ n > 0 ∧ ¬ (od + n ≤ os ∨ os + n ≤ od)) := by
    rintro ⟨e, -, hc⟩; exact hc (hov e.symm)
  simp only [Ptr.memcpy, space_get_heap, hd, hs, h1, h2, and_self, hno, ↓reduceIte]
  simp only [Space.ro, Heap.isRo, Bool.false_eq_true, ↓reduceIte, Space.modify, Heap.modifyBytes,
    Tbl.modify_opt h.bytes bd _ ad hd]
  rw [← ZlibNgF.Proof.InflateDict.memcpy_loop]

theorem copyFold_out (src : Array UInt8) (od os n : Nat) (a : Array UInt8) (j : Nat) (hj : j < od ∨ od + n ≤ j) :
    (copyFold src od os (List.range' 0 n) a)[j]! = a[j]! :=
  copyFold_get src od os _ a j (fun i hi => by simp only [List.mem_range'_1] at hi; omega)

/-- `p + k` inside an object. -/
theorem add_in {h : Heap} {r : BRef} {off k : Nat} {a : Array UInt8} (hb : Space.get h r = some a)
    (hk : off + k ≤ a.size) : Ptr.add (Ptr.ref r off) (Int.ofNat k) h = .ok (.ref r (off + k), h) := by
  have e : ((off : Int) + Int.ofNat k).toNat = off + k := by simp only [Int.ofNat_eq_natCast]; omega
  have hc : off ≤ a.size ∧ 0 ≤ (off : Int) + Int.ofNat k ∧ (off : Int) + Int.ofNat k ≤ (a.size : Int) := by
    simp only [Int.ofNat_eq_natCast]; omega
  simp only [Ptr.add, hb, hc, and_self, ↓reduceIte, e]

/-- `p[k]` inside an object. -/
theorem index_in {h : Heap} {r : BRef} {off k : Nat} {a : Array UInt8} (hb : Space.get h r = some a)
    (hk : off + k < a.size) : index8 (Ptr.ref r off) (Int.ofNat k) h = .ok (a[off + k]!, h) := by
  simp only [index8, Ptr.index, bind_app, add_in hb (Nat.le_of_lt hk)]
  simp [Ptr.load, hb, hk]

/-! ## Header buffers -/

theorem HBuf.keep {E : Env} {H : Heap} {p : BPtr} {n : Nat} (hb : HBuf E E.H0 p n) (sk : SizeKeep E.H0 H E.b) :
    HBuf E H p n := by
  rcases hb with h0 | ⟨bd, off, data, rfl, hd, hsz, hne, hw, hdj⟩
  · exact Or.inl h0
  · obtain ⟨d', hd', hs'⟩ := sk.1 bd hne data hd
    exact Or.inr ⟨bd, off, d', rfl, hd', by omega, hne, hw, hdj⟩

theorem HBuf.or_null {E : Env} {H : Heap} {p q : BPtr} {n : Nat} (hb : HBuf E H p n) (hq : q = p ∨ q = .null) :
    HBuf E H q n := by
  rcases hq with rfl | rfl
  · exact hb
  · exact Or.inl rfl

/-- The buffers of the registered header in a state with the invariant. -/
theorem LI.hbufs {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (eo : EnvOK E)
    (li : LI E l H z S) {k : Nat} (hk : E.hp = some k) {g : GzHeader} (hg : H.gzheaders k = some g) :
    HBuf E H g.extra g.extra_max.toNat ∧ HBuf E H g.name g.name_max.toNat ∧
      HBuf E H g.comment g.comm_max.toNat := by
  have hd := li.hdr
  unfold HdrOK at hd
  rw [hk] at hd
  obtain ⟨g0, g1, e0, e1, a1, a2, a3, a4, a5, a6⟩ := hd
  rw [hg] at e1; cases e1
  obtain ⟨b1, b2, b3⟩ := eo.hdrBuf k g0 hk e0
  refine ⟨?_, ?_, ?_⟩
  · rw [a2]; exact (b1.keep li.sz).or_null a1
  · rw [a4]; exact (b2.keep li.sz).or_null a3
  · rw [a6]; exact (b3.keep li.sz).or_null a5

/-- One byte of a header buffer with room: the store keeps `LI`. -/
theorem LI.storeBuf {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (li : LI E l H z S)
    {bd off n : Nat} {data : Array UInt8} (hd : H.bytes bd = some data) (hsz : off + n ≤ data.size)
    (hne : bd ≠ E.b) (hw : ((.ref (.heap bd) off : BPtr), n) ∈ E.W) (i : Nat) (hi : i < n) (v : UInt8) :
    Sat H (Ptr.store (Ptr.ref (BRef.heap bd) (off + i)) v) (fun _ H' => LI E l H' z S) :=
  ⟨(), _, store_heap hd (by omega) v, li.wrBytes (od := off + i) (n := 1) hd hne (by simp) (fun j hj => set_get _ _ _ _ (by omega)) hw
    (by omega) (by omega)⟩

/-- `next` advanced by `c ≤ have` bytes. -/
theorem LI.consume {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (li : LI E l H z S)
    {r : BRef} {o : Nat} (hn : l.next = .ref r o) (c : UInt32) (hc : c ≤ l.have_) (l' : IL)
    (e1 : l'.next = .ref r (o + c.toNat)) (e2 : l'.have_ = l.have_ - c) (e3 : l'.put = l.put) (e4 : l'.out = l.out)
    (e5 : l'.left = l.left) (e6 : l'.bits = l.bits) (e7 : l'.in_ = l.in_ := by rfl)
    (e8 : l'.ret = l.ret := by rfl) : LI E l' H z S := by
  obtain ⟨hle, hat⟩ := li.inAt
  have hc' : c.toNat ≤ l.have_.toNat := hc
  have hle' : l.have_.toNat ≤ E.A0.toNat := hle
  have hs : (l.have_ - c).toNat = l.have_.toNat - c.toNat := UInt32.toNat_sub_of_le _ _ hc
  refine ⟨li.inv, li.frame, li.sz, li.hz, li.hb, li.hs, li.head, li.hdr, ?_, by rw [e3, e4, e5]; exact li.outAt,
    by rw [e6]; exact li.bits, by rw [e7]; exact li.inn, by rw [e4]; exact li.outO, by rw [e8]; exact li.retB, li.sacc, li.msgK⟩
  rw [e1, e2]
  refine ⟨by rw [UInt32.le_iff_toNat_le, hs]; omega, ?_⟩
  revert hat
  cases E.inp with
  | null => intro hat; rw [hn] at hat; cases hat.1
  | ref r' o' =>
    intro hat
    rw [hn] at hat
    injection hat with h1 h2
    subst h1; subst h2
    show Ptr.ref r (o' + (E.A0 - l.have_).toNat + c.toNat) = Ptr.ref r (o' + (E.A0 - (l.have_ - c)).toNat)
    rw [UInt32.toNat_sub_of_le _ _ hle, UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, hs]; omega), hs]
    congr 1; omega

/-! ## `headerString` -/

/-- The body of the loop of `headerString`. -/
def hsBody (c : Ctx) (field : GzHeader → BPtr) (maxOf : GzHeader → UInt32) : X Unit := do
  let l ← get
  let b ← index8 l.next (Int.ofNat l.copy.toNat)
  modify fun l => { l with copy := l.copy + 1, len := b.toUInt32 }
  let hd ← headOf c.st
  if hd != none then
    let g ← ldHeader hd
    if field g != .null then
      let s ← ldState c.st
      if s.length < maxOf g then
        ZlibNg.Inflate.wrS c.st fun s => { s with length := s.length + 1 }
        Ptr.store (← (field g).add (Int.ofNat s.length.toNat)) (← get).len.toUInt8

theorem headerString_eq (c : Ctx) (field : GzHeader → BPtr) (maxOf : GzHeader → UInt32) :
    headerString c field maxOf = (do
      modify fun l => { l with copy := 0 }
      hsBody c field maxOf
      xwhile (do let l ← get; return l.len != 0 && l.copy < l.have_) (hsBody c field maxOf)) := rfl

/-- The locals keep the input and output positions and the bit buffer. -/
def Same (l l' : IL) : Prop :=
  l'.next = l.next ∧ l'.have_ = l.have_ ∧ l'.bits = l.bits ∧ l'.left = l.left ∧ l'.put = l.put ∧ l'.out = l.out

/-- One trip of the body: reads `next[copy]` (`copy < have`), may store a byte into the header buffer. -/
theorem hsBody_ok {E : Env} (eo : EnvOK E) (field : GzHeader → BPtr) (maxOf : GzHeader → UInt32)
    (hF : ∀ {l H z S}, LI E l H z S → ∀ k g, E.hp = some k → H.gzheaders k = some g →
      HBuf E H (field g) (maxOf g).toNat)
    {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (li : LI E l H z S)
    (hlt : l.copy < l.have_) :
    SatX H l (hsBody E.c field maxOf) (fun r l' H' => r = .ok () ∧ ∃ S', LI E l' H' z S' ∧ S'.mode = S.mode ∧
      Same l l' ∧ l'.copy = l.copy + 1) := by
  have hlt' : l.copy.toNat < l.have_.toNat := hlt
  have hh : l.have_ ≠ 0 := fun e => by rw [e] at hlt'; exact absurd hlt' (Nat.not_lt_zero _)
  obtain ⟨r, o, d, hnx, hg, hsz⟩ := li.inBytes eo hh
  unfold hsBody
  refine SatX.bind (SatX.get ?_)
  dsimp only
  rw [hnx]
  refine SatX.bind (SatX.lift_eq (index_in hg (by omega)) ?_)
  refine SatX.bind (SatX.modify ?_)
  dsimp only
  let l1 : IL := { l with copy := l.copy + 1, len := (d[o + l.copy.toNat]!).toUInt32 }
  have li1 : LI E l1 H z S := li.locals rfl rfl rfl rfl rfl rfl
  have hs1 : Same l l1 := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine SatX.bind (SatX.lift_eq li1.headOf ?_)
  dsimp only
  cases hhp : E.hp with
  | none =>
    have he : ((none : HeaderPtr) != none) = false := rfl
    simp only [he, Bool.false_eq_true, ↓reduceIte]
    exact SatX.pure ⟨rfl, S, li1, rfl, hs1, rfl⟩
  | some kk =>
    have hne : (some kk != (none : HeaderPtr)) = true := rfl
    simp only [hne, ↓reduceIte]
    obtain ⟨g, hgk⟩ := li1.hdrRec hhp
    refine SatX.bind (SatX.lift_eq (show ldHeader (some kk) H = .ok (g, H) by simp [ldHeader, hgk]) ?_)
    dsimp only
    split
    · rename_i hfn
      rcases hF li1 kk g hhp hgk with h0 | ⟨bd, off, data, hfe, hd, hsz', hbne, hw, -⟩
      · rw [h0] at hfn; exact absurd hfn (by decide)
      refine SatX.bind (SatX.lift_eq li1.ldState ?_)
      dsimp only
      split
      · rename_i hml
        have hml' : S.length.toNat < (maxOf g).toNat := hml
        refine SatX.bind (SatX.lift (Sat.mono (li1.wrST (fun s => { s with length := s.length + 1 })
          (fun _ _ c => { c with }) rfl) ?_))
        rintro _ H2 ⟨li2, eb, -⟩
        rw [hfe]
        rw [hfe] at hw
        have hd2 : H2.bytes bd = some data := by rw [eb]; exact hd
        refine SatX.bind (SatX.lift_eq (add_heap hd2 (by omega)) ?_)
        refine SatX.bind (SatX.get ?_)
        refine SatX.lift (Sat.mono (li2.storeBuf hd2 hsz' hbne hw S.length.toNat hml' _) ?_)
        intro _ H3 li3
        exact ⟨rfl, _, li3, rfl, hs1, rfl⟩
      · exact SatX.pure ⟨rfl, S, li1, rfl, hs1, rfl⟩
    · exact SatX.pure ⟨rfl, S, li1, rfl, hs1, rfl⟩

theorem Same.trans {l1 l2 l3 : IL} (a : Same l1 l2) (b : Same l2 l3) : Same l1 l3 :=
  ⟨b.1.trans a.1, b.2.1.trans a.2.1, b.2.2.1.trans a.2.2.1, b.2.2.2.1.trans a.2.2.2.1,
    b.2.2.2.2.1.trans a.2.2.2.2.1, b.2.2.2.2.2.trans a.2.2.2.2.2⟩

theorem succ_toNat {a b : UInt32} (h : a < b) : (a + 1).toNat = a.toNat + 1 := by
  have h' : a.toNat < b.toNat := h
  have := b.toNat_lt
  rw [UInt32.toNat_add]; show (a.toNat + 1) % 2 ^ 32 = _; omega

/-- `headerString`: with `have != 0`, it reads `copy` bytes, `1 ≤ copy ≤ have`, and keeps `LI`. -/
theorem headerString_ok {E : Env} (eo : EnvOK E) (field : GzHeader → BPtr) (maxOf : GzHeader → UInt32)
    (hF : ∀ {l H z S}, LI E l H z S → ∀ k g, E.hp = some k → H.gzheaders k = some g →
      HBuf E H (field g) (maxOf g).toNat)
    {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (li : LI E l H z S)
    (hh : l.have_ ≠ 0) :
    SatX H l (headerString E.c field maxOf) (fun r l' H' => r = .ok () ∧ ∃ S', LI E l' H' z S' ∧
      S'.mode = S.mode ∧ Same l l' ∧ 1 ≤ l'.copy.toNat ∧ l'.copy ≤ l.have_) := by
  have hh' : 0 < l.have_.toNat := by
    rcases Nat.eq_zero_or_pos l.have_.toNat with e | e
    · exact absurd (UInt32.toNat_inj.mp (by rw [e]; rfl)) hh
    · exact e
  rw [headerString_eq]
  refine SatX.bind (SatX.modify ?_)
  let l0 : IL := { l with copy := 0 }
  have li0 : LI E l0 H z S := li.locals rfl rfl rfl rfl rfl rfl
  refine SatX.bind (SatX.mono (hsBody_ok eo field maxOf hF li0 (show (0 : UInt32) < l.have_ from hh')) ?_)
  rintro r l1 H1 ⟨rfl, S1, li1, hm1, hs1, hc1⟩
  have hc1' : l1.copy.toNat = 1 := by rw [hc1]; rfl
  unfold xwhile
  refine xwhileBrk_rank (fun l' H' => ∃ S', LI E l' H' z S' ∧ S'.mode = S.mode ∧ Same l l' ∧
      1 ≤ l'.copy.toNat ∧ l'.copy ≤ l.have_) (fun l' _ => l.have_.toNat - l'.copy.toNat) _ ?_
    ⟨S1, li1, hm1, hs1, by omega, by rw [UInt32.le_iff_toNat_le]; omega⟩
    (by have := l.have_.toNat_lt; unfold fuel; omega)
  rintro l' H' ⟨S', li', hm', hs', hc1', hc2'⟩
  refine SatX.bind (SatX.get ?_)
  refine SatX.pure ?_
  by_cases hcond : (l'.len != 0 && decide (l'.copy < l'.have_)) = true
  · rw [hcond]
    have hlt : l'.copy < l'.have_ := by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond; exact hcond.2
    refine SatX.bind (SatX.mono (hsBody_ok eo field maxOf hF li' hlt) ?_)
    rintro r l2 H2 ⟨rfl, S2, li2, hm2, hs2, hc⟩
    refine SatX.pure ⟨⟨S2, li2, hm2.trans hm', hs'.trans hs2, ?_, ?_⟩, ?_⟩
    · rw [hc, succ_toNat hlt]; omega
    · have h1 : l'.copy.toNat < l'.have_.toNat := hlt
      rw [hc, UInt32.le_iff_toNat_le, succ_toNat hlt, ← hs'.2.1]; omega
    · have h1 : l'.copy.toNat < l'.have_.toNat := hlt
      show l.have_.toNat - l2.copy.toNat < l.have_.toNat - l'.copy.toNat
      rw [hc, succ_toNat hlt, ← hs'.2.1]; omega
  · have hf : (l'.len != 0 && decide (l'.copy < l'.have_)) = false := by simpa using hcond
    rw [hf]
    exact ⟨rfl, S', li', hm', hs', hc1', hc2'⟩

/-! ## The header check value over the input read -/

theorem LI.crcTab {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (eo : EnvOK E)
    (li : LI E l H z S) : H.crcTable = ZlibNg.Crc32Tbl.crc_table :=
  li.frame.2.2.2.2.2.2.1.trans eo.crc

/-- `if ((state->flags & 0x0200) && (state->wrap & 4)) state->check = crc32(state->check, l.next, l.copy);` then
`k`, with `copy ≤ have`. -/
theorem crcN_tail {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (eo : EnvOK E)
    (li : LI E l H z S) (h0 : l.have_ ≠ 0) (hc : l.copy ≤ l.have_) (k : X Unit) {Q : Except Ex Unit → IL → Heap → Prop}
    (hk : ∀ H' S', LI E l H' z S' → S'.mode = S.mode → SatX H' l k Q) :
    SatX H l (do
      if ← ZlibNg.Inflate.hcrcOn E.c.st then
        let l ← get
        let v ← ZlibNg.Crc32.crc32_small (← ZlibNg.Inflate.rdS E.c.st (·.check)).toUInt32 l.next l.copy.toUInt64
        ZlibNg.Inflate.wrS E.c.st fun s => { s with check := v.toUInt64 }
      k) Q := by
  refine SatX.bind (SatX.lift_eq li.hcrcOn ?_)
  dsimp only
  split
  · refine SatX.bind (SatX.get ?_)
    refine SatX.bind (SatX.lift_eq (li.rdS (·.check)) ?_)
    have hc' : l.copy.toNat ≤ l.have_.toNat := hc
    obtain ⟨r, o, d, hnx, hg, hsz⟩ := li.inBytes eo h0
    rw [hnx]
    obtain ⟨v, ev, -⟩ := ZlibNgF.Proof.Crc32.crc32_small_ok (li.crcTab eo) hg S.check.toUInt32 o l.copy.toUInt64
      (by rw [UInt32.toNat_toUInt64]; omega)
    refine SatX.bind (SatX.lift_eq ev ?_)
    refine SatX.bind (SatX.lift (Sat.mono (li.wrS (fun s => { s with check := v.toUInt64 }) (fun _ _ c => c) rfl) ?_))
    intro _ H1 li1
    exact hk _ _ li1 rfl
  · exact hk _ _ li rfl

/-- The string part of `NAME` / `COMMENT` (with the flag set) followed by `k`: it leaves with no input, or reads the
string up to its zero byte or the end of the input, consuming at least one byte. -/
theorem strPart_ok {E : Env} (eo : EnvOK E) (field : GzHeader → BPtr) (maxOf : GzHeader → UInt32)
    (hF : ∀ {l H z S}, LI E l H z S → ∀ k g, E.hp = some k → H.gzheaders k = some g →
      HBuf E H (field g) (maxOf g).toNat)
    {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (li : LI E l H z S) {m : Nat}
    (k : X Unit)
    (hk : ∀ l' H' S', LI E l' H' z S' → S'.mode = S.mode → l'.bits = l.bits → l'.left = l.left →
      l'.have_.toNat + 1 ≤ l.have_.toNat → SatX H' l' k (Post E m)) :
    SatX H l (do
      if (← get).have_ == 0 then throw Ex.leave
      headerString E.c field maxOf
      if ← ZlibNg.Inflate.hcrcOn E.c.st then
        let l ← get
        let v ← ZlibNg.Crc32.crc32_small (← ZlibNg.Inflate.rdS E.c.st (·.check)).toUInt32 l.next l.copy.toUInt64
        ZlibNg.Inflate.wrS E.c.st fun s => { s with check := v.toUInt64 }
      let l ← get
      let nx ← l.next.add (Int.ofNat l.copy.toNat)
      modify fun l => { l with have_ := l.have_ - l.copy, next := nx }
      if (← get).len != 0 then throw Ex.leave
      k) (Post E m) := by
  refine SatX.bind (SatX.get ?_)
  dsimp only
  split
  · rename_i h0
    exact SatX.bind (SatX.throw ⟨⟨z, S, li⟩, Why.have0 (by simpa using h0)⟩)
  rename_i h0
  have hh : l.have_ ≠ 0 := by simpa using h0
  refine SatX.bind (SatX.mono (headerString_ok eo field maxOf hF li hh) ?_)
  rintro r l1 H1 ⟨rfl, S1, li1, hm1, hs1, hc1, hc2⟩
  have hh1 : l1.have_ ≠ 0 := by rw [hs1.2.1]; exact hh
  have hc2' : l1.copy ≤ l1.have_ := by rw [hs1.2.1]; exact hc2
  refine crcN_tail eo li1 hh1 hc2' _ ?_
  intro H2 S2 li2 hm2
  refine SatX.bind (SatX.get ?_)
  obtain ⟨r, o, d, hnx, hg, hsz⟩ := li2.inBytes eo hh1
  have hc3 : l1.copy.toNat ≤ l1.have_.toNat := hc2'
  dsimp only
  rw [hnx]
  refine SatX.bind (SatX.lift_eq (add_in hg (by omega)) ?_)
  refine SatX.bind (SatX.modify ?_)
  have li3 := li2.consume hnx l1.copy hc2' { l1 with have_ := l1.have_ - l1.copy, next := .ref r (o + l1.copy.toNat) }
    rfl rfl rfl rfl rfl rfl
  refine SatX.bind (SatX.get ?_)
  dsimp only
  split
  · have hA : l1.have_ - l1.copy < E.A0 := by
      have h1 : l.have_.toNat ≤ E.A0.toNat := li.inAt.1
      have h2 : l1.have_.toNat = l.have_.toNat := by rw [hs1.2.1]
      rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_sub_of_le _ _ hc2']; omega
    exact SatX.bind (SatX.throw ⟨⟨z, S2, li3⟩, Why.read hA⟩)
  refine hk _ _ _ li3 (hm2.trans hm1) hs1.2.2.1 hs1.2.2.2.1 ?_
  show (l1.have_ - l1.copy).toNat + 1 ≤ l.have_.toNat
  rw [UInt32.toNat_sub_of_le _ _ hc2', hs1.2.1]
  rw [hs1.2.1] at hc3
  omega

/-! ## The modes -/

theorem run_COMMENT (E : Env) (eo : EnvOK E) (hX : ModeRun E inflate_HCRC (·.mode = HCRC)) :
    ModeRun E inflate_COMMENT (·.mode = COMMENT) := by
  intro l H z S li hm m hμ
  have hμ' : 32 * (8 * l.have_.toNat + l.bits.toNat + l.left.toNat) + 19 ≤ m := by
    unfold μ at hμ; rwa [hm, rank_COMMENT] at hμ
  unfold inflate_COMMENT
  refine SatX.bind (SatX.lift_eq li.ldState ?_)
  dsimp only
  split
  · refine strPart_ok eo (·.comment) (·.comm_max) (fun li k g hk hg => (li.hbufs eo hk hg).2.2) li
      _ ?_
    intro l' H' S' li' hm' hb hl hh
    exact fall_ok hX (by decide) (by decide) (Or.inl (by decide)) li' (by rw [rank_HCRC, hb, hl]; omega)
      (Or.inl (li'.outEq (by rw [hm', hm]; decide)))
  · refine hdr1_tail eo li (fun g => { g with comment := .null })
      (fun g => ⟨Or.inl rfl, rfl, Or.inl rfl, rfl, Or.inr rfl, rfl⟩) _ ?_
    intro H3 li3
    exact fall_ok hX (by decide) (by decide) (Or.inl (by decide)) li3 (by rw [rank_HCRC]; omega)
      (Or.inl (li3.outEq (by rw [hm]; decide)))

theorem run_NAME (E : Env) (eo : EnvOK E) (hX : ModeRun E inflate_COMMENT (·.mode = COMMENT)) :
    ModeRun E inflate_NAME (·.mode = NAME) := by
  intro l H z S li hm m hμ
  have hμ' : 32 * (8 * l.have_.toNat + l.bits.toNat + l.left.toNat) + 20 ≤ m := by
    unfold μ at hμ; rwa [hm, rank_NAME] at hμ
  have tail : ∀ l' H' z' S', LI E l' H' z' S' → l'.out = E.O0 →
      32 * (8 * l'.have_.toNat + l'.bits.toNat + l'.left.toNat) + 19 ≤ m →
      SatX H' l' (do
        (MonadLiftT.monadLift (ZlibNg.Inflate.wrS E.c.st fun s => { s with length := 0 }) : X Unit)
        (MonadLiftT.monadLift (setMode E.c.st COMMENT) : X Unit)
        inflate_COMMENT E.c) (Post E m) := by
    intro l' H' z' S' li' hO hb
    refine SatX.bind (SatX.lift (Sat.mono (li'.wrS (fun s => { s with length := 0 })
      (fun _ _ c => { c with }) rfl) ?_))
    intro _ H2 li2
    exact fall_ok hX (by decide) (by decide) (Or.inl (by decide)) li2 (by rw [rank_COMMENT]; omega) (Or.inl hO)
  unfold inflate_NAME
  refine SatX.bind (SatX.lift_eq li.ldState ?_)
  dsimp only
  split
  · refine strPart_ok eo (·.name) (·.name_max) (fun li k g hk hg => (li.hbufs eo hk hg).2.1) li
      _ ?_
    intro l' H' S' li' hm' hb hl hh
    exact tail _ _ _ _ li' (li'.outEq (by rw [hm', hm]; decide)) (by rw [hb, hl]; omega)
  · refine hdr1_tail eo li (fun g => { g with name := .null })
      (fun g => ⟨Or.inl rfl, rfl, Or.inr rfl, rfl, Or.inl rfl, rfl⟩) _ ?_
    intro H3 li3
    exact tail _ _ _ _ li3 (li3.outEq (by rw [hm]; decide)) (by omega)

/-! ## `EXTRA` -/

/-- `if (state->length) goto inf_leave;` then `k`. -/
theorem leaveLen {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (li : LI E l H z S) {m : Nat}
    (k : X Unit) (hw : S.length ≠ 0 → Why E l) (hk : S.length = 0 → SatX H l k (Post E m)) :
    SatX H l (do
      if (← ZlibNg.Inflate.rdS E.c.st (·.length)) != 0 then throw Ex.leave
      k) (Post E m) := by
  refine SatX.bind (SatX.lift_eq (li.rdS (·.length)) ?_)
  dsimp only
  split
  · rename_i h; exact SatX.bind (SatX.throw ⟨⟨z, S, li⟩, hw (by simpa using h)⟩)
  · rename_i h; exact hk (by simpa using h)

/-- `state->length = 0; state->mode = NAME;` and the fall-through into `NAME`, from `EXTRA`. -/
theorem tailN {E : Env} (hN : ModeRun E inflate_NAME (·.mode = NAME)) {l : IL} {H : Heap} {z : ZStream}
    {S : InflateState} (li : LI E l H z S) {m : Nat}
    (hμ : 32 * (8 * l.have_.toNat + l.bits.toNat + l.left.toNat) + 20 ≤ m) (hO : l.out = E.O0) :
    SatX H l (do
      (MonadLiftT.monadLift (ZlibNg.Inflate.wrS E.c.st fun s => { s with length := 0 }) : X Unit)
      (MonadLiftT.monadLift (setMode E.c.st NAME) : X Unit)
      inflate_NAME E.c) (Post E m) := by
  refine SatX.bind (SatX.lift (Sat.mono (li.wrS (fun s => { s with length := 0 }) (fun _ _ c => { c with }) rfl) ?_))
  intro _ H2 li2
  exact fall_ok hN (by decide) (by decide) (Or.inl (by decide)) li2 (by rw [rank_NAME]; omega) (Or.inl hO)

/-- `if (hcrc) state->check = crc32_small(state->check, p, n);` then `k`, with `n` readable bytes at `p`. -/
theorem crcE_tail {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (eo : EnvOK E)
    (li : LI E l H z S) (p : BPtr) (n : UInt32) {r : BRef} {o : Nat} {d : Array UInt8} (hp : p = .ref r o)
    (hg : Space.get H r = some d) (hn : o + n.toNat ≤ d.size) (k : X Unit) {Q : Except Ex Unit → IL → Heap → Prop}
    (hk : ∀ H' S', LI E l H' z S' → S'.mode = S.mode → S'.length = S.length → SatX H' l k Q) :
    SatX H l (do
      if ← ZlibNg.Inflate.hcrcOn E.c.st then
        let v ← ZlibNg.Crc32.crc32_small (← ZlibNg.Inflate.rdS E.c.st (·.check)).toUInt32 p n.toUInt64
        ZlibNg.Inflate.wrS E.c.st fun s => { s with check := v.toUInt64 }
      k) Q := by
  refine SatX.bind (SatX.lift_eq li.hcrcOn ?_)
  dsimp only
  split
  · refine SatX.bind (SatX.lift_eq (li.rdS (·.check)) ?_)
    rw [hp]
    obtain ⟨v, ev, -⟩ := ZlibNgF.Proof.Crc32.crc32_small_ok (li.crcTab eo) hg S.check.toUInt32 o n.toUInt64
      (by rw [UInt32.toNat_toUInt64]; omega)
    refine SatX.bind (SatX.lift_eq ev ?_)
    refine SatX.bind (SatX.lift (Sat.mono (li.wrS (fun s => { s with check := v.toUInt64 }) (fun _ _ c => c) rfl) ?_))
    intro _ H1 li1
    exact hk _ _ li1 rfl rfl
  · exact hk _ _ li rfl rfl

/-- The end of the `copy != 0` branch of `EXTRA`: the header check value, `next += copy`, `have -= copy`,
`state->length -= copy`. -/
theorem extraTail_ok {E : Env} (eo : EnvOK E) {l : IL} {H : Heap} {z : ZStream} {S : InflateState}
    (li : LI E l H z S) (hS : S.mode = EXTRA) (lc : IL) (c : UInt32) (hsame : Same lc l) (hc : c ≤ lc.have_)
    (hc0 : c ≠ 0) (k : X Unit) {Q : Except Ex Unit → IL → Heap → Prop}
    (hk : ∀ l' H' S', LI E l' H' z S' → S'.mode = EXTRA → l'.have_.toNat + c.toNat = lc.have_.toNat →
      l'.bits = lc.bits → l'.left = lc.left → SatX H' l' k Q) :
    SatX H l (do
      if ← ZlibNg.Inflate.hcrcOn E.c.st then
        let v ← ZlibNg.Crc32.crc32_small (← ZlibNg.Inflate.rdS E.c.st (·.check)).toUInt32 lc.next c.toUInt64
        ZlibNg.Inflate.wrS E.c.st fun s => { s with check := v.toUInt64 }
      let nx ← lc.next.add (Int.ofNat c.toNat)
      modify fun l => { l with have_ := l.have_ - c, next := nx }
      ZlibNg.Inflate.wrS E.c.st fun s => { s with length := s.length - c }
      k) Q := by
  have hc' : c.toNat ≤ l.have_.toNat := by rw [hsame.2.1]; exact hc
  have hc0' : 0 < c.toNat := by
    rcases Nat.eq_zero_or_pos c.toNat with e | e
    · exact absurd (UInt32.toNat_inj.mp (by rw [e]; rfl)) hc0
    · exact e
  have hh : l.have_ ≠ 0 := fun e => by rw [e] at hc'; exact absurd hc' (by show ¬ (c.toNat ≤ 0); omega)
  obtain ⟨r, o, d, hnx, hg, hsz⟩ := li.inBytes eo hh
  have hnx' : lc.next = .ref r o := by rw [← hsame.1]; exact hnx
  refine crcE_tail eo li lc.next c hnx' hg (by omega) _ ?_
  intro H1 S1 li1 hm1 _
  rw [hnx']
  obtain ⟨r1, o1, d1, hnx1, hg1', hsz1⟩ := li1.inBytes eo hh
  rw [hnx] at hnx1
  obtain ⟨rfl, rfl⟩ : r = r1 ∧ o = o1 := by cases hnx1; exact ⟨rfl, rfl⟩
  refine SatX.bind (SatX.lift_eq (add_in hg1' (by omega)) ?_)
  refine SatX.bind (SatX.modify ?_)
  have hcl' : c ≤ l.have_ := by rw [hsame.2.1]; exact hc
  have li2 := li1.consume hnx c hcl' { l with have_ := l.have_ - c, next := .ref r (o + c.toNat) }
    rfl rfl rfl rfl rfl rfl
  refine SatX.bind (SatX.lift (Sat.mono (li2.wrS (fun s => { s with length := s.length - c })
    (fun _ _ cc => { cc with }) rfl) ?_))
  intro _ H2 li3
  refine hk _ _ _ li3 (by rw [← hS, ← hm1]) ?_ hsame.2.2.1 hsame.2.2.2.1
  show (l.have_ - c).toNat + c.toNat = lc.have_.toNat
  rw [UInt32.toNat_sub_of_le _ _ hcl', ← hsame.2.1]; omega

/-- The header part of the `copy != 0` branch of `EXTRA`: the copy into `head->extra`. -/
theorem extraHdr_ok {E : Env} (eo : EnvOK E) {l : IL} {H : Heap} {z : ZStream} {S : InflateState}
    (li : LI E l H z S) (lc : IL) (c : UInt32) (hsame : Same lc l) (hc : c ≤ lc.have_)
    (hc0 : c ≠ 0) (k : X Unit) {Q : Except Ex Unit → IL → Heap → Prop}
    (hk : ∀ l' H', LI E l' H' z S → Same l l' → SatX H' l' k Q) :
    SatX H l (do
      let hd ← headOf E.c.st
      if hd != none then
        let g ← ldHeader hd
        if g.extra != .null && S.length ≤ g.extra_len then
          let len := g.extra_len - S.length
          modify fun l => { l with len := len }
          if len < g.extra_max then
            let n := if c > g.extra_max - len then g.extra_max - len else c
            Ptr.memcpy (← g.extra.add (Int.ofNat len.toNat)) lc.next n.toNat
      k) Q := by
  have hs0 : Same l l := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine SatX.bind (SatX.lift_eq li.headOf ?_)
  dsimp only
  cases hhp : E.hp with
  | none =>
    have he : ((none : HeaderPtr) != none) = false := rfl
    simp only [he, Bool.false_eq_true, ↓reduceIte]
    exact hk _ _ li hs0
  | some kk =>
    have hne : (some kk != (none : HeaderPtr)) = true := rfl
    simp only [hne, ↓reduceIte]
    obtain ⟨g, hgk⟩ := li.hdrRec hhp
    refine SatX.bind (SatX.lift_eq (show ldHeader (some kk) H = .ok (g, H) by simp [ldHeader, hgk]) ?_)
    dsimp only
    split
    · rename_i hxn
      have hx : g.extra ≠ .null := by simp only [Bool.and_eq_true, bne_iff_ne] at hxn; exact hxn.1
      rcases (li.hbufs eo hhp hgk).1 with h0 | ⟨bd, off, data, hfe, hd, hsz', hbne, hw, hdj⟩
      · exact absurd h0 hx
      refine SatX.bind (SatX.modify ?_)
      dsimp only
      have li1 : LI E { l with len := g.extra_len - S.length } H z S := li.locals rfl rfl rfl rfl rfl rfl
      have hs1 : Same l { l with len := g.extra_len - S.length } := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      split
      · rename_i hlt
        have hlt' : (g.extra_len - S.length).toNat < g.extra_max.toNat := hlt
        have hsub : (g.extra_max - (g.extra_len - S.length)).toNat =
            g.extra_max.toNat - (g.extra_len - S.length).toNat :=
          UInt32.toNat_sub_of_le _ _ (UInt32.le_of_lt hlt)
        have hn : ∀ n : UInt32, n = (if c > g.extra_max - (g.extra_len - S.length) then
            g.extra_max - (g.extra_len - S.length) else c) →
            n.toNat + (g.extra_len - S.length).toNat ≤ g.extra_max.toNat ∧ n.toNat ≤ c.toNat := by
          intro n hn
          split at hn
          · rename_i hgt
            subst hn
            have hgt' : (g.extra_max - (g.extra_len - S.length)).toNat < c.toNat := hgt
            omega
          · rename_i hgt
            rw [hn]
            have : ¬ (g.extra_max - (g.extra_len - S.length)).toNat < c.toNat := hgt
            omega
        generalize hN : (if c > g.extra_max - (g.extra_len - S.length) then
          g.extra_max - (g.extra_len - S.length) else c) = n
        obtain ⟨hn1, hn2⟩ := hn n hN.symm
        rw [hfe]
        rw [hfe] at hw hdj
        refine SatX.bind (SatX.lift_eq (add_heap hd (by omega)) ?_)
        have hc' : c.toNat ≤ l.have_.toNat := by rw [hsame.2.1]; exact hc
        have hh : l.have_ ≠ 0 := fun e => by
          rw [e] at hc'
          have e0 : (0 : UInt32).toNat = 0 := rfl
          exact hc0 (UInt32.toNat_inj.mp (by show c.toNat = 0; omega))
        obtain ⟨r, o, d, hnx, hg, hsz⟩ := li.inBytes eo hh
        have hnx' : lc.next = .ref r o := by rw [← hsame.1]; exact hnx
        rw [hnx']
        have hov : r = .heap bd → (off + (g.extra_len - S.length).toNat) + n.toNat ≤ o ∨
            o + n.toNat ≤ off + (g.extra_len - S.length).toNat := by
          intro er
          obtain ⟨hle, hat⟩ := li.inAt
          have hle' : l.have_.toNat ≤ E.A0.toNat := hle
          rcases hinp : E.inp with _ | ⟨r0, o0⟩
          · rw [hinp, hnx] at hat; cases hat.1
          · rw [hinp] at hat hdj
            rw [hnx] at hat
            injection hat with f1 f2
            subst f1 er
            rw [UInt32.toNat_sub_of_le _ _ hle] at f2
            rcases hdj with hne | hdj | hdj
            · exact absurd rfl hne
            · right; omega
            · left; omega
        refine SatX.bind (SatX.lift (Sat.of_eq (memcpy_heap' hd hg hov (by omega) (by omega)) ?_))
        refine hk _ _ (li1.wrBytes hd hbne (copyFold_size _ _ _ _ _) (copyFold_out _ _ _ _ _) hw
          (Nat.le_add_right _ _) (by omega)) hs1
      · exact hk _ _ li1 hs1
    · exact hk _ _ li hs0

theorem run_EXTRA (E : Env) (eo : EnvOK E) (hN : ModeRun E inflate_NAME (·.mode = NAME)) :
    ModeRun E inflate_EXTRA (·.mode = EXTRA) := by
  intro l H z S li hm m hμ
  have hμ' : 32 * (8 * l.have_.toNat + l.bits.toNat + l.left.toNat) + 21 ≤ m := by
    unfold μ at hμ; rwa [hm, rank_EXTRA] at hμ
  unfold inflate_EXTRA
  refine SatX.bind (SatX.lift_eq li.ldState ?_)
  dsimp (config := { zeta := false }) only
  by_cases hf : (S.flags &&& 1024 != 0) = true
  · refine SatX.ite (fun _ => ?_) (fun h => absurd hf h)
    refine SatX.bind (SatX.get ?_)
    dsimp (config := { zeta := false }) only
    extract_lets copy jp2 jpc cp2
    suffices key : ∀ c, c ≤ l.have_ → (c = l.have_ ∨ c = copy) → SatX H l (jpc () c) (Post E m) by
      refine SatX.ite (fun h => key _ (UInt32.le_refl _) (Or.inl rfl)) (fun h => key _ ?_ (Or.inr rfl))
      exact UInt32.not_lt.mp h
    intro c hc1 hcv
    dsimp (config := { zeta := false }) only [jpc]
    refine SatX.bind (SatX.modify ?_)
    dsimp (config := { zeta := false }) only
    have li1 : LI E { l with copy := c } H z S := li.locals rfl rfl rfl rfl rfl rfl
    have hs1 : Same l { l with copy := c } := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    split
    · rename_i hc0'
      have hc0 : c ≠ 0 := by simpa using hc0'
      refine extraHdr_ok eo li1 l c hs1 hc1 hc0 _ ?_
      intro l' H' li' hs'
      refine extraTail_ok eo li' hm l c (hs1.trans hs') hc1 hc0 _ ?_
      intro l'' H'' S'' li'' hm'' hh hb hl
      have hA : l''.have_ < E.A0 := by
        have h1 : l.have_.toNat ≤ E.A0.toNat := li.inAt.1
        have h2 : 0 < c.toNat := by
          rcases Nat.eq_zero_or_pos c.toNat with e | e
          · exact absurd (UInt32.toNat_inj.mp (by rw [e]; rfl)) hc0
          · exact e
        rw [UInt32.lt_iff_toNat_lt]; omega
      refine leaveLen li'' _ (fun _ => Why.read hA)
        (fun _ => tailN hN li'' ?_ (li''.outEq (by rw [hm'']; decide)))
      rw [hb, hl]; omega
    · rename_i hc0'
      have hc0 : c = 0 := by simpa using hc0'
      refine leaveLen li1 _ (fun hl => ?_) (fun _ => tailN hN li1
        (by show 32 * (8 * l.have_.toNat + l.bits.toNat + l.left.toNat) + 20 ≤ m; omega)
        (li1.outEq (by rw [hm]; decide)))
      rcases hcv with e | e
      · exact Why.have0 (show l.have_ = 0 by rw [← e, hc0])
      · exact absurd (show S.length = 0 by rw [← hc0, e]) hl
  · refine SatX.ite (fun h => absurd h hf) (fun _ => ?_)
    exact tailN hN li (by omega) (li.outEq (by rw [hm]; decide))

end ZlibNgF.Proof.InflateLoop
