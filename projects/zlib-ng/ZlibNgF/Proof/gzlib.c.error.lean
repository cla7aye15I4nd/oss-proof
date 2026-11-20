import ZlibNgF.Proof.«gzlib.c.seek»

/-!
# `gz_error` with a message (`ZlibNgF`)

`gz_error(state, err, msg)` with a message (`gzlib.c:580-607`): after the part that frees the old message and stores
`err` (`gz_error_null` covers it), it allocates `strlen(path) + strlen(msg) + 3` bytes and writes
`path ": " msg` into them with `snprintf`. The new block is fresh, so the heap grows only by blocks from `nextBlk` on
and by static strings (`HExt`); the message of the state is `NULL` (no allocation for `Z_MEM_ERROR`, or `malloc`
failed and `err` becomes `Z_MEM_ERROR`) or the new block, which `GzMsg` accepts because it asks only for a live block.

The literal `": "` is read with `strlen`, so the literal table of the world must hold the literals it names
(`LitOk`): a static string in C, made at its first use in the model.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace ZlibNgF.Proof.GzMode
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Gz ZlibNgF.Proof.GzInv ZlibNgF.Proof.GzSat

/-! ## Heaps that grow by fresh blocks and static strings -/

/-- `h'` differs from `h` only by blocks numbered from `h.nextBlk` on and by added static strings. -/
structure HExt (h h' : Heap) : Prop where
  old : ∀ c, c < h.nextBlk → h'.bytes c = h.bytes c ∧ h'.savedPtrs c = h.savedPtrs c
  beyond : ∀ c, h'.nextBlk ≤ c → h'.bytes c = h.bytes c
  next : h.nextBlk ≤ h'.nextBlk
  streams : h'.streams = h.streams
  istates : h'.istates = h.istates
  iallocs : h'.iallocs = h.iallocs
  dstates : h'.dstates = h.dstates
  dallocs : h'.dallocs = h.dallocs
  crc : h'.crcTable = h.crcTable
  x2n : h'.x2nTable = h.x2nTable
  base : h'.baseAddr = h.baseAddr
  hdr : h'.gzheaders = h.gzheaders
  consts : ∀ k a, h.consts k = some a → h'.consts k = some a

theorem HExt.refl (h : Heap) : HExt h h :=
  ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl, Nat.le_refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ e => e⟩

theorem HExt.trans {a b c : Heap} (x : HExt a b) (y : HExt b c) : HExt a c := by
  refine ⟨fun k hk => ?_, fun k hk => ?_, Nat.le_trans x.next y.next, y.streams.trans x.streams,
    y.istates.trans x.istates, y.iallocs.trans x.iallocs, y.dstates.trans x.dstates, y.dallocs.trans x.dallocs,
    y.crc.trans x.crc, y.x2n.trans x.x2n, y.base.trans x.base, y.hdr.trans x.hdr, fun k a e => y.consts k a (x.consts k a e)⟩
  · have hk' : k < b.nextBlk := Nat.lt_of_lt_of_le hk x.next
    exact ⟨(y.old k hk').1.trans (x.old k hk).1, (y.old k hk').2.trans (x.old k hk).2⟩
  · rw [y.beyond k hk, x.beyond k (Nat.le_trans y.next hk)]

/-- An object of `h` is an object of a heap that grows from it. -/
theorem HExt.get {h h' : Heap} (x : HExt h h') (fr : FreshBlocks h) (r : BRef) (d : Array UInt8)
    (hd : Space.get h r = some d) : Space.get h' r = some d := by
  cases r with
  | heap c =>
    have hc : c < h.nextBlk := by
      refine Nat.lt_of_not_le fun hc => ?_
      have e : h.bytes c = some d := hd
      rw [(fr c hc).2.2] at e; cases e
    show h'.bytes c = some d
    rw [(x.old c hc).1]; exact hd
  | const k => exact x.consts k d hd
  | str k => exact hd

theorem HExt.cstr {h h' : Heap} (x : HExt h h') (fr : FreshBlocks h) {p : BPtr} {n : Nat} (hp : CStringLen h p n) :
    CStringLen h' p n :=
  GzOpen.cstr_of_get (x.get fr) hp

theorem HExt.fresh {h h' : Heap} (x : HExt h h') (fr : FreshBlocks h) : FreshBlocks h' := by
  intro c hc
  refine ⟨by rw [x.istates]; exact (fr c (Nat.le_trans x.next hc)).1,
    by rw [x.iallocs]; exact (fr c (Nat.le_trans x.next hc)).2.1, ?_⟩
  rw [x.beyond c hc]; exact (fr c (Nat.le_trans x.next hc)).2.2

theorem HExt.nalloc (h : Heap) : HExt h { h with nalloc := h.nalloc + 1 } :=
  ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl, Nat.le_refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ e => e⟩

theorem HExt.alloc (h : Heap) (n : Nat) : HExt h (GzOpen.allocH h n) := by
  refine ⟨fun c hc => ?_, fun c hc => ?_, by simp [GzOpen.allocH], rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    fun _ _ e => e⟩
  · have hne : c ≠ h.nextBlk := by omega
    simp [GzOpen.allocH, upd_ne _ _ _ _ hne]
  · have hne : c ≠ h.nextBlk := by simp [GzOpen.allocH] at hc; omega
    simp [GzOpen.allocH, upd_ne _ _ _ _ hne]

theorem HExt.lit (h : Heap) (a : Array UInt8) : HExt h { h with consts := upd h.consts h.consts.arr.size (some a) } :=
  ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl, Nat.le_refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    fun k b e => GzReach.consts_grow h a k b e⟩

/-- A store into a block that is fresh with respect to `h0`. -/
theorem HExt.store {h0 h : Heap} (x : HExt h0 h) {c : Nat} (hc : h0.nextBlk ≤ c) (hc' : c < h.nextBlk)
    {a : Array UInt8} (ha : h.bytes c = some a) (g : Array UInt8 → Array UInt8) :
    HExt h0 { h with bytes := h.bytes.modify c (Option.map g) } := by
  have hg := GzOpen.modify_some h.bytes c a g ha
  refine ⟨fun y hy => ⟨?_, (x.old y hy).2⟩, fun y hy => ?_, x.next, x.streams, x.istates, x.iallocs, x.dstates,
    x.dallocs, x.crc, x.x2n, x.base, x.hdr, x.consts⟩
  · show (h.bytes.modify c (Option.map g)) y = _
    simp only [hg, show y ≠ c by omega, ite_false]; exact (x.old y hy).1
  · show (h.bytes.modify c (Option.map g)) y = _
    simp only [hg, show y ≠ c by simp at hy; omega, ite_false]; exact x.beyond y hy

/-! ## The literal table -/

/-- A literal without a zero byte. -/
def NoNul (lit : String) : Prop := ∀ j, j < lit.toUTF8.size → lit.toUTF8.data[j]! ≠ 0

instance (lit : String) : Decidable (NoNul lit) := by unfold NoNul; infer_instance

theorem litBytes_cstr {h : Heap} {k : Nat} {lit : String} (hk : h.consts k = some (Heap.litBytes lit))
    (hn : NoNul lit) : CStringLen h (.ref (.const k) 0) lit.toUTF8.size := by
  have e : lit.toUTF8.data.size = lit.toUTF8.size := rfl
  have hn' : ∀ j, j < lit.toUTF8.size → lit.toUTF8.data[j]! ≠ 0 := hn
  have hk' : Space.get h (BRef.const k) = some (lit.toUTF8.data.push 0) := hk
  generalize lit.toUTF8.size = n at e hn'
  generalize lit.toUTF8.data = a at e hn' hk'
  subst e
  refine ⟨.const k, 0, a.push 0, rfl, hk', by simp, ?_, fun j hj => ?_⟩
  · rw [Nat.zero_add, getElem!_pos _ _ (by simp), Array.getElem_push_eq]
  · have := hn' j hj
    rw [Nat.zero_add, getElem!_pos _ _ (by simp; omega), Array.getElem_push_lt hj]
    rwa [getElem!_pos a j hj] at this

/-- `gzLit` of a literal of the table: a static string holding the literal, which stays in the table. -/
theorem gzLit_spec (lit : String) (i : Nat) (hi : gzLits.findIdx? (· == lit) = some i) (hl : gzLits[i]? = some lit)
    (hn : NoNul lit) {w : World} {h : Heap} (hw : LitOk w h) :
    GSat w h (gzLit lit) (fun p W H => W.gzs = w.gzs ∧ W.fs = w.fs ∧ HExt h H ∧ LitOk W H ∧
      CStringLen H p lit.toUTF8.size ∧ ∀ c o, p ≠ .ref (.heap c) o) := by
  cases hk : w.litKeys.find? (·.1 == i) with
  | some e =>
    have hm := List.mem_of_find?_eq_some hk
    have he : e.1 = i := by simpa using List.find?_some hk
    obtain ⟨lit', e1, e2⟩ := hw e hm
    rw [he, hl] at e1; cases e1
    refine ⟨.ref (.const e.2) 0, w, h, by simp [gzLit, hi, hk, StateT.run, bind, StateT.bind, get, getThe,
      MonadStateOf.get, StateT.get, pure, StateT.pure], rfl, rfl, HExt.refl h, hw, litBytes_cstr e2 hn,
      fun c o e => by cases e⟩
  | none =>
    refine ⟨.ref (.const h.consts.arr.size) 0, { w with litKeys := (i, h.consts.arr.size) :: w.litKeys },
      { h with consts := upd h.consts h.consts.arr.size (some (Heap.litBytes lit)) }, ?_, rfl, rfl, HExt.lit h _, ?_,
      litBytes_cstr (by simp) hn, fun c o e => by cases e⟩
    · simp [gzLit, hi, hk, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
        StateT.pure, lm, StateT.lift, newConst, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet]
    · intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact ⟨lit, hl, by simp⟩
      · exact (LitOk.ext (w' := w) hw rfl fun k a e => GzReach.consts_grow h _ k a e) p hp

/-! ## The part of `gz_error` that makes the message -/

open ZlibNg.Inflate in
/-- The part of `gz_error` after `state->err = err` (`gzlib.c:594-606`), copied from the translation. -/
def errTail (state : GzPtr) (err : Int32) (msg : BPtr) : G Unit := do
  if msg == .null then
    return
  if err == Z_MEM_ERROR then
    return
  let m ← lm (allocB ((← lm (strlenB (← (← ldGz state).path.get))) + (← lm (strlenB msg)) + 3).toNat)
  wrG state fun s => { s with msg := .val m }
  if m == .null then
    wrG state fun s => { s with err := Z_MEM_ERROR }
    return
  let path ← (← ldGz state).path.get
  let n := (← lm (strlenB path)) + (← lm (strlenB msg)) + 3
  let _ ← lm (snprintfSSS (← (← ldGz state).msg.get) n path (← (gzLit ": ")) msg)

/-- `gz_error` is its first part (`gz_error_null`), then `errTail`. -/
theorem gz_error_run {w : World} {h : Heap} {b : Nat} {s : GzState} (hs : w.gz h b = some s) (hm : GzMsg h s)
    (hbc : ∀ c o, s.msg = .val (.ref (.heap c) o) → c ≠ b) (e : Int32) (msg : BPtr) :
    gz_error (some b) e msg w h =
      errTail (some b) e msg { w with gzs := upd w.gzs b (some (errSt s e)) } (freeMsg h s) := by
  obtain ⟨db, hdb⟩ := gz_live hs
  rcases hm.msg with hn | ⟨c, d, hc, e2⟩
  · by_cases he : e ≠ ZlibNg.Inflate.Z_OK ∧ e ≠ ZlibNg.Inflate.Z_BUF_ERROR <;>
    simp [gz_error, errTail, ldGz_app hs, wrG_app hs, hn, freeMsg, errSt, he,
      Ival.get, liftM, monadLift, MonadLift.monadLift, wrG_upd hdb, ldGz_upd hdb, rdG_upd hdb, InflateInv.upd_upd]
  · have hd : h.bytes c = some d := e2
    by_cases hme : s.err = ZlibNg.Inflate.Z_MEM_ERROR
    · exact absurd (hm.mem hme) (by rw [hc]; simp)
    have hcb := hbc c 0 hc
    have hdb1 : (upd h.bytes c none) b = some db := by rw [upd_ne _ _ _ _ hcb.symm]; exact hdb
    have hs1 : w.gz { h with bytes := upd h.bytes c none, savedPtrs := upd h.savedPtrs c none } b = some s := by
      unfold World.gz at hs ⊢; simp only [hdb1]; rw [hdb] at hs; exact hs
    by_cases he : e ≠ ZlibNg.Inflate.Z_OK ∧ e ≠ ZlibNg.Inflate.Z_BUF_ERROR <;>
    simp [gz_error, errTail, ldGz_app hs, rdG_app' hs, wrG_app hs1, hc, freeMsg, errSt, he, hme,
        Ival.get, liftM, monadLift, MonadLift.monadLift,
        wrG_upd (h := { h with bytes := upd h.bytes c none, savedPtrs := upd h.savedPtrs c none }) hdb1,
        ldGz_upd (h := { h with bytes := upd h.bytes c none, savedPtrs := upd h.savedPtrs c none }) hdb1, freeB, hd,
        InflateInv.upd_upd]

/-- `snprintf(buf, size, "%s%s%s", a, b, c)` into a block of `size` bytes: it writes into that block only. -/
theorem snprintfSSS_blk {H : Heap} {c : Nat} {a : Array UInt8} (ha : H.bytes c = some a) (N : UInt64)
    (hN : a.size = N.toNat) {p1 p2 p3 : BPtr} {n1 n2 n3 : Nat} (h1 : CStringLen H p1 n1) (h2 : CStringLen H p2 n2)
    (h3 : CStringLen H p3 n3) :
    ∃ r H', snprintfSSS (.ref (.heap c) 0) N p1 p2 p3 H = .ok (r, H') ∧
      (H' = H ∨ ∃ g, H' = { H with bytes := H.bytes.modify c (Option.map g) }) := by
  obtain ⟨b1, e1, -, -⟩ := GzOpen.strBytes_of h1
  obtain ⟨b2, e2, -, -⟩ := GzOpen.strBytes_of h2
  obtain ⟨b3, e3, -, -⟩ := GzOpen.strBytes_of h3
  by_cases hN0 : N = 0
  · exact ⟨_, H, by simp only [snprintfSSS, snprintfOut, bind_app, e1, e2, e3, hN0]; simp; rfl, Or.inl rfl⟩
  · have hpos : 1 ≤ N.toNat := by
      have : N.toNat ≠ 0 := fun e => hN0 (UInt64.toNat_inj.mp (by simpa using e))
      omega
    have est := GzOpen.storeBytes_heap (h := H) (c := c) (off := 0) (cap := N.toNat)
      (bs := ((b1 ++ b2 ++ b3).extract 0 (min (b1 ++ b2 ++ b3).size (N.toNat - 1))).push 0) ha (by omega)
      (by simp; omega)
    have hN0' : (N != 0) = true := by simpa using hN0
    exact ⟨_, _, by simp only [snprintfSSS, snprintfOut, bind_app, e1, e2, e3, hN0', ite_true, est]; simp; exact ⟨rfl, rfl⟩,
      Or.inr ⟨_, rfl⟩⟩

/-- What `gz_error` leaves as message and error: `NULL` for `Z_MEM_ERROR`, otherwise `NULL` with `Z_MEM_ERROR` (the
allocation failed) or a live block numbered from `n` on. -/
def MsgNew (n : Nat) (H : Heap) (e : Int32) (mv : Ival BPtr) (ev : Int32) : Prop :=
  (ev = ZlibNg.Inflate.Z_MEM_ERROR → mv = .val .null) ∧ (ev = e ∨ ev = ZlibNg.Inflate.Z_MEM_ERROR) ∧
  (mv = .val .null ∨ ∃ c, mv = .val (.ref (.heap c) 0) ∧ n ≤ c ∧ ∃ d, H.bytes c = some d)

theorem errTail_spec {w : World} {h : Heap} {b : Nat} {s : GzState} (hs : w.gz h b = some s)
    (hfr : FreshBlocks h) (hlit : LitOk w h) (hp : OwnedStr h s.path) (hs0 : s.msg = .val .null) (e : Int32)
    (he0 : s.err = e) (msg : BPtr) (hmsg : msg = .null ∨ CStr h msg) :
    GSat w h (errTail (some b) e msg) (fun _ W H => ∃ mv ev,
      (∀ c, c ≠ b → W.gzs c = w.gzs c) ∧ W.gz H b = some { s with msg := mv, err := ev } ∧ W.fs = w.fs ∧
      HExt h H ∧ LitOk W H ∧ MsgNew h.nextBlk H e mv ev) := by
  have done : GSat w h (pure () : G Unit) (fun _ W H => ∃ mv ev,
      (∀ c, c ≠ b → W.gzs c = w.gzs c) ∧ W.gz H b = some { s with msg := mv, err := ev } ∧ W.fs = w.fs ∧
      HExt h H ∧ LitOk W H ∧ MsgNew h.nextBlk H e mv ev) :=
    GSat.pure ⟨s.msg, s.err, fun _ _ => rfl, by rw [hs], rfl, HExt.refl h, hlit, fun _ => hs0,
      Or.inl he0, Or.inl hs0⟩
  unfold errTail
  apply GSat.ite
  · intro _; exact done
  intro hmn
  have hmn' : msg ≠ .null := by intro e; simp [e] at hmn
  obtain ⟨nm, hmsg⟩ := hmsg.resolve_left hmn'
  apply GSat.ite
  · intro _; exact done
  intro heM
  obtain ⟨cp, np, hpe, hcp⟩ := hp
  obtain ⟨db, hdb⟩ := gz_live hs
  have hbn : b < h.nextBlk := by
    refine Nat.lt_of_not_le fun hc => ?_
    rw [(hfr b hc).2.2] at hdb; cases hdb
  refine GSat.bind (GSat.of_eq (ldGz_app hs) ?_)
  refine GSat.bind (GSat.of_eq (GzOpen.liftGet_app hpe _ _) ?_)
  refine GSat.bind (GSat.lm ⟨_, h, GzOpen.strlenB_of hcp, ?_⟩)
  refine GSat.bind (GSat.lm ⟨_, h, GzOpen.strlenB_of hmsg, ?_⟩)
  by_cases hok : h.allocOk h.nalloc = true
  · refine GSat.bind (GSat.lm ⟨_, _, GzOpen.allocB_ok hok _, ?_⟩)
    have x1 := HExt.alloc h (UInt64.ofNat np + UInt64.ofNat nm + 3).toNat
    have hb1 : (GzOpen.allocH h (UInt64.ofNat np + UInt64.ofNat nm + 3).toNat).bytes b = some db := by rw [(x1.old b hbn).1]; exact hdb
    have hs1 : w.gz (GzOpen.allocH h (UInt64.ofNat np + UInt64.ofNat nm + 3).toNat) b = some s := by rw [GzOpen.gz_of_bytes (x1.old b hbn).1]; exact hs
    refine GSat.bind (GSat.of_eq (wrG_app hs1 _) ?_)
    apply GSat.ite
    · intro hc; simp at hc
    intro _
    have hs2 := gz_upd_same hs1 { s with msg := .val (.ref (.heap h.nextBlk) 0) }
    refine GSat.bind (GSat.of_eq (ldGz_app hs2) ?_)
    refine GSat.bind (GSat.of_eq (GzOpen.liftGet_app hpe _ _) ?_)
    refine GSat.bind (GSat.lm ⟨_, _, GzOpen.strlenB_of (x1.cstr hfr hcp), ?_⟩)
    refine GSat.bind (GSat.lm ⟨_, _, GzOpen.strlenB_of (x1.cstr hfr hmsg), ?_⟩)
    refine GSat.bind (GSat.of_eq (ldGz_app hs2) ?_)
    refine GSat.bind (GSat.of_eq (GzOpen.liftGet_app rfl _ _) ?_)
    have hL11 : gzLits.findIdx? (· == ": ") = some 11 := by simp [gzLits, List.findIdx?_cons]
    refine GSat.bind (GSat.mono (gzLit_spec ": " 11 hL11 (by decide) (by decide) (LitOk.ext hlit rfl fun _ _ e => e))
      fun p W3 H3 q => ?_)
    obtain ⟨hg3, hf3, x3, hl3, hc3, -⟩ := q
    have x13 := x1.trans x3
    have hn1 : h.nextBlk < (GzOpen.allocH h (UInt64.ofNat np + UInt64.ofNat nm + 3).toNat).nextBlk := by
      simp [GzOpen.allocH]
    have hd3 : H3.bytes h.nextBlk = some (Array.ofFn (n := (UInt64.ofNat np + UInt64.ofNat nm + 3).toNat)
        fun j => Junk.of (h.garbage h.nalloc j.val)) := by
      rw [(x3.old _ hn1).1]; simp [GzOpen.allocH]
    obtain ⟨r, H4, e4, hH4⟩ := snprintfSSS_blk hd3 (UInt64.ofNat np + UInt64.ofNat nm + 3) (by simp)
      (x13.cstr hfr hcp) hc3 (x13.cstr hfr hmsg)
    refine GSat.bind (GSat.lm ⟨r, H4, e4, ?_⟩)
    have x4 : HExt h H4 := by
      rcases hH4 with rfl | ⟨g, rfl⟩
      · exact x13
      · exact x13.store (Nat.le_refl _) (Nat.lt_of_lt_of_le hn1 x3.next) hd3 g
    have hb4 : H4.bytes b = some db := by rw [(x4.old b hbn).1]; exact hdb
    refine GSat.pure ⟨.val (.ref (.heap h.nextBlk) 0), e, fun c hc => by rw [hg3]; simp [upd_ne _ _ _ _ hc], ?_,
      hf3, x4, ?_, fun hm => absurd hm (by simpa using heM), Or.inl rfl, Or.inr ⟨h.nextBlk, rfl, Nat.le_refl _, ?_⟩⟩
    · unfold World.gz; rw [hb4, hg3]; simp [← he0]
    · rcases hH4 with rfl | ⟨g, rfl⟩
      · exact hl3
      · exact LitOk.ext hl3 rfl fun _ _ e => e
    · rcases hH4 with rfl | ⟨g, rfl⟩
      · exact ⟨_, hd3⟩
      · exact ⟨_, by show (H3.bytes.modify _ _) _ = _; rw [GzOpen.modify_some _ _ _ _ hd3]; simp; rfl⟩
  · refine GSat.bind (GSat.lm ⟨.null, { h with nalloc := h.nalloc + 1 }, by simp [allocB, hok], ?_⟩)
    have hs1 : w.gz { h with nalloc := h.nalloc + 1 } b = some s := hs
    refine GSat.bind (GSat.of_eq (wrG_app hs1 _) ?_)
    apply GSat.ite
    · intro _
      have hs2 := gz_upd_same hs1 { s with msg := .val .null }
      refine GSat.bind (GSat.of_eq (wrG_app hs2 _) ?_)
      refine GSat.pure ⟨.val .null, ZlibNg.Inflate.Z_MEM_ERROR, fun c hc => by simp [upd_ne _ _ _ _ hc], ?_, rfl,
        HExt.nalloc h, LitOk.ext hlit rfl fun _ _ e => e, fun _ => rfl, Or.inr rfl, Or.inl rfl⟩
      simp [InflateInv.upd_upd]; exact gz_upd_same hs1 _
    · intro hc; simp at hc

/-! ## The fields after `gz_error` -/

/-- `x.have = 0` (or unchanged) keeps the fields. -/
theorem shape_have {h : Heap} {s : GzState} (sh : GzShape h s) (v : UInt32) (hv : v = 0 ∨ v = s.«have») :
    GzShape h { s with «have» := v } := by
  rcases hv with rfl | rfl
  · have P := sh.pos
    refine ⟨sh.mode, sh.path, sh.strm, sh.want_lo, sh.want_hi, sh.size, ⟨P.1, P.2, P.3, P.4⟩, ⟨sh.msg.1, sh.msg.2⟩,
      fun hr => ?_, fun hw => ⟨fun hsz => ?_, (sh.write hw).nobuf, rfl⟩, fun hz => sh.dead hz⟩
    rotate_left
    · obtain ⟨c, base, z, hb, hz, W⟩ := (sh.write hw).bufs hsz
      exact ⟨c, base, z, ⟨hb.1, hb.2, hb.3, hb.4, hb.5, hb.6⟩, hz, ⟨W.1, W.2, W.3, W.4, W.5⟩⟩
    have R := sh.read hr
    refine ⟨R.how, fun hsz => ?_, fun _ => rfl, fun hk => ?_, R.fresh,
      by have := R.pos_have; simp; omega, fun h1 h2 => by have := R.look_pos h1 h2; simp; omega⟩
    · obtain ⟨c, base, z, hb, hi, hz, -, hai, hreg, hmsg⟩ := R.bufs hsz
      exact ⟨c, base, z, ⟨hb.1, hb.2, hb.3, hb.4, hb.5, hb.6⟩, hi, hz, Or.inl rfl, hai, hreg, hmsg⟩
    · show s.pos.toInt + s.skip.toInt + ((0 : UInt32).toNat : Int) ≤ _
      simpa using sh.pos.pos_skip
  · exact sh

/-- The blocks of `h` an `HExt` step keeps. -/
theorem HK_ext {h H : Heap} (x : HExt h H) (s : GzState) (L : List Nat) (hlt : ∀ c ∈ L, c < h.nextBlk) :
    HK h H s L :=
  ⟨by rw [x.streams], fun c hc => (x.old c (hlt c hc)).1, fun c _ => by rw [x.istates],
    fun c _ => by rw [x.iallocs], fun c _ => by rw [x.dstates], fun c _ => by rw [x.dallocs], x.base, x.next,
    fun _ c _ hc0 hc1 => by rw [(x.old c hc1).1]; exact hc0, fun c hc => (x.old c (hlt c hc)).2⟩

theorem freeMsg_consts (h : Heap) (s : GzState) : (freeMsg h s).consts = h.consts := by
  unfold freeMsg; split <;> (try split) <;> rfl

theorem freeMsg_next (h : Heap) (s : GzState) : (freeMsg h s).nextBlk = h.nextBlk := (HLess.free h s).next

theorem HLess.freshB {h h' : Heap} (x : HLess h h') (fr : FreshBlocks h) : FreshBlocks h' := by
  intro c hc
  rw [x.next] at hc
  refine ⟨by rw [x.istates]; exact (fr c hc).1, by rw [x.iallocs]; exact (fr c hc).2.1, ?_⟩
  cases e : h'.bytes c with
  | none => rfl
  | some d => have := (fr c hc).2.2; rw [x.bytes c d e] at this; cases this

/-- The fields after the first part of `gz_error` (old message freed, `err` stored, `x.have` cleared on an error). -/
theorem err0_keep {h : Heap} {b : Nat} {s : GzState} (sh : GzShape h s) (hn : (ownL h b s).Nodup) (e : Int32) :
    GzShape (freeMsg h s) (errSt s e) ∧ (ownL (freeMsg h s) b (errSt s e)).Nodup := by
  have sh0 := shape_have sh (if e ≠ ZlibNg.Inflate.Z_OK ∧ e ≠ ZlibNg.Inflate.Z_BUF_ERROR then 0 else s.«have»)
    (by split <;> simp)
  have sh1 := shape_msg sh0 s.eof s.past e (.val .null) ⟨Or.inl rfl, fun _ => rfl⟩
  have e1 : errSt s e = { ({ s with «have» := if e ≠ ZlibNg.Inflate.Z_OK ∧ e ≠ ZlibNg.Inflate.Z_BUF_ERROR then 0
      else s.«have» }) with eof := s.eof, past := s.past, err := e, msg := .val .null } := rfl
  rw [← e1] at sh1
  have hL : ownL h b (errSt s e) = [b] ++ blkOf s.path ++ (if s.size = 0 then [] else blkOf s.buffers ++ stBlk h s) := by
    simp [ownL, errSt, blkOf, stBlk]; rfl
  have hnot : ∀ c ∈ ownL h b (errSt s e), c ∉ blkOf s.msg := by
    rw [hL]
    intro c hc hcm
    unfold ownL at hn
    rw [List.nodup_append] at hn
    simp only [List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · exact (List.nodup_append.mp hn.1).2.2 c (List.mem_append.mpr (Or.inl hc)) c hcm rfl
    · exact (List.nodup_append.mp hn.1).2.2 c (List.mem_append.mpr (Or.inr hc)) c hcm rfl
    · exact hn.2.2 c (List.mem_append.mpr (Or.inr hcm)) c hc rfl
  have hk : HK h (freeMsg h s) (errSt s e) (ownL h b (errSt s e)) := by
    refine ⟨by rw [freeMsg_streams], fun c hc => freeMsg_bytes h s c (hnot c hc), ?_, ?_, ?_, ?_, ?_, ?_,
      fun _ c _ hc0 _ => freeMsg_none h s c hc0, fun c hc => freeMsg_saved h s c (hnot c hc)⟩ <;>
      (try intro c _) <;> (unfold freeMsg; split <;> (try split) <;> first | rfl | exact Nat.le_refl _)
  obtain ⟨sh2, e2'⟩ := shape_keep sh1 hk
  refine ⟨sh2, ?_⟩
  rw [e2', hL]
  unfold ownL at hn
  rw [List.nodup_append] at hn ⊢
  exact ⟨(List.nodup_append.mp hn.1).1, hn.2.1, fun a ha b' hb' => hn.2.2 a (List.mem_append.mpr (Or.inl ha)) b' hb'⟩

/-! ## Steps of a call on a file -/

/-- `Frame` from `h` to `h2` through `h1`, where the library blocks of the second step that are older than `h` are
library blocks of the first. -/
theorem frame_trans {h h1 h2 : Heap} {S L L1 G : List Nat} {W : List (BPtr × Nat)} (f : Frame h h1 S L G W)
    (g : Frame h1 h2 S L1 G W) (hL : ∀ c ∈ L1, c < h.nextBlk → c ∈ L) : Frame h h2 S L G W := by
  obtain ⟨s1, g1, i1, b1, n1, c1, r1, x1, a1, k1⟩ := f
  obtain ⟨s2, g2, i2, b2, n2, c2, r2, x2, a2, k2⟩ := g
  have hn : ∀ c, c < h.nextBlk → c ∉ L → c ∉ L1 := fun c hc hn m => hn (hL c m hc)
  refine ⟨fun j hj => (s2 j hj).trans (s1 j hj), fun j hj => (g2 j hj).trans (g1 j hj),
    fun c hc hc' => ⟨((i2 c (by omega) (hn c hc hc')).1).trans (i1 c hc hc').1,
      ((i2 c (by omega) (hn c hc hc')).2).trans (i1 c hc hc').2⟩,
    fun c hc hc' data hd => ?_, fun c hc hc' hd => n2 c (by omega) (hn c hc hc') (n1 c hc hc' hd), c2.trans c1,
    r2.trans r1, x2.trans x1, a2.trans a1, Nat.le_trans k1 k2⟩
  obtain ⟨d2, e2, s2', q2⟩ := b1 c hc hc' data hd
  obtain ⟨d3, e3, s3, q3⟩ := b2 c (by omega) (hn c hc hc') d2 e2
  exact ⟨d3, e3, s3.trans s2', fun j hj hw => (q3 j (by omega) hw).trans (q2 j hj hw)⟩

/-- A step of a call on the file `b` (internal functions included): the frame of the call, the blocks of the file
after the step that are older than the start belonged to it before, and the embedded stream stays. -/
structure GStep (w : World) (h : Heap) (W : World) (H : Heap) (b : Nat) (wr : List (BPtr × Nat)) : Prop where
  frame : GzFrame w h W H (some b) wr
  own : ∀ c ∈ GzOwned W H (some b), c < h.nextBlk → c ∈ GzOwned w h (some b)
  strm : ∀ s s', w.gz h b = some s → W.gz H b = some s' → s'.strm = s.strm

theorem GStep.refl (w : World) (h : Heap) (b : Nat) (wr : List (BPtr × Nat)) : GStep w h w h b wr :=
  ⟨gzframe_refl w h _ wr, fun _ m _ => m, fun _ _ e1 e2 => by rw [e1] at e2; cases e2; rfl⟩

theorem frame_consts {h1 h2 : Heap} {S L G : List Nat} {W : List (BPtr × Nat)} (f : Frame h1 h2 S L G W)
    (K : Tbl (Option (Array UInt8))) : Frame { h1 with consts := K } { h2 with consts := K } S L G W := by
  obtain ⟨a, b, c, d, e, -, g, i, j, k⟩ := f
  exact ⟨a, b, c, d, e, rfl, g, i, j, k⟩

theorem GStep.trans {w w1 w2 : World} {h h1 h2 : Heap} {b : Nat} {wr : List (BPtr × Nat)}
    (x : GStep w h w1 h1 b wr) (y : GStep w1 h1 w2 h2 b wr) (h0b : ∃ s, w.gz h b = some s)
    (h1b : ∃ s1, w1.gz h1 b = some s1) : GStep w h w2 h2 b wr := by
  obtain ⟨⟨⟨f1, d1⟩, c1, g1⟩, o1, t1⟩ := x
  obtain ⟨⟨⟨f2, d2⟩, c2, g2⟩, o2, t2⟩ := y
  obtain ⟨s, hs⟩ := h0b
  obtain ⟨s1, hs1⟩ := h1b
  have k1 : h.nextBlk ≤ h1.nextBlk := f1.2.2.2.2.2.2.2.2.2
  simp only [hs, hs1] at f1 f2
  rw [t1 s s1 hs hs1] at f2
  have f2' := frame_consts f2 h.consts
  have hL : ∀ c ∈ GzOwned w1 h1 (some b), c < h.nextBlk → c ∈ GzOwned w h (some b) := o1
  refine ⟨⟨⟨?_, fun c hc hc' => ?_⟩, fun k a e => c2 k a (c1 k a e), fun b' hb' hlt => (g2 b' hb' (by omega)).trans
    (g1 b' hb' hlt)⟩, fun c hc hlt => o1 c (o2 c hc (by omega)) hlt, fun s0 s2 e0 e2 => ?_⟩
  · simp only [hs]
    exact frame_trans f1 f2' hL
  · have hc2 : c ∉ GzOwned w1 h1 (some b) := fun m => hc' (hL c m hc)
    exact ⟨(d2 c (by omega) hc2).1.trans (d1 c hc hc').1, (d2 c (by omega) hc2).2.trans (d1 c hc hc').2⟩
  · rw [hs] at e0; cases e0
    rw [t2 s1 s2 hs1 e2, t1 s s1 hs hs1]

/-! ## Well-formedness after a step that grows the heap -/

theorem wfr_ext {w W : World} {h h' : Heap} {b : Nat} {s : GzState} (hw : GzWFr w h) (hs : w.gz h b = some s)
    (hg : ∀ c, c ≠ b → W.gzs c = w.gzs c) (hgb : ∀ s', W.gzs b = some s' → s'.strm = s.strm)
    (hf : GzOpen.FsLe w.fs W.fs) (x : HExt h h') (hL : LitOk W h') : GzWFr W h' := by
  obtain ⟨hc, ⟨hfr, hdf⟩, hgz, hst, hb, hn, hlk, -⟩ := hw
  obtain ⟨d0, hd0⟩ := gz_live hs
  have hbn : b < h.nextBlk := by
    refine Nat.lt_of_not_le fun e => ?_
    rw [(hfr b e).2.2] at hd0; cases hd0
  have fs := GzOpen.FsLe.wf ⟨hb, hn, hlk⟩ hf
  refine ⟨⟨by rw [x.crc]; exact hc.1, by rw [x.x2n]; exact hc.2⟩, ⟨x.fresh hfr, fun c e => ?_⟩, fun c e => ?_,
    fun c s2 e => ?_, fs.1, fs.2.1, fs.2.2, hL⟩
  · rw [x.dstates, x.dallocs]; exact hdf c (Nat.le_trans x.next e)
  · rw [hg c (by have := x.next; omega)]; exact hgz c (Nat.le_trans x.next e)
  · unfold World.gz at e
    split at e
    · next d hd =>
      by_cases hcb : c = b
      · subst hcb; rw [hgb s2 e, x.streams]; exact hst c s hs
      · rw [hg c hcb] at e
        by_cases hlt : c < h.nextBlk
        · rw [(x.old c hlt).1] at hd
          obtain ⟨z, hz⟩ := hst c s2 (by unfold World.gz; rw [hd]; exact e)
          exact ⟨z, by rw [x.streams]; exact hz⟩
        · rw [hgz c (by omega)] at e; cases e
    · cases e

/-! ## The blocks of a read handle are live -/

theorem ownL_live {h : Heap} {b : Nat} {s : GzState} (sh : GzShape h s) (hr : s.mode = GZ_READ)
    (hb : ∃ d, h.bytes b = some d) : ∀ c ∈ ownL h b s, ∃ d, h.bytes c = some d := by
  intro c hc
  unfold ownL at hc
  simp only [List.mem_append, List.mem_singleton] at hc
  rcases hc with ((rfl | hc) | hc) | hc
  · exact hb
  · obtain ⟨c', n, e, r, off, d, e1, e2, -⟩ := sh.path
    rw [e] at hc; simp [blkOf] at hc; subst hc; cases e1; exact ⟨d, e2⟩
  · rcases sh.msg.msg with e | ⟨c', d, e, hd⟩
    · rw [e] at hc; simp [blkOf] at hc
    · rw [e] at hc; simp [blkOf] at hc; subst hc; exact ⟨d, hd⟩
  · split at hc
    · simp at hc
    · next hsz =>
      obtain ⟨c0, base, z, hbf, hi, hz, -, -, -⟩ := (sh.read hr).bufs hsz
      simp only [List.mem_append] at hc
      rcases hc with hc | hc
      · rw [hbf.buffers] at hc; simp [blkOf] at hc; subst hc
        obtain ⟨d, hd, -⟩ := hbf.fits; exact ⟨d, hd⟩
      · obtain ⟨i, z0, sb, st, al, e, hz0, hsb, hst, -, -⟩ := hi
        cases e; rw [hz] at hz0; cases hz0
        simp [stBlk, hz, hsb] at hc; subst hc
        unfold Heap.istate at hst; split at hst
        · next d hd => exact ⟨d, hd⟩
        · cases hst

theorem live_lt {h : Heap} (fr : FreshBlocks h) {c : Nat} (hc : ∃ d, h.bytes c = some d) : c < h.nextBlk := by
  obtain ⟨d, hd⟩ := hc
  refine Nat.lt_of_not_le fun e => ?_
  rw [(fr c e).2.2] at hd; cases hd

theorem ownL_msg {H : Heap} {b : Nat} {s : GzState} (hn : (ownL H b s).Nodup) (hs0 : s.msg = .val .null) (c : Nat)
    (hc : c ∉ ownL H b s) : (ownL H b { s with msg := .val (.ref (.heap c) 0) }).Nodup := by
  have e1 : ownL H b { s with msg := .val (.ref (.heap c) 0) } =
      ([b] ++ blkOf s.path) ++ ([c] ++ (if s.size = 0 then [] else blkOf s.buffers ++ stBlk H s)) := by
    simp [ownL, blkOf, stBlk]
  have e0 : ownL H b s = ([b] ++ blkOf s.path) ++ (if s.size = 0 then [] else blkOf s.buffers ++ stBlk H s) := by
    simp [ownL, hs0, blkOf]
  rw [e0] at hn hc
  rw [e1]
  rw [List.nodup_append] at hn ⊢
  refine ⟨hn.1, ?_, fun a ha a' ha' => ?_⟩
  · rw [List.nodup_append]
    exact ⟨by simp, hn.2.1, fun a ha a' ha' => by simp at ha; subst ha; intro e; subst e; exact hc (by simp [ha'])⟩
  · simp only [List.mem_append, List.mem_singleton] at ha'
    rcases ha' with rfl | ha'
    · intro e; subst e; exact hc (List.mem_append.mpr (Or.inl ha))
    · exact hn.2.2 a ha a' ha'

/-! ## `gz_error` on a read handle -/

/-- The state after `gz_error(state, e, msg)`: as `s` with `x.have` cleared on an error, and a new message and
error (`e`, or `Z_MEM_ERROR`). -/
def ErrOf (s : GzState) (e : Int32) (s' : GzState) : Prop :=
  s' = { errSt s e with msg := s'.msg, err := s'.err } ∧ (s'.err = e ∨ s'.err = ZlibNg.Inflate.Z_MEM_ERROR)

theorem cstr_free {h : Heap} {s : GzState} {p : BPtr} (hp : CStr h p) (hk : ∀ c o, p ≠ .ref (.heap c) o) :
    CStr (freeMsg h s) p := by
  obtain ⟨n, r, off, d, e, hg, rest⟩ := hp
  refine ⟨n, r, off, d, e, ?_, rest⟩
  cases r with
  | heap c => exact absurd e (hk c off)
  | const k => show (freeMsg h s).consts k = some d; rw [freeMsg_consts]; exact hg
  | str k => exact hg

/-- A step that frees blocks of the file, adds static strings, makes fresh blocks and changes only the file's
`gz_state` (keeping its stream) is a step of a call on the file. -/
theorem gstep_mk {w W : World} {h H : Heap} {b : Nat} {s s' : GzState} (hs : w.gz h b = some s)
    (hs' : W.gz H b = some s') (hstrm : s'.strm = s.strm)
    (hg : ∀ c, c ≠ b → c < h.nextBlk → W.gzs c = w.gzs c)
    (hstreams : ∀ i, i ≠ s.strm → H.streams i = h.streams i) (hhdr : H.gzheaders = h.gzheaders)
    (hobj : ∀ c, c < h.nextBlk → c ∉ GzOwned w h (some b) → H.bytes c = h.bytes c ∧ H.istates c = h.istates c ∧
      H.iallocs c = h.iallocs c ∧ H.dstates c = h.dstates c ∧ H.dallocs c = h.dallocs c)
    (hc : ∀ k a, h.consts k = some a → H.consts k = some a) (hcrc : H.crcTable = h.crcTable)
    (hx2n : H.x2nTable = h.x2nTable) (hbase : H.baseAddr = h.baseAddr) (hnext : h.nextBlk ≤ H.nextBlk)
    (hown : ∀ c ∈ GzOwned W H (some b), c < h.nextBlk → c ∈ GzOwned w h (some b)) : GStep w h W H b [] := by
  refine ⟨⟨⟨⟨fun i hi => ?_, fun k _ => by simp [hhdr], fun c hc' hn => ⟨(hobj c hc' hn).2.1, (hobj c hc' hn).2.2.1⟩,
    fun c hc' hn d hd => ⟨d, by simp only; rw [(hobj c hc' hn).1]; exact hd, rfl, fun _ _ _ => rfl⟩,
    fun c hc' hn hd => by simp only; rw [(hobj c hc' hn).1]; exact hd, rfl, hcrc, hx2n, hbase, hnext⟩,
    fun c hc' hn => ⟨(hobj c hc' hn).2.2.2.1, (hobj c hc' hn).2.2.2.2⟩⟩, hc, fun c hcb hlt => hg c
      (fun e => hcb (by rw [e])) hlt⟩, hown, fun s0 s2 e0 e2 => ?_⟩
  · simp only [hs, List.mem_singleton] at hi
    exact hstreams i hi
  · rw [hs] at e0; rw [hs'] at e2; cases e0; cases e2; exact hstrm

theorem gz_error_inv {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvR w h (some b))
    (hs : w.gz h b = some s) (e : Int32) (msg : BPtr) (hmsg : msg = .null ∨ CStr h msg)
    (hmk : ∀ c o, msg ≠ .ref (.heap c) o) :
    GSat w h (gz_error (some b) e msg) (fun _ W H => ∃ s', W.gz H b = some s' ∧ ErrOf s e s' ∧
      GzInvR W H (some b) ∧ LitOk W H ∧ W.fs = w.fs ∧ GStep w h W H b []) := by
  have hlit : LitOk w h := hv.2.2.lit
  obtain ⟨⟨b0, s0, e0, hs0, sh, hn⟩, hm, hw⟩ := hv
  cases e0; rw [hs] at hs0; cases hs0
  have hr := modeOf hs hm
  obtain ⟨db, hdb⟩ := gz_live hs
  have fr : FreshBlocks h := hw.2.1.1
  have hdb1 : (freeMsg h s).bytes b = some db := freeMsg_bytes_b hn hdb
  have hs1 : ({ w with gzs := upd w.gzs b (some (errSt s e)) } : World).gz (freeMsg h s) b = some (errSt s e) := by
    unfold World.gz; rw [hdb1]; simp
  obtain ⟨sh1, hn1⟩ := err0_keep sh hn e
  have fr1 : FreshBlocks (freeMsg h s) := (HLess.free h s).freshB fr
  obtain ⟨r, W, H, eq, mv, ev, hgz, hsW, hfs, x, hlW, hMN⟩ := errTail_spec hs1 fr1
    (LitOk.ext (w := w) hlit rfl fun k a e' => by rw [freeMsg_consts]; exact e') sh1.path rfl e rfl msg
    (hmsg.imp_right fun hp => cstr_free hp hmk)
  rw [freeMsg_next] at hMN
  have hr1 : (errSt s e).mode = GZ_READ := hr
  have hlt : ∀ c ∈ ownL (freeMsg h s) b (errSt s e), c < h.nextBlk := fun c hc => by
    rw [← freeMsg_next h s]; exact live_lt fr1 (ownL_live sh1 hr1 ⟨db, hdb1⟩ c hc)
  have hk := HK_ext x (errSt s e) _ (by rw [freeMsg_next]; exact hlt)
  obtain ⟨shH, eH⟩ := shape_keep sh1 hk
  have hnH : (ownL H b (errSt s e)).Nodup := by rw [eH]; exact hn1
  let s' : GzState := { errSt s e with msg := mv, err := ev }
  have hmsgH : GzMsg H s' := by
    refine ⟨?_, hMN.1⟩
    rcases hMN.2.2 with e' | ⟨c, e', -, d, hd⟩
    · exact Or.inl e'
    · exact Or.inr ⟨c, d, e', hd⟩
  have shS : GzShape H s' := shape_congr shH ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hmsgH
  have hnS : (ownL H b s').Nodup := by
    rcases hMN.2.2 with e' | ⟨c, e', hc, -⟩
    · have : ownL H b s' = ownL H b (errSt s e) := by simp [ownL, s', e', errSt, stBlk]
      rw [this]; exact hnH
    · have : ownL H b s' = ownL H b { errSt s e with msg := .val (.ref (.heap c) 0) } := by simp [ownL, s', e', stBlk]
      rw [this]
      refine ownL_msg hnH rfl c fun m => ?_
      rw [eH] at m
      have := hlt c m; omega
  have hgb : ∀ s2, W.gzs b = some s2 → s2.strm = (errSt s e).strm := by
    intro s2 e2; rw [gzs_of hsW] at e2; cases e2; rfl
  have wf1 : GzWFr { w with gzs := upd w.gzs b (some (errSt s e)) } (freeMsg h s) :=
    wfr_step hw hs (fun c hc => by simp [upd_ne _ _ _ _ hc]) (fun s2 e2 => by simp at e2; rw [← e2]; rfl)
      (GzOpen.FsLe.refl _) (HLess.free h s) (LitOk.ext hlit rfl (HLess.free h s).consts)
  have wfW : GzWFr W H := wfr_ext wf1 hs1 hgz hgb (by rw [hfs]; exact GzOpen.FsLe.refl _) x hlW
  have hstH : H.streams = h.streams := x.streams.trans (freeMsg_streams h s)
  refine ⟨r, W, H, by rw [gz_error_run hs sh.msg (msg_ne_b hn) e msg]; exact eq, s', hsW, ⟨rfl, hMN.2.1⟩,
    ⟨⟨b, s', rfl, hsW, shS, hnS⟩, ⟨b, s', rfl, hsW, hr⟩, wfW⟩, hlW, hfs, ?_⟩
  refine gstep_mk hs hsW rfl (fun c hc _ => by rw [hgz c hc]; simp [upd_ne _ _ _ _ hc])
    (fun i _ => by rw [hstH]) (x.hdr.trans (HLess.free h s).hdr) (fun c hc hno => ?_)
    (fun k a e' => x.consts k a (by rw [freeMsg_consts]; exact e')) (x.crc.trans (HLess.free h s).crc)
    (x.x2n.trans (HLess.free h s).x2n) (x.base.trans (HLess.free h s).base)
    (by have := x.next; rw [freeMsg_next] at this; exact this) (fun c hc hlt' => ?_)
  · have hc' : c < (freeMsg h s).nextBlk := by rw [freeMsg_next]; exact hc
    refine ⟨by rw [(x.old c hc').1]; exact freeMsg_bytes h s c fun hm' => hno (ownL_owned hs c (by unfold ownL; simp only [List.mem_append]; exact Or.inl (Or.inr hm'))), ?_, ?_, ?_, ?_⟩
    · rw [x.istates, (HLess.free h s).istates]
    · rw [x.iallocs, (HLess.free h s).iallocs]
    · rw [x.dstates, (HLess.free h s).dstates]
    · rw [x.dallocs, (HLess.free h s).dallocs]
  · simp only [GzOwned, hsW, hs, List.mem_append, hstH] at hc ⊢
    rcases hc with (((h1 | h2) | h3) | h4) | h5
    · exact Or.inl (Or.inl (Or.inl (Or.inl h1)))
    · exact Or.inl (Or.inl (Or.inl (Or.inr h2)))
    · exfalso
      rcases hMN.2.2 with e' | ⟨c', e', hc', -⟩
      · simp [s', e'] at h3
      · simp [s', e'] at h3; omega
    · exact Or.inl (Or.inr h4)
    · exact Or.inr h5

end ZlibNgF.Proof.GzMode
