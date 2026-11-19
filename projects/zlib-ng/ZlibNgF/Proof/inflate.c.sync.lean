import ZlibNgF.Proof.«inflate.c.window»
import ZlibNgF.Proof.«adler32_c.c.kernel»

/-!
# `inflateSync` (`ZlibNgF`)

`inflateSync` on an invariant stream with valid input: the whole bytes of the bit buffer (at most 32 bits, so at most
four bytes: the local `buf[4]` does not overflow) go to the search pattern, `syncsearch` reads only the `avail_in`
bytes of `next_in`, `next_in` moves only when `len != 0` (patch 0008), and the call changes only the stream record and
the state. The invariant holds after.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InflateSync
open C ZlibNgF.Spec ZlibNg.Inflate
open ZlibNgF.Proof.InflateInv (Inv Core Shape Live view ldState_app ldStream_app setZS upd_upd)
open ZlibNgF.Proof.InflateAlloc (bind_mf bind_fm bind_ff)
open ZlibNgF.Proof.InflateWindow (add_ref)

/-! ## Calls that change only one stream record and one state -/

/-- From `h` to `h'` only stream `i` and the state of block `b` changed. -/
structure Touch (h h' : Heap) (i b : Nat) : Prop where
  bytes : h'.bytes = h.bytes
  streams : ∀ j, j ≠ i → h'.streams j = h.streams j
  istates : ∀ c, c ≠ b → h'.istates c = h.istates c
  iallocs : h'.iallocs = h.iallocs
  gz : h'.gzheaders = h.gzheaders
  consts : h'.consts = h.consts
  crc : h'.crcTable = h.crcTable
  x2n : h'.x2nTable = h.x2nTable
  base : h'.baseAddr = h.baseAddr
  next : h'.nextBlk = h.nextBlk

theorem Touch.refl (h : Heap) (i b : Nat) : Touch h h i b :=
  ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Touch.trans {h1 h2 h3 : Heap} {i b : Nat} (a : Touch h1 h2 i b) (c : Touch h2 h3 i b) : Touch h1 h3 i b :=
  ⟨c.bytes.trans a.bytes, fun j hj => (c.streams j hj).trans (a.streams j hj),
    fun k hk => (c.istates k hk).trans (a.istates k hk), c.iallocs.trans a.iallocs, c.gz.trans a.gz,
    c.consts.trans a.consts, c.crc.trans a.crc, c.x2n.trans a.x2n, c.base.trans a.base, c.next.trans a.next⟩

theorem touch_S (h : Heap) (i b : Nat) (x : Option InflateState) :
    Touch h { h with istates := upd h.istates b x } i b :=
  ⟨rfl, fun _ _ => rfl, fun _ hc => upd_ne _ _ _ _ hc, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem touch_Z (h : Heap) (i b : Nat) (x : Option ZStream) :
    Touch h { h with streams := upd h.streams i x } i b :=
  ⟨rfl, fun _ hj => upd_ne _ _ _ _ hj, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Touch.frame {h h' : Heap} {i b : Nat} (t : Touch h h' i b) : Frame h h' [i] [b] [] [] := by
  refine ⟨fun j hj => t.streams j (by simpa using hj), fun _ _ => by rw [t.gz], fun c _ hc => ⟨t.istates c
    (by simpa using hc), by rw [t.iallocs]⟩, fun c _ _ data hd => ⟨data, by rw [t.bytes]; exact hd, rfl,
    fun _ _ _ => rfl⟩, fun c _ _ hn => by rw [t.bytes]; exact hn, t.consts, t.crc, t.x2n, t.base,
    Nat.le_of_eq t.next.symm⟩

theorem Touch.space {h h' : Heap} {i b : Nat} (t : Touch h h' i b) (r : BRef) :
    Space.get h' r = Space.get h r := by
  cases r <;> simp [Space.get, Heap.getBytes, t.bytes, t.consts]

/-- A store into the stream record that keeps `state`, `zalloc`, `zfree` keeps the invariant. -/
theorem inv_setZ {h : Heap} {i : Nat} {z z' : ZStream} (hv : Inv h (some i)) (hz : h.streams i = some z)
    (e1 : z'.state = z.state) (e2 : z'.zalloc = z.zalloc) (e3 : z'.zfree = z.zfree) :
    Inv { h with streams := upd h.streams i (some z') } (some i) := by
  obtain ⟨i', z0, b, st, al, e, hz0, hb, hst, hal, c⟩ := hv
  obtain rfl := Option.some.inj e
  rw [hz] at hz0; obtain rfl := Option.some.inj hz0
  refine ⟨i, z', b, st, al, rfl, by simp, e1.trans hb, hst, hal, ?_⟩
  exact { c with toShape := { c.toShape with zalloc := e2.trans c.zalloc, zfree := e3.trans c.zfree } }

/-! ## Runs with a postcondition -/

/-- `m` runs on `H` without fault to a result and heap that satisfy `Q`. -/
def Sat {α : Type} (H : Heap) (m : M α) (Q : α → Heap → Prop) : Prop := ∃ r H', m H = .ok (r, H') ∧ Q r H'

theorem Sat.bind {α β : Type} {H : Heap} {m : M α} {f : α → M β} {Q : β → Heap → Prop}
    (hm : Sat H m (fun a H' => Sat H' (f a) Q)) : Sat H (m >>= f) Q := by
  obtain ⟨a, H1, e1, r, H2, e2, q⟩ := hm
  exact ⟨r, H2, by simp only [bind_app, e1]; exact e2, q⟩

theorem Sat.pure {α : Type} {H : Heap} {a : α} {Q : α → Heap → Prop} (q : Q a H) : Sat H (Pure.pure a) Q :=
  ⟨a, H, rfl, q⟩

theorem Sat.of_eq {α : Type} {H H' : Heap} {m : M α} {a : α} {Q : α → Heap → Prop} (e : m H = .ok (a, H'))
    (q : Q a H') : Sat H m Q := ⟨a, H', e, q⟩

theorem Sat.mono {α : Type} {H : Heap} {m : M α} {P Q : α → Heap → Prop} (hm : Sat H m P)
    (hpq : ∀ a H', P a H' → Q a H') : Sat H m Q := by
  obtain ⟨a, H', e, p⟩ := hm; exact ⟨a, H', e, hpq a H' p⟩

/-- `while (cond) body` over a changing heap, with a decreasing measure. -/
theorem sat_cwhile {σ : Type} {cond : σ → M (Bool × σ)} {body : σ → M σ} (I : σ → Heap → Prop) (μ : σ → Nat)
    (Q : σ → Heap → Prop)
    (hstep : ∀ s H, I s H → Sat H (cond s) (fun cs H1 =>
      (cs.1 = true → Sat H1 (body cs.2) (fun s2 H2 => I s2 H2 ∧ μ s2 < μ s)) ∧ (cs.1 = false → Q cs.2 H1)))
    {s : σ} {H : Heap} (hI : I s H) (hμ : μ s < fuel) : Sat H (cwhile cond body s) Q := by
  unfold cwhile
  suffices ∀ n s H, I s H → μ s < n → Sat H (cwhile.go cond body n s) Q from this _ s H hI hμ
  intro n
  induction n with
  | zero => intro s _ _ hlt; omega
  | succ n ih =>
    intro s H hI hlt
    obtain ⟨⟨c, s1⟩, H1, ec, ht, hf⟩ := hstep s H hI
    cases c with
    | false => exact ⟨s1, H1, by simp [cwhile.go, bind_app, ec], hf rfl⟩
    | true =>
      obtain ⟨s2, H2, eb, hI2, hμ2⟩ := ht rfl
      obtain ⟨s', H', eg, q⟩ := ih s2 H2 hI2 (by omega)
      exact ⟨s', H', by simp [cwhile.go, bind_app, ec, eb, eg], q⟩

/-- A `for` loop over a list whose body only computes (no fault, no heap change). -/
theorem forIn_pure_list {α β : Type} (H : Heap) (f : α → β → M (ForInStep β))
    (hf : ∀ a r, ∃ r', f a r H = .ok (.yield r', H)) : ∀ (l : List α) (init : β),
    ∃ v, (forIn l init f : M β) H = .ok (v, H) := by
  intro l
  induction l with
  | nil => intro init; exact ⟨init, rfl⟩
  | cons x l ih =>
    intro init
    obtain ⟨r', e⟩ := hf x init
    obtain ⟨v, ev⟩ := ih r'
    exact ⟨v, by simp only [List.forIn_cons, bind_app, e]; exact ev⟩

/-! ## Steps on an invariant stream -/

/-- `Hk` is reached from `H` by changes of stream `i` and state `b` only, holds the invariant, and stream `i` is `zk`
with state `Sk` in block `b`. -/
structure St (H Hk : Heap) (i b : Nat) (zk : ZStream) (Sk : InflateState) : Prop where
  inv : Inv Hk (some i)
  touch : Touch H Hk i b
  hz : Hk.streams i = some zk
  hb : zk.state = some b
  hs : Hk.istate b = some Sk

theorem St.live {H Hk : Heap} {i b : Nat} {zk : ZStream} {Sk : InflateState} (t : St H Hk i b zk Sk) :
    Live Hk i zk b Sk ∧ ∃ al, Hk.iallocsOf b = some al ∧ Core Hk (some i) zk b (view Sk) al := by
  obtain ⟨i', z', b', st', al, e, L, hal, c⟩ := InflateInv.live t.inv
  obtain rfl := Option.some.inj e
  have : z' = zk := Option.some.inj (L.hz.symm.trans t.hz)
  subst this
  have : b' = b := Option.some.inj (L.hb.symm.trans t.hb)
  subst this
  have : st' = Sk := Option.some.inj (L.istate.symm.trans t.hs)
  subst this
  exact ⟨L, al, hal, c⟩

theorem sat_ldStream {H Hk : Heap} {i b : Nat} {zk : ZStream} {Sk : InflateState} (t : St H Hk i b zk Sk) :
    Sat Hk (ldStream (some i)) (fun r H' => zk = r ∧ Hk = H') :=
  ⟨zk, Hk, ldStream_app t.hz, rfl, rfl⟩

theorem sat_ldState {H Hk : Heap} {i b : Nat} {zk : ZStream} {Sk : InflateState} (t : St H Hk i b zk Sk) :
    Sat Hk (ldState (some b)) (fun r H' => Sk = r ∧ Hk = H') :=
  ⟨Sk, Hk, ldState_app t.hs, rfl, rfl⟩

theorem sat_rdS {α : Type} {H Hk : Heap} {i b : Nat} {zk : ZStream} {Sk : InflateState} (t : St H Hk i b zk Sk)
    (g : InflateState → α) : Sat Hk (rdS (some b) g) (fun r H' => g Sk = r ∧ Hk = H') :=
  ⟨g Sk, Hk, by simp [rdS, bind_app, ldState_app t.hs], rfl, rfl⟩

/-- A store into the state that keeps every clause of the invariant. -/
theorem step_S {H Hk : Heap} {i b : Nat} {zk : ZStream} {Sk : InflateState} (t : St H Hk i b zk Sk)
    (f : InflateState → InflateState)
    (keep : ∀ al z, Core Hk (some i) z b (view Sk) al → Core Hk (some i) z b (view (f Sk)) al) :
    Sat Hk (ZlibNg.Inflate.wrS (some b) f) (fun _ H' => St H H' i b zk (f Sk)) := by
  obtain ⟨e, hi⟩ := InflateInv.wrS t.inv f ⟨zk, ⟨i, rfl, t.hz⟩, t.hb⟩ t.hs keep
  obtain ⟨d, hd⟩ : ∃ d, Hk.bytes b = some d := by
    have := t.hs; unfold Heap.istate at this; split at this <;> simp_all
  exact ⟨(), _, e, hi, t.touch.trans (touch_S _ _ _ _), t.hz, t.hb, by simp [Heap.istate, hd]⟩

/-- A store into the stream record that keeps `state`, `zalloc`, `zfree`. -/
theorem step_Z {H Hk : Heap} {i b : Nat} {zk : ZStream} {Sk : InflateState} (t : St H Hk i b zk Sk)
    (f : ZStream → ZStream) (e1 : (f zk).state = zk.state) (e2 : (f zk).zalloc = zk.zalloc)
    (e3 : (f zk).zfree = zk.zfree) :
    Sat Hk (wrZ (some i) f) (fun _ H' => St H H' i b (f zk) Sk) := by
  refine ⟨(), { Hk with streams := upd Hk.streams i (some (f zk)) }, ?_, inv_setZ t.inv t.hz e1 e2 e3,
    t.touch.trans (touch_Z _ _ _ _), by simp, e1.trans t.hb, t.hs⟩
  simp [wrZ, bind_app, ldStream_app t.hz, stStream, t.hz]

/-- `inflateReset` on a stream reached by such steps. -/
theorem step_reset {H Hk : Heap} {i b : Nat} {zk : ZStream} {Sk : InflateState} (t : St H Hk i b zk Sk) :
    Sat Hk (inflateReset (some i)) (fun _ H' =>
      St H H' i b (InflateReset.rkZ zk Sk.wrap) (InflateReset.rkS b (InflateReset.rS Sk))) := by
  obtain ⟨L, al, hal, c⟩ := t.live
  have e := InflateReset.reset_run L
  obtain ⟨i', z', b', st', e', er, hinv⟩ := InflateReset.reset_inv t.inv
  obtain rfl := Option.some.inj e'
  have e0 : C.run (inflateReset (some i)) Hk = .ok (Z_OK, setZS Hk i (InflateReset.rkZ zk Sk.wrap) b
      (InflateReset.rkS b (InflateReset.rS Sk))) := e
  rw [e0] at er
  obtain ⟨-, hh⟩ := Prod.mk.inj (Except.ok.inj er)
  obtain ⟨d, hd⟩ := L.hd
  refine ⟨Z_OK, _, e, hh ▸ hinv, ?_, by simp [setZS], t.hb, by simp [setZS, Heap.istate, hd]⟩
  exact t.touch.trans ((touch_Z _ _ _ _).trans (touch_S _ _ _ _))

/-! ## `syncsearch` -/

open ZlibNgF.Proof.Adler32Kernel (Ok Ok.pure Ok.bind cwhile_measure index8_ok) in
/-- `syncsearch` over `len` readable bytes (or a `NULL` buffer with `len == 0`) reads only those bytes, changes
nothing, and consumes at most `len` bytes. -/
theorem syncsearch_ok (h : Heap) (have_ : UInt32) (buf : BPtr) (len : UInt32) (hin : NullOrRead h buf len.toNat)
    (hnull : buf = .null → len = 0) :
    ∃ got next, C.run (syncsearch have_ buf len) h = .ok ((got, next), h) ∧ next ≤ len := by
  have hlen := len.toNat_lt
  have hk : Ok h (syncsearch have_ buf len) (fun r => r.2 ≤ len) := by
    unfold syncsearch
    refine Ok.bind (cwhile_measure (fun s : UInt32 × UInt32 => s.2 ≤ len)
      (fun s => len.toNat - s.2.toNat) (fun s => s.2 ≤ len) ?_ (UInt32.zero_le) ?_) (fun v hv => Ok.pure hv)
    · intro ⟨got, next⟩ hI
      refine Ok.pure ⟨fun hc => ?_, fun hc => hI⟩
      have hlt : next < len := by simp at hc; exact hc.1
      have hlt' : next.toNat < len.toNat := hlt
      rcases hin with hn | ⟨r, off, data, rfl, hg, hle⟩
      · have := hnull hn; subst this; exact absurd hlt' (by simp)
      refine Ok.bind (index8_ok hg (Int.ofNat next.toNat) (by simp) (by simp; omega)) (fun _ _ => Ok.pure ?_)
      have e : (next + 1).toNat = next.toNat + 1 := by rw [UInt32.toNat_add]; simp; omega
      refine ⟨?_, ?_⟩
      · show next + 1 ≤ len; rw [UInt32.le_iff_toNat_le, e]; omega
      · show len.toNat - (next + 1).toNat < len.toNat - next.toNat; rw [e]; omega
    · show len.toNat - (0 : UInt32).toNat < fuel
      unfold fuel; simp; omega
  obtain ⟨⟨got, next⟩, e, hle⟩ := hk
  exact ⟨got, next, e, hle⟩

/-! ## The run of `inflateSync` -/

/-- The end of `inflateSync` after a sync point is found. -/
def syncEnd (strm : StreamPtr) (st : StatePtr) : M Int32 := do
  let flags ← rdS st (·.flags)
  let z ← ldStream strm
  let in_ := z.total_in
  let out := z.total_out
  let _ ← inflateReset strm
  wrZ strm fun z => { z with total_in := in_, total_out := out }
  wrS st fun s => { s with flags := flags }
  if (← rdS st (·.wbits)) == 0 then wrS st fun s => { s with wbits := MAX_WBITS.toUInt32 }
  setMode st TYPE
  return Z_OK

/-- `inflateSync` after the input is advanced. -/
def syncJp (strm : StreamPtr) (st : StatePtr) (len : UInt32) : M Int32 := do
  wrZ strm fun z => { z with total_in := z.total_in + len.toUInt64 }
  if (← rdS st (·.«have»)) != 4 then return Z_DATA_ERROR
  if (← rdS st (·.flags)) == -1 then
    wrS st fun s => { s with wrap := 0 }
  else
    wrS st fun s => { s with wrap := s.wrap &&& ~~~4 }
  syncEnd strm st

/-- `inflateSync` after the bit buffer is moved to the search pattern. -/
def syncTail (strm : StreamPtr) (st : StatePtr) : M Int32 := do
  let z ← ldStream strm
  let (hv, len) ← syncsearch (← rdS st (·.«have»)) z.next_in z.avail_in
  wrS st fun s => { s with «have» := hv }
  wrZ strm fun z => { z with avail_in := z.avail_in - len }
  if len != 0 then
    let nx ← z.next_in.add (Int.ofNat len.toNat)
    wrZ strm fun z => { z with next_in := nx }
  syncJp strm st len

theorem sync_split (strm : StreamPtr) : inflateSync strm = (do
    if ← inflateStateCheck strm then return Z_STREAM_ERROR
    let st ← stateOf strm
    let z ← ldStream strm
    let s ← ldState st
    if z.avail_in == 0 && s.bits < 8 then return Z_BUF_ERROR
    if s.mode != SYNC then
      setMode st SYNC
      let s ← ldState st
      let hold ← shr64 s.hold (s.bits &&& 7)
      wrS st fun s => { s with hold := hold, bits := s.bits - (s.bits &&& 7) }
      let (buf, _) ← cwhile
        (fun ((buf, _) : Array UInt8 × Unit) => do pure ((← rdS st (·.bits)) >= 8, (buf, ())))
        (fun ((buf, _) : Array UInt8 × Unit) => do
          let s ← ldState st
          let buf := buf.push s.hold.toUInt8
          let hold ← shr64 s.hold 8
          wrS st fun s => { s with hold := hold, bits := s.bits - 8 }
          pure (buf, ()))
        (#[], ())
      if buf.size > 4 then ub "buf[4] overflow"
      wrS st fun s => { s with «have» := 0 }
      let mut got : UInt32 := 0
      for b in buf do
        if got < 4 then
          let want : UInt32 := if got < 2 then 0 else 0xff
          got := if b.toUInt32 == want then got + 1 else if b != 0 then 0 else 4 - got
      wrS st fun s => { s with «have» := got }
    syncTail strm st) := rfl

theorem syncEnd_ok {H Hk : Heap} {i b : Nat} {zk : ZStream} {Sk : InflateState} (t : St H Hk i b zk Sk) :
    Sat Hk (syncEnd (some i) (some b)) (fun _ H' => Touch H H' i b ∧ Inv H' (some i)) := by
  unfold syncEnd
  refine Sat.bind (Sat.mono (sat_rdS t (·.flags)) ?_)
  rintro r H1 ⟨rfl, rfl⟩
  refine Sat.bind (Sat.mono (sat_ldStream t) ?_)
  rintro r H1 ⟨rfl, rfl⟩
  refine Sat.bind (Sat.mono (step_reset t) ?_)
  rintro - H2 t2
  refine Sat.bind (Sat.mono (step_Z t2 (fun z => { z with total_in := zk.total_in, total_out := zk.total_out })
    rfl rfl rfl) ?_)
  rintro - H3 t3
  refine Sat.bind (Sat.mono (step_S t3 (fun s => { s with flags := Sk.flags }) (fun _ _ c => c)) ?_)
  rintro - H4 t4
  refine Sat.bind (Sat.mono (sat_rdS t4 (·.wbits)) ?_)
  rintro r H5 ⟨rfl, rfl⟩
  have tail : ∀ (H6 : Heap) (z6 : ZStream) (S6 : InflateState), St H H6 i b z6 S6 →
      Sat H6 (do setMode (some b) TYPE; pure Z_OK : M Int32) (fun _ H' => Touch H H' i b ∧ Inv H' (some i)) := by
    intro H6 z6 S6 t6
    refine Sat.bind (Sat.mono (step_S t6 (fun s => { s with mode := TYPE })
      (fun _ _ c => { c with
        mode_lo := by show HEAD ≤ TYPE; decide
        mode_hi := by show TYPE ≤ SYNC; decide
        modes := InflateInv.ModeOK.quiet _ _ (Or.inl (by show TYPE < LENLENS; decide)) })) ?_)
    rintro - H7 t7
    exact Sat.pure ⟨t7.touch, t7.inv⟩
  dsimp only [InflateReset.rkS, InflateReset.rS]
  by_cases hw : Sk.reqbits = 0
  · simp only [hw, beq_self_eq_true, ↓reduceIte]
    refine Sat.bind (Sat.mono (step_S t4 (fun s => { s with wbits := MAX_WBITS.toUInt32 })
      (fun _ _ c => { c with wbits := by show MAX_WBITS.toUInt32 ≤ 15; decide })) ?_)
    rintro - H6 t6
    exact tail H6 _ _ t6
  · have hw' : (Sk.reqbits == 0) = false := by simpa using hw
    simp only [hw', Bool.false_eq_true, ↓reduceIte]
    exact tail H4 _ _ t4

theorem syncJp_ok {H Hk : Heap} {i b : Nat} {zk : ZStream} {Sk : InflateState} (t : St H Hk i b zk Sk)
    (len : UInt32) :
    Sat Hk (syncJp (some i) (some b) len) (fun _ H' => Touch H H' i b ∧ Inv H' (some i)) := by
  unfold syncJp
  refine Sat.bind (Sat.mono (step_Z t (fun z => { z with total_in := z.total_in + len.toUInt64 }) rfl rfl rfl) ?_)
  rintro - H1 t1
  refine Sat.bind (Sat.mono (sat_rdS t1 (·.«have»)) ?_)
  rintro r H2 ⟨rfl, rfl⟩
  dsimp only
  by_cases h4 : (Sk.have != 4) = true
  · simp only [h4, ↓reduceIte]
    exact Sat.pure ⟨t1.touch, t1.inv⟩
  · have h4' : (Sk.have != 4) = false := by simpa using h4
    simp only [h4', Bool.false_eq_true, ↓reduceIte]
    refine Sat.bind (Sat.mono (sat_rdS t1 (·.flags)) ?_)
    rintro r H2 ⟨rfl, rfl⟩
    by_cases hf : (Sk.flags == -1) = true
    · simp only [hf, ↓reduceIte]
      refine Sat.bind (Sat.mono (step_S t1 (fun s => { s with wrap := 0 }) (fun _ _ c => c)) ?_)
      rintro - H3 t3
      exact syncEnd_ok t3
    · have hf' : (Sk.flags == -1) = false := by simpa using hf
      simp only [hf', Bool.false_eq_true, ↓reduceIte]
      refine Sat.bind (Sat.mono (step_S t1 (fun s => { s with wrap := s.wrap &&& ~~~4 }) (fun _ _ c => c)) ?_)
      rintro - H3 t3
      exact syncEnd_ok t3

theorem syncTail_ok {H Hk : Heap} {i b : Nat} {zk : ZStream} {Sk : InflateState} (t : St H Hk i b zk Sk)
    (hm : Sk.mode = SYNC)
    (hin : NullOrRead Hk zk.next_in zk.avail_in.toNat) (hnull : zk.next_in = .null → zk.avail_in = 0) :
    Sat Hk (syncTail (some i) (some b)) (fun _ H' => Touch H H' i b ∧ Inv H' (some i)) := by
  unfold syncTail
  refine Sat.bind (Sat.mono (sat_ldStream t) ?_)
  rintro r H1 ⟨rfl, rfl⟩
  refine Sat.bind (Sat.mono (sat_rdS t (·.«have»)) ?_)
  rintro r H1 ⟨rfl, rfl⟩
  obtain ⟨got, len, es, hle⟩ := syncsearch_ok Hk Sk.have zk.next_in zk.avail_in hin hnull
  refine Sat.bind (Sat.of_eq es ?_)
  dsimp only
  refine Sat.bind (Sat.mono (step_S t (fun s => { s with «have» := got }) (fun _ _ c => { c with
    modes := InflateInv.ModeOK.quiet _ _ (Or.inr (by show LIT < Sk.mode; rw [hm]; decide)) })) ?_)
  rintro - H2 t2
  refine Sat.bind (Sat.mono (step_Z t2 (fun z => { z with avail_in := z.avail_in - len }) rfl rfl rfl) ?_)
  rintro - H3 t3
  by_cases hl : (len != 0) = true
  · simp only [hl, ↓reduceIte]
    have hl0 : len ≠ 0 := by simpa using hl
    rcases hin with hn | ⟨r, off, data, hp, hg, hsz⟩
    · exfalso; apply hl0; have := hnull hn; rw [this] at hle; u32_omega
    have hg3 : Space.get H3 r = some data := by rw [t3.touch.space, ← t.touch.space]; exact hg
    rw [hp]
    have hle' : len.toNat ≤ zk.avail_in.toNat := hle
    refine Sat.bind (Sat.of_eq (add_ref hg3 (by omega : off + len.toNat ≤ data.size)) ?_)
    refine Sat.bind (Sat.mono (step_Z t3 (fun z => { z with next_in := .ref r (off + len.toNat) }) rfl rfl rfl) ?_)
    rintro - H4 t4
    exact syncJp_ok t4 len
  · have hl' : (len != 0) = false := by simpa using hl
    simp only [hl', Bool.false_eq_true, ↓reduceIte]
    exact syncJp_ok t3 len

theorem and7 (a : UInt32) : (a &&& 7).toNat = a.toNat % 8 := by
  rw [UInt32.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod a.toNat 3

theorem space_read {h h' : Heap} {i b : Nat} (t : Touch h h' i b) {p : BPtr} {n : Nat} (hr : NullOrRead h p n) :
    NullOrRead h' p n := by
  rcases hr with hn | ⟨r, off, data, hp, hg, hsz⟩
  · exact Or.inl hn
  · exact Or.inr ⟨r, off, data, hp, by rw [t.space]; exact hg, hsz⟩

theorem sync_noState {h : Heap} {s : StreamPtr} (hn : InflateControl.NoState h s) :
    C.run (inflateSync s) h = .ok (Z_STREAM_ERROR, h) := by
  simp [C.run, inflateSync, bind_app,
    show inflateStateCheck s h = .ok (true, h) from InflateControl.stateCheck_noState hn]

/-- `inflateSync` on an invariant stream with valid input: no fault, only the stream record and the state change,
the invariant holds after. -/
theorem sync_inv {h : Heap} {s : StreamPtr} (hv : Inv h s) (hio : StreamIO h s) (hsi : SyncInput h s) :
    ∃ r h', C.run (inflateSync s) h = .ok (r, h') ∧ Inv h' s ∧ Frame h h' (streamIds s) (stateIds h s) [] [] := by
  obtain ⟨i, z, b, st, al, rfl, L, hal, c⟩ := InflateInv.live hv
  have hin : NullOrRead h z.next_in z.avail_in.toNat := by
    obtain ⟨z', b', hp, ⟨i', hi', hz'⟩, -, -, -, hr, -⟩ := hio
    obtain rfl := Option.some.inj hi'
    rw [L.hz] at hz'; obtain rfl := Option.some.inj hz'
    exact hr
  have hnull : z.next_in = .null → z.avail_in = 0 := by
    obtain ⟨z', ⟨i', hi', hz'⟩, hn⟩ := hsi
    obtain rfl := Option.some.inj hi'
    rw [L.hz] at hz'; obtain rfl := Option.some.inj hz'
    exact hn
  have hids : stateIds h (some i) = [b] := by simp [stateIds, L.hz, L.hb]
  rw [hids]
  have t0 : St h h i b z st := ⟨hv, Touch.refl h i b, L.hz, L.hb, L.istate⟩
  suffices hs : Sat h (inflateSync (some i)) (fun _ H' => Touch h H' i b ∧ Inv H' (some i)) by
    obtain ⟨r, h', e, ht, hi⟩ := hs
    exact ⟨r, h', e, hi, ht.frame⟩
  rw [sync_split]
  refine Sat.bind (Sat.of_eq L.check ?_)
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine Sat.bind (Sat.of_eq L.stateOf ?_)
  refine Sat.bind (Sat.mono (sat_ldStream t0) ?_)
  rintro r H1 ⟨rfl, rfl⟩
  refine Sat.bind (Sat.mono (sat_ldState t0) ?_)
  rintro r H1 ⟨rfl, rfl⟩
  by_cases hbuf : (z.avail_in == 0 && decide (st.bits < 8)) = true
  · simp only [hbuf, ↓reduceIte]
    exact Sat.pure ⟨Touch.refl h i b, hv⟩
  have hbuf' : (z.avail_in == 0 && decide (st.bits < 8)) = false := by simpa using hbuf
  simp only [hbuf', Bool.false_eq_true, ↓reduceIte]
  by_cases hm' : (st.mode != SYNC) = false
  · simp only [hm', Bool.false_eq_true, ↓reduceIte]
    exact syncTail_ok t0 (by simpa using hm') hin hnull
  have hm : (st.mode != SYNC) = true := by simpa using hm'
  simp only [hm, ↓reduceIte]
  have hb32 : st.bits.toNat ≤ 39 := c.bits
  unfold setMode
  refine Sat.bind (Sat.mono (step_S t0 (fun s => { s with mode := SYNC })
    (fun _ _ c => { c with
      mode_lo := by show HEAD ≤ SYNC; decide
      mode_hi := UInt32.le_refl _
      modes := InflateInv.ModeOK.quiet _ _ (Or.inr (by show LIT < SYNC; decide)) })) ?_)
  rintro - H1 t1
  refine Sat.bind (Sat.mono (sat_ldState t1) ?_)
  rintro r H2 ⟨rfl, rfl⟩
  have h7 : (st.bits &&& 7) < 64 := by
    rw [UInt32.lt_iff_toNat_lt, and7]; show _ < 64; omega
  refine Sat.bind (Sat.of_eq (show shr64 st.hold (st.bits &&& 7) H1 = .ok (st.hold >>> (st.bits &&& 7).toUInt64, H1)
    by simp [shr64, h7]) ?_)
  have hsub : (st.bits - (st.bits &&& 7)).toNat = st.bits.toNat - st.bits.toNat % 8 := by
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, and7]; omega), and7]
  let hold1 := st.hold >>> (st.bits &&& 7).toUInt64
  have hb2 : st.bits - (st.bits &&& 7) ≤ 32 := by
    rw [UInt32.le_iff_toNat_le, hsub]; show _ ≤ 32; omega
  refine Sat.bind (Sat.mono (step_S t1 (fun s => { s with hold := hold1, bits := s.bits - (s.bits &&& 7) })
    (fun _ _ c => { c with bits := UInt32.le_trans hb2 (by decide) })) ?_)
  rintro - H2 t2
  have hb2' : (st.bits - (st.bits &&& 7)).toNat % 8 = 0 := by rw [hsub]; omega
  refine Sat.bind (Sat.mono (sat_cwhile (s := ((#[] : Array UInt8), ()))
    (fun (x : Array UInt8 × Unit) Hk => ∃ Sk, St h Hk i b z Sk ∧ Sk.mode = SYNC ∧ Sk.bits.toNat % 8 = 0 ∧
      Sk.bits.toNat + 8 * x.1.size ≤ 32)
    (fun x => 5 - x.1.size) (fun x Hk => ∃ Sk, St h Hk i b z Sk ∧ Sk.mode = SYNC ∧ x.1.size ≤ 4) ?_
    ⟨_, t2, rfl, hb2', by show (st.bits - (st.bits &&& 7)).toNat + 8 * (#[] : Array UInt8).size ≤ 32; simp only [hsub, List.size_toArray, List.length_nil]; omega⟩
    (by unfold fuel; simp)) ?_)
  · rintro ⟨buf, u⟩ Hk ⟨Sk, tk, hmk, h8, hle⟩
    dsimp only at hle ⊢
    refine Sat.bind (Sat.mono (sat_rdS tk (·.bits)) ?_)
    rintro r H3 ⟨rfl, rfl⟩
    refine Sat.pure ⟨fun hc => ?_, fun hc => ⟨Sk, tk, hmk, ?_⟩⟩
    · have hge : 8 ≤ Sk.bits.toNat := by simpa [UInt32.le_iff_toNat_le] using hc
      dsimp only
      refine Sat.bind (Sat.mono (sat_ldState tk) ?_)
      rintro r H4 ⟨rfl, rfl⟩
      refine Sat.bind (Sat.of_eq (show shr64 Sk.hold 8 Hk = .ok (Sk.hold >>> (8 : UInt32).toUInt64, Hk) by
        simp [shr64]) ?_)
      have hs8 : (Sk.bits - 8).toNat = Sk.bits.toNat - 8 := UInt32.toNat_sub_of_le _ _ (by
        rw [UInt32.le_iff_toNat_le]; exact hge)
      have hb3 : Sk.bits - 8 ≤ 32 := by rw [UInt32.le_iff_toNat_le, hs8]; show _ ≤ 32; omega
      let hold2 := Sk.hold >>> (8 : UInt32).toUInt64
      refine Sat.bind (Sat.mono (step_S tk (fun s => { s with hold := hold2, bits := s.bits - 8 })
        (fun _ _ c => { c with bits := UInt32.le_trans hb3 (by decide) })) ?_)
      rintro - H5 t5
      refine Sat.pure ⟨⟨_, t5, hmk, ?_, ?_⟩, ?_⟩
      · show (Sk.bits - 8).toNat % 8 = 0; rw [hs8]; omega
      · show (Sk.bits - 8).toNat + 8 * (buf.push Sk.hold.toUInt8).size ≤ 32; rw [hs8, Array.size_push]; omega
      · show 5 - (buf.push Sk.hold.toUInt8).size < 5 - buf.size; rw [Array.size_push]; omega
    · have hlt : Sk.bits.toNat < 8 := by simpa [UInt32.le_iff_toNat_le] using hc
      show buf.size ≤ 4; omega
  rintro ⟨buf, u⟩ H3 ⟨S3, t3, hm3, hsz⟩
  dsimp only at hsz ⊢
  have hsz' : ¬ buf.size > 4 := by omega
  simp only [hsz', ↓reduceIte]
  refine Sat.bind (Sat.mono (step_S t3 (fun s => { s with «have» := 0 }) (fun _ _ c => { c with
    modes := InflateInv.ModeOK.quiet _ _ (Or.inr (by show LIT < S3.mode; rw [hm3]; decide)) })) ?_)
  rintro - H4 t4
  obtain ⟨got, eg⟩ := forIn_pure_list H4 (fun (b : UInt8) (r : UInt32) =>
      if r < 4 then
        (pure (ForInStep.yield (if (b.toUInt32 == if r < 2 then 0 else 255) = true then r + 1
          else if (b != 0) = true then 0 else 4 - r)) : M (ForInStep UInt32))
      else pure (ForInStep.yield r))
    (fun a r => by by_cases hr : r < 4 <;> simp only [hr, ↓reduceIte] <;> exact ⟨_, rfl⟩) buf.toList 0
  rw [Array.forIn_toList] at eg
  refine Sat.bind (Sat.of_eq eg ?_)
  refine Sat.bind (Sat.mono (step_S t4 (fun s => { s with «have» := got }) (fun _ _ c => { c with
    modes := InflateInv.ModeOK.quiet _ _ (Or.inr (by show LIT < S3.mode; rw [hm3]; decide)) })) ?_)
  rintro - H5 t5
  have ht5 : Touch h H5 i b := t5.touch
  exact syncTail_ok t5 hm3 (space_read ht5 hin) hnull

end ZlibNgF.Proof.InflateSync
