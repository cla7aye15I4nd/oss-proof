import ZlibNgF.Proof.«deflate.c.fill_window.facts»
import ZlibNgF.Proof.«deflate_p.h.flush»

/-!
# `fill_window` inside a strategy (`ZlibNgF`)

`fill_io`: `fill_window` on an invariant stream with valid and set buffers and the CRC tables leaves the invariant,
valid and set buffers (the input after is a tail of the input before, `InTail`), the CRC tables, and a change of the
stream record and the stream's block only. `streamIO_in` carries `DStreamIO` over a change of the bytes of the
stream's block, of `L` output bytes, and of the input to a tail of it.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.FillIO
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInit ZlibNgF.Proof.WinBase
open ZlibNgF.Proof.WinInv ZlibNgF.Proof.FillFacts ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateFacts
open ZlibNgF.Proof.DeflateFlush

/-- A range disjoint from `[oo, oo + A)` stays disjoint from `[oo + L, oo + A)` when it shrinks to a tail. -/
theorem disj_shift {ob oo A L : Nat} {r : BRef} {os s a a' : Nat}
    (hd : Disjoint (.ref (.heap ob) oo) A (.ref r os) a) (hL : L ≤ A) (hs : s + a' ≤ a) :
    Disjoint (.ref (.heap ob) (oo + L)) (A - L) (.ref r (os + s)) a' := by
  rcases hd with hne | h1 | h2
  · exact .inl hne
  · exact .inr (.inl (by omega))
  · exact .inr (.inr (by omega))

/-- The stream's buffers stay valid when `L` output bytes are written, `next_out` / `avail_out` move past them, and
the input becomes a tail of itself. -/
theorem streamIO_in {h h' : Heap} {i : Nat} {z z' : ZStream} {b ob oo L : Nat} {st st' : DeflateState}
    (hio : DStreamIO h (some i)) (hz : h.streams i = some z) (hb : z.state = some b) (hst : h.dstate b = some st)
    (hno : z.next_out = .ref (.heap ob) oo) (hL : L ≤ z.avail_out.toNat) (O : OutOnly h h' b ob oo L)
    (hz' : h'.streams i = some z') (hzs : z'.state = z.state) (hai : z'.avail_in.toNat ≤ z.avail_in.toNat)
    (ht : InTail z z') (hrd : NullOrRead h' z'.next_in z'.avail_in.toNat)
    (hno' : z'.next_out = .ref (.heap ob) (oo + L))
    (hav : z'.avail_out.toNat = z.avail_out.toNat - L) (hst' : h'.dstate b = some st')
    (hgz : st'.gzhead = st.gzhead) : DStreamIO h' (some i) := by
  obtain ⟨z0, b0, hp, ⟨i0, e0, hz0⟩, hb0, ⟨b1, st1, ⟨⟨z1, ⟨i1, e1, hz1⟩, hb1⟩, hst1⟩, hg1⟩, hhd, -, hout0, hnb0,
    hdj⟩ := hio
  obtain rfl : i = i0 := Option.some.inj e0
  obtain rfl : i = i1 := Option.some.inj e1
  obtain rfl : z = z0 := Option.some.inj (hz.symm.trans hz0)
  obtain rfl : z = z1 := Option.some.inj (hz.symm.trans hz1)
  obtain rfl : b = b0 := Option.some.inj (hb.symm.trans hb0)
  obtain rfl : b = b1 := Option.some.inj (hb.symm.trans hb1)
  obtain rfl : st = st1 := Option.some.inj (hst.symm.trans hst1)
  have hgz' : h'.gzheaders = h.gzheaders := O.2.1
  have hob : ob ≠ b := fun e => hnb0 oo (by rw [hno, e])
  have hcs : ∀ p, (p = .null ∨ ∃ n, CStringLen h p n) → (∀ n, CStringLen h p n → Disjoint z.next_out
      z.avail_out.toNat p (n + 1) ∧ NotInBlock b p) →
      (p = .null ∨ ∃ n, CStringLen h' p n) ∧ ∀ n, CStringLen h' p n → CStringLen h p n := by
    intro p hp hpd
    rcases hp with hp | ⟨n, hn⟩
    · refine ⟨.inl hp, fun n hn => ?_⟩
      obtain ⟨_, _, _, e, -⟩ := hn; rw [hp] at e; cases e
    · have ⟨hd1, hnb1⟩ := hpd n hn
      rw [hno] at hd1
      have hn' := cstr_out O hn hnb1 (disj_mono hd1 hL (Nat.le_refl _))
      exact ⟨.inr ⟨n, hn'⟩, fun m hm => by rw [← cstr_unique hn' hm]; exact hn⟩
  have shift : ∀ q m, Disjoint z.next_out z.avail_out.toNat q m →
      Disjoint z'.next_out z'.avail_out.toNat q m := by
    intro q m hd
    rw [hno', hav]; rw [hno] at hd
    match q, hd with
    | .ref _ _, .inl hne => exact .inl hne
    | .ref _ _, .inr (.inl h) => exact .inr (.inl (by omega))
    | .ref _ _, .inr (.inr h) => exact .inr (.inr (by omega))
    | .null, _ => trivial
  refine ⟨z', b, hp, ⟨i, rfl, hz'⟩, by rw [hzs]; exact hb, ⟨b, st', ⟨⟨z', ⟨i, rfl, hz'⟩, by rw [hzs]; exact hb⟩, hst'⟩,
    by rw [hgz]; exact hg1⟩, ?_, hrd, ?_, ?_, ?_⟩
  · intro k hk
    obtain ⟨g, hg, hx, hn, hc⟩ := hhd k hk
    have rx : DReadRange h z hp (g.extra, g.extra_len.toNat) := .inr ⟨k, hk, g, hg, .inl rfl⟩
    have dn := hcs g.name hn (fun n hn' => hdj _ (.inr ⟨k, hk, g, hg, .inr (.inl ⟨n, hn', rfl⟩)⟩))
    have dc := hcs g.comment hc (fun n hn' => hdj _ (.inr ⟨k, hk, g, hg, .inr (.inr ⟨n, hn', rfl⟩)⟩))
    exact ⟨g, by rw [hgz']; exact hg, nullOrRead_out O hx (hdj _ rx).2, dn.1, dc.1⟩
  · rw [hno', hav]
    rcases hout0 with e | ⟨ob', oo', ad, e, had, hle⟩
    · rw [hno] at e; cases e
    · rw [hno] at e; injection e with e1 e2; injection e1 with e1; subst e1; subst e2
      obtain ⟨ad', h1, h2, -⟩ := O.2.2 _ hob ad had
      exact .inr ⟨_, _, ad', rfl, h1, by omega⟩
  · rw [hno']; intro off e; injection e with e1; injection e1 with e1; exact hob e1
  · intro r hr
    rcases hr with e | ⟨k, hk, g, hg, hx⟩
    · subst e
      obtain ⟨hd, hn⟩ := hdj _ (.inl rfl)
      rcases ht with ⟨e1, e2⟩ | ⟨r0, os, e1, e2⟩
      · simp only [] at hd hn ⊢
        rw [e1, e2]; exact ⟨shift _ _ hd, hn⟩
      · simp only [] at hd hn ⊢
        refine ⟨?_, fun off e => ?_⟩
        · rw [hno', hav, e2]; rw [hno, e1] at hd
          exact disj_shift hd hL (by omega)
        · rw [e2] at e; injection e with e3; exact hn os (by rw [e1, e3])
    · rw [hgz'] at hg
      obtain ⟨g0, hg0, -, hn, hc⟩ := hhd k hk
      obtain rfl : g = g0 := Option.some.inj (hg.symm.trans hg0)
      have hr' : DReadRange h z hp r := by
        refine .inr ⟨k, hk, g, hg0, ?_⟩
        rcases hx with e | ⟨n, hn', e⟩ | ⟨n, hn', e⟩
        · exact .inl e
        · exact .inr (.inl ⟨n, (hcs g.name hn (fun n hn' => hdj _ (.inr ⟨k, hk, g, hg0,
            .inr (.inl ⟨n, hn', rfl⟩)⟩))).2 n hn', e⟩)
        · exact .inr (.inr ⟨n, (hcs g.comment hc (fun n hn' => hdj _ (.inr ⟨k, hk, g, hg0,
            .inr (.inr ⟨n, hn', rfl⟩)⟩))).2 n hn', e⟩)
      obtain ⟨hd, hn⟩ := hdj r hr'
      exact ⟨shift _ _ hd, hn⟩

/-- What `fill_window` leaves inside a strategy. -/
structure FillIO (h h' : Heap) (i b : Nat) : Prop where
  inv : DInv h' (some i)
  io : DStreamIO h' (some i)
  set : DBufsSet h' (some i)
  crc : CrcGlobals h'
  post : FillPost h h' (some i)
  frame : DFrame h h' [i] [b] [] []

/-- `fill_window` on an invariant stream with valid and set buffers, the CRC tables, and `lookahead < 262`. -/
theorem fill_io {h : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} (hv : DInv h (some i))
    (hio : DStreamIO h (some i)) (hset : DBufsSet h (some i)) (hcrc : CrcGlobals h)
    (hz : h.streams i = some z) (hb : z.state = some b) (hst : h.dstate b = some st)
    (hla : st.lookahead.toNat < 262) :
    ∃ h', C.run (ZlibNg.Deflate.fill_window (some b)) h = .ok ((), h') ∧ FillIO h h' i b := by
  have hio0 := hio
  obtain ⟨z2, b2, hp, ⟨i2, e2, hz2⟩, hb2, -, -, hin0, hout, hnb, hdj⟩ := hio0
  obtain rfl : i = i2 := Option.some.inj e2
  obtain rfl : z = z2 := Option.some.inj (hz.symm.trans hz2)
  obtain rfl : b = b2 := Option.some.inj (hb.symm.trans hb2)
  obtain ⟨z3, ⟨i3, e3, hz3⟩, hnn, hni⟩ := hset
  obtain rfl : i = i3 := Option.some.inj e3
  obtain rfl : z = z3 := Option.some.inj (hz.symm.trans hz3)
  obtain ⟨ob, oo, ad, hno, had, hoo⟩ := hout.resolve_left hnn
  have hob : ob ≠ b := fun e => hnb oo (by rw [hno, e])
  have hdin : DInput h (some i) := ⟨z, b, ⟨i, rfl, hz⟩, hb, hin0, (hdj _ (.inl rfl)).2, hni⟩
  obtain ⟨h', e, P, i4, z4, z', st', d', e4, hz4, rfl, zr⟩ :=
    fill_window_ok2 h (some i) b st (DInvW.of_inv hv) ⟨i, z, rfl, hz, hb, hst⟩ hdin (fun _ => hcrc) hla
  obtain rfl : i = i4 := Option.some.inj e4
  obtain rfl : z = z4 := Option.some.inj (hz.symm.trans hz4)
  have hinv := FillPost.inv hv P
  have P0 := P
  obtain ⟨-, ⟨z5, b5, ⟨i5, e5, hz5⟩, hb5, hrd, -, -⟩, -, -⟩ := P0
  obtain rfl : i = i5 := Option.some.inj e5
  obtain rfl : z' = z5 := Option.some.inj ((SH_streams _ _ _ _ _ _).symm.trans hz5)
  obtain ⟨hle, ⟨ni, ai, ti, adl, ez⟩, ht⟩ := zr
  have hzs : z'.state = z.state := by rw [ez]
  have O : OutOnly h (SH h i z' b st' d') b ob oo 0 :=
    ⟨rfl, rfl, fun c hc data hd => ⟨data, by simp only [SH]; rw [upd_ne _ _ _ _ hc]; exact hd, rfl, fun _ _ => rfl⟩⟩
  have hgz : st'.gzhead = st.gzhead := by
    obtain ⟨-, -, -, i6, z6, z7, b6, st6, st7, e6, hz6, hz7, hb6, hst6, hst7, -, -, -, -, -, -, -, -, -, hg, -⟩ := P
    obtain rfl : i = i6 := Option.some.inj e6
    obtain rfl : z = z6 := Option.some.inj (hz.symm.trans hz6)
    obtain rfl : b = b6 := Option.some.inj (hb.symm.trans hb6)
    obtain rfl : st = st6 := Option.some.inj (hst.symm.trans hst6)
    obtain rfl : st' = st7 := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst7)
    exact hg
  have hno' : z'.next_out = .ref (.heap ob) (oo + 0) := by rw [ez, hno]; rfl
  have hav : z'.avail_out.toNat = z.avail_out.toNat - 0 := by rw [ez]; rfl
  refine ⟨_, e, hinv, streamIO_in hio hz hb hst hno (Nat.zero_le _) O (SH_streams _ _ _ _ _ _) hzs hle ht hrd hno'
    hav (SH_dstate _ _ _ _ _ _) hgz, ⟨z', ⟨i, rfl, SH_streams _ _ _ _ _ _⟩, by rw [hno']; simp, fun ha => ?_⟩,
    hcrc, P, ZlibNgF.Proof.DeflateReset.dframe_SH _ _ _ _ _ _⟩
  rcases ht with ⟨e1, e2⟩ | ⟨r, os, -, e2⟩
  · rw [e1]; exact hni (by rw [← e2]; exact ha)
  · rw [e2]; exact fun e => by cases e

end ZlibNgF.Proof.FillIO
