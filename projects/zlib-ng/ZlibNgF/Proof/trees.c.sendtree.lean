import ZlibNgF.Proof.«trees.c.header»
import ZlibNgF.Proof.«trees.c.compress»

/-!
# `send_tree` (`ZlibNgF`)

On `SH` heaps: `send_tree(s, tree, max_code)` on a tree array whose first `m = max_code + 1` code lengths are at most
15 and whose `tree[m].Len` is the `0xffff` guard of `scan_tree` sends the bit-length symbols of the model's
`treeTokens` with the codes of `bl_tree` (lengths at most 7) and their extra bits: `8 * pending + bi_valid` grows by
exactly `(treeTokens …).map (blLen t + blExtra t)` summed, every 8-byte store of `send_bits` ends below `pbo + Lim`
when all its bits fit in `8 * Lim + 7` bits (the form of `room_header`), and only the pending count, the bit buffer
and the bytes after the pending bytes change.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.TreesSendTree
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNg.Trees ZlibNgF.Proof.DeflateInit ZlibNgF.Proof.TreesPrims
open ZlibNgF.Proof.TreesHeader ZlibNgF.Proof.TreesEmitP ZlibNgF.Proof.DeflateBits
open ZlibNgF.Math.Huff
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono sat_cwhile)
open ZlibNgF.Proof.DeflateAlloc (pure_bind_M ite_t ite_f)
open ZlibNgF.Proof.TreesCompress (sat_cdoWhile')

/-- The loop state of `send_tree`: `n`, `prevlen`, `nextlen`, `count`, `max_count`, `min_count`, `bi_buf`,
`bi_valid`. -/
abbrev TX := Int32 × Int32 × Int32 × Int32 × Int32 × Int32 × UInt64 × UInt32

/-- The symbols of one group of `send_tree` (the `if` chain after the run test). -/
def sendGroupK {β : Type} (st : StatePtr) (bltree : CtPtr) (curlen prevlen count min_count : Int32)
    (bi_buf : UInt64) (bi_valid : UInt32) (k : UInt64 × UInt32 → M β) : M β := do
  let (bi_buf, bi_valid) ←
   if count < min_count then do
     let (_, bi_buf, bi_valid) ← cdoWhile
       (fun ((count, bi_buf, bi_valid) : Int32 × UInt64 × UInt32) => do
         let (bi_buf, bi_valid) ← ZlibNg.TreesEmit.send_code st curlen.toInt bltree bi_buf bi_valid
         pure (count, bi_buf, bi_valid))
       (fun ((count, bi_buf, bi_valid) : Int32 × UInt64 × UInt32) => do
         let count ← chkI32 (count.toInt - 1)
         pure (count != 0, (count, bi_buf, bi_valid)))
       (count, bi_buf, bi_valid)
     pure (bi_buf, bi_valid)
   else if curlen != 0 then do
     let mut count := count
     let mut bi_buf := bi_buf
     let mut bi_valid := bi_valid
     if curlen != prevlen then
       (bi_buf, bi_valid) ← ZlibNg.TreesEmit.send_code st curlen.toInt bltree bi_buf bi_valid
       count ← chkI32 (count.toInt - 1)
     (bi_buf, bi_valid) ← ZlibNg.TreesEmit.send_code st REP_3_6 bltree bi_buf bi_valid
     let v ← chkI32 (count.toInt - 3)
     ZlibNg.TreesEmit.send_bits st v.toInt64.toUInt64 2 bi_buf bi_valid
   else if count <= 10 then do
     let (bi_buf, bi_valid) ← ZlibNg.TreesEmit.send_code st REPZ_3_10 bltree bi_buf bi_valid
     let v ← chkI32 (count.toInt - 3)
     ZlibNg.TreesEmit.send_bits st v.toInt64.toUInt64 3 bi_buf bi_valid
   else do
     let (bi_buf, bi_valid) ← ZlibNg.TreesEmit.send_code st REPZ_11_138 bltree bi_buf bi_valid
     let v ← chkI32 (count.toInt - 11)
     ZlibNg.TreesEmit.send_bits st v.toInt64.toUInt64 7 bi_buf bi_valid
  k (bi_buf, bi_valid)

/-- The end of an iteration of `send_tree` after a group. -/
def sendCont (n curlen nextlen : Int32) : UInt64 × UInt32 → M TX := fun r =>
  match r with
  | (bi_buf, bi_valid) =>
    let count : Int32 := 0
    let prevlen := curlen
    match (if nextlen == 0 then ((138 : Int32), (3 : Int32))
        else if curlen == nextlen then (6, 3)
        else (7, 4)) with
    | (max_count, min_count) => pure (n + 1, prevlen, nextlen, count, max_count, min_count, bi_buf, bi_valid)

/-- The loop body of `send_tree` (a copy of the translation's lambda). -/
def sendBody (st : StatePtr) (tree : CtPtr) : TX → M TX :=
    (fun ((n, prevlen, nextlen, count, max_count, min_count, bi_buf, bi_valid) :
        Int32 × Int32 × Int32 × Int32 × Int32 × Int32 × UInt64 × UInt32) => do
      let bltree ← blTreeP st
      let curlen := nextlen
      let nextlen : Int32 := (← ctDl tree (n.toInt + 1)).toUInt32.toInt32
      let count ← chkI32 (count.toInt + 1)
      if count < max_count && curlen == nextlen then
        return (n + 1, prevlen, nextlen, count, max_count, min_count, bi_buf, bi_valid)
      sendGroupK st bltree curlen prevlen count min_count bi_buf bi_valid (sendCont n curlen nextlen))

/-- The tail of `send_tree` after the initial `max_count` / `min_count`. -/
def sendTail (st : StatePtr) (tree : CtPtr) (max_code : Int32) (nextlen : Int32) (max_count min_count : Int32) :
    M Unit := do
  let bi_valid : UInt32 := (← rdD st (·.bi_valid)).toUInt32
  let bi_buf : UInt64 ← rdD st (·.bi_buf)
  let (_, _, _, _, _, _, bi_buf, bi_valid) ← cwhile
    (fun (x : TX) => pure (x.1 <= max_code, x))
    (sendBody st tree)
    ((0 : Int32), (-1 : Int32), nextlen, (0 : Int32), max_count, min_count, bi_buf, bi_valid)
  wrD st fun s => { s with bi_buf := bi_buf, bi_valid := bi_valid.toInt32 }

theorem send_tree_eq (st : StatePtr) (tree : CtPtr) (max_code : Int32) :
    send_tree st tree max_code = (do
      let nextlen : Int32 := (← ctDl tree 0).toUInt32.toInt32
      if nextlen == 0 then sendTail st tree max_code nextlen 138 3 else sendTail st tree max_code nextlen 7 4) := by
  rfl

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8}

/-- `E` bits written since the start (state `st`, bytes `d`, `bv0` bits waiting at the start): the state differs
from `st` only in `pending`, the bytes only after the pending bytes of `st`, and `bv` bits wait. -/
def BAcc (H : Heap) (i : Nat) (z : ZStream) (b : Nat) (st : DeflateState) (d : Array UInt8) (pbo bv0 E : Nat)
    (bv : UInt32) (H' : Heap) : Prop :=
  ∃ (np : UInt32) (d' : Array UInt8), H' = SH H i z b { st with pending := np } d' ∧
    WrIn d (pbo + st.pending.toNat) (pbo + np.toNat) d' ∧ st.pending.toNat ≤ np.toNat ∧
    8 * np.toNat + bv.toNat = 8 * st.pending.toNat + bv0 + E ∧ bv.toNat < 64

/-- `send_bits` after `E` bits, when the bits after it still fit below `Lim - 8` bytes. -/
theorem bacc_send_bits {pbo bv0 E Lim : Nat} (hpb : st.pending_buf = .val (.ref (.heap b) pbo))
    (hLim : pbo + Lim + 8 ≤ d.size) (hL32 : Lim < 2 ^ 31) {bv : UInt32} {H' : Heap}
    (hA : BAcc H i z b st d pbo bv0 E bv H') (val : UInt64) (len : UInt32) (bb : UInt64) (hlen : len.toNat ≤ 64)
    (hroom : 8 * st.pending.toNat + bv0 + E + len.toNat ≤ 8 * Lim + 7) :
    Sat H' (ZlibNg.TreesEmit.send_bits (some b) val len bb bv)
      (fun r H'' => BAcc H i z b st d pbo bv0 (E + len.toNat) r.2 H'') := by
  obtain ⟨np, d', rfl, w, hle, hacc, hbv⟩ := hA
  have hsz : d'.size = d.size := w.1
  refine Sat.mono (send_bits_SH (st := { st with pending := np }) (d := d') hpb val len bb bv hbv hlen
    (by dsimp only; omega) (by dsimp only; omega)) ?_
  rintro r _ ⟨np2, d2, rfl, w2, hacc2, hr, hle2, hge2⟩
  dsimp only at w2 hacc2 hle2 hge2
  refine ⟨np2, d2, rfl, ?_, by omega, by omega, hr⟩
  exact (w.widen (Nat.le_refl _) (by omega)).trans (w2.widen (by omega) (Nat.le_refl _)) (Nat.le_refl _) (Nat.le_refl _)

/-- `send_code(s, k, s->bl_tree, …)` after `E` bits: `bl_tree[k].Len` bits more. -/
theorem bacc_send_code {pbo bv0 E Lim : Nat} (hpb : st.pending_buf = .val (.ref (.heap b) pbo))
    (hLim : pbo + Lim + 8 ≤ d.size) (hL32 : Lim < 2 ^ 31) {bv : UInt32} {H' : Heap}
    (hA : BAcc H i z b st d pbo bv0 E bv H') (k : Nat) (hk : k < st.bl_tree.size) (h7 : (st.bl_tree[k]!).dl.toNat ≤ 7)
    (bb : UInt64) (hroom : 8 * st.pending.toNat + bv0 + E + (st.bl_tree[k]!).dl.toNat ≤ 8 * Lim + 7) :
    Sat H' (ZlibNg.TreesEmit.send_code (some b) (k : Int) (.ref (.bl_tree b) 0) bb bv)
      (fun r H'' => BAcc H i z b st d pbo bv0 (E + (st.bl_tree[k]!).dl.toNat) r.2 H'') := by
  obtain ⟨np, d', rfl, hrest⟩ := hA
  unfold ZlibNg.TreesEmit.send_code
  refine Sat.bind (Sat.of_eq (ctFc_T (H := H) (i := i) (z := z) (b := b) (d := d') .bl_desc { st with pending := np } k hk) ?_)
  refine Sat.bind (Sat.of_eq (ctDl_T (H := H) (i := i) (z := z) (b := b) (d := d') .bl_desc { st with pending := np } k hk) ?_)
  have e : (st.bl_tree[k]!).dl.toUInt32.toNat = (st.bl_tree[k]!).dl.toNat := UInt16.toNat_toUInt32 _
  have := bacc_send_bits (H := H) (i := i) (z := z) hpb hLim hL32 ⟨np, d', rfl, hrest⟩ ((st.bl_tree[k]!).fc.toUInt64)
    ((st.bl_tree[k]!).dl.toUInt32) bb (by rw [e]; omega) (by rw [e]; omega)
  rw [e] at this
  exact this

/-- The bits of bit-length symbol `t`: its code in `bl_tree` and its extra bits. -/
def tokCost (BL : Array Ct) (t : Nat) : Nat := (BL[t]!).dl.toNat + blExtra t

/-- The bits of a list of bit-length symbols. -/
def tokBits (BL : Array Ct) (l : List Nat) : Nat := (l.map (tokCost BL)).sum

theorem chk_small (v : Int) (h1 : -1000 ≤ v) (h2 : v ≤ 1000) : chkI32 v = pure (Int32.ofInt v) := by
  unfold chkI32; rw [ite_t (by omega)]

theorem ofInt_small (v : Int) (h1 : -1000 ≤ v) (h2 : v ≤ 1000) : (Int32.ofInt v).toInt = v := by
  rw [Int32.toInt_ofInt]; apply Int.bmod_eq_of_le <;> simp [Int32.size] <;> omega

theorem send_group {β : Type} {pbo bv0 E Lim : Nat} (hpb : st.pending_buf = .val (.ref (.heap b) pbo))
    (hLim : pbo + Lim + 8 ≤ d.size) (hL32 : Lim < 2 ^ 31) (hbl : 19 ≤ st.bl_tree.size)
    (h7 : ∀ t, t < 19 → (st.bl_tree[t]!).dl.toNat ≤ 7) {bv : UInt32} {H' : Heap}
    (hA : BAcc H i z b st d pbo bv0 E bv H') (curlen prevlen count min_count : Int32) (nl' cN mnN : Nat) (p' : Int)
    (hc : curlen.toInt = nl') (hnl : nl' ≤ 15) (hp : prevlen.toInt = p') (hcn : count.toInt = cN) (hc1 : 1 ≤ cN)
    (hc2 : cN ≤ 138) (hmn : min_count.toInt = mnN) (hm3 : 3 ≤ mnN) (hm4 : mnN ≤ 4) (bb : UInt64)
    (hroom : 8 * st.pending.toNat + bv0 + E + tokBits st.bl_tree (groupTokens p' cN mnN nl') ≤ 8 * Lim + 7)
    (k : UInt64 × UInt32 → M β) (Q : β → Heap → Prop)
    (hk : ∀ r H'', BAcc H i z b st d pbo bv0 (E + tokBits st.bl_tree (groupTokens p' cN mnN nl')) r.2 H'' →
      Sat H'' (k r) Q) :
    Sat H' (sendGroupK (some b) (.ref (.bl_tree b) 0) curlen prevlen count min_count bb bv k) Q := by
  have hcur : curlen.toInt = ((nl' : Nat) : Int) := hc
  have h7n := h7 nl' (by omega)
  have h16 := h7 16 (by omega)
  have h17 := h7 17 (by omega)
  have h18 := h7 18 (by omega)
  have ex0 : blExtra nl' = 0 := by unfold blExtra; split <;> (try split) <;> (try split) <;> omega
  unfold sendGroupK
  dsimp only
  by_cases c1 : cN < mnN
  · rw [ite_t (Int32.lt_iff_toInt_lt.mpr (by omega))]
    have hG : groupTokens p' cN mnN nl' = List.replicate cN nl' := by unfold groupTokens; rw [ite_t c1]
    have hrep : tokBits st.bl_tree (List.replicate cN nl') = cN * (st.bl_tree[nl']!).dl.toNat := by
      unfold tokBits tokCost; rw [List.map_replicate, sum_rep, ex0, Nat.add_zero]
    rw [hG, hrep] at hroom hk
    obtain ⟨L, hLe⟩ : ∃ L, (st.bl_tree[nl']!).dl.toNat = L := ⟨_, rfl⟩
    rw [hLe] at hroom hk
    refine Sat.bind (Sat.mono (sat_cdoWhile' (fun (x : Int32 × UInt64 × UInt32) H2 => ∃ r : Nat, x.1.toInt = r ∧
        1 ≤ r ∧ r ≤ cN ∧ BAcc H i z b st d pbo bv0 (E + (cN - r) * L) x.2.2 H2) (fun x => x.1.toInt.toNat)
        (fun x H2 => BAcc H i z b st d pbo bv0 (E + cN * L) x.2.2 H2) ?_
        ⟨cN, hcn, hc1, Nat.le_refl _, by rw [Nat.sub_self, Nat.zero_mul, Nat.add_zero]; exact hA⟩
        (by simp [fuel, hcn]; omega)) ?_)
    · rintro ⟨c, bb1, bv1⟩ H2 ⟨r, hr, h1, h2, hA2⟩
      dsimp only at hr hA2 ⊢
      rw [hcur]
      have hle : (cN - r) * L + L ≤ cN * L := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
      refine Sat.bind (Sat.mono (bacc_send_code hpb hLim hL32 hA2 nl' (by omega) h7n bb1 (by rw [hLe]; omega)) ?_)
      rintro ⟨bb2, bv2⟩ H3 hA3
      refine Sat.pure ?_
      try dsimp only
      rw [chk_small _ (by omega) (by omega)]
      have hc0 : ∀ hc : (Int32.ofInt (c.toInt - 1) != 0) = true, 2 ≤ r := fun hc => by
        have h0 : Int32.ofInt (c.toInt - 1) ≠ 0 := by simpa using hc
        have h1' : (Int32.ofInt (c.toInt - 1)).toInt ≠ 0 := fun e => h0 (Int32.toInt_inj.mp (by rw [e]; rfl))
        rw [ofInt_small _ (by omega) (by omega), hr] at h1'
        omega
      refine Sat.bind (Sat.pure (Sat.pure ⟨fun hc => ⟨⟨r - 1, ?_, by have := hc0 hc; omega, by omega, ?_⟩, ?_⟩,
        fun hc => ?_⟩))
      · dsimp only; rw [ofInt_small _ (by omega) (by omega), hr]; have := hc0 hc; omega
      · have e : E + (cN - r) * L + L = E + (cN - (r - 1)) * L := by
          rw [show cN - (r - 1) = (cN - r) + 1 by omega, Nat.succ_mul]; omega
        rw [hLe] at hA3; rw [← e]; exact hA3
      · dsimp only; rw [ofInt_small _ (by omega) (by omega), hr]; omega
      · dsimp only at hc ⊢
        have h0 : Int32.ofInt (c.toInt - 1) = 0 := by simpa using hc
        have h1' := congrArg Int32.toInt h0
        rw [ofInt_small _ (by omega) (by omega), hr] at h1'
        obtain rfl : r = 1 := by simp at h1'; omega
        rw [hLe] at hA3
        have e : E + (cN - 1) * L + L = E + cN * L := by
          have : (cN - 1) * L + L = cN * L := by
            rw [← Nat.succ_mul, show (cN - 1).succ = cN by omega]
          omega
        rw [← e]; exact hA3
    · rintro ⟨c, bb3, bv3⟩ H4 hA4
      try dsimp only
      exact Sat.bind (Sat.pure (hk _ _ hA4))
  rw [ite_f (fun h => c1 (by have := Int32.lt_iff_toInt_lt.mp h; omega))]
  have r16 : REP_3_6 = ((16 : Nat) : Int) := rfl
  have r17 : REPZ_3_10 = ((17 : Nat) : Int) := rfl
  have r18 : REPZ_11_138 = ((18 : Nat) : Int) := rfl
  have e2 : (2 : UInt32).toNat = 2 := rfl
  have e3 : (3 : UInt32).toNat = 3 := rfl
  have e7 : (7 : UInt32).toNat = 7 := rfl
  rw [hcur, r16, r17, r18]
  by_cases c3 : nl' ≠ 0
  · rw [ite_t (by rw [i32_ne_toInt, hcur]; simp; omega)]
    by_cases c4 : (nl' : Int) ≠ p'
    · rw [ite_t (by rw [i32_ne_toInt, hcur, hp]; exact c4)]
      have hG : tokBits st.bl_tree (groupTokens p' cN mnN nl') =
          (st.bl_tree[nl']!).dl.toNat + ((st.bl_tree[16]!).dl.toNat + 2) := by
        unfold groupTokens; rw [ite_f (by omega), ite_t c3, ite_t c4]
        simp only [List.cons_append, List.nil_append, tokBits, tokCost, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, ex0]
        have : blExtra 16 = 2 := rfl
        omega
      rw [hG] at hroom hk
      refine Sat.bind (Sat.mono (bacc_send_code hpb hLim hL32 hA nl' (by omega) h7n bb (by omega)) ?_)
      rintro ⟨bb2, bv2⟩ H3 hA3
      try dsimp only
      rw [chk_small _ (by omega) (by omega)]
      refine Sat.bind (Sat.pure ?_)
      try dsimp only
      refine Sat.bind (Sat.mono (bacc_send_code hpb hLim hL32 hA3 16 (by omega) h16 bb2 (by omega)) ?_)
      rintro ⟨bb3, bv3⟩ H4 hA4
      try dsimp only
      rw [chk_small _ (by rw [ofInt_small _ (by omega) (by omega)]; omega)
        (by rw [ofInt_small _ (by omega) (by omega)]; omega)]
      refine Sat.bind (Sat.pure ?_)
      refine Sat.bind (Sat.mono (bacc_send_bits hpb hLim hL32 hA4 _ 2 bb3 (by rw [e2]; omega) (by rw [e2]; omega)) ?_)
      rintro r H5 hA5
      rw [e2] at hA5
      exact hk r H5 (by rw [← Nat.add_assoc, ← Nat.add_assoc]; exact hA5)
    · rw [ite_f (by rw [i32_ne_toInt, hcur, hp]; exact c4)]
      have hG : tokBits st.bl_tree (groupTokens p' cN mnN nl') = (st.bl_tree[16]!).dl.toNat + 2 := by
        unfold groupTokens; rw [ite_f (by omega), ite_t c3, ite_f c4]
        simp [tokBits, tokCost, blExtra]
      rw [hG] at hroom hk
      refine Sat.bind (Sat.mono (bacc_send_code hpb hLim hL32 hA 16 (by omega) h16 bb (by omega)) ?_)
      rintro ⟨bb3, bv3⟩ H4 hA4
      try dsimp only
      rw [chk_small _ (by omega) (by omega)]
      refine Sat.bind (Sat.pure ?_)
      refine Sat.bind (Sat.mono (bacc_send_bits hpb hLim hL32 hA4 _ 2 bb3 (by rw [e2]; omega) (by rw [e2]; omega)) ?_)
      rintro r H5 hA5
      rw [e2] at hA5
      exact hk r H5 (by rw [← Nat.add_assoc]; exact hA5)
  · rw [ite_f (by rw [i32_ne_toInt, hcur]; simp; omega)]
    by_cases c5 : cN ≤ 10
    · rw [ite_t (Int32.le_iff_toInt_le.mpr (by rw [hcn]; simp; omega))]
      have hG : tokBits st.bl_tree (groupTokens p' cN mnN nl') = (st.bl_tree[17]!).dl.toNat + 3 := by
        unfold groupTokens; rw [ite_f (by omega), ite_f (by omega), ite_t c5]
        simp [tokBits, tokCost, blExtra]
      rw [hG] at hroom hk
      refine Sat.bind (Sat.mono (bacc_send_code hpb hLim hL32 hA 17 (by omega) h17 bb (by omega)) ?_)
      rintro ⟨bb3, bv3⟩ H4 hA4
      try dsimp only
      rw [chk_small _ (by omega) (by omega)]
      refine Sat.bind (Sat.pure ?_)
      refine Sat.bind (Sat.mono (bacc_send_bits hpb hLim hL32 hA4 _ 3 bb3 (by rw [e3]; omega) (by rw [e3]; omega)) ?_)
      rintro r H5 hA5
      rw [e3] at hA5
      exact hk r H5 (by rw [← Nat.add_assoc]; exact hA5)
    · rw [ite_f (fun h => c5 (by have := Int32.le_iff_toInt_le.mp h; rw [hcn] at this; simp at this; omega))]
      have hG : tokBits st.bl_tree (groupTokens p' cN mnN nl') = (st.bl_tree[18]!).dl.toNat + 7 := by
        unfold groupTokens; rw [ite_f (by omega), ite_f (by omega), ite_f c5]
        simp [tokBits, tokCost, blExtra]
      rw [hG] at hroom hk
      refine Sat.bind (Sat.mono (bacc_send_code hpb hLim hL32 hA 18 (by omega) h18 bb (by omega)) ?_)
      rintro ⟨bb3, bv3⟩ H4 hA4
      try dsimp only
      rw [chk_small _ (by omega) (by omega)]
      refine Sat.bind (Sat.pure ?_)
      refine Sat.bind (Sat.mono (bacc_send_bits hpb hLim hL32 hA4 _ 7 bb3 (by rw [e7]; omega) (by rw [e7]; omega)) ?_)
      rintro r H5 hA5
      rw [e7] at hA5
      exact hk r H5 (by rw [← Nat.add_assoc]; exact hA5)

theorem mxmn32 (nx nl : Int32) (NL nl' : Nat) (h1 : nx.toInt = NL) (h2 : nl.toInt = nl') :
    (if (nx == 0) = true then ((138 : Int32), (3 : Int32)) else if (nl == nx) = true then (6, 3) else (7, 4)).1.toInt =
      ((if NL = 0 then 138 else if nl' = NL then 6 else 7 : Nat) : Int) ∧
    (if (nx == 0) = true then ((138 : Int32), (3 : Int32)) else if (nl == nx) = true then (6, 3) else (7, 4)).2.toInt =
      ((if NL = 0 then 3 else if nl' = NL then 3 else 4 : Nat) : Int) := by
  have a : (nx == 0) = true ↔ NL = 0 := by rw [i32_eq_toInt]; simp only [Int32.toInt_zero]; omega
  have c : (nl == nx) = true ↔ nl' = NL := by rw [i32_eq_toInt]; omega
  by_cases e1 : NL = 0
  · simp [a.mpr e1, e1]
  · have e1' : ¬ (nx == 0) = true := fun h => e1 (a.mp h)
    by_cases e2 : nl' = NL
    · simp [e1, e1', c.mpr e2, e2]
    · have e2' : ¬ (nl == nx) = true := fun h => e2 (c.mp h)
      simp [e1, e1', e2, e2']

theorem tokBits_append (BL : Array Ct) (a c : List Nat) : tokBits BL (a ++ c) = tokBits BL a + tokBits BL c := by
  simp [tokBits]

theorem tArr_pend (t : DescSel) (s : DeflateState) (np : UInt32) : tArr t { s with pending := np } = tArr t s := by
  cases t <;> rfl

/-- The loop invariant of `send_tree` on tree `t` of `st` with `m` codes: `E` bits sent, and `E` plus the bits of the
symbols still to come are the bits of all of `treeTokens`. -/
def TInv (H : Heap) (i : Nat) (z : ZStream) (b : Nat) (st : DeflateState) (d : Array UInt8) (pbo bv0 : Nat)
    (t : DescSel) (m : Nat) (x : TX) (H' : Heap) : Prop :=
  ∃ (n p : Nat) (p' : Int) (nl cnt mxN mnN E : Nat), BAcc H i z b st d pbo bv0 E x.2.2.2.2.2.2.2 H' ∧
    x.1.toInt = n ∧ n ≤ m ∧ x.2.1.toInt = p' ∧ x.2.2.1.toInt = nl ∧ (n < m → nl ≤ 15) ∧
    (p' = -1 ∨ (0 ≤ p' ∧ p' ≤ 15)) ∧ x.2.2.2.1.toInt = cnt ∧ cnt < mxN ∧ x.2.2.2.2.1.toInt = mxN ∧ mxN ≤ 138 ∧
    x.2.2.2.2.2.1.toInt = mnN ∧ 3 ≤ mnN ∧ mnN ≤ 4 ∧ p = 0 ∧
    E + tokBits st.bl_tree (scanTokens (lenOf (tArr t st)) m (m - n) n p' cnt mxN mnN nl) =
      tokBits st.bl_tree (treeTokens (lenOf (tArr t st)) m)

theorem send_step {pbo bv0 Lim : Nat} (hpb : st.pending_buf = .val (.ref (.heap b) pbo))
    (hLim : pbo + Lim + 8 ≤ d.size) (hL32 : Lim < 2 ^ 31) (hbl : 19 ≤ st.bl_tree.size)
    (h7 : ∀ t, t < 19 → (st.bl_tree[t]!).dl.toNat ≤ 7) (t : DescSel) (m : Nat) (mc : Int32)
    (hmc : mc.toInt + 1 = m) (hm : m < (tArr t st).size) (hm1k : m ≤ 1000) (hA : ((tArr t st)[m]!).dl = 0xffff)
    (hA15 : ∀ n, n < m → lenOf (tArr t st) n ≤ 15)
    (hroom : 8 * st.pending.toNat + bv0 + tokBits st.bl_tree (treeTokens (lenOf (tArr t st)) m) ≤ 8 * Lim + 7)
    (x : TX) (H' : Heap) (hI : TInv H i z b st d pbo bv0 t m x H') (hlt : x.1 ≤ mc) :
    Sat H' (sendBody (some b) (.ref (tRef t b) 0) x)
      (fun x' H2 => TInv H i z b st d pbo bv0 t m x' H2 ∧ m - x'.1.toInt.toNat < m - x.1.toInt.toNat) := by
  obtain ⟨n, p, nl, cnt, mx, mn, bb, bv⟩ := x
  obtain ⟨n', -, p', nl', cN, mxN, mnN, E, hB, hn, hnm, hp, hnl, hnl15, hp15, hcn, hcm, hmx, hmx1, hmn, hmn3, hmn4,
    -, hcount⟩ := hI
  dsimp only at hB hn hp hnl hcn hmx hmn hcount hlt ⊢
  have hlt' : n' < m := by have := Int32.le_iff_toInt_le.mp hlt; omega
  have hk : m - n' = (m - (n' + 1)) + 1 := by omega
  have e1 : n.toInt + 1 = ((n' + 1 : Nat) : Int) := by omega
  obtain ⟨np, d', rfl, hrest⟩ := hB
  unfold sendBody
  simp only [blTreeP, pure_bind_M, e1]
  refine Sat.bind (Sat.of_eq (ctDl_T t { st with pending := np } (n' + 1) (by rw [tArr_pend]; omega)) ?_)
  rw [tArr_pend]
  have hNL : ((tArr t st)[n' + 1]!.dl.toUInt32.toInt32).toInt = nextLen (lenOf (tArr t st)) m n' := by
    have e : ((tArr t st)[n' + 1]!.dl.toUInt32.toInt32).toInt = ((tArr t st)[n' + 1]!.dl.toNat : Int) := by
      have := ((tArr t st)[n' + 1]!).dl.toNat_lt
      rw [DeflateAlloc.u32_toInt32_toInt _ (by simp only [UInt16.toNat_toUInt32]; omega), UInt16.toNat_toUInt32]
    rw [e]; unfold nextLen lenOf
    split
    · rfl
    · obtain rfl : n' + 1 = m := by omega
      rw [hA]; rfl
  have hNL15 : n' + 1 < m → nextLen (lenOf (tArr t st)) m n' ≤ 15 := fun h => by
    unfold nextLen; rw [ite_t h]; exact hA15 _ h
  rw [hk] at hcount
  simp only [scanTokens] at hcount
  generalize (tArr t st)[n' + 1]!.dl.toUInt32.toInt32 = nx at hNL ⊢
  generalize nextLen (lenOf (tArr t st)) m n' = NL at hNL hNL15 hcount
  rw [chk_small _ (by omega) (by omega)]
  refine Sat.bind (Sat.pure ?_)
  have hc1 : (Int32.ofInt (cnt.toInt + 1)).toInt = ((cN + 1 : Nat) : Int) := by
    rw [ofInt_small _ (by omega) (by omega)]; omega
  have hsucc : (n + 1).toInt = ((n' + 1 : Nat) : Int) := by
    rw [TreesInit.i32_succ n (by omega) (by omega)]; omega
  have hmu : m - (n + 1).toInt.toNat < m - n.toInt.toNat := by rw [hsucc, hn]; omega
  have bc1 : ((decide (Int32.ofInt (cnt.toInt + 1) < mx) && nl == nx) = true) ↔ (cN + 1 < mxN ∧ nl' = NL) := by
    rw [Bool.and_eq_true, decide_eq_true_iff, Int32.lt_iff_toInt_lt, hc1, hmx, i32_eq_toInt, hnl, hNL]; omega
  by_cases c1 : cN + 1 < mxN ∧ nl' = NL
  · rw [ite_t (bc1.mpr c1)]
    simp only [ite_t c1] at hcount
    exact Sat.pure ⟨⟨n' + 1, 0, p', NL, cN + 1, mxN, mnN, E, ⟨np, d', rfl, hrest⟩, hsucc, by omega, hp, hNL, hNL15,
      hp15, hc1, c1.1, hmx, hmx1, hmn, hmn3, hmn4, rfl, hcount⟩, hmu⟩
  rw [ite_f (fun h => c1 (bc1.mp h))]
  simp only [ite_f c1] at hcount
  have hnl15' := hnl15 hlt'
  rw [tokBits_append] at hcount
  refine send_group hpb hLim hL32 hbl h7 ⟨np, d', rfl, hrest⟩ nl p _ mn nl' (cN + 1) mnN p' hnl hnl15' hp hc1
    (by omega) (by omega) hmn hmn3 hmn4 bb (by omega) _ _ ?_
  rintro ⟨bb2, bv2⟩ H3 hB3
  unfold sendCont
  obtain ⟨m1, m2⟩ := mxmn32 nx nl NL nl' hNL hnl
  generalize (if (nx == 0) = true then ((138 : Int32), (3 : Int32)) else if (nl == nx) = true then (6, 3) else (7, 4))
    = pr at m1 m2 ⊢
  obtain ⟨mx', mn'⟩ := pr
  dsimp only at m1 m2 ⊢
  refine Sat.pure ⟨⟨n' + 1, 0, nl', NL, 0, _, _, _, hB3, hsucc, by omega, hnl, hNL, hNL15, Or.inr ⟨by omega, by omega⟩,
    rfl, ?_, m1, ?_, m2, ?_, ?_, rfl, ?_⟩, hmu⟩
  · split <;> (try split) <;> omega
  · split <;> (try split) <;> omega
  · split <;> (try split) <;> omega
  · split <;> (try split) <;> omega
  · rw [Nat.add_assoc]; exact hcount

/-- What `send_tree` leaves: the pending count and the bit buffer advanced by exactly `bits`, the bytes changed only
after the pending bytes of `st`, fewer than 64 bits waiting. -/
def SendPost (H : Heap) (i : Nat) (z : ZStream) (b : Nat) (st : DeflateState) (d : Array UInt8) (pbo bits : Nat)
    (H' : Heap) : Prop :=
  ∃ (np : UInt32) (bb : UInt64) (bv : UInt32) (d' : Array UInt8),
    H' = SH H i z b { st with pending := np, bi_buf := bb, bi_valid := bv.toInt32 } d' ∧
    WrIn d (pbo + st.pending.toNat) (pbo + np.toNat) d' ∧ st.pending.toNat ≤ np.toNat ∧
    8 * np.toNat + bv.toNat = 8 * st.pending.toNat + st.bi_valid.toInt.toNat + bits ∧ bv.toNat < 64

theorem send_tail {pbo Lim : Nat} (hpb : st.pending_buf = .val (.ref (.heap b) pbo))
    (hLim : pbo + Lim + 8 ≤ d.size) (hL32 : Lim < 2 ^ 31) (hbl : 19 ≤ st.bl_tree.size)
    (h7 : ∀ t, t < 19 → (st.bl_tree[t]!).dl.toNat ≤ 7) (t : DescSel) (m : Nat) (mc : Int32)
    (hmc : mc.toInt + 1 = m) (hm1 : 1 ≤ m) (hm : m < (tArr t st).size) (hm1k : m ≤ 1000)
    (hA : ((tArr t st)[m]!).dl = 0xffff) (hA15 : ∀ n, n < m → lenOf (tArr t st) n ≤ 15)
    (v0 : 0 ≤ st.bi_valid.toInt) (v64 : st.bi_valid.toInt < 64)
    (hroom : 8 * st.pending.toNat + st.bi_valid.toInt.toNat +
      tokBits st.bl_tree (treeTokens (lenOf (tArr t st)) m) ≤ 8 * Lim + 7)
    (nl : Int32) (hnl : nl.toInt = lenOf (tArr t st) 0) (mx mn : Int32)
    (hmx : mx.toInt = ((if lenOf (tArr t st) 0 = 0 then 138 else 7 : Nat) : Int))
    (hmn : mn.toInt = ((if lenOf (tArr t st) 0 = 0 then 3 else 4 : Nat) : Int)) :
    Sat (SH H i z b st d) (sendTail (some b) (.ref (tRef t b) 0) mc nl mx mn)
      (fun _ H' => SendPost H i z b st d pbo (tokBits st.bl_tree (treeTokens (lenOf (tArr t st)) m)) H') := by
  unfold sendTail
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  have hv := toU32 _ v0
  refine Sat.bind (Sat.mono (sat_cwhile (TInv H i z b st d pbo st.bi_valid.toInt.toNat t m)
    (fun x => m - x.1.toInt.toNat) (fun x H' => TInv H i z b st d pbo st.bi_valid.toInt.toNat t m x H' ∧ ¬ x.1 ≤ mc)
    ?_ ?_ (by simp [fuel]; omega)) ?_)
  · intro x H' hI
    refine Sat.pure ⟨fun hc => send_step hpb hLim hL32 hbl h7 t m mc hmc hm hm1k hA hA15 hroom x H' hI
      (of_decide_eq_true hc), fun hc => ⟨hI, fun h => by simp [h] at hc⟩⟩
  · refine ⟨0, 0, -1, lenOf (tArr t st) 0, 0, _, _, 0, ⟨st.pending, d, rfl, WrIn.refl _ _ _,
      Nat.le_refl _, by dsimp only; rw [hv]; omega, by dsimp only; rw [hv]; omega⟩, rfl, by omega, rfl, hnl,
      fun h => hA15 0 h, Or.inl rfl, rfl, ?_, hmx, ?_, hmn, ?_, ?_, rfl, ?_⟩
    · split <;> omega
    · split <;> omega
    · split <;> omega
    · split <;> omega
    · simp only [Nat.zero_add, Nat.sub_zero]; rfl
  · rintro ⟨n, p, nl2, cnt, mx2, mn2, bb, bv⟩ _ ⟨⟨n', -, p', nl', cN, mxN, mnN, E, ⟨np, d', rfl, w, hle, hacc, hbv⟩,
      hn, hnm, -, -, -, -, -, -, -, -, -, -, -, -, hcount⟩, hx⟩
    dsimp only at hn hcount hx hacc hbv ⊢
    have hmn' : n' = m := by have := Int32.lt_iff_toInt_lt.mp (Int32.not_le.mp hx); omega
    subst hmn'
    rw [Nat.sub_self] at hcount
    simp only [scanTokens, tokBits, List.map_nil, List.sum_nil, Nat.add_zero] at hcount
    refine Sat.of_eq (wrD_SH _) ⟨np, bb, bv, d', rfl, w, hle, ?_, hbv⟩
    unfold tokBits; omega

/-- **`send_tree`** on tree `t` with `m = max_code + 1` codes of lengths at most 15 and the `0xffff` guard at `m`,
`bl_tree` code lengths at most 7, fewer than 64 bits waiting, and room for every bit of `treeTokens` plus one 8-byte
store below `pbo + Lim`: no fault, exactly the bits of `treeTokens` sent (`SendPost`). -/
theorem send_tree_SH {pbo Lim : Nat} (hpb : st.pending_buf = .val (.ref (.heap b) pbo))
    (hLim : pbo + Lim + 8 ≤ d.size) (hL32 : Lim < 2 ^ 31) (hbl : 19 ≤ st.bl_tree.size)
    (h7 : ∀ t, t < 19 → (st.bl_tree[t]!).dl.toNat ≤ 7) (t : DescSel) (m : Nat) (mc : Int32)
    (hmc : mc.toInt + 1 = m) (hm1 : 1 ≤ m) (hm : m < (tArr t st).size) (hm1k : m ≤ 1000)
    (hA : ((tArr t st)[m]!).dl = 0xffff) (hA15 : ∀ n, n < m → lenOf (tArr t st) n ≤ 15)
    (v0 : 0 ≤ st.bi_valid.toInt) (v64 : st.bi_valid.toInt < 64)
    (hroom : 8 * st.pending.toNat + st.bi_valid.toInt.toNat +
      tokBits st.bl_tree (treeTokens (lenOf (tArr t st)) m) ≤ 8 * Lim + 7) :
    Sat (SH H i z b st d) (send_tree (some b) (.ref (tRef t b) 0) mc)
      (fun _ H' => SendPost H i z b st d pbo (tokBits st.bl_tree (treeTokens (lenOf (tArr t st)) m)) H') := by
  rw [send_tree_eq]
  refine Sat.bind (Sat.of_eq (ctDl_T t st 0 (by omega)) ?_)
  have e : ((tArr t st)[0]!.dl.toUInt32.toInt32).toInt = lenOf (tArr t st) 0 := by
    have := (tArr t st)[0]!.dl.toNat_lt
    rw [DeflateAlloc.u32_toInt32_toInt _ (by simp only [UInt16.toNat_toUInt32]; omega), UInt16.toNat_toUInt32]; rfl
  have b0 : ((tArr t st)[0]!.dl.toUInt32.toInt32 == 0) = true ↔ lenOf (tArr t st) 0 = 0 := by
    rw [i32_eq_toInt, e]; simp
  dsimp only
  split
  · rename_i h
    exact send_tail hpb hLim hL32 hbl h7 t m mc hmc hm1 hm hm1k hA hA15 v0 v64 hroom _ e _ _
      (by simp [b0.mp h]) (by simp [b0.mp h])
  · rename_i h
    have h' : lenOf (tArr t st) 0 ≠ 0 := fun h2 => h (b0.mpr h2)
    exact send_tail hpb hLim hL32 hbl h7 t m mc hmc hm1 hm hm1k hA hA15 v0 v64 hroom _ e _ _
      (by simp [h']) (by simp [h'])

end

end ZlibNgF.Proof.TreesSendTree
