import ZlibNgF.Proof.«inflate.c.sync»
import ZlibNgF.Proof.«inflate.c.dict»
import ZlibNgF.ZlibNg.arch.generic.«chunkset_c.c»

/-!
# Memory steps of the chunk copies (`ZlibNgF`)

The chunk copies of `chunkset_tpl.h` and `inflate_p.h` read and write one heap block, the caller's output buffer
`ob`. `ORun H0 H ob N lo hi` says that `H` is `H0` with only the bytes `[lo, hi)` of block `ob` (of `N` bytes)
changed. Each memory primitive (`Ptr.add`, `Ptr.diff`, `Ptr.lt`, byte loads and stores, `memread`/`memwrite`,
`memcpy`, `memmove`, `memset` inside the block) gets a `Sat` lemma: no fault, the exact result, and `ORun`.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.ChunkMem
open C
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono sat_cwhile)
open ZlibNgF.Proof.InflateDict (copyFold copyFold_size copyFold_get memcpy_loop space_get_heap)
open ZlibNgF.Proof.InflateInv (upd_upd)

theorem upd_self {α : Type} (t : Tbl (Option α)) (k : Nat) (a : α) (h : t k = some a) :
    upd t k (some a) = t := by
  have hk : k < t.arr.size := Tbl.lt_size_of_get_ne t k (by simp [Tbl.get] at h ⊢; simp [h])
  have ha : t.arr[k] = some a := by
    have : t.get k = some a := h
    rw [Tbl.get_eq, Array.getElem?_eq_getElem hk] at this
    simpa using this
  unfold upd Tbl.set
  simp only [hk, ↓reduceIte, Array.set!_eq_setIfInBounds]
  cases t with
  | mk arr =>
    congr 1
    apply Array.ext_getElem?
    intro j
    simp only [Array.getElem?_setIfInBounds]
    split
    · rename_i e; subst e; simp only at ha; rw [Array.getElem?_eq_getElem hk, ha]
    · rfl

/-! ## Runs that change only some bytes of the output block -/

/-- From `H0` to `H` only the bytes `[lo, hi)` of heap block `ob`, of `N` bytes, changed. -/
structure ORun (H0 H : Heap) (ob N lo hi : Nat) : Prop where
  eq : H = { H0 with bytes := upd H0.bytes ob (H.bytes ob) }
  blk : ∃ a0 a, H0.bytes ob = some a0 ∧ H.bytes ob = some a ∧ a0.size = N ∧ a.size = N ∧
    ∀ j, (j < lo ∨ hi ≤ j) → a[j]! = a0[j]!

theorem ORun.refl {H : Heap} {ob N : Nat} {a : Array UInt8} (hd : H.bytes ob = some a) (hN : a.size = N)
    (lo hi : Nat) : ORun H H ob N lo hi := by
  refine ⟨?_, a, a, hd, hd, hN, hN, fun _ _ => rfl⟩
  rw [hd, upd_self _ _ _ hd]

theorem ORun.cur {H0 H : Heap} {ob N lo hi : Nat} (r : ORun H0 H ob N lo hi) :
    ∃ a, H.bytes ob = some a ∧ a.size = N := by
  obtain ⟨_, a, _, ha, _, hN, _⟩ := r.blk; exact ⟨a, ha, hN⟩

theorem ORun.init {H0 H : Heap} {ob N lo hi : Nat} (r : ORun H0 H ob N lo hi) :
    ∃ a, H0.bytes ob = some a ∧ a.size = N := by
  obtain ⟨a, _, ha, _, hN, _⟩ := r.blk; exact ⟨a, ha, hN⟩

theorem ORun.mono {H0 H : Heap} {ob N lo hi lo' hi' : Nat} (r : ORun H0 H ob N lo hi) (h1 : lo' ≤ lo)
    (h2 : hi ≤ hi') : ORun H0 H ob N lo' hi' := by
  obtain ⟨a0, a, e0, e, s0, s, hp⟩ := r.blk
  exact ⟨r.eq, a0, a, e0, e, s0, s, fun j hj => hp j (by omega)⟩

theorem ORun.trans {H0 H1 H2 : Heap} {ob N lo hi : Nat} (r1 : ORun H0 H1 ob N lo hi)
    (r2 : ORun H1 H2 ob N lo hi) : ORun H0 H2 ob N lo hi := by
  obtain ⟨a0, a1, e0, e1, s0, s1, p1⟩ := r1.blk
  obtain ⟨b1, a2, f1, e2, _, s2, p2⟩ := r2.blk
  rw [e1] at f1; cases f1
  refine ⟨?_, a0, a2, e0, e2, s0, s2, fun j hj => (p2 j hj).trans (p1 j hj)⟩
  have q1 := r1.eq
  have q2 := r2.eq
  rw [q2, q1]
  simp only [upd_upd, upd_same]

/-- A write of a new array of the same size into block `ob` that keeps the bytes outside `[lo, hi)`. -/
theorem ORun.write {H0 H : Heap} {ob N lo hi : Nat} (r : ORun H0 H ob N lo hi) {a a' : Array UInt8}
    (ha : H.bytes ob = some a) (hs : a'.size = a.size) (hp : ∀ j, (j < lo ∨ hi ≤ j) → a'[j]! = a[j]!) :
    ORun H0 { H with bytes := upd H.bytes ob (some a') } ob N lo hi := by
  have r2 : ORun H { H with bytes := upd H.bytes ob (some a') } ob N lo hi := by
    obtain ⟨a1, ha1, hN⟩ := r.cur
    rw [ha] at ha1; cases ha1
    refine ⟨?_, a, a', ha, upd_same _ _ _, hN, hs.trans hN, hp⟩
    simp only [upd_same]
  exact r.trans r2

theorem ORun.bytes_ne {H0 H : Heap} {ob N lo hi : Nat} (r : ORun H0 H ob N lo hi) {c : Nat} (hc : c ≠ ob) :
    H.bytes c = H0.bytes c := by
  rw [r.eq]; exact upd_ne _ _ _ _ hc

theorem ORun.get_ne {H0 H : Heap} {ob N lo hi : Nat} (r : ORun H0 H ob N lo hi) {rr : BRef}
    (hr : rr ≠ .heap ob) : Space.get H rr = Space.get H0 rr := by
  rw [r.eq]
  cases rr with
  | heap c =>
    have : c ≠ ob := fun e => hr (e ▸ rfl)
    show upd H0.bytes ob _ c = H0.bytes c
    exact upd_ne _ _ _ _ this
  | const _ => rfl
  | str _ => rfl

/-! ## Pointer arithmetic and comparison inside one object -/

theorem sat_add {H : Heap} {r : BRef} {a : Array UInt8} {off : Nat} (hb : Space.get H r = some a)
    (ho : off ≤ a.size) (k : Int) (m : Nat) (hm : (off : Int) + k = m) (hmN : m ≤ a.size) :
    Sat H (Ptr.add (.ref r off) k) (fun p H' => p = .ref r m ∧ H' = H) := by
  have hc : off ≤ a.size ∧ 0 ≤ (off : Int) + k ∧ (off : Int) + k ≤ (a.size : Int) := by omega
  have e : ((off : Int) + k).toNat = m := by omega
  exact ⟨_, _, by simp only [Ptr.add, hb, hc, and_self, ↓reduceIte, e], rfl, rfl⟩

theorem sat_diff {H : Heap} {r : BRef} {a : Array UInt8} {o1 o2 : Nat} (hb : Space.get H r = some a)
    (h1 : o1 ≤ a.size) (h2 : o2 ≤ a.size) (hN : a.size < 2 ^ 63) :
    Sat H (Ptr.diff (.ref r o1) (.ref r o2)) (fun d H' => d = Int64.ofInt ((o1 : Int) - o2) ∧ H' = H) := by
  have hr : -(2 ^ 63 : Int) ≤ (o1 : Int) - (o2 : Int) ∧ (o1 : Int) - (o2 : Int) < 2 ^ 63 := by omega
  exact ⟨_, _, by simp only [Ptr.diff, hb, h1, h2, and_self, ↓reduceIte, hr], rfl, rfl⟩

theorem sat_lt {H : Heap} {r : BRef} {a : Array UInt8} {o1 o2 : Nat} (hb : Space.get H r = some a)
    (h1 : o1 ≤ a.size) (h2 : o2 ≤ a.size) :
    Sat H (Ptr.lt (.ref r o1) (.ref r o2)) (fun c H' => c = decide (o1 < o2) ∧ H' = H) :=
  ⟨_, _, by simp only [Ptr.lt, hb, h1, h2, and_self, ↓reduceIte], rfl, rfl⟩

theorem sat_le {H : Heap} {r : BRef} {a : Array UInt8} {o1 o2 : Nat} (hb : Space.get H r = some a)
    (h1 : o1 ≤ a.size) (h2 : o2 ≤ a.size) :
    Sat H (Ptr.le (.ref r o1) (.ref r o2)) (fun c H' => c = decide (o1 ≤ o2) ∧ H' = H) := by
  refine ⟨decide (o1 ≤ o2), H, ?_, rfl, rfl⟩
  have e : (!decide (o2 < o1)) = decide (o1 ≤ o2) := by rw [Bool.eq_iff_iff]; simp
  simp only [Ptr.le, bind_app, Ptr.lt, hb, h1, h2, and_self, ↓reduceIte, e]
  rfl

theorem toNat_ofInt_nonneg (w : Int) (h0 : 0 ≤ w) (h1 : w < 2 ^ 63) :
    (Int64.ofInt w).toUInt64.toNat = w.toNat := by
  rw [Int64.toNat_toUInt64_of_le, Int64.toNatClampNeg_ofInt_of_le (by omega) h1]
  rw [Int64.le_iff_toInt_le, Int64.toInt_ofInt_of_le (by omega) h1]
  simpa using h0

/-- `(size_t)ABS(d)` of a `ptrdiff_t` value `d` that is not `PTRDIFF_MIN`. -/
theorem absI64 (v : Int) (h1 : -2 ^ 63 < v) (h2 : v < 2 ^ 63) :
    (if Int64.ofInt v < 0 then -Int64.ofInt v else Int64.ofInt v).toUInt64.toNat = v.natAbs := by
  by_cases hv : 0 ≤ v
  · have : ¬ Int64.ofInt v < 0 := by
      rw [Int64.lt_iff_toInt_lt, Int64.toInt_ofInt_of_le (by omega) h2]; simp; omega
    simp only [this, ↓reduceIte]; rw [toNat_ofInt_nonneg v hv h2]; omega
  · have : Int64.ofInt v < 0 := by
      rw [Int64.lt_iff_toInt_lt, Int64.toInt_ofInt_of_le (by omega) h2]; simp; omega
    simp only [this, ↓reduceIte]; rw [Int64.neg_ofInt, toNat_ofInt_nonneg (-v) (by omega) (by omega)]; omega

/-! ## Loads -/

theorem sat_load {H : Heap} {r : BRef} {a : Array UInt8} {k : Nat} (hb : Space.get H r = some a)
    (hk : k < a.size) : Sat H (Ptr.load (.ref r k) : M UInt8) (fun _ H' => H' = H) :=
  ⟨a[k], _, by simp [Ptr.load, hb, hk], rfl⟩

theorem sat_index8 {H : Heap} {r : BRef} {a : Array UInt8} {k : Nat} (hb : Space.get H r = some a)
    (i : Nat) (hk : k + i < a.size) : Sat H (index8 (.ref r k) (i : Int)) (fun _ H' => H' = H) := by
  unfold index8 Ptr.index
  refine Sat.bind (Sat.mono (sat_add hb (by omega) (i : Int) (k + i) (by omega) (by omega)) ?_)
  rintro p H' ⟨rfl, rfl⟩
  exact sat_load hb hk

theorem sat_memread4 {H : Heap} {r : BRef} {a : Array UInt8} {k : Nat} (hb : Space.get H r = some a)
    (hk : k + 4 ≤ a.size) : Sat H (memread4 (.ref r k)) (fun _ H' => H' = H) := by
  unfold memread4
  refine Sat.bind (Sat.mono (sat_index8 hb 0 (by omega)) ?_); rintro _ H' rfl
  refine Sat.bind (Sat.mono (sat_index8 hb 1 (by omega)) ?_); rintro _ H' rfl
  refine Sat.bind (Sat.mono (sat_index8 hb 2 (by omega)) ?_); rintro _ H' rfl
  refine Sat.bind (Sat.mono (sat_index8 hb 3 (by omega)) ?_); rintro _ H' rfl
  exact Sat.pure rfl

theorem sat_memread8 {H : Heap} {r : BRef} {a : Array UInt8} {k : Nat} (hb : Space.get H r = some a)
    (hk : k + 8 ≤ a.size) : Sat H (memread8 (.ref r k)) (fun _ H' => H' = H) := by
  unfold memread8
  refine Sat.bind (Sat.mono (sat_memread4 hb (by omega)) ?_); rintro _ H' rfl
  refine Sat.bind (Sat.mono (sat_add hb (by omega) 4 (k + 4) (by omega) (by omega)) ?_)
  rintro p H' ⟨rfl, rfl⟩
  refine Sat.bind (Sat.mono (sat_memread4 hb (by omega)) ?_); rintro _ H' rfl
  exact Sat.pure rfl

/-! ## Stores into the output block -/

theorem space_heap (H : Heap) (b : Nat) : Space.get H (BRef.heap b) = H.bytes b := rfl

theorem ORun.sat_store {H0 H : Heap} {ob N lo hi : Nat} (r : ORun H0 H ob N lo hi) {k : Nat} (v : UInt8)
    (h1 : lo ≤ k) (h2 : k < hi) (hk : k < N) :
    Sat H (Ptr.store (Ptr.ref (BRef.heap ob) k) v) (fun _ H' => ORun H0 H' ob N lo hi) := by
  obtain ⟨a, ha, hN⟩ := r.cur
  have hk' : k < a.size := by omega
  refine ⟨(), { H with bytes := upd H.bytes ob (some (a.set! k v)) }, ?_, ?_⟩
  · simp only [Ptr.store, space_heap, ha, Space.ro, Heap.isRo, Bool.false_eq_true, ↓reduceIte, hk',
      Space.modify, Heap.modifyBytes, Tbl.modify_opt H.bytes ob _ a ha]
  · refine r.write ha (by simp [Array.set!_eq_setIfInBounds]) (fun j hj => ?_)
    have : k ≠ j := by omega
    simp [Array.set!_eq_setIfInBounds, getElem!_def, this]

/-- `*(p + j) = w; rest` at a byte of the frame. -/
theorem ORun.sat_store_add {H0 H : Heap} {ob N lo hi : Nat} (r : ORun H0 H ob N lo hi) {k : Nat} (j : Int)
    (m : Nat) (hm : (k : Int) + j = m) (hk : k ≤ N) (h1 : lo ≤ m) (h2 : m < hi) (hmN : m < N) (w : UInt8)
    {β : Type} (rest : M β) (Q : β → Heap → Prop) (hr : ∀ H', ORun H0 H' ob N lo hi → Sat H' rest Q) :
    Sat H (do let p ← Ptr.add (Ptr.ref (BRef.heap ob) k) j; Ptr.store p w; rest) Q := by
  obtain ⟨a, ha, hN⟩ := r.cur
  refine Sat.bind (Sat.mono (sat_add (space_heap H ob ▸ ha) (by omega) j m hm (by omega)) ?_)
  rintro p H' ⟨rfl, rfl⟩
  exact Sat.bind (Sat.mono (r.sat_store w h1 h2 hmN) fun _ H2 r2 => hr H2 r2)

theorem ORun.sat_memwrite8 {H0 H : Heap} {ob N lo hi : Nat} (r : ORun H0 H ob N lo hi) {k : Nat} (v : UInt64)
    (h1 : lo ≤ k) (h2 : k + 8 ≤ hi) (hk : k + 8 ≤ N) :
    Sat H (memwrite8 (Ptr.ref (BRef.heap ob) k) v) (fun _ H' => ORun H0 H' ob N lo hi) := by
  unfold memwrite8
  refine r.sat_store_add 0 (k + 0) (by omega) (by omega) (by omega) (by omega) (by omega) _ _ _ fun H1 r1 => ?_
  refine r1.sat_store_add 1 (k + 1) (by omega) (by omega) (by omega) (by omega) (by omega) _ _ _ fun H1 r1 => ?_
  refine r1.sat_store_add 2 (k + 2) (by omega) (by omega) (by omega) (by omega) (by omega) _ _ _ fun H1 r1 => ?_
  refine r1.sat_store_add 3 (k + 3) (by omega) (by omega) (by omega) (by omega) (by omega) _ _ _ fun H1 r1 => ?_
  refine r1.sat_store_add 4 (k + 4) (by omega) (by omega) (by omega) (by omega) (by omega) _ _ _ fun H1 r1 => ?_
  refine r1.sat_store_add 5 (k + 5) (by omega) (by omega) (by omega) (by omega) (by omega) _ _ _ fun H1 r1 => ?_
  refine r1.sat_store_add 6 (k + 6) (by omega) (by omega) (by omega) (by omega) (by omega) _ _ _ fun H1 r1 => ?_
  obtain ⟨a, ha, hN⟩ := r1.cur
  refine Sat.bind (Sat.mono (sat_add (space_heap H1 ob ▸ ha) (by omega) 7 (k + 7) (by omega) (by omega)) ?_)
  rintro p H' ⟨rfl, rfl⟩
  exact r1.sat_store _ (by omega) (by omega) (by omega)

/-! ## `memset`, `memmove`, `memcpy` inside the output block -/

/-- The loop of `memset`. -/
def fillFold (byte : UInt8) (od : Nat) (l : List Nat) (a : Array UInt8) : Array UInt8 :=
  l.foldl (fun out i => out.set! (od + i) byte) a

theorem fillFold_size (byte : UInt8) (od : Nat) (l : List Nat) (a : Array UInt8) :
    (fillFold byte od l a).size = a.size := by
  induction l generalizing a with
  | nil => rfl
  | cons x l ih =>
    simp only [fillFold, List.foldl_cons] at ih ⊢
    rw [ih]; simp [Array.set!_eq_setIfInBounds]

theorem fillFold_get (byte : UInt8) (od : Nat) (l : List Nat) (a : Array UInt8) (j : Nat)
    (hj : ∀ i ∈ l, od + i ≠ j) : (fillFold byte od l a)[j]! = a[j]! := by
  induction l generalizing a with
  | nil => rfl
  | cons x l ih =>
    simp only [fillFold, List.foldl_cons] at ih ⊢
    rw [ih _ (fun i hi => hj i (List.mem_cons_of_mem _ hi))]
    have hx : od + x ≠ j := hj x (List.mem_cons_self ..)
    simp only [Array.set!_eq_setIfInBounds, getElem!_def, Array.getElem?_setIfInBounds]
    simp [hx]

theorem memset_loop (a : Array UInt8) (byte : UInt8) (od n : Nat) :
    (Id.run do
      let mut out := a
      for i in [0:n] do
        out := out.set! (od + i) byte
      return out) = fillFold byte od (List.range' 0 n) a := by
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp [fillFold]
  rfl

theorem modify_heap (H : Heap) (ob : Nat) (a : Array UInt8) (ha : H.bytes ob = some a) (g : Array UInt8 → Array UInt8) :
    Space.modify H (BRef.heap ob) g = { H with bytes := upd H.bytes ob (some (g a)) } := by
  simp only [Space.modify, Heap.modifyBytes, Tbl.modify_opt H.bytes ob _ a ha]

theorem mem_range'_bound {i od n j : Nat} (hi : i ∈ List.range' 0 n) (hj : j < od ∨ od + n ≤ j) : od + i ≠ j := by
  rw [List.mem_range'] at hi; omega

theorem ORun.sat_memset {H0 H : Heap} {ob N lo hi : Nat} (r : ORun H0 H ob N lo hi) {od : Nat} (byte : UInt8)
    (n : Nat) (h1 : lo ≤ od) (h2 : od + n ≤ hi) (hN : od + n ≤ N) :
    Sat H (Ptr.memset (Ptr.ref (BRef.heap ob) od) byte n) (fun _ H' => ORun H0 H' ob N lo hi) := by
  obtain ⟨a, ha, haN⟩ := r.cur
  have hs : od + n ≤ a.size := by omega
  refine ⟨(), _, ?_, r.write ha (fillFold_size byte od (List.range' 0 n) a) (fun j hj =>
    fillFold_get byte od (List.range' 0 n) a j (fun i hi => mem_range'_bound hi (by omega)))⟩
  simp only [Ptr.memset, space_heap, ha, Space.ro, Heap.isRo, Bool.false_eq_true, ↓reduceIte, hs]
  rw [modify_heap H ob a ha, memset_loop]

theorem ORun.sat_memmove {H0 H : Heap} {ob N lo hi : Nat} (r : ORun H0 H ob N lo hi) {od os : Nat}
    (n : Nat) (h1 : lo ≤ od) (h2 : od + n ≤ hi) (hN : od + n ≤ N) (hs : os + n ≤ N) :
    Sat H (Ptr.memmove (Ptr.ref (BRef.heap ob) od) (Ptr.ref (BRef.heap ob) os) n)
      (fun _ H' => ORun H0 H' ob N lo hi) := by
  obtain ⟨a, ha, haN⟩ := r.cur
  have hd : od + n ≤ a.size ∧ os + n ≤ a.size := by omega
  refine ⟨(), _, ?_, r.write ha (copyFold_size a od os (List.range' 0 n) a) (fun j hj =>
    copyFold_get a od os (List.range' 0 n) a j (fun i hi => mem_range'_bound hi (by omega)))⟩
  simp only [Ptr.memmove, space_heap, ha, Space.ro, Heap.isRo, Bool.false_eq_true, ↓reduceIte, hd]
  rw [modify_heap H ob a ha, memcpy_loop]
  simp

theorem ORun.sat_memcpy {H0 H : Heap} {ob N lo hi : Nat} (r : ORun H0 H ob N lo hi) {od os : Nat}
    (n : Nat) (h1 : lo ≤ od) (h2 : od + n ≤ hi) (hN : od + n ≤ N) (hs : os + n ≤ N)
    (hov : od + n ≤ os ∨ os + n ≤ od) :
    Sat H (Ptr.memcpy (Ptr.ref (BRef.heap ob) od) (Ptr.ref (BRef.heap ob) os) n)
      (fun _ H' => ORun H0 H' ob N lo hi) := by
  obtain ⟨a, ha, haN⟩ := r.cur
  have hd : od + n ≤ a.size ∧ os + n ≤ a.size := by omega
  have hno : ¬ (True ∧ n > 0 ∧ ¬ (od + n ≤ os ∨ os + n ≤ od)) := by
    intro ⟨_, _, h⟩; exact h hov
  refine ⟨(), _, ?_, r.write ha (copyFold_size a od os (List.range' 0 n) a) (fun j hj =>
    copyFold_get a od os (List.range' 0 n) a j (fun i hi => mem_range'_bound hi (by omega)))⟩
  simp only [Ptr.memcpy, space_heap, ha, Space.ro, Heap.isRo, Bool.false_eq_true, ↓reduceIte, hd]
  rw [modify_heap H ob a ha, memcpy_loop]
  simp only [and_self, ↓reduceIte, hno]

/-- `memcpy` into the output block from another object (the window). -/
theorem ORun.sat_memcpy_ext {H0 H : Heap} {ob N lo hi : Nat} (r : ORun H0 H ob N lo hi) {od os : Nat}
    {rs : BRef} {src : Array UInt8} (hrs : rs ≠ BRef.heap ob) (hsrc : Space.get H0 rs = some src)
    (n : Nat) (h1 : lo ≤ od) (h2 : od + n ≤ hi) (hN : od + n ≤ N) (hs : os + n ≤ src.size) :
    Sat H (Ptr.memcpy (Ptr.ref (BRef.heap ob) od) (Ptr.ref rs os) n)
      (fun _ H' => ORun H0 H' ob N lo hi) := by
  obtain ⟨a, ha, haN⟩ := r.cur
  have hsrc' : Space.get H rs = some src := (r.get_ne hrs).trans hsrc
  refine ⟨(), _, ZlibNgF.Proof.InflateDict.memcpy_heap ha hsrc' hrs (by omega) hs,
    r.write ha (copyFold_size src od os (List.range' 0 n) a) (fun j hj =>
    copyFold_get src od os (List.range' 0 n) a j (fun i hi => mem_range'_bound hi (by omega)))⟩

end ZlibNgF.Proof.ChunkMem
