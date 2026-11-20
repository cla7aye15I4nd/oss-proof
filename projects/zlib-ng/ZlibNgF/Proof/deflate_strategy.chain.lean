import ZlibNgF.Proof.«deflate_strategy.common»
import ZlibNgF.Proof.«deflate.c.side»

/-!
# The hash chains across `FLUSH_BLOCK` (`ZlibNgF`)

`FLUSH_BLOCK` changes the bytes of the state's block only inside `pending_buf` (`FBPost.pbuf`: `zng_tr_flush_block`
writes the block there, `flush_pending` the bits of `bi_buf`), which lies after `head` and `prev`, and keeps
`level`, `strategy`, `head`, `prev`, `strstart`, `lookahead` and `w_size` (`FBKeeps`). So `ChainOk` of the state
before gives `ChainOk` after (`ChainKeep`).

* `flush_chain`: from the preconditions of `FlushBlock.flush_block_ok`;
* `slf_flush_chain`: from the preconditions of `Strategy.slf_flush` (`SLF`, no pending bytes, the window).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.StrategyChain
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateFacts ZlibNgF.Proof.Strategy
open ZlibNgF.Proof.InflateSync (Sat)
open ZlibNgF.Proof.FlushBlock (flush_block_ok)
open ZlibNg.DeflateP

/-- `ChainOk` of the state and the bytes of block `b` in `H` carries to the state and bytes of block `b` in `H2`. -/
def ChainKeep (b : Nat) (H H2 : Heap) : Prop :=
  ∀ st d st2 d2, H.dstate b = some st → H.bytes b = some d → H2.dstate b = some st2 → H2.bytes b = some d2 →
    ChainOk b d st → ChainOk b d2 st2

/-- **The hash chains survive `FLUSH_BLOCK(s, window, last)`**, from the preconditions of `flush_block_ok`. -/
theorem flush_chain (T : TreesFacts) {h : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {wo : Nat}
    (last : Int32) (hl0 : 0 ≤ last) (hl1 : last ≤ 1) (hv : DInv h (some i)) (hio : DStreamIO h (some i))
    (hset : DBufsSet h (some i)) (hz : h.streams i = some z) (hb : z.state = some b) (hst : h.dstate b = some st)
    (hp0 : st.pending = 0) (hlv : 0 < st.level) (h8 : st.bi_valid < 8)
    (hwin : st.window = .val (.ref (.heap b) wo)) :
    Sat h (FLUSH_BLOCK (some b) (.ref (.heap b) wo) last) (fun _ h' => ChainKeep b h h') := by
  obtain ⟨r, h', e, P, -⟩ := flush_block_ok T last hl0 hl1 hv hio hset hz hb hst hp0 hlv h8 hwin
  refine ⟨r, h', e, fun st0 d st2 d2 h0 hd h2 hd2 C => ?_⟩
  obtain rfl := Option.some.inj (hst.symm.trans h0)
  obtain ⟨z', st', L, -, hst', -, -, -, -, -, -, st1, hK1, hst'e⟩ := P.out
  obtain rfl := Option.some.inj (hst'.symm.trans h2)
  have hk : st'.level = st.level ∧ st'.strategy = st.strategy ∧ st'.head = st.head ∧ st'.prev = st.prev ∧
      st'.strstart = st.strstart ∧ st'.lookahead = st.lookahead ∧ st'.w_size = st.w_size := by
    rw [hst'e, hK1]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := hk
  obtain ⟨i', z0, b0, st0', al, e0, hz0, hb0, hst0, -, c⟩ := hv
  obtain rfl : i = i' := Option.some.inj e0
  obtain rfl : z = z0 := Option.some.inj (hz.symm.trans hz0)
  obtain rfl : b = b0 := Option.some.inj (hb.symm.trans hb0)
  obtain rfl : st = st0' := Option.some.inj (hst.symm.trans hst0)
  obtain ⟨d1, -, po, ho, pbo, hd1, -, hp, hh, hpb, -, h2', h3, -⟩ := c.lay
  obtain rfl : d = d1 := Option.some.inj (hd.symm.trans hd1)
  obtain ⟨w1, -⟩ := c.sizes
  simp only [dview] at hp hh hpb h2' h3 w1
  obtain ⟨da, db, ha, hdb, -, q⟩ := P.pbuf pbo hpb
  obtain rfl : da = d := Option.some.inj (ha.symm.trans hd)
  obtain rfl : db = d2 := Option.some.inj (hdb.symm.trans hd2)
  have C2 : ChainOk b db st := DeflateSide.ChainOk.of_bytes C (by omega) fun ho' po' hh' hp' => by
    rw [hh] at hh'; rw [hp] at hp'
    obtain rfl : ho = ho' := by injection hh' with e; injection e
    obtain rfl : po = po' := by injection hp' with e; injection e
    exact ⟨fun j _ hj => q j (Or.inl (by omega)), fun j _ hj => q j (Or.inl (by omega))⟩
  exact DeflateSide.ChainOk.of_state C2 k1 k2 k3 k4 k5 k6 k7

/-- **The hash chains survive `FLUSH_BLOCK(s, window, last)`** inside a strategy loop, from the preconditions of
`slf_flush` (`SLF`, no pending bytes, the window at offset `wo`). -/
theorem slf_flush_chain (T : TreesFacts) {h H : Heap} {i b wo : Nat} (last : Int32) (hl0 : 0 ≤ last)
    (hl1 : last ≤ 1) (F : SLF h i b H)
    (hp : ∀ st, H.dstate b = some st → st.pending = 0 ∧ st.window = .val (.ref (.heap b) wo)) :
    Sat H (FLUSH_BLOCK (some b) (.ref (.heap b) wo) last) (fun _ H2 => ChainKeep b H H2) := by
  obtain ⟨z, st, al, hz, hb, hst, -, -⟩ := F.live
  obtain ⟨hp0, hwin⟩ := hp st hst
  obtain ⟨hlv, -, -, h8⟩ := F.st st hst
  exact flush_chain T last hl0 hl1 F.inv F.io F.set hz hb hst hp0 hlv h8 hwin

end ZlibNgF.Proof.StrategyChain
