import ZlibF.Proof.«inflate.c.meaning-call»
import ZlibF.Proof.«inflate.c.meaning-call-exit»
import ZlibF.Proof.«inflate.c.completes-keep-run»
import ZlibF.Proof.«inflate.c.config-source-observer»

/-!
# inflate.c: one `inflate` call of a history with more than one raw dictionary (`CallUnstaged`)

A history has `singleDictionary = false` only after a raw dictionary replaced during a data epoch.
Every stage clause of `ParseMeaning` is guarded by `singleDictionary = true`, and a call keeps
`singleDictionary`. So `ParseMeaning` after the call needs only facts of the actual call:

* the invariant after the call and the modes of the return codes (`callExit_after`, from the
  safety proof of the same deterministic run);
* `ConfigMatches` after the call: `wrap`, `reqwrap` and `reqbits` are kept by every call
  (`ConfigObserver.inflate_config_unchanged`); the header pointer is kept and `SYNC` is not
  entered (`call_inflate`); `wbits` follows from `reqbits` and the invariant after the call
  (`InflateConfig.reqbits`).
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public Zlib.Inflate.KeepProofs
set_option autoImplicit false

/-- `CallUnstaged`: one call of a history with more than one raw dictionary keeps
`ParseMeaning`. -/
theorem call_unstaged : CallUnstaged := by
  intro wb r h after log pending flush rc input output used meaning single fit step
  obtain ⟨wrap, configured, i, z, s, wbits, inv, config, _, _, _, _, _⟩ := meaning
  obtain ⟨z0, z', get, get', buffers, active, _, _, _, run⟩ := step
  have zEq : z0 = z := Option.some.inj (get.symm.trans inv.good.live.hz)
  subst zEq
  obtain ⟨zF, sF, _, _, invF, _, modes⟩ := callExit_after inv fit buffers active run
  obtain ⟨wrapEq, reqwrapEq, reqbitsEq⟩ :=
    ConfigObserver.inflate_config_unchanged run inv.good.live.hs invF.good.live.hs
  have k := call_inflate (some r) flush h rc after run
  obtain ⟨s0, g0, ctl⟩ := k.states i sF invF.good.live.hs
  rw [inv.good.live.hs] at g0
  cases g0
  obtain ⟨cWrap, cReqwrap, cHead, cReqbits, cWbits, cSync⟩ := config
  have config' : ConfigMatches sF wrap configured := by
    refine ⟨wrapEq.trans cWrap, reqwrapEq.trans (cReqwrap.trans wrapEq.symm),
      ctl.head.trans cHead, by rw [reqbitsEq]; exact cReqbits, ?_, ctl.sync cSync⟩
    intro nonzero
    rcases invF.config.reqbits with same | ⟨zero, _⟩
    · rw [← same, reqbitsEq]
      exact cReqbits
    · exfalso
      apply nonzero
      have toNat := congrArg UInt32.toNat zero
      rw [← cReqbits, ← reqbitsEq]
      exact toNat.trans rfl
  refine ⟨wrap, configured, i, zF, sF, wbits, invF, config', fun e => Or.inl (modes.2.2.1 e),
    fun e => Or.inl (modes.1 e), ?_, ?_, ?_⟩
  · intro e
    have e' : log.singleDictionary = true := e
    rw [single] at e'
    cases e'
  · intro e
    have e' : log.singleDictionary = true := e
    rw [single] at e'
    cases e'
  · intro e
    have e' : log.singleDictionary = true := e
    rw [single] at e'
    cases e'

#print axioms call_unstaged

end Zlib.Inflate.Proofs
