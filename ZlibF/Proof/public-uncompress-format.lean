import ZlibF.Proof.«inflate.c.completes-meaning»
import ZlibF.Proof.«inflate.c.meaning-held-within»
import ZlibF.Spec.Functional.Streams
import ZlibF.Proof.«inflate.c.meaning-accept»
import ZlibF.Proof.«inflate.c.meaning-init»
import ZlibF.Proof.Format.Huffman
import ZlibF.Proof.Format.Api
import ZlibF.Proof.Api.InflateCausality
import ZlibF.Proof.«inflate.c.completes-stops»
import ZlibF.Proof.«inflate.c.completes-blocked»
import ZlibF.Proof.«inflate.c.completes-gzip-fields»
import ZlibF.Proof.Api.Examples
import ZlibF.Spec.Functional.Sequences
import ZlibF.Spec.Functional.Utilities

/-!
# uncompr.c: the data relation from the last decoder call

After the call loop of `uncompress2_z`, the actual history of its local stream
is a protocol history with window bits 15 and no dictionary. From the decoder
facts and the last call, the returned code, the output and the consumed source
satisfy `Api.Uncompress2`.
-/

namespace ZlibF.Spec.Public.Proofs.Uncompress
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Inflate.Proofs
set_option autoImplicit false

/-- The return code of `uncompress2_z` from the last `inflate` result and the
unused source length (`len` after the loop). -/
def finalCode (err : Int32) (rest : UInt64) : Int32 :=
  if err == Z_STREAM_END then Z_OK
  else if err == Z_NEED_DICT then Z_DATA_ERROR
  else if err == Z_BUF_ERROR && rest == 0 then Z_DATA_ERROR
  else err

theorem inflWbits_15 : Api.inflWbits (15 : Int32).toInt = some (.zlib, 15) := by decide

theorem zlib_fits_15 {s o : List UInt8} (d : Zlib.Decodes [] s o) : Api.ZlibFits 15 s := by
  obtain ⟨cmf, flg, pre, rest, rfl, ⟨-, cinfo, -⟩, -, -⟩ := d
  exact Or.inr ⟨cmf, rfl, by omega⟩

theorem zlib_layer {s o : List UInt8} (d : Zlib.Decodes [] s o) : Api.Layer.Decodes .zlib 15 [] s o :=
  ⟨d, zlib_fits_15 d⟩

theorem zlib_full {s : List UInt8} : Api.FullWindow .zlib 15 s := Or.inl rfl

theorem zlib_decodes_long {d s o : List UInt8} (h : Zlib.Decodes d s o) : 2 ≤ s.length := by
  obtain ⟨cmf, flg, pre, rest, rfl, -⟩ := h
  simp

theorem accepted_zlib {s o : List UInt8} (h : Api.Layer.InflateAccepted .zlib 15 [] s o) :
    Zlib.Decodes [] s o := by
  obtain ⟨⟨cmf, flg, pre, rest, e, hdr, h0, h1⟩, -⟩ := h
  exact ⟨cmf, flg, pre, rest, e, hdr, h0, fun f => by simpa using h1 f⟩

/-- The log after one observed call, as in `InflateProtocolTrace.step`. -/
def stepLog (log : DataLog) (rc : Int32) (input output : List UInt8) (used : Nat) : DataLog :=
  { log with
    input := log.input ++ input.take used, output := log.output ++ output
    result := rc, finished := log.finished || rc == Z_STREAM_END }

/-- The empty output with nothing consumed: initialization failed. -/
theorem uncompressed_mem_init (src : List UInt8) (cap : Nat) : Uncompressed src cap Z_MEM_ERROR [] 0 := by
  unfold Uncompressed Api.Uncompress2
  rw [ite_eq_right (by decide)]
  refine ⟨Nat.zero_le _, Nat.zero_le _, Or.inr (Or.inr (Or.inr (by decide))), fun h => absurd h (by decide),
    fun h => absurd h (by decide), fun _ _ _ _ => List.nil_prefix, ?_, ?_⟩
  · refine ⟨[], List.nil_prefix, ⟨[], Api.zA, [0x61], rfl, Or.inl List.nil_prefix, Api.zA_layer⟩, ?_⟩
    intro _ _ _ _ _ _
    exact List.nil_prefix
  · intro m o _ _
    exact ⟨List.nil_prefix, fun _ => ⟨fun _ => Or.inr (by decide), fun _ => Or.inr (by decide)⟩⟩

end ZlibF.Spec.Public.Proofs.Uncompress
