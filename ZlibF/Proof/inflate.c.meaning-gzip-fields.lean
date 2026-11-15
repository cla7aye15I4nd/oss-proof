import ZlibF.Proof.«inflate.c.meaning-gzip-fields-flags»
import ZlibF.Proof.«inflate.c.meaning-trip-modes»

/-!
# inflate.c: the gzip header field modes keep the format meaning (`TripGzipFields`)

One dispatch from `FLAGS` .. `HCRC` runs the C from `case m:` and falls through the later field
modes. It ends at a short leave (`NEEDBITS` without input, or inside the extra field, the name or
the comment) with the loop meaning at the longer header position, at a rejection (`BAD`: method,
reserved flags, header CRC) with the input read so far doomed, or at the end of `HCRC` with the
body at its first block boundary. The per-mode steps are in `inflate.c.meaning-gzip-fields-*`;
each calls the step of the mode it falls into.

In a zlib or raw configuration the modes do not occur (`gzip_fields_absent`). In a gzip or
automatic configuration the call's facts give the state (`CallSide`): no header record, the
CRC-32 tables, the local `hbuf`, and `hbuf` apart from the unread input (`HbufInputApart`).
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs.MeaningGzipFields
set_option autoImplicit false

/-- The gzip header field modes `FLAGS` .. `HCRC`, in every configuration. -/
theorem trip_gzip_fields : TripGzipFields := by
  intro c f r h l side loop range
  have side0 := side
  obtain ⟨zs, z, s, strm, st, inv, _, loc, _, apart⟩ := side
  have E : Env c h r zs z s := ⟨strm, st, inv.good.live.hz, inv.good.live.hs⟩
  have rng : FLAGS ≤ s.mode ∧ s.mode ≤ HCRC := range zs s st E.hs
  have plainOr : (f.wrap = .zlib ∨ f.wrap = .raw) ∨ (f.wrap = .gzip ∨ f.wrap = .auto) := by
    cases f.wrap <;> simp
  rcases plainOr with plain | gz
  · exact absurd rng (gzip_fields_absent c f r h l side0 loop plain zs s st E.hs)
  obtain ⟨bytes, rest, g⟩ := GzAt.of_loop loop st E.hs rng gz
  have statics : Zlib.Crc32.Proofs.StaticsOK h := LibraryGlobals.statics inv.globals
  have local_ := loc (UInt32.le_trans (by decide) rng.1) rng.2
  obtain ⟨b, a, hbAt, hbytes, hsize, hro⟩ := local_.hbuf
  have hb : Hbuf c h b a := ⟨hbAt, hbytes, hsize, hro⟩
  rcases gzip_header_mode_cases rng with m | m | m | m | m | m | m | m
  · obtain ⟨res, l', h', run, out⟩ := flags_step E g m statics hb apart
    exact ⟨res, l', h', (inflate_dispatch_FLAGS E l m).trans run, Or.inl out⟩
  · obtain ⟨res, l', h', run, out⟩ := time_step E g m statics hb apart
    exact ⟨res, l', h', (inflate_dispatch_TIME E l m).trans run, Or.inl out⟩
  · obtain ⟨res, l', h', run, out⟩ := os_step E g m statics hb apart
    exact ⟨res, l', h', (inflate_dispatch_OS E l m).trans run, Or.inl out⟩
  · obtain ⟨res, l', h', run, out⟩ := exlen_step E g m statics hb apart
    exact ⟨res, l', h', (inflate_dispatch_EXLEN E l m).trans run, Or.inl out⟩
  · obtain ⟨res, l', h', run, out⟩ := extra_step E g m statics
    exact ⟨res, l', h', (inflate_dispatch_EXTRA E l m).trans run, Or.inl out⟩
  · obtain ⟨res, l', h', run, out⟩ := name_step E g m statics
    exact ⟨res, l', h', (inflate_dispatch_NAME E l m).trans run, Or.inl out⟩
  · obtain ⟨res, l', h', run, out⟩ := comment_step E g m statics
    exact ⟨res, l', h', (inflate_dispatch_COMMENT E l m).trans run, Or.inl out⟩
  · obtain ⟨res, l', h', run, out⟩ := hcrc_step E g m
    exact ⟨res, l', h', (inflate_dispatch_HCRC E l m).trans run, Or.inl out⟩

#print axioms trip_gzip_fields

end Zlib.Inflate.Proofs
