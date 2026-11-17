import ZlibF.Spec.Common.Sequences

open C ZlibF.Spec.Public

/-! The write region of `inflateGetDictionary` and `deflateGetDictionary` was `⟨p, 32768⟩` for
both calls, while the arguments ask the destination to be writable only for the dictionary length
(inflate: `whave`; deflate: `min(w_size, strstart + lookahead)`). The frame then admitted a change
of up to 32768 bytes at `p`, beyond the caller's buffer, which the C never makes
(`getdictionary-frame.c`: the bytes after a buffer of exactly the dictionary length stay
unchanged). The region is now the dictionary's bytes, and nothing for `NULL`. This regression
fails if the region is widened again: the byte right after the dictionary is not covered. -/
namespace GetDictionaryFrameRegression

theorem inflate_region {h : Heap} {r : ZStreamRef} {z : ZStream} {i : Nat}
    {s : InflateState} (ref : BRef) (off : Nat) (dl : Option UInt32)
    (hz : r.get h = some z) (zst : z.state = some (.inflate i)) (hs : h.istates i = some s) :
    StreamWriteRegions h r (.inflateGetDictionary (some r) (.ref ref off) dl) =
      [⟨.ref ref off, s.whave.toNat⟩] := by
  simp only [StreamWriteRegions, InflateDictionaryLength, hz, zst, hs]

theorem deflate_region {h : Heap} {r : ZStreamRef} {z : ZStream} {i : Nat}
    {d : DeflateState} (ref : BRef) (off : Nat) (hasDictLength : Bool)
    (hz : r.get h = some z) (zst : z.state = some (.deflate i)) (hs : h.dstates i = some d) :
    StreamWriteRegions h r (.deflateGetDictionary (some r) (.ref ref off) hasDictLength) =
      [⟨.ref ref off, min d.w_size.toNat (d.strstart.toNat + d.lookahead.toNat)⟩] := by
  simp only [StreamWriteRegions, DeflateDictionaryLength, hz, zst, hs]

theorem inflate_null (h : Heap) (r : ZStreamRef) (dl : Option UInt32) :
    StreamWriteRegions h r (.inflateGetDictionary (some r) .null dl) = [] := rfl

theorem deflate_null (h : Heap) (r : ZStreamRef) (hasDictLength : Bool) :
    StreamWriteRegions h r (.deflateGetDictionary (some r) .null hasDictLength) = [] := rfl

/-- The byte after the inflate dictionary is outside the region. -/
theorem inflate_after_not_covered {h : Heap} {r : ZStreamRef} {z : ZStream} {i : Nat}
    {s : InflateState} (ref : BRef) (off : Nat) (dl : Option UInt32)
    (hz : r.get h = some z) (zst : z.state = some (.inflate i)) (hs : h.istates i = some s) :
    ¬ ∃ region, region ∈ StreamWriteRegions h r (.inflateGetDictionary (some r) (.ref ref off) dl) ∧
      region.covers ref (off + s.whave.toNat) := by
  rw [inflate_region ref off dl hz zst hs]
  rintro ⟨region, member, off', pointer, _, past⟩
  simp only [List.mem_singleton] at member
  subst member
  cases pointer
  omega

/-- The byte after the deflate dictionary is outside the region. -/
theorem deflate_after_not_covered {h : Heap} {r : ZStreamRef} {z : ZStream} {i : Nat}
    {d : DeflateState} (ref : BRef) (off : Nat) (hasDictLength : Bool)
    (hz : r.get h = some z) (zst : z.state = some (.deflate i)) (hs : h.dstates i = some d) :
    ¬ ∃ region, region ∈
        StreamWriteRegions h r (.deflateGetDictionary (some r) (.ref ref off) hasDictLength) ∧
      region.covers ref (off + min d.w_size.toNat (d.strstart.toNat + d.lookahead.toNat)) := by
  rw [deflate_region ref off hasDictLength hz zst hs]
  rintro ⟨region, member, off', pointer, _, past⟩
  simp only [List.mem_singleton] at member
  subst member
  cases pointer
  omega

end GetDictionaryFrameRegression
