import ZlibF.Zlib.gzfs

/-!
# printf format regression

The model's printf (`formatGo`) formats the library's own fixed-format `snprintf` calls (`gz_error`'s `"%s%s%s"`,
`gz_open`'s `"%s"`, `gzdopen`'s `"<fd:%d>"`), where zlib is the caller and its calls must be shown defined. It used to
format conversion specifications that C17 7.21.6.1 leaves undefined (it then also served the caller's format of
`gzprintf`). Each format below was accepted with an ordinary output and is now rejected, so the model faults if it is
reached. A wide conversion (`%lc`, `%ls`) is not modelled and is rejected as well. The string argument is a
resolvable `char *` and the integer arguments are of the kind the conversion asks for, so each rejection comes from
the specification alone, except where the argument is the point (a `NULL` `%s`, a negative value for `%u`). The
second half shows the other direction: valid formats still give the output glibc gives.

Nothing compiles this directory automatically. Check it after a build of the library with
`lake env lean tests/verification/regressions/printf-format-undefined.lean`.
-/
namespace ZlibF.Regression.PrintfFormat
open Zlib.GzFs C

private def S : BPtr := .ref (.blk 7) 0
private def res (p : BPtr) : Option (Array UInt8) := if p == S then some #[97, 98] else none
private def bytes (s : String) : Array UInt8 := (s.toList.map (·.toNat.toUInt8)).toArray

/-- The model rejects `f` with arguments `a`. -/
def rejects (f : String) (a : List VaArg) : Bool :=
  match formatGo (bytes f) res ((bytes f).size + 1) 0 a #[] with
  | .error _ => true
  | .ok _ => false

-- a length modifier on s or c (p7), or a wide conversion
theorem ls : rejects "%ls" [.str S] = true := by decide +kernel
theorem lls : rejects "%lls" [.str S] = true := by decide +kernel
theorem zs : rejects "%zs" [.str S] = true := by decide +kernel
theorem js : rejects "%js" [.str S] = true := by decide +kernel
theorem ts : rejects "%ts" [.str S] = true := by decide +kernel
theorem lc : rejects "%lc" [.int 65] = true := by decide +kernel
theorem llc : rejects "%llc" [.int 65] = true := by decide +kernel
theorem zc : rejects "%zc" [.int 65] = true := by decide +kernel
-- no length modifier `zl`, `jl`, `tl`: the conversion character would be `l` (p9)
theorem zld : rejects "%zld" [.long 5] = true := by decide +kernel
theorem jld : rejects "%jld" [.long 5] = true := by decide +kernel
theorem tld : rejects "%tld" [.long 5] = true := by decide +kernel
-- `%%` is the whole specification (p8)
theorem pct_minus : rejects "%-5%" [] = true := by decide +kernel
theorem pct_zero : rejects "%05%" [] = true := by decide +kernel
theorem pct_prec : rejects "%.3%" [] = true := by decide +kernel
-- the `0` flag on s and c, the `#` flag on d, i, u, c and s (p6), a precision on c (p4)
theorem zero_s : rejects "%05s" [.str S] = true := by decide +kernel
theorem zero_c : rejects "%0c" [.int 65] = true := by decide +kernel
theorem alt_d : rejects "%#d" [.int 5] = true := by decide +kernel
theorem alt_i : rejects "%#i" [.int 5] = true := by decide +kernel
theorem alt_u : rejects "%#u" [.uint 5] = true := by decide +kernel
theorem alt_s : rejects "%#s" [.str S] = true := by decide +kernel
theorem alt_c : rejects "%#c" [.int 65] = true := by decide +kernel
theorem prec_c : rejects "%.3c" [.int 65] = true := by decide +kernel
-- a NULL `%s` argument (p8), a negative signed argument for an unsigned conversion (p9)
theorem null_s : rejects "%s" [.str .null] = true := by decide +kernel
theorem neg_u : rejects "%u" [.int (-1)] = true := by decide +kernel
theorem neg_x : rejects "%x" [.int (-1)] = true := by decide +kernel
theorem neg_lu : rejects "%lu" [.long (-1)] = true := by decide +kernel

/-- The model's output for `f` with arguments `a` is the text `s`. -/
def outputs (f : String) (a : List VaArg) (s : String) : Bool :=
  match formatGo (bytes f) res ((bytes f).size + 1) 0 a #[] with
  | .error _ => false
  | .ok o => o.toList == (bytes s).toList

-- valid specifications keep the output glibc gives
theorem ok_s : outputs "%s|%5s|%-4.1s|" [.str S, .str S, .str S] "ab|   ab|a   |" = true := by decide +kernel
theorem ok_d : outputs "[%5d|%-5d|%05d|%+d|% d]" [.int 7, .int 7, .int (-7), .int 5, .int 5]
    "[    7|7    |-0007|+5| 5]" = true := by decide +kernel
theorem ok_u : outputs "%u %x %X %o %#x %#o" [.uint 255, .uint 255, .uint 255, .uint 8, .uint 255, .uint 8]
    "255 ff FF 10 0xff 010" = true := by decide +kernel
theorem ok_nonneg_int : outputs "%u %x" [.int 255, .int 255] "255 ff" = true := by decide +kernel
theorem ok_long : outputs "%ld %lld %zd %jd %td %lu %zu %lx" [.long (-5), .long 6, .long 7, .long 8, .long 9,
    .ulong 10, .ulong 11, .ulong 255] "-5 6 7 8 9 10 11 ff" = true := by decide +kernel
theorem ok_c : outputs "%c%-3c|" [.int 65, .int 66] "AB  |" = true := by decide +kernel
theorem ok_prec : outputs "%.0d|%.5d|%.3x" [.int 0, .int 42, .uint 10] "|00042|00a" = true := by decide +kernel
theorem ok_pct : outputs "100%%" [] "100%" = true := by decide +kernel

end ZlibF.Regression.PrintfFormat
