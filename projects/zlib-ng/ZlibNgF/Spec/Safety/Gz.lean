import ZlibNgF.Spec.Common.Gz

/-!
# Safety goals of the gz* file functions (`ZlibNgF`)

`gzlib.c`, `gzread.c`, `gzwrite.c`. Each goal says that for every world and heap a C program reaches (`GzWF`, which
quantifies over every allocation outcome, every OS-call result the oracles allow, every `strerror` text and every
`vsnprintf` result), every accepted file (`GzHandle`: `NULL` or reachable) and valid caller arguments, the call
does not fault (no undefined behaviour) and returns, and changes only what `GzFrame` names; `gzclose`,
`gzclose_r` and `gzclose_w` of a reachable file of their mode also release everything of it (`GzReleased`: no
leak, nothing left to dangle). That a call keeps the file reachable is part of `GzReachable`.
-/

set_option autoImplicit false

namespace ZlibNgF.Spec.Safety
open ZlibNgF.Spec C ZlibNg.Gz

/-! ## Opening -/

/-- `gzFile gzopen(const char *path, const char *mode)`: for `NULL` or string `path` and `mode`, does not fault, and
changes only fresh blocks, fresh `gz_state` objects, the heap's stream table (a fresh embedded stream) and the file
system. -/
def Goal.gzopen_safety : Prop :=
  ∀ (w : World) (h : Heap) (path mode : BPtr),
    GzWF w h → (path = .null ∨ CStr h path) → (mode = .null ∨ CStr h mode) →
    ∃ r w' h', GzRun (gzopen path mode) w h r w' h' ∧ GzFrame w h w' h' none [] ∧ GzWF w' h'

/-- `gzFile gzopen64(const char *path, const char *mode)`: as `gzopen`. -/
def Goal.gzopen64_safety : Prop :=
  ∀ (w : World) (h : Heap) (path mode : BPtr),
    GzWF w h → (path = .null ∨ CStr h path) → (mode = .null ∨ CStr h mode) →
    ∃ r w' h', GzRun (gzopen64 path mode) w h r w' h' ∧ GzFrame w h w' h' none [] ∧ GzWF w' h'

/-- `gzFile gzdopen(int fd, const char *mode)`: for every `fd` and a `NULL` or string `mode`, as `gzopen`. -/
def Goal.gzdopen_safety : Prop :=
  ∀ (w : World) (h : Heap) (fd : Int32) (mode : BPtr),
    GzWF w h → (mode = .null ∨ CStr h mode) →
    ∃ r w' h', GzRun (gzdopen fd mode) w h r w' h' ∧ GzFrame w h w' h' none [] ∧ GzWF w' h'

/-- Non-vacuity of `GzReachable` for reading: in some well-formed world whose file system holds a file `"f"`,
`gzopen("f", "rb")` returns a reachable file. -/
def Goal.gzopen_read_nonvacuous : Prop :=
  ∃ (w : World) (h : Heap) (path mode : BPtr) (w' : World) (h' : Heap) (f : GzPtr),
    GzWF w h ∧ CStringLen h path 1 ∧ CStringLen h mode 2 ∧
    GzRun (gzopen path mode) w h f w' h' ∧ f ≠ none ∧ GzReachable w' h' f ∧
    (∃ b s, f = some b ∧ w'.gz h' b = some s ∧ s.mode = GZ_READ)

/-- Non-vacuity of `GzReachable` for writing: `gzopen(path, "wb")` returns a reachable file in write mode. -/
def Goal.gzopen_write_nonvacuous : Prop :=
  ∃ (w : World) (h : Heap) (path mode : BPtr) (w' : World) (h' : Heap) (f : GzPtr),
    GzWF w h ∧ CStringLen h path 1 ∧ CStringLen h mode 2 ∧
    GzRun (gzopen path mode) w h f w' h' ∧ f ≠ none ∧ GzReachable w' h' f ∧
    (∃ b s, f = some b ∧ w'.gz h' b = some s ∧ s.mode = GZ_WRITE)

/-! ## Calls on an open file -/

/-- `int gzbuffer(gzFile file, unsigned size)`: for every `size`. Accepted file, no fault, frame. -/
def Goal.gzbuffer_safety : Prop :=
  ∀ (w : World) (h : Heap) (f : GzPtr) (size : UInt32),
    GzWF w h → GzHandle w h f →
    ∃ r w' h', GzRun (gzbuffer f size) w h r w' h' ∧ GzFrame w h w' h' f []

/-- `int gzsetparams(gzFile file, int level, int strategy)`: for every `level` and `strategy`. Accepted file, no fault, frame. -/
def Goal.gzsetparams_safety : Prop :=
  ∀ (w : World) (h : Heap) (f : GzPtr) (level strategy : Int32),
    GzWF w h → GzHandle w h f →
    ∃ r w' h', GzRun (gzsetparams f level strategy) w h r w' h' ∧ GzFrame w h w' h' f []

/-- `int gzgetc(gzFile file)` (the function; the macro is a caller step). Accepted file, no fault, frame. -/
def Goal.gzgetc_safety : Prop :=
  ∀ (w : World) (h : Heap) (f : GzPtr),
    GzWF w h → GzHandle w h f →
    ∃ r w' h', GzRun (gzgetc f) w h r w' h' ∧ GzFrame w h w' h' f []

/-- `int gzgetc_(gzFile file)`. Accepted file, no fault, frame. -/
def Goal.gzgetc__safety : Prop :=
  ∀ (w : World) (h : Heap) (f : GzPtr),
    GzWF w h → GzHandle w h f →
    ∃ r w' h', GzRun (gzgetc_ f) w h r w' h' ∧ GzFrame w h w' h' f []

/-- `int gzungetc(int c, gzFile file)`: for every `c`. Accepted file, no fault, frame. -/
def Goal.gzungetc_safety : Prop :=
  ∀ (w : World) (h : Heap) (f : GzPtr) (c : Int32),
    GzWF w h → GzHandle w h f →
    ∃ r w' h', GzRun (gzungetc c f) w h r w' h' ∧ GzFrame w h w' h' f []

/-- `int gzputc(gzFile file, int c)`: for every `c`. Accepted file, no fault, frame. -/
def Goal.gzputc_safety : Prop :=
  ∀ (w : World) (h : Heap) (f : GzPtr) (c : Int32),
    GzWF w h → GzHandle w h f →
    ∃ r w' h', GzRun (gzputc f c) w h r w' h' ∧ GzFrame w h w' h' f []

/-- `int gzflush(gzFile file, int flush)`: for every `flush`. Accepted file, no fault, frame. -/
def Goal.gzflush_safety : Prop :=
  ∀ (w : World) (h : Heap) (f : GzPtr) (flush : Int32),
    GzWF w h → GzHandle w h f →
    ∃ r w' h', GzRun (gzflush f flush) w h r w' h' ∧ GzFrame w h w' h' f []

/-- `z_off_t gzseek(gzFile file, z_off_t offset, int whence)`: for every `offset` and `whence`. Accepted file, no fault, frame. -/
def Goal.gzseek_safety : Prop :=
  ∀ (w : World) (h : Heap) (f : GzPtr) (offset : Int64) (whence : Int32),
    GzWF w h → GzHandle w h f →
    ∃ r w' h', GzRun (gzseek f offset whence) w h r w' h' ∧ GzFrame w h w' h' f []

/-- `z_off64_t gzseek64(gzFile file, z_off64_t offset, int whence)`: for every `offset` and `whence`. Accepted file, no fault, frame. -/
def Goal.gzseek64_safety : Prop :=
  ∀ (w : World) (h : Heap) (f : GzPtr) (offset : Int64) (whence : Int32),
    GzWF w h → GzHandle w h f →
    ∃ r w' h', GzRun (gzseek64 f offset whence) w h r w' h' ∧ GzFrame w h w' h' f []

/-- `int gzrewind(gzFile file)`. Accepted file, no fault, frame. -/
def Goal.gzrewind_safety : Prop :=
  ∀ (w : World) (h : Heap) (f : GzPtr),
    GzWF w h → GzHandle w h f →
    ∃ r w' h', GzRun (gzrewind f) w h r w' h' ∧ GzFrame w h w' h' f []

/-- `z_off_t gztell(gzFile file)`. Accepted file, no fault, frame. -/
def Goal.gztell_safety : Prop :=
  ∀ (w : World) (h : Heap) (f : GzPtr),
    GzWF w h → GzHandle w h f →
    ∃ r w' h', GzRun (gztell f) w h r w' h' ∧ GzFrame w h w' h' f []

/-- `z_off64_t gztell64(gzFile file)`. Accepted file, no fault, frame. -/
def Goal.gztell64_safety : Prop :=
  ∀ (w : World) (h : Heap) (f : GzPtr),
    GzWF w h → GzHandle w h f →
    ∃ r w' h', GzRun (gztell64 f) w h r w' h' ∧ GzFrame w h w' h' f []

/-- `z_off_t gzoffset(gzFile file)`. Accepted file, no fault, frame. -/
def Goal.gzoffset_safety : Prop :=
  ∀ (w : World) (h : Heap) (f : GzPtr),
    GzWF w h → GzHandle w h f →
    ∃ r w' h', GzRun (gzoffset f) w h r w' h' ∧ GzFrame w h w' h' f []

/-- `z_off64_t gzoffset64(gzFile file)`. Accepted file, no fault, frame. `GzWF` admits the `lseek` values POSIX allows
(`-1` or not negative): `offset - avail_in` cannot overflow on them (deviations page). -/
def Goal.gzoffset64_safety : Prop :=
  ∀ (w : World) (h : Heap) (f : GzPtr),
    GzWF w h → GzHandle w h f →
    ∃ r w' h', GzRun (gzoffset64 f) w h r w' h' ∧ GzFrame w h w' h' f []

/-- `int gzeof(gzFile file)`. Accepted file, no fault, frame. -/
def Goal.gzeof_safety : Prop :=
  ∀ (w : World) (h : Heap) (f : GzPtr),
    GzWF w h → GzHandle w h f →
    ∃ r w' h', GzRun (gzeof f) w h r w' h' ∧ GzFrame w h w' h' f []

/-- `int gzdirect(gzFile file)`. Accepted file, no fault, frame. -/
def Goal.gzdirect_safety : Prop :=
  ∀ (w : World) (h : Heap) (f : GzPtr),
    GzWF w h → GzHandle w h f →
    ∃ r w' h', GzRun (gzdirect f) w h r w' h' ∧ GzFrame w h w' h' f []

/-- `const char *gzerror(gzFile file, int *errnum)`: with `errnum` `NULL` or not (`hasErrnum`). Accepted file, no fault, frame. -/
def Goal.gzerror_safety : Prop :=
  ∀ (w : World) (h : Heap) (f : GzPtr) (hasErrnum : Bool),
    GzWF w h → GzHandle w h f →
    ∃ r w' h', GzRun (gzerror f hasErrnum) w h r w' h' ∧ GzFrame w h w' h' f []

/-- `void gzclearerr(gzFile file)`. Accepted file, no fault, frame. -/
def Goal.gzclearerr_safety : Prop :=
  ∀ (w : World) (h : Heap) (f : GzPtr),
    GzWF w h → GzHandle w h f →
    ∃ r w' h', GzRun (gzclearerr f) w h r w' h' ∧ GzFrame w h w' h' f []

/-- `int gzread(gzFile file, void *buf, unsigned len)`: `buf` has `len` writable bytes outside the file's blocks when `len` fits in an `int` (otherwise the call refuses before using it). Accepted file, no fault, frame. -/
def Goal.gzread_safety : Prop :=
  ∀ (w : World) (h : Heap) (f : GzPtr) (buf : BPtr) (len : UInt32),
    GzWF w h → GzHandle w h f → (len.toInt32 ≥ 0 → GzOut w h f buf len.toNat) →
    ∃ r w' h', GzRun (gzread f buf len) w h r w' h' ∧ GzFrame w h w' h' f [(buf, len.toNat)]

/-- `size_t gzfread(void *buf, size_t size, size_t nitems, gzFile file)`: `buf` has `size * nitems` writable bytes when the product does not overflow. Accepted file, no fault, frame. -/
def Goal.gzfread_safety : Prop :=
  ∀ (w : World) (h : Heap) (f : GzPtr) (buf : BPtr) (size nitems : UInt64),
    GzWF w h → GzHandle w h f → (size.toNat * nitems.toNat < 2 ^ 64 → GzOut w h f buf (size.toNat * nitems.toNat)) →
    ∃ r w' h', GzRun (gzfread buf size nitems f) w h r w' h' ∧ GzFrame w h w' h' f [(buf, size.toNat * nitems.toNat)]

/-- `char *gzgets(gzFile file, char *buf, int len)`: `buf` is `NULL` or has `len` writable bytes when `len >= 1`. Accepted file, no fault, frame. -/
def Goal.gzgets_safety : Prop :=
  ∀ (w : World) (h : Heap) (f : GzPtr) (buf : BPtr) (len : Int32),
    GzWF w h → GzHandle w h f → (len ≥ 1 → buf = .null ∨ GzOut w h f buf len.toNatClampNeg) →
    ∃ r w' h', GzRun (gzgets f buf len) w h r w' h' ∧ GzFrame w h w' h' f [(buf, len.toNatClampNeg)]

/-- `int gzwrite(gzFile file, voidpc buf, unsigned len)`: `buf` has `len` readable bytes outside the file's blocks when `len` fits in an `int`. Accepted file, no fault, frame. -/
def Goal.gzwrite_safety : Prop :=
  ∀ (w : World) (h : Heap) (f : GzPtr) (buf : BPtr) (len : UInt32),
    GzWF w h → GzHandle w h f → (len.toInt32 ≥ 0 → GzIn w h f buf len.toNat) →
    ∃ r w' h', GzRun (gzwrite f buf len) w h r w' h' ∧ GzFrame w h w' h' f []

/-- `size_t gzfwrite(voidpc buf, size_t size, size_t nitems, gzFile file)`: `buf` has `size * nitems` readable bytes when the product does not overflow. Accepted file, no fault, frame. -/
def Goal.gzfwrite_safety : Prop :=
  ∀ (w : World) (h : Heap) (f : GzPtr) (buf : BPtr) (size nitems : UInt64),
    GzWF w h → GzHandle w h f → (size.toNat * nitems.toNat < 2 ^ 64 → GzIn w h f buf (size.toNat * nitems.toNat)) →
    ∃ r w' h', GzRun (gzfwrite buf size nitems f) w h r w' h' ∧ GzFrame w h w' h' f []

/-- `int gzputs(gzFile file, const char *s)`: `s` is a string outside the file's blocks. Accepted file, no fault, frame. -/
def Goal.gzputs_safety : Prop :=
  ∀ (w : World) (h : Heap) (f : GzPtr) (s : BPtr),
    GzWF w h → GzHandle w h f → CStr h s → OutsideGz w h f s →
    ∃ r w' h', GzRun (gzputs f s) w h r w' h' ∧ GzFrame w h w' h' f []

/-- `int gzprintf(gzFile file, const char *format, ...)`: `format` is a string; the arguments match it (the `vsnprintf` oracle). Accepted file, no fault, frame. -/
def Goal.gzprintf_safety : Prop :=
  ∀ (w : World) (h : Heap) (f : GzPtr) (format : BPtr),
    GzWF w h → GzHandle w h f → CStr h format →
    ∃ r w' h', GzRun (gzprintf f format) w h r w' h' ∧ GzFrame w h w' h' f []

/-- `int gzvprintf(gzFile file, const char *format, va_list va)`: as `gzprintf`. Accepted file, no fault, frame. -/
def Goal.gzvprintf_safety : Prop :=
  ∀ (w : World) (h : Heap) (f : GzPtr) (format : BPtr),
    GzWF w h → GzHandle w h f → CStr h format →
    ∃ r w' h', GzRun (gzvprintf f format) w h r w' h' ∧ GzFrame w h w' h' f []

/-! ## Closing -/

/-- `int gzclose(gzFile file)`: does not fault on an accepted file, and on a reachable file frees every block
of it, ends its `gz_state` and embedded `z_stream` and closes its descriptor. -/
def Goal.gzclose_safety : Prop :=
  ∀ (w : World) (h : Heap) (f : GzPtr),
    GzWF w h → GzHandle w h f →
    ∃ r w' h', GzRun (gzclose f) w h r w' h' ∧ GzFrame w h w' h' f [] ∧ GzReleased w h w' h' f

/-- `int gzclose_r(gzFile file)`: does not fault on an accepted file, and on a reachable file of mode `GZ_READ` frees every block
of it, ends its `gz_state` and embedded `z_stream` and closes its descriptor. -/
def Goal.gzclose_r_safety : Prop :=
  ∀ (w : World) (h : Heap) (f : GzPtr),
    GzWF w h → GzHandle w h f →
    ∃ r w' h', GzRun (gzclose_r f) w h r w' h' ∧ GzFrame w h w' h' f [] ∧ ((∃ b s, f = some b ∧ w.gz h b = some s ∧ s.mode = GZ_READ) → GzReleased w h w' h' f)

/-- `int gzclose_w(gzFile file)`: does not fault on an accepted file, and on a reachable file of mode `GZ_WRITE` frees every block
of it, ends its `gz_state` and embedded `z_stream` and closes its descriptor. -/
def Goal.gzclose_w_safety : Prop :=
  ∀ (w : World) (h : Heap) (f : GzPtr),
    GzWF w h → GzHandle w h f →
    ∃ r w' h', GzRun (gzclose_w f) w h r w' h' ∧ GzFrame w h w' h' f [] ∧ ((∃ b s, f = some b ∧ w.gz h b = some s ∧ s.mode = GZ_WRITE) → GzReleased w h w' h' f)

end ZlibNgF.Spec.Safety
