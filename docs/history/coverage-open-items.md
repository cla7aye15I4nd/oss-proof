# No-fault coverage: earlier open items (historical)

This page keeps the numbered list "Miscounts and open items" of the section "No-fault coverage of zlib.h functions" of [progress](../progress.md), as it stood
after the required goals were accepted on `bde170e9`. The text is unchanged apart from relative links. It is a historical
record: states such as "open" and "checked", hours, counts and dates describe the time each
entry was written. They are not current status. Current status and remaining work are only in
[progress](../progress.md).

#### Miscounts and open items

Documented functions with no checked no-fault theorem for their full documented domain:

1. **inflateBack**: registered (`inflate_back_sequence_safety`). The domain narrows as the deviation rows say: `inputBound < 2^48`, the window and every input chunk in a heap byte block.
2. **deflateCopy**: registered. `source ≠ dest` is assumed (deviation row).
3. **inflateEnd**: closed. NULL, state NULL, after `End`, after a failed init and the destination of a failed copy are covered by `Goal.inflate_refusal` (checked).
4. **inflateCopy**: closed. An inconsistent source is covered by `Goal.inflate_refusal` (checked).
5. **NULL or inconsistent stream refusal**: closed. `Goal.inflate_refusal` and `Goal.deflate_refusal` (checked) cover `inflate`, `deflate`, `inflateEnd`, `inflateReset`, `inflateReset2`, `inflateGetDictionary`, `inflateSetDictionary`, `inflateCopy`, `deflateSetDictionary`, `deflateParams`, `deflateGetDictionary` and `deflateCopy`. These goals and `deflateGetDictionary_reject` are registered.
6. **deflateParams, deflateSetDictionary, deflatePrime, deflateBound, deflateBound_z, inflateSync**: their per-function safety goals (`Goal.*_safety`) are registered (dd73d9d2). Their functional own goals have no theorem and are not planned.
7. **adler32, adler32_z**: domain narrower than zlib.h (NULL only with `len = 0`). `len = 1` is a real C fault (deviation row). NULL with `len ≥ 2` is safe but unproved.
8. **gz functions**: `Goal.gz_sequence_safety` is registered (`gz_sequence_safety_public`, no premise), with its non-vacuity goal. The `gzgetc` macro path (audit A1) and a second handle on one fd (audit B1) are in the goal. `NULL` handles are covered by `Goal.gz_refusal`.
9. Related, not a function: `Goal.deflate_initialisation_domain` (nonvacuity) is registered (`deflate_initialisation_domain_public`, 06cbfd06; registered in dd73d9d2). `Goal.gz_initialisation_domain` is not required (see [Scope](../progress.md#scope)).
