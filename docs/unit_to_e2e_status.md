# Unit → E2E Promotion Status (Jul 14, 2026)

Sweep methodology: every `test/unit/*.sis` compiled to C
(`main.exe --c=...`), **run from inside `test/unit/`** so `%$include`
resolves (include paths are relative to the compiler's cwd).  A test is
"covered" when `test/e2e/` already holds it or its `_dv`/`_e2e`
derivative.  Suite baseline at sweep time: e2e 173/173, cram 19
intentional lines.

**Totals: 313 unit tests; 171 emit C; 123 emitters have no e2e
counterpart.**

## Bucket A — promotable now (emit C; need array→array_dv rewrite + reference driver)

Standing rules for every port: all arrays become `array_dv` (flat
dope-vector; rank-2 for matrices, rows via `A[i, ..]`, row replace via
`A[i: row]`); expected values come from a reference C implementation or
ground truth by construction, never snapshots; 5 registration points
(dv_run_all.cpp extern/testfn/dispatch/no-macro-guard, run_dv_e2e.sh
run_group, positive.t); underscore-only stems; delete stale .cpp before
every compile; never swallow compiler stderr in test loops.

If a port turns out NON-mechanical — array-of-arrays structure that does
not flatten naturally, or masked stores (`when`/`unless` on scatter
returns) — STOP and discuss the rewrite instead of forcing it.

- **Sorting family (9)**: batcher, pbatcher, sbatcher, seqbatcher,
  simplebatcher, mesort, insert, insertion1, insertion2, pinsert
  (+pinsertdata).  Verify against C sorts.
- **Numeric kernels**: simpson, life2, mmult2, minmax, fft, alphabeta,
  ada, crypto, crossovers, parpi1, parpi2, parpi_babb.
  (simpson/life2/minmax landed Jul 14, e97de98/393e15b; also mesort_dv +
  insertion1_dv from the sort family.)
- **SIMPLE-physics family (~15)**: AngMom, Energy, Freq, PassFreq,
  PassGrid, Spec, Specam, UVSpec, TStep, Linear, VSphere, SIFuncs, Sas,
  cdf, noise, gen_extent.
- **Loop/forall coverage**: for_all_argmax, for_all_reduce (**pins the
  backlogged masked-reduction-ignores-`when` bug — promote red, then
  fix**), for_initial_loopa, for_initial_simple,
  test_forall_{cross,dot,matmul,simple}, tst_loop2, tst_loopAt1/2,
  tst_loopX/X2.
- **Type features**: tuple_add/hash/kw/mixed/mixed2/mixed3/tests,
  record1, record2, test_record1, union, union0, union1, quadtypes,
  complex_types, verify_numpy_broadcast (the last two long known as
  compile-clean-need-drivers).  (tuple_fn_val moved to the NESTED-FN
  parked group.)
- **Recheck**: newgaussj_dv now EMITS (its old "4 cc errors" were
  clang-side; retry after the recent type fixes).
- **Sorts update (Jul 14 pm)**: heapsort/modern_heapsort/quicksort/
  quicksort1 now EMIT after two backend fixes (recursive procedure
  collection for NESTED function definitions + function-typed symtab
  names skipped in pre_declare and infer_types.pass1 — they are nominal,
  no C type).  heapsort_dv's port is PARKED on a further backend bug:
  a two-result IF nested in Heapify's let references phantom p1 outputs
  across compound levels (undeclared v_..._p1_o + float-sentinel casts);
  the minimal 2-result-IF-with-nested-IF repro PASSES, so the trigger
  needs Heapify's full let/if nesting.  Nested fns that CAPTURE enclosing
  values remain unsupported (captures would become unfed parameters).

## Bucket B — blocked on missing backend lowerings

| Missing op | Files blocked | Note |
|---|---|---|
| ARRAY_FILL | 28 | biggest single lever; trivial alloc+fill |
| ~~ARRAY_REML / ARRAY_ADDL~~ | ~~9 + 9~~ | RESOLVED Jul 15: AADDL/AADJUST aliased onto the DV lowerings (runtime helpers were already bounds-faithful: addl decrements lower_bound, adjust re-bases to lo); AREML/AREMH got new rank-aware slab helpers (reml bumps lower_bound, remh keeps it). |
| VECMATMUL | 6 | |
| REDUCE | 6 | |
| ~~ARRAY_ADJUST~~ | ~~6~~ | RESOLVED Jul 15 (see above). |
| DV_RESHAPE / EXPAND / EINSUM | 5 + 2 | the known APL bucket |
| VBUILD / VSPLAT / SWIZZLE / MATSPLAT | 7 | vector-swizzle tests |
| ~~ARRAY_REMH~~ | ~~1~~ | RESOLVED Jul 15 (see above). |

## PARKED GROUP: NESTED-FN (function defined inside a function)

Per directive (Jul 14): every test that defines a function INSIDE another
function is parked as one family, regardless of current emit status, until
the class is handled end to end.  Two backend fixes already landed
(fef0be8: recursive procedure collection + function-typed symtab names
skipped in pre_declare/pass1), which made the sort members EMIT — but the
heapsort port then hit the phantom-p1 multi-output-IF bug, and CAPTURING
nested functions are structurally unsupported (captures would become
unfed parameters).  Un-park only after (a) the multi-output-IF
cross-compound port bug is fixed and (b) a capture policy exists
(reject-with-error at minimum).

The 33 members: anneal, bad, capture, capture2, common, fem, funcarray,
funcarray2, gurd, heapsort, lambda_typed, lambda_untyped, mashi,
modern_heapsort, moldyn, nested, newfem, newqueens, nico, nico2, nucleic,
outs, outs2, quadrature, queens, quicksort, quicksort1, reset_ast,
rest_ast, scan1, scan2, tuple_fn_val, unsplit.

(newqueens and tuple_fn_val are removed from Bucket A accordingly.
Detection recipe: scan function/end-function nesting depth ignoring
%-comments; a `function` at depth >= 1 marks the file.)

## Bucket C — out of scope by standing decisions

- STREAM-typed tests (8): streams unbuilt.
- FUNCTION_TYPE in signatures (~14): higher-order/closures unbuilt.
- letrec family (6): local fn defs rejected by the parallel-copy binder
  (honest error; already-broken feature; ledger'd in cram).
- for-initial gather TEST-compare limitation (9): gather in a while-form
  whose test is not a plain comparison.
- Deliberate negative tests (cross/dot mixing, replace type errors).

## Recommended order

1. ARRAY_FILL backend lowering (unblocks 28; stops hand-rewriting it in
   every port).
2. Batch-port sorting family + simpson/life2/minmax (mechanical, easy
   references).
3. Promote for_all_reduce; fix the masked-reduction bug it pins.
4. Drivers for verify_numpy_broadcast + complex_types.
5. ARRAY_ADDL/REML/ADJUST trio (unlocks the physics family idioms).
