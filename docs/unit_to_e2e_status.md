# Unit → E2E Promotion Status (Jul 14, 2026; CLOSED Jul 17, 2026)

**BUCKET A IS COMPLETE (Jul 17 2026, suite 227/227).**  Every mechanically
portable unit test has an e2e group with a C-reference/qsort/by-construction
driver.  Final unported set, each with a recorded reason (commit 6003867):
crossovers + cdf + crypto (masked gathers / nested-array elements /
records-with-array-fields — boxed-array & records-phase-2 territory);
PassFreq/PassGrid (missing extern prototypes for non-intrinsic globals);
newgaussj_dv (emits+compiles, redundant with 5 solver groups);
test_forall_* + mmult2 (redundant); fft.sis (truncated fragment);
gen_extent (compiler-regression unit); pbatcher/sbatcher (programs
mis-sort — skeleton pinned via the seqbatcher dataflow mirror);
tst_loopAt1 (landed BOTH ways under the strict-dot-lengths ruling).
Bucket B ops, the NESTED-FN parked group, and Bucket C features remain
per project_master_sequencing (review+coverage next, then boxed arrays,
then streams).

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
| ~~ARRAY_FILL~~ | ~~28~~ | RESOLVED Jul 15 (826e33b): explicit array_fill / array_dv_fill intrinsic split. |
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

---

# REOPENED — refreshed sweep (suite 241; streams+nested-fn+masked-gather+records landed)

Re-swept every `test/unit/*.sis` with no e2e/_dv/_e2e counterpart
(case-insensitive; 207 uncovered) — compiled to C++ from inside `test/unit/`,
then `clang++ -std=c++23 -fsyntax-only` on the output.  Tally:

- **89 CPP_OK** — emit C++ that compiles (~50 with a `func_MAIN`).
- **58 CPP_FAIL** — emit C but won't compile (backend gap).
- **59 FRONTEND_NO_C** — no C (frontend gap, or include-fragments/non-programs).

Note the coverage matcher is stem-based: stream tests (sieve, sieve_v2,
uprime2, arsieve) ARE covered under `stream_*_dv`; `uprime1` is intentionally
parked (fragile reference).

## Genuinely-new promotable now (compile + run verified, by-construction refs)

- **Union/tagcase dispatch (4):** tagcase_bare, tagcase_bare_mixed,
  tagcase_bare_nested, tagcase_ii — purpose-built bare-tagcase regression
  pins (member_dv / bare-tagcase work).  Integer outputs.  Verified:
  tagcase_bare_nested(1)=tagcase_bare_nested(7)=2.
- **If / nested-capture (3):** test_if_nested_capture, test_if_complex_review,
  test_if_let_cascade — pure scalar.  Verified: nested_capture(1,T,77)=77,
  (1,F,77)=42, (2,*,*)=0.

## Deferred — need array→array_dv rewrite (NON-mechanical, per the standing rule)

- crypto (`type string = array[character]`), cyk
  (`array[array[array[boolean]]]` AoA / boxed-array territory).

## Backend gaps blocking the 58 CPP_FAIL (grouped by first error)

- `sisal_array_addh_f32` missing overload (8) — float array-append growth.
- lambda-as-value (12): `undeclared LAMBDA` (5) + call-to-lambda-object (7)
  — higher-order function values not lowered.
- multi-output masked gather on the PLAIN-`array of` path `v_*_n__N_p1_o`
  undeclared (~7: quicksort1, mashi, bad, lu.npiv, outs/outs2, ...) — NOT an
  independent bug.  A forall returning several masked arrays (e.g. Split's
  L/Middle/R = `returns array of E when ... / array of E when ... / array of E
  when ...`) only gets its FIRST output port declared on the plain-`array`
  path; ports 1+ are referenced but never emitted.  The array_dv path wires
  all outputs (proven: rewriting quicksort1 -> array_dv declares p0/p1/p2 and
  compiles clean; cf. the working quicksort_dv/heapsort 3-output Split).  So
  these are just the standard array->array_dv rewrite, per
  project_c_lowering_array_dv_only ("C lowering = array_dv only").
- union `incomplete type struct union_un_NNN` (3) — union boxing/fwd-decl.
- intrinsic double-emission: `redefinition of func_ASINR`, "functions differ
  only in return type" (4); `conflicting types for func_MAIN` (2).

---

# REFRESHED SWEEP — Aug 9, 2026 (suite 344)

Measured, not recalled: `test/unit/*.sis` stems with no `test/e2e` counterpart
(matching after stripping `_dv` / `_e2e` / `_dv_e2e`), each rewritten
mechanically to array_dv (`array[` → `array_dv[`, `returns array of` →
`returns array_dv of`, `array_fill` → `array_dv_fill`) and compiled to C.

    unit .sis                        291
    e2e stems                        350
    unit with no e2e counterpart     162
      of which compile to C after the array_dv rewrite:  162  (ALL of them)

**Compilation is no longer the gate.** Every uncovered unit file lowers to C.
What a promotion costs now is the REFERENCE and the dependencies, so the tiers
below are cut by that, not by whether the compiler copes.

## Landed this campaign

| file | what it bought |
|---|---|
| `mdfftfreq_dv` | whole frequency-direction FFT stack vs a naive DFT |
| `mdfftgrid_dv` | inverse stack vs naive IDFT; pinned a source bug (`nfax<=1` uses `inc2=2`, should be 1 → grid at stride 2) |
| `newsieve_dv`  | `array_dv[boolean]` end to end — the 1-byte element path, incl. `elem_bytes==1` across the C boundary |
| `ck_yb_dv`     | ragged input as a LIST of array_dv rows; zero-trip `least`/`greatest` identities |

## PENDING — `switch` (the one deferred candidate)

`test/unit/switch.sis`, 75 lines. Simulated-annealing move generator for the TSP
(`Make_Change` / `Single_Change`). **Not promoted; deferred deliberately.**

It needs three dependencies inlined, per the self-contained-e2e convention:

    global Remove_Edge  ( C : Cross_List; E : Edge_Type ... )
    global Check_Crossed( E : Edge_Type; Itinerary : Itin_Type ... )
    global Choose_Random( seed : Four_Plex; Itinerary : Itin_Type ... )

Why it is harder than the FFT inlining that unblocked `passfreq`/`mdfftfreq`:

1. `Cross_List` is a NESTED, mutated structure, not a read-only ragged one, so
   the `ck_yb` trick (rewrite as a list because only sizes are read) does not
   apply — `Remove_Edge` edits it.
2. Its entry points are `Make_Change` / `Single_Change`, neither named `main`;
   an e2e port needs a driver written around them.
3. `Choose_Random` makes it stochastic, so the reference has to pin the RNG the
   way `ranf_dv` / `psa_rng_dv` do, or the move set must be driven
   deterministically.

Re-assess after the boxed / array-of-array phase, when a mutable nested
structure has a supported representation. Nothing blocks it in the compiler
today — it compiles — the cost is the driver plus a deterministic reference.

## What else is left, by cost

- **47 — standalone, non-ragged, no `global`, not a negative test.** Reference
  is the only work. Biggest first: `scan1`/`scan2` (411), `quad` (275),
  `quadtree` (260), `basic_dv` (218), `zbuffer1`/`zbuffer2` (165), `sp.init`
  (140), `newgaussj` (139), `stand_alone_gauss` (116), `gaussj_1`/`gaussj`
  (109-110), `rank_reduce_suite` (81), `gaussjnew` (77), `lu.piv` (75).
  The Gauss/LU cluster is the obvious next block — one linear-solve reference
  (residual `‖Ax-b‖`, or compare against a C LU) serves five or six files.
- **25 — need dependencies inlined (`global` decls).** Same shape as the FFT
  promotions; mechanical but bulky. Includes `InitFFT`, `cfft_dv`, `feo.fft`,
  `sieve`, `sieve_v2`, `kin16_dv`, `anneal`, the `bmk11a*` pair.
- **21 — ragged, need the LIST rewrite** ([[reference_ragged_arrays_as_lists]]):
  `tsp`, `cyk`, `fem`/`newfem`, `monolith`, `scat`, `newqueens`, `ssphot`,
  `format`, `out`, `send`, `para`, and the `test_forall_*` trio.
  `ck_yb` proved the route; check what the algorithm actually READS first.
- **59 — helper fragments** with no matching entry function (`mat_ops`,
  `vec_ip`, `innerproduct`, the `capture*`/`lambda_*` set, ...). Mostly already
  exercised indirectly by the files that include them; not standalone
  promotable.
- **12 — negative tests**, already asserted in `test/errors.t`. Do NOT promote;
  they are expected to fail to compile.
