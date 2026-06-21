# `A + B` broadcast (array_dv `+` array_dv) — bottom-up test plan

Goal: validate the auto-generated NumPy-style broadcast pipeline **leaves first**,
each piece in isolation with a tiny driver and a hand-computed expected output.
Only assemble upward once each part passes on its own. Same discipline as
`gaussj_test_plan.md`: do NOT run the full `A + B` until steps 0–5 are green.

## The pipeline (from the IF1 of `main(A,B: array_dv[integer]) returns A + B`)

The compiler lifts `A + B` (possibly different rank/shape) into this proc-level
chain (node ids from `/tmp/apb.if1`, MAIN graph):

```
A,B ─┬─ __1 DV_NUM_RANK(A) ─► LFR1 ─┐
     └─ __2 DV_NUM_RANK(B) ─► LFR2 ─┴─ __3 IF ─► LFMR (max rank)
        │ (A,B,LFR1,LFR2,LFMR)
        ▼
   __5  CONFORM/SHAPE forall  → out0 __LFSH (broadcast shape), out1 compat(bool)
        │ shape                  │ compat
        ▼                        ▼
   __9 REDUCE_ALL product   __7 NOT ─► __8 ERROR (PANIC: BROADCAST_ERROR)
        │ = __LFTOTAL (count)
        ▼ (LFTOTAL,A,shape,B)
   __10 OFFSET element-wise forall  `for __LFI in 0, __LFTOTAL-1`
        │   per index: DV_OFFSET_AT into A&B, DV_LOAD_LINEAR, add → flat result
        ▼ (flat, shape)
   __12 DV_RESHAPE_BY_SHAPE ─► final array_dv ─► output
```

Key internal symbols: `__LFR1/__LFR2` (operand ranks), `__LFMR` (max rank),
`__LFSH`/`__LFSH_INT` (broadcast shape), `__LFTOTAL` (element count), `__LFI`
(linear index), `__LFIDX1/__LFIDX2` (per-operand offset SUBTRACTs), `__LFCOMPAT`
(conformability bool).

The investigation problem: several of these are **synthesized** builtins, not
surface Sisal (`DV_OFFSET_AT`, `DV_LOAD_LINEAR`, `DV_RESHAPE_BY_SHAPE`,
`DV_NUM_RANK`). For each step we must first find a Sisal snippet (or a minimal
hand-built `array_dv` driver) that provokes the same node, then check it e2e.

## Reusable driver helper (build an array_dv descriptor, 1-based, integer)

```c
// type_id 6 = int32 (4 bytes); sisal indices are 1-based so lower_bound = 1.
static sisal_array_t mk(int32_t* d, int rank, int n0, int n1){
  sisal_array_t a={}; a.type_id=6; a.ref_count=1; a.rank=rank; a.data=d;
  if(rank==2){a.size=(uint64_t)n0*n1; a.dims[0]=n0;a.dims[1]=n1;
              a.lower_bound[0]=1;a.lower_bound[1]=1; a.stride[1]=4;a.stride[0]=4*n1;}
  else {a.size=n0; a.dims[0]=n0; a.lower_bound[0]=1; a.stride[0]=4;}
  return a;
}
```

---

Enabling change: `DV_NUM_RANK`, `DV_OFFSET_AT`, `DV_RESHAPE_BY_SHAPE` were
synthesized-only; exposed as direct intrinsic calls in the `up_fn` dispatch
(`to_if1.ml`, next to the existing `DV_LOAD_LINEAR`/`DV_ELEMENT` handles) so each
leaf is testable on its own. Pieces live in `test/broadcast_parts.sis`, group
`BROADCAST_PARTS` in `dv_run_all.cpp` (11/11).

## Step 0 (leaf) — `DV_NUM_RANK` + max-rank `IF`  ✅ DONE (Jun 2026)
- `DV_NUM_RANK(A)` = number of dimensions; the `IF` picks `max(R1,R2)`.
- `bp_rank([3])=1`, `bp_rank([2×3])=2`. (max-rank IF is trivial scalar; covered
  implicitly — revisit if the conform forall needs it explicitly.)

## Step 1 (leaf) — `REDUCE_ALL product` over a shape array  ✅ DONE (Jun 2026)
- `bp_product([2,3])=6`, `bp_product([2,3,4])=24`.

## Step 2 (leaf) — `DV_RESHAPE_BY_SHAPE`  ✅ DONE (Jun 2026)
- `bp_reshape(flat[1..6], [2,3])` → rank-2, dims [2,3], data 1..6.
- NOTE: runtime reshape ALIASES the input data (`res = a`), so callers must not
  double-free the result + the source.

## Step 3 (leaf) — `DV_OFFSET_AT` + `DV_LOAD_LINEAR`  ✅ DONE (Jun 2026)
- `bp_load(a,0)=10`, `bp_load(a,2)=30`.
- `bp_offset([10,20,30] broadcast across [2,3])` → `0 1 2 0 1 2` (size-1/missing
  axis contributes 0 — the broadcast reuse). Matches the hand-traced row-major walk.

## Step 4 — OFFSET element-wise forall (`__10`, `for __LFI in 0, __LFTOTAL-1`)  ✅ DONE (Jun 2026)
- `bp_bcast_add(A,B,S,total)`: per linear index, offset+load both operands, add.
- same-shape `[10,20,30]+[1,2,3]` → `11 22 33`; real broadcast `A=[2,3] flat 1..6`
  `+ B=[3]` (row-broadcast), shape [2,3] → `11 22 33 14 25 36`.
- The expression upper bound `total-1` is exactly the generator-as-graph extent
  fix (commit 92f3faf). The heart of `A + B` works given a precomputed shape/total.

## Step 5 — CONFORM/SHAPE forall (`__5`, mixed gather+reduce)  ✅ DONE (Jun 2026)
- produces `__LFSH` (broadcast shape = per-axis max of A,B dims) AND `compat`.
- On the real `A+B` path BOTH outputs are consumed (shape feeds reshape/product/
  offset-forall; compat feeds the error check), so the `declare_outputs`
  unconsumed-port issue does NOT apply here — it only hits `dv_agreement` (a
  dot-forall where the conform shape is unconsumed; still a separate open bug).
- The REAL Step-5 bug was an **off-by-one** in `emit_dv_conform_check`
  (`to_if1.ml:3631+`): `__LFI` runs 1..MR (1-based), `__LFIDX = LFI-(MR-rank)` was
  used directly as a 0-based `dims[]` index, and the guard was `>= 1`.  So axis 1
  read `dims[1]`, the last axis ran off the end into the `a.size` fallback ->
  `[2,3]+[3]` gave shape `[3,6]`.  Same-rank worked only by accident (size==dims
  for the out-of-range fallback on a rank-1 array).
  Fix: make the index 0-based (`(LFI-1)-(MR-rank)`) and the guard `>= 0`; a
  negative index = a missing leading axis -> broadcast as 1.  Verified by tracing
  + a runtime `[DV_DIM]` print (removed after).
- STATUS: DONE for array+array.  Caveats: (a) SCALAR + array still returns a
  rank-1 result shape (separate scalar-path bug); (b) `dv_agreement` declare bug
  is independent.

## Step 6 — full `A + B` end-to-end   ✅ DONE (Jun 2026, array+array)
- same-rank `[1,2,3]+[10,20,30]` → `11 22 33`; broadcast `mat[2,3]+vec[3]` →
  rank-2 `[2,3]` `11 22 33 14 25 36` (and commutative `vec+mat`).
- Group `BROADCAST_COMPLEX` (G) now asserts correct numpy shapes/values
  (previously asserted the `[3,6]` bug); `bcast_vec_mat`/`bcast_unit` give
  `[2,3]`.  Scalar+matrix values correct, shape still rank-1 (TODO).
- STATUS: DONE for array+array; remaining = scalar-path shape + `dv_agreement`.

## Scalar `op` array — shape restore  ✅ DONE (Jun 2026)
- `S + M` (and `M + S`) flattens the array operand to a rank-1 elementwise forall
  (`for i in LIML..LIMH`), which discarded the array's rank -> result came back
  rank-1 `[9]` instead of `[3,3]`.  A scalar broadcasts to anything, so the result
  shape IS the array's shape — no conform needed.
- Fix (`lift_binop_forall`, both scalar branches): keep the flat loop, then
  `restore_rank` — reshape the rank-1 result back to the array's shape, built at
  RUNTIME (`for k in 1, DV_NUM_RANK(arr) returns DV_DIMENSION(arr, k-1)` ->
  `DV_RESHAPE_BY_SHAPE`).  Rank is rank-polymorphic so it must be a runtime loop.
- Verified: `100 + mat[3,3]` -> `[3,3]` 101..109; `mat[2,3] + 100` -> `[2,3]`;
  `5 + vec[3]` -> rank-1 `[3]` (rank-1 stays rank-1).  Group G updated.

## Open follow-ups
- **`dv_agreement`** (`for i in A dot j in B returns array_dv of i + j`): build
  fails because the dot-conform forall's port-0 gather output is unconsumed at
  proc scope, so `declare_outputs` never declares it.  Fix: declare a forall's own
  output ports even with no consumer edge (or route the gather alloc through
  `assign_with_cast`).
- Related: [[project_nested_array_dv_invariant]], the broadcast lift in
  `to_if1.ml` (~3771+), and the offset-forall synthetic AST.
