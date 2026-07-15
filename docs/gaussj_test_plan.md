# Gauss-Jordan DV (`gaussj_dv_rr.sis`) — bottom-up test plan

Goal: validate `gaussj_dv_rr.sis` **leaves first**, in isolation, each with a tiny
driver and a hand-computed expected output. Only assemble upward once each part
passes on its own. Do NOT run the whole solve until steps 0–4 are green.

Subject file: `test/gaussj_dv_rr.sis` — functions `idfamax`, `idfmax`, `GetPivot`,
`Compute`, `Main`. The explicit-rank conventions: `A[i,j]`=scalar load,
`DV_RANK_REDUCE(A,i)`=row, `A[i,..:row]`=row replace (`DV_RANK_REPLACE`).

## Reusable driver helper (build an array_dv descriptor, 1-based, double)

```c
// type_id 4 = double (8 bytes); sisal indices are 1-based so lower_bound = 1.
static sisal_array_t mk(double* d, int rank, int n0, int n1){
  sisal_array_t a={}; a.type_id=4; a.ref_count=1; a.rank=rank; a.data=d;
  if(rank==2){a.size=(uint64_t)n0*n1; a.dims[0]=n0;a.dims[1]=n1;
              a.lower_bound[0]=1;a.lower_bound[1]=1; a.stride[1]=8;a.stride[0]=8*n1;}
  else {a.size=n0; a.dims[0]=n0; a.lower_bound[0]=1; a.stride[0]=8;}
  return a;
}
// integer rows (PIVR): type_id 6, esz 4, stride 4.
```
Compile pattern: `clang++ -std=c++17 -I runtime -o run gen.c drv.cpp`.

---

## Step 0 — multi-output function return  ✅ DONE (Jun 2026)
Had TWO layers, both fixed in `apple_lower.ml`:
1. **Call-site gate** (~516-540): was gated on live out-edge count; now gates on the
   callee's ARITY (computed from `procedures_info`/`proc_map`: does it return a
   `*_results` record?). Builds the `_mr_` temp + extracts `.res_<port>` for each
   LIVE output (dead outputs bind nothing).
2. **Forall callee only emitted ONE output array** (the real value bug): `lower_forall`
   folded the body RETURNS edges keeping only the LAST (so port 0 got the last `… of`
   expr; port 1 never allocated). Now collects ALL body outputs (`body_outs`, sorted
   by port) and the gather path allocates + stores EACH (shared loop extents).
Verified: `mr_two_array → 11 21 31`, `two_both (P[i]+Q[i]) → 31 61 91`; corpus 384,
e2e 6/6 (single-output foralls intact), slice anchors intact. TODO: fold
`mr_two_array`/`mr_two_scalar` into the e2e harness.

## (historical notes for Step 0 below)
`Compute` and `GetPivot` each return **two** values, lowered to a result record
(`struct FUNC_*_results`). The full-run attempt died here:
```
error: no matching conversion from 'FUNC_COMPUTE_results' to 'sisal_array_t'
  ... v_..._A = SISAL_CAST(sisal_array_t, func_COMPUTE(...))
```
i.e. the call site casts the whole record to `sisal_array_t` instead of
destructuring `.field0 / .field1`. **This blocks steps 3,4,5.** Fix the
multi-output destructure at the call site first.
- **ROOT CAUSE LOCALIZED (Jun 2026)** — NOT an "array-wrap". Repros saved:
  - `test/mr_two_array.sis` — `let P,Q := Two(..) in P` (Q DEAD), **FAILS**.
  - `test/mr_two_scalar.sis` — scalar 2-output, both used, **works**.
  - `/tmp/two_both.sis` — array 2-output, BOTH used (`P[i]+Q[i]`), **works** and
    emits the correct `_mr_` temp + `.res_0/.res_1`.
  The only difference between fail and pass is whether the 2nd output is USED.
- The gate (apple_lower.ml ~518-531): `out_ports` = node's outputs that have a
  LIVE consumer edge (counted from `gr.eset`, `sn=nid`). `if length out_ports > 1`
  -> build `_mr_ struct` + read `.res_<port>`; else -> `assign_with_cast` =
  `SISAL_CAST(port_type, rhs)`. A DEAD output drops the live count to 1, so a
  record-returning call falls into the single-value path and casts the whole
  record to `sisal_array_t`. The `SISAL_CAST(sisal_array_t,…)` is just the normal
  single-output assignment, NOT a special wrap.
- **Real fix**: gate on the callee's ARITY (does it return a `*_results` record?),
  not on `out_ports > 1`. When it returns a record, always build the `_mr_` temp
  and extract `.res_<port>` for each LIVE output (even just one).
- gaussj `Compute` is the SAME root: one call site (grr.c:610), single-cast path,
  no `_mr_`. ⚠️ OPEN QUESTION for Step 3: B is NOT extracted at the call there even
  though `returns value of B` uses it — confirm B is actually wired (the dead-output
  undercount may be silently DROPPING B = a correctness bug, not just a compile err).
- Done when: `test/mr_two_array.sis` compiles + (extend it to) read both outputs back.

## Step 1 (leaf) — `idfamax` / `idfmax` (argmax over a 1-D row)
- `idfamax(A,n)` = `argmax abs(A[i])`; `idfmax(A,n)` = `argmax A[i]`, i in 1..n.
- Test input row `A=[1,-5,3]`, n=3.  Expected: `idfamax=2` (|−5| largest),
  `idfmax=3` (3 largest).
- Isolates: the `argmax`-reduction over `A[i]` scalar loads (1-based lb).
- RISK to watch: `argmax abs(A[i])` — earlier we hit `argmin/argmax (EXPR)` with a
  leading `(` parsing as a call. Here the token after argmax is `abs` (ident), so
  likely fine, but confirm the IF1 has a REDUCE(argmax), not a call to ABS.
- Done when: both return the indices above for the fixed row.

## Step 2 (leaf) — row swap (`DV_RANK_REPLACE`)  ✅ ALREADY GREEN
- `test/slice_store.sis` (`A[2,..:Z]` → `11 12 13 0 0 0 31 32 33`) and the
  standalone swap `/tmp/swap.sis` (`A[1,..:A[2,..];2,..:A[1,..]]` →
  `21 22 23 11 12 13 31 32 33`) both pass. Keep as the regression anchor.
- Note (do NOT re-verify by running gaussj): gaussj's swap now lowers to 2×
  `DV_RANK_REPLACE` / `sisal_dv_replace_slice`, 0× `replace_arr`.

## Step 3 — `Compute`  ✅ DONE (Jun 2026)
Fixed by box-then-flatten in `lower_forall`: `array_dv of <inner-forall row>` was boxing
row descriptors (nested); now re-packs into a flat rank-(outer+elem) array_dv (reads
elem shape once off the first boxed row, memcpy per row). `A'=1 2 0 1`, `B'=1 2`. A
DV_GATHER increments rank; scalar gather = the rank-0 case. Corpus 384, e2e 6/6.

## (historical) Step 3 — `Compute` (multi-output elimination)   [needs Step 0]
- `Compute(n,pvtrow,Ain,Bin)` → `(A', B')`, one Gauss-Jordan elimination step.
- Test: n=2, pvtrow=1, `A=[[2,4],[1,3]]`, `B=[2,3]`.
  - pvtele=A[1,1]=2. i=1(pvt): Arow=[1,2], Bele=1. i=2: mult=1/2=.5,
    Arow=[1−.5·2, 3−.5·4]=[0,1], Bele=3−.5·2=2.
  - Expected `A'=[[1,2],[0,1]]` (flat `1 2 0 1`), `B'=[1,2]`.
- Isolates: per-row inner forall, the `if i=pvtrow` branch, scalar loads, the
  multi-output return (depends on Step 0).
- Done when: both A' (flat) and B' match.
- **STATUS (Jun 2026): B' = 1 2 ✓ ; A' = GARBAGE (BLOCKED).** `Bele` is a scalar so
  its gather works. `Arow` is itself an array (the inner `for j` row), so
  `array_dv of Arow` gathers ARRAY-valued bodies. Current lowering allocs the outer
  result as rank-1 of `sisal_array_t` (elem type 94) and STORES the row DESCRIPTOR
  into each slot -> builds `array_dv[array_dv]` = the [[project_nested_array_dv_invariant]]
  violation. Reading flat -> garbage. Pre-existing: single-output `/tmp/aor.sis`
  (`for i: Arow:=for j..; returns array_dv of Arow`) fails identically (NOT caused
  by the Step 0 multi-output fix).
- **BLOCKER = nested->flat gather.** Need: when a body output is an array_dv, the
  outer gather must allocate a FLAT rank-(outer_axes + body_rank) result and COPY
  the sub-array's elements at the Horner offset (not store the descriptor). Hard
  part: the inner extent (row length) lives in a SEPARATE inner forall inside the
  BODY, so `fa_extents` (which walks only the outer generator nest) doesn't see it;
  the outer alloc/offset must discover the body-array's extent and fold it in.

## Step 4 — `GetPivot`  ✅ DONE (Jun 2026): A=[[0,2],[3,0]],PIVR=[0,0] → Icol=1,Irow=2.

## (historical) Step 4 — `GetPivot` (nested forall + the argmax helpers)
- `GetPivot(n,A,PIVR)` → `(Icol, Irow)`.
- Test: `A=[[0,2],[3,0]]`, `PIVR=[0,0]`, n=2.
  - row1 argmax-abs → col 2 (val 2); row2 → col 1 (val 3); maxs=[2,3];
    irow=argmax(maxs)=2; Icol=cols[2]=1.
  - Expected `Icol=1, Irow=2` (off-diagonal → forces a swap downstream).
- Isolates: the outer forall building `cols`/`maxs`, the `if PIVR[i]=0` guard,
  `DV_RANK_REDUCE(A,i)` feeding `idfamax`, and a 2-scalar-output return.
- Done when: returns (1,2).

## Step 5 — `Main`  ✅ DONE (Jun 2026): FULL gaussj solves end-to-end.
swap-forcing [[0,2],[3,0]] b=[4,9] -> x=[3,2]; no-swap diag -> x=[2,3].
Took TWO for-initial fixes: (a) to_if1 parameter-seeded carry MERGE (A:=Ain), and
(b) apple_lower var_map FIRST-WINS: pre_declare_graph_locals bound a port slot once
per symbol name (last-wins -> PIVR), but get_c_name/get_port_name resolve producers
to the FIRST name (OLD PIVR) -> forall stored OLD_PIVR, seeds read empty PIVR ->
old PIVR={0} -> GetPivot segfault. Fix: skip var_map bind if port already bound.
Corpus 387, FOR_INITIAL 28/0, GAUSSJ_PARTS 13/0, no regression.

## (historical) Step 5 — `Main`  was BLOCKED: for-initial array-carry bug
Steps 0-4 all green in isolation, but the full solve SEGFAULTs (139), and bisection
pins it to `lower_for_initial`, NOT the forall work:
- The carried ARRAY's `old` value is never wired into the loop body. `OLD_A` is
  declared `{0}` and dereferenced -> crash. Scalar carry (`I` counter) works; there
  is NO `MERGE_A`/`MERGE_OLD_A` for array recurrences.
- Repros (forall-free): `test/loopcarry_identity.sis` (`A,B:=old A,old B` -> returns
  EMPTY B), `test/loopcarry_used.sis` (`A:=...old A[i]*2...` -> SEGFAULT on `old A[i]`).
- Next: examine the for-initial IF1 (does the LoopB MERGE exist for the array carry?
  IF1 vs backend), then fix the `old`-array wiring in `lower_for_initial`.

## (historical) Step 5 — `Main` (assemble: for-initial loop + swap)   [needs 0–4]
- Two systems:
  - (a) **swap-forcing** `A=[[0,2],[3,0]]`, `B=[4,9]` → `x=[3,2]`
    (A[1,1]=0 forces pivot; exercises the `DV_RANK_REPLACE` swap inside the loop).
  - (b) **no-swap diagonal** `A=[[2,0],[0,3]]`, `B=[4,9]` → `x=[2,3]`
    (Icol==Irow path, the `else old A,old B`).
  - (c) optional 3×3 once (a)+(b) pass.
- Isolates: the `for initial … while I<n repeat` carried state (A,B,PIVR,I), the
  MERGE-carried arrays, and the swap-vs-noswap `if`.
- Done when: (a)→`3 2`, (b)→`2 3`.

## After it all passes
This is the motivating case for the **ref-count / copy-elim** backlog item
([[project_refcount_copyelim_backlog]]): each loop iteration currently full-copies
A and B (always-copy). gaussj is O(N³)-ish work that the in-place optimization
should make practical. Measure copies-per-iteration once correct, before optimizing.
