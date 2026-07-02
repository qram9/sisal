# Forall → `array_dv` Lowering — Design Notes

Status: in progress (branch `forall-extent-rework`). This records the structural
analysis and the connectivity model for lowering array-building `forall` loops to C,
modelled on the (working, mechanical) `for initial` / LoopB lowering.

---

## 1. Goal

Build arrays with `forall` and lower them to C using the **`array_dv`** model (Sisal 2.0
flat dope vectors — one buffer + rank/dims, never nested `array_dv[array_dv[…]]`). The
target is for the lowering to be **mechanical** — "read the subgraphs, follow the
outer-graph edges, emit" — exactly like `for initial` already is, rather than the current
body/generator *shortcut* in `lower_forall`.

---

## 2. The template: `for initial` (LoopB) connectivity

LoopB is mechanical because **every** dataflow is an explicit edge through the outer
(`loop_gr`) graph, mediated by visible **MERGE** (phi) nodes. Per carried variable `X`:

```
INIT.out_X  → MERGE_X.1     (seed: initial value)
BODY.out_X  → MERGE_X.2     (update: per-iteration / backedge)
MERGE_first → MERGE_X.0     (control)
MERGE_X.0   → BODY.in_X, TEST.in_X     (read by consumers)

For returns:
- `value of X` (FinalVal):
  MERGE_X.0  → RETURNS.in_R            (result: uses MERGE output to handle 0-iteration case)
- `array of X` (Dv_array_of / reductions):
  BODY.out_X → RETURNS.in_R            (result: reads body stream directly)

boundary    → INIT/TEST/BODY           (loop-invariant externals)
RETURNS.out → loop boundary out
```

C lowering (committed, `c5ed20c`): declare one C var per MERGE; **seed** from `.1` before
the loop; **capture** body outputs into `bodycap` temps and **copy** them into the MERGE
vars on the backedge (snapshots ⇒ swap-safe); RETURNS reads the in-scope `bodycap`. Tests:
`test/for_initial_e2e.sis` (sum/product/final-i/passthrough/swap/fib, LoopB + LoopA),
wired into `test/dv_run_all.cpp` / `run_dv_e2e.sh` (group `FOR_INITIAL`).

Role table (the thing to reproduce for forall):

| role | for-initial edge |
|---|---|
| seed (initial) | `INIT → MERGE.1` |
| update (per-iter) | `BODY → MERGE.2` |
| read (consumers) | `MERGE.0 → BODY/TEST` |
| result (FinalVal) | `MERGE.0 → RETURNS` |
| result (Array_of) | `BODY → RETURNS` |
| invariant | `boundary → INIT/BODY` |
| mediator node | `MERGE` (in the outer graph) |

---

## 3. Forall structure

A `forall` is the same skeleton: **GENERATOR / BODY / RETURNS** subgraphs wired through
the outer (`FORALL`) graph, with **`DV_GATHER`** (inside RETURNS) as the mediator (≈ MERGE).

Even the bare `for i in 1, n returns array_dv of i` has a (degenerate identity) BODY: it
forwards `i` to its boundary output. So **the gathered value is always a body output** —
there is no "bodyless" forall to special-case.

### Generator forms

| form | generator node | extent on gen boundary out 0 | loop var per iter |
|---|---|---|---|
| range `for i in 1,n` | `RANGEGEN(1,N)` | `(N-1)+1` | `i = lb + idx` |
| element `for a in A` | `DV_SCATTER(A)` | `A.size` (lowers like `ASIZE`) | `a = A.data[idx]` |
| element `… at i` | `DV_SCATTER(A)` (2 outputs) | out0=`A.size`, **out1 = index (`LONG`)** | `i = idx (+lb)` |

The generator's **boundary out 0 is the extent** — `lower_forall` reads it as `count`
(`apple_lower.ml:596-602`) and uses it for both `alloc_empty(count)` and the loop bound.

---

## 4. Name binding / export (consistent with for-initial)

Names flow between subgraphs through `If1.get_symbol_id` (`if1.ml:4389`): a name referenced
in a subgraph but defined in the parent is **imported by creating a boundary input bound to
that name**, plus an outer edge. The forall front end already uses this:

- `axis_name` (`to_if1.ml:1254-1261`) extracts the loop-var name (`i`/`a`);
- RETURNS imports it by name (`get_symbol_id`, 1334-1342) — comment: *"consistent with
  for_initial"*;
- `wire_all_syms_to_compound` connects the import back to the generator.

**Unnamed values** (the extent, literal/expression bounds `lb`/`ub`) have no name to ride
the symtab path, so they must get **gensym'd temp names** (the established `__LF…`
convention — `__LFI`, `__LFA`, `__LFB`). Rule:

```
boundary output already a user name (a, i, n)  → use it
else (extent, literal lb, expression ub/lb)    → gensym (__forall_extent, …); register in forall symtab
```

---

## 5. The handoffs, and what's missing

RETURNS needs two things: the **extent** (sizing) and the **value** (gathered). The value
is always a (possibly trivial) body output, handed off **by name** — i.e. a
`BODY → RETURNS` edge, like for-initial's `BODY → RETURNS`.

What the forall outer graph had:

```
present:  GENERATOR.0 → BODY                 (index/extent → body)
present:  GENERATOR.0 → RETURNS              (extent)  — but landed on the gather VALUE port
MISSING:  BODY        → RETURNS              (the per-iteration value)   ← the gap
present:  boundary    → GEN/BODY             (invariants)
```

So the extent handoff existed; the **value handoff (`BODY → RETURNS`) does not** — which is
why `lower_forall` falls back to reading the body output directly (positional shortcut),
why multi-gather mis-binds, etc.

### `DV_GATHER` / `DV_DIMENSION` (the RETURNS graph)

`create_return_nodes` (`to_if1.ml:8563+`) builds, per `returns array_dv of <expr>`:

```
DV_GATHER  port 0 = INDEX     (HALF-typed; the iteration coordinate)
           port 1 = VALUE     (the body value, type tt)
           port 2 = SHAPE/RANK (from DV_DIMENSION, or a rank literal)
           port 3 = MASK      (only with a `when` clause)
           out    = array_dv[tt]
DV_DIMENSION port 0 = axis/dope-vector ; port 1 = dimension index (literal)
           out = "lo record{…}" triplet (lower bound + extent for that dimension)
```

This is a complete typed spec of the build — but the backend currently **ignores it**
(takes extent from the generator, value from the body output directly). It's the lever for
**gather placement** (Sisal 2.0): RETURNS is decoupled from the iterator, so `DV_GATHER`
port 0 could carry an arbitrary placement expression rather than the implicit `idx`.

---

## 6. Changes made this session (uncommitted)

1. **`to_if1.ml` (forall wiring, ~1358)** — removed the `add_edge gn 0 rn next_rn` edge that
   landed the **extent on `DV_GATHER`'s value port**. The extent already reaches RETURNS's
   sizing via the named axis import; the value port is now empty, reserved for the future
   named `BODY → RETURNS` edge. Verified: `for i in 1,n returns array_dv of i` ⇒ `[1..5]`;
   dv suite green.

2. **`apple_lower.ml` (`is_dv_elem_forall`, ~615)** — fixed the **`at` index** crash. The
   path previously paired *every* `Basic` loop var with an array via `fold_left2`; the `at`
   index is a second `Basic` var with no array, so lengths mismatched →
   `Invalid_argument("List.fold_left2")`. Now classify by the **generator symtab's defining
   node/port**, not the type:
   - name defined by `DV_SCATTER` at **port 0** ⇒ element (`A.data[idx]`, zip with array);
   - at a **higher scatter port** ⇒ `at` index (`A.lower_bound + idx`).

   Why not by type: `At_exp` (`to_if1.ml:1043-1066`) hard-codes **two different types** for
   the same index — the *symtab entry* `INTEGRAL` (line 1056) but the *boundary-output edge*
   `LONG` (line 1065) — so the loop symtab can't distinguish element from index by type.
   Verified: `for x in A at i returns array_dv of x*i`, `A=[10,20,30]` ⇒ `[10,40,90]`;
   `for b in A returns array_dv of b*2` ⇒ `[10,12,14]`; dv suite green.

---

## 7. Case-insensitivity caveat (`for a in A`)

Identifiers are **case-folded** (the IF1 is all-uppercase), so Sisal here is
case-insensitive: `a` ≡ `A`. Thus `for a in A` is really `for A in A` — the loop variable
**shadows the array**, the array becomes unreachable by name, and the loop symtab keeps a
single `"A"` (the element) with **no array entry**. There is nothing well-defined to lower
(self-shadowing); it crashed before this work too. **Fix: use distinct names** (`for b in
A`, `for x in A`). Long-term, this should be a clean front-end diagnostic.

---

## 8. Status matrix (array-building forall)

| case | status |
|---|---|
| 1-D `array_dv` build (`for i in 1,n returns array_dv of expr`) | ✓ works (generic gather path) |
| element iteration, distinct names (`for x in A …`) | ✓ works |
| element + `at i`, distinct names | ✓ works (fixed this session) |
| **multi-gather** (`returns array_dv of i, array_dv of i*i`) | ✗ gather path is single-output (`res_v`/`body_elem_port`) |
| **multi-dim / cross** (`for i cross j …`) | ✗ outer body slot is a nested FORALL → `find_subgraph "BODY"` = "no BODY" |
| explicit nested → flat rank-2 | ✗ emits but builds nested int-buffer-of-arrays (wrong; type/size mismatch) |
| `for a in A` (name collision) | odd — self-shadow; use distinct names |

---

## 9. Next steps (in order)

1. **Named `BODY → RETURNS` value edge** — feed `DV_GATHER`'s now-empty value port from the
   body's return-value output, by name. Elementary `for i in 1,n returns array_dv of i` is
   the minimal test (trivial body emits named `i`). Then RETURNS is self-contained.
2. **Multi-gather** — generalize the gather path from one `res_v`/`alloc`/`store` to one per
   forall output port (all sharing the one generator extent).
3. **Flat rank-N nested build** — make `lower_forall` recurse when the body slot is a nested
   FORALL; allocate **one** flat `array_dv` of size = product of extents, dims = per-level
   extents, store at the linear index. Never nested `array_dv[array_dv]`.
4. **Drive the build from RETURNS** (`DV_GATHER`/`DV_DIMENSION`) instead of the
   body/generator shortcut — unlocks **gather placement** (Sisal 2.0 decoupled gather:
   arbitrary index/permutation, masked `when`).
5. Front-end diagnostic for case-insensitive self-shadow (`for a in A`).

Pointers: `lower_forall` `apple_lower.ml:590-779`; forall construction
`to_if1.ml:1243-1378`; returns-gather construction `to_if1.ml:8563+`; `get_symbol_id(_old)`
`if1.ml:4389/4422`.
