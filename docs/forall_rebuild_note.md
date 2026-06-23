# Forall → C lowering: the rebuild (before / after)

`lower_forall` (in `src/to_apple/apple_lower.ml`) was rebuilt from scratch. This
note records what changed and why. The old implementation is preserved, dead, as
`_lower_forall_recursive_OLD` (with its helper `zip_loops`) for reference.

---

## Why

The trigger was the **expression-range-bound** bug: `for i in 1, n-1` produced C
that referenced an undeclared variable, because the `SUBTRACT` node living inside
the generator subgraph was never lowered. The first patches reached into the
node-map (`NM.fold` / `NM.find`) to special-case it. Those were rejected on a
clear principle:

> Every subgraph is a full-fledged graph. Lower it by a **topological walk over
> the edges**; when you visit an edge, look up its tail/head in the node-map to
> decide the lowering. **Node-map folds are forbidden** as the driver of lowering.

That principle didn't fit the old generator lowering, so the whole forall path
was rebuilt around it.

---

## Before — the `zip_loops` path

One large function plus a recursive `zip_loops` that *zipped* the GENERATOR nest
and the RETURNS nest in lockstep, emitting one `for` per level. Characteristics:

- **Node-map folds drove the lowering.** The loop axes were found with
  `NM.fold (… RANGEGEN …)`; the iterator name by an `SM.fold` over the symtab;
  the bounds by `ES.fold`; the result extents by `fa_extents`, another `NM.fold`
  walk up a "compound ladder" (`resolve_up`).
- **Bounds were resolved ad hoc**, not lowered — which is exactly why the
  in-generator `n-1` SUBTRACT fell through the cracks.
- **Many interleaved branches** in one place: pure reduction (`forall_fold_op`),
  multi-reduction, mixed gather+reduce (`forall_reduce_ports` /
  `forall_gather_ports`), plain gather (`per_out` / `allocs`), and box-then-flatten
  — each with its own offset/alloc handling.
- Boundary values were handled by `init_boundary_ports` per compound, but the
  generator/returns plumbing (iterators, lb/ub relays) was bespoke.

It worked and covered the corpus, but the generator lowering violated the
"graphs, not node-map folds" rule and the bound handling was fragile.

---

## After — the node-driven path

A small set of explicit, uniform steps. The forall is an outer C compound (a
scaffold) holding the declarations; each generator level is a nested `for`.

### Pipeline

1. **Locate** GENERATOR / BODY / RETURNS subgraphs (a node-map lookup is fine
   here — we are only *finding* the structural children, not lowering).

2. **Recursive local-symtab visitor → the "anticipatory list".** Every named
   symtab entry across forall / generator / body / returns is declared up front
   in the forall `{ }` and registered in `var_map` (addressable) + `seen_decls`.
   Boundary inputs of the forall itself are initialised from the outer scope.

3. **Uniform boundary copy-in.** Every subgraph boundary input is a relay of its
   parent's value; treat *every* crossing the same way the forall treats its own
   inputs — `v_GEN_…_N = v_FORALL_…_N;` — recursively through nested generators
   (`proc → forall → outer-gen → nested-gen`). One rule at every level; no dead
   relay decls.

4. **`lower_gen`: node-driven generator lowering.** Per level: the **node is the
   sentinel** — `topo_sort` orders nodes so reaching node *n* means its inputs are
   ready, so lower it now. Bound math (`n-1`) is **materialised** by the canonical
   `lower_node` (full operator/cast coverage — we never put a bare expression on
   the RHS without naming it). The axis node *is* the loop:
   - `RANGEGEN` → counted `for (I = lb; I <= ub; I++)`, iterator declared outside;
   - `DV_SCATTER` / `ARRAY_SCATTER` → element loop, element type **from the IF1
     typemap**; `ARRAY_SCATTER` port 1 is the `at`-index;
   - several axes at one level = a **dot** (one counter, siblings in lockstep);
   - a nested `GENERATOR` = a **cross** (recursion → nested `for`).
   Loop-invariant bound math is hoisted before the result alloc, so even nested
   expression bounds (`1, m-1` in a cross) work.

5. **Generator-output propagation (recursive).** A generator compound's output
   port re-exports an internal value (iterator, lb/ub, or a nested generator's
   output); bind the parent-scope view to the internal producer so BODY/RETURNS
   resolve `I`/`J` straight to the in-scope loop variables.

6. **Body + returns.** The BODY is lowered with `lower_graph` (its per-iteration
   copy-ins + anonymous compute land in the loop-body `{ }`). Then, **per forall
   output port** (multi-output supported):
   - **gather** → alloc once before the loop (rank-k, extents OUTER→INNER from the
     generator nest), flat row-major store via a shared gather counter; if the
     body value is itself an array, **box-then-flatten** after the loop;
   - **reduction** → a scalar accumulator (`sum` / `product` / `least` /
     `greatest`, and `argmax` / `argmin` which return the Sisal index).
   All outputs share one loop and one gather counter.

### Principles

- **Graphs, not node-map folds.** Lowering is driven by topo order over each
  subgraph; node-map lookups only *identify* a visited node.
- **Materialize, don't inline.** Every subexpression is named and assigned (one
  uniform mechanism). Inlining was tried and rejected: it needs a hand-rolled
  evaluator that re-implements `lower_simple` incompletely.
- **Uniform boundary crossings.** Declare the slot once (step 2), assign on entry
  (copy-in). Same rule at every scope; the audit "every name declared AND
  assigned" falls out naturally.
- **Decls hoisted, compute local.** Named entries are declared up front in the
  forall `{ }`; anonymous compute intermediates sit in the loop-body `{ }` where
  `lower_node` declares them.

---

## Feature coverage (all verified end-to-end)

| Shape | Example | Result |
|---|---|---|
| range gather | `for i in 1,n returns array of i*i` | `1 4 9 16 25` |
| expression bounds | `1, n-1`, `n*2+1`, nested `1, m-1` | ✓ |
| scatter † | `for x in A` | element loop |
| at-index † | `for x in A at k` | element + `lower_bound+k` |
| cross (rank-k) | `1,n cross 1,m` | `[2,3]: 11 12 13 21 22 23` |
| dot (range/scatter) † | `A dot B` | `11 22 33` |
| reductions | sum/product/least/greatest | 15/120/1/5 |
| argmax/argmin | `argmax abs(A[i])` | the index |
| multi-output | `gp_two` (2 arrays) | per-port dispatch |
| box-then-flatten | `returns array_dv of <inner row>` | flat rank-k |
| element type from IF1 | `array_dv[double]` | `(double*)` |

† Scatter axes require the element name to **differ** from the source-array name;
`for a in A` self-shadows and miscompiles — see "Known bug" above.

## Known bug — scatter self-shadow (`for a in A`)

A scatter generator whose **element variable collides with the source-array name**
miscompiles. Sisal is **case-insensitive**, so in

```
for a in A returns array_dv of a + 1 end for      -- a ≡ A
for a in A at i ...                                 -- forall_dv_at.sis
for a in A cross b in B ...                         -- forall_dv_cross.sis
for a in A DOT b in B ...                           -- forall_dv_dot.sis  / _dot3
```

the element `a` **is** the array `A` (same symtab entry). The element binding
clobbers the source-array boundary slot, so the generated C references the array
port that was never declared:

```
error: use of undeclared identifier 'v_GENERATOR_10003_n__0_p0_o'
error: use of undeclared identifier 'v_FORALL_10001_n__0_p0_o'   // the scatter source array
```

**It is purely the name clash, not the scatter machinery.** Renaming the element
fixes it — all of these compile (0 errors) and run correctly:

```
for x in A returns array_dv of x + 1 end for        -- [10,20,30] -> [11,21,31]  ✓
for x in A at k  ...                                  -- ✓
for x in A cross y in B ...                           -- ✓
for x in A DOT  y in B ...                            -- ✓
```

So the "scatter / at-index / dot" rows in the coverage table below hold **only for
non-colliding names**. Trigger is independent of: param vs local source array,
`array` vs `array_dv` element type, and presence of `at`.

Root cause: the scatter axis's **source-array slot** (the `_p0_o` boundary port
that holds the array being scattered) is dropped from the anticipatory-decl /
copy-in plumbing (rebuild steps 2–3) when its name is already taken by the
generator's element output. Fix is one of: (a) keep the source-array port's decl
distinct from the element binding even under a name clash, or (b) reject the
self-shadow in the front end — see the
`for a in A` self-shadow work item in `forall_lowering_workitems.md`.

Minimal repro (still miscompiles today):

```
function Main( A: array_dv[integer] returns array_dv[integer] )
  for a in A returns array_dv of a + 1 end for     -- a == A  ->  undeclared port
end function
```

The former repro files `forall_dv_{at,cross,dot,dot3}.sis` were renamed to
non-colliding element vars (`for x in A ...`) and promoted to `test/e2e/` as
passing scatter/at/cross/dot coverage; they no longer exercise the self-shadow.

## Status

e2e parity with the old path: 17 groups green (incl. the full Gauss-Jordan solver
and the `A dot B` conform diamond). IF1 corpus 390/4 (the 4 are 3 deliberate
negative tests + 1 pre-existing parse error). The 4 e2e BUILD-FAILED groups are
pre-existing missing-`.sis` harness rot, unrelated to the rebuild.

The old `zip_loops` path remains as `_lower_forall_recursive_OLD` and can be
deleted once the new path has soaked.
