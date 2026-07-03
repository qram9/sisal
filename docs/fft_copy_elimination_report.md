# FFT Copy Elimination — Audit, Theory, and What the Current IR Can Already Do

*July 2, 2026 — companion to the `array_dv(exts) of elem at [..]` scatter work
(commits 83d74be, d09ef75, 924ee68).*

## 1. The audit: where the copies are in the generated FFT

`feo_fft_dv.sis` compiles to ~4,800 lines of C.  There are **no inline memcpys**
in the generated code itself — every byte moved goes through a runtime helper,
which makes the traffic auditable by counting calls:

| calls | helper                    | verdict |
|------:|---------------------------|---------|
|    52 | `sisal_array_addh_arr`    | **suspect** — the `A \|\| B` operator: alloc + copy both sides |
|    48 | `sisal_dv_slice`          | clean — `w1re[i, ..]` row access is a zero-copy view |
|    39 | `sisal_array_alloc_empty` | clean — allocations, no copying |
|    26 | `sisal_array_empty`       | clean — zeroed descriptors (seeds) |
|    20 | `sisal_array_catenate`    | **suspect** — `value of catenate X` accumulators |
|     6 | `sisal_array_shaped_store`| clean — the ported `W` gathers: exact prealloc, one memcpy per row |

The two suspects are both *compositionally* quadratic even though each call does
the minimum for its local semantics:

**(a) `value of catenate X` reductions** (levelA_i / levelA_B / levelB_i).
Each of the 8 streams per level runs `acc = catenate(acc, chunk)` every
iteration of the `j` loop — a fresh allocation plus a **full re-copy of the
accumulator** per iteration.  Building a size-N stream over `packs` iterations
moves O(N · packs) bytes where O(N) suffices.

**(b) `Are || Cre || Bre || Dre` quarter assembly.**
Each `||` allocates and copies both operands, so the 4-chain copies `Are` three
times, `Cre` twice, `Bre` twice.  Worst single case: `levelA_g`'s
`Are || singleton(0.0d0)` — a full-array realloc-and-copy **to append one
zero**, immediately followed by another full copy in the catenate that consumes
it.

## 2. The theory: three distinct ideas, three language families

These are not one optimization; they are three, and it matters which one each
fix belongs to.

### 2.1 Uniqueness — Sisal's *update-in-place*
Mutate a value in place iff it has exactly one consumer.  Sisal's OSC (Cann,
LLNL) combined static fanout analysis with a runtime `refcount == 1` check.
Type-level descendants: Clean's uniqueness types, Rust ownership, and the
modern star — Koka's **Perceus / FBIP** ("functional but in-place") and Lean 4's
RC-reuse ("counting immutable beans"): a refcount-1 value about to be dropped is
reused as the allocation of the result.  In this compiler, the inert
`sisal_array_t.ref_count` field is the placeholder for this entire branch
(see `project_refcount_copyelim_backlog`).

### 2.2 Destination-passing — Sisal's *build-in-place*
Don't build a piece and copy it home; pass the **home** inward, so the producer
writes at a caller-supplied buffer + offset.  OSC did this at IF1→IF2 lowering
(IF2 introduces explicit buffers).  Academic line: Minamide's hole abstraction,
Shaikhha et al.'s destination-passing style (DPS).

**Key observation: our scatter `array_dv(n) of v at [place]` is DPS as surface
syntax.**  A placement *is* a destination.  The even/odd "scatter packing" idea
(fill disjoint parts of one allocation at different times, prove disjointness of
affine placement sets, delete the merge) is DPS plus a cheap parity/stride
disjointness check.

### 2.3 Fusion / deforestation — Haskell's answer
Make the intermediate **never exist**: producer and consumer loops interleave
(Wadler's deforestation; GHC's `foldr/build` shortcut fusion; stream fusion).
Haskell has no "update-in-place" because it refuses the premise — and recovers
mutation only via `ST` or, recently, linear types (idea 2.1 arriving late).
SaC (Single Assignment C) is the living descendant of the Sisal school and uses
all three at once (with-loop folding + RC reuse) on dope-vector arrays.

### 2.4 How the peephole relates to deforestation
They are **not** the same idea:

- *Deforestation* fuses computation: two loop bodies interleave; elements are
  produced and consumed without ever living in memory.  It must see both loops.
- *The `||` peephole* fuses only the **storage plan**: the data is already
  computed; reassociating the chain avoids re-copying prefixes.  Every element
  still lands in memory exactly once.  It needs only sizes and the expression
  tree — operands may be opaque.

They meet one level up: push the *destination* into the producers of the
concatenated pieces and the intermediates vanish as allocations — that is DPS,
and doing it across loop boundaries is where it shades into true fusion
(SaC's with-loop folding).  The spectrum:

1. **Peephole** — reassociate `A||C||B||D`: one alloc, k memcpys.  No fusion.
2. **DPS / build-in-place** — producers write into their final slots;
   intermediates vanish as allocations; loop structure unchanged.
3. **Deforestation** — loops interleave; the intermediate vanishes as a
   concept.

For a strict, array-based dataflow IR, level 2 is most of the win: "fusing" a
gather into a consuming concat mostly *means* redirecting where its stores go —
exactly what `at [offset]` expresses.

## 3. What the current IR can already express

### 3.1 The catenate-reduce fix needs nothing new: an identity

The `catenate` reductions in the FFT are **order-preserving** — no shuffle at
all.  So the scatter isn't even needed:

```
value of catenate Are        ≡        ravel( array_dv of Are )
```

Left side: quadratic accumulator re-copying.
Right side: the **forall row gather** (`returns array_dv of Are`) already
lowers to box-then-flatten — one memcpy per row into a `(packs, cards/4)`
rank-2 result, i.e. exactly linear — and whose row-major flat buffer **is** the
concatenation.  The `ravel` back to rank-1 is a pure dope rewrite: rank/dims
change, same data pointer, zero copies (`sisal_array_reshape_by_shape` in the
runtime is already implemented this way).

So "moving the concat into the Pack_j's" for these streams is a **source-level
rewrite available today**, and later a mechanical IF1 rewrite (recognize
`REDUCE(catenate)` whose operand is a loop product → replace with
`DV_GATHER` + reshape).

### 3.2 One gap found while demonstrating: `DV_RESHAPE` has no C lowering

The surface `reshape(A, dims..)` parses and reaches IF1 (`DV_RESHAPE` node),
but `apple_lower` has no case for it — the demonstration program fails with
`Unsupported IF1 Simple node symbol: DV_RESHAPE`.  The fix is small: lower it
zero-copy (rank/dims rewrite on the same buffer), modeled on the existing
`sisal_array_reshape_by_shape`.  *Status: in progress; this is the only thing
between the identity above and a passing A/B test.*

### 3.3 The `||` chains: peephole now, DPS later

Peephole (no analysis): recognize a `||`-chain (`ACATENATE`/`addh_arr`
left-spine), sum the operand sizes, emit one alloc + k offset memcpys.
DPS (the real ending): the quarters are produced by the same level loop, so
with forall scatters (`at [quarter_base + ..]`-style offsets) each quarter is
written directly into the final buffer and the chain disappears entirely.

### 3.4 What genuinely needs the packing analysis

One thing is **not** expressible in the current IR: several *returns clauses*
sharing one destination buffer.  Each clause is one output; the 8 streams of a
level are 8 clauses → 8 buffers, and the A/C/B/D merge across clause results
still needs either an explicit merge (today) or the disjoint-placement fusion
(the even/odd packing idea: prove placement sets disjoint + fanout=1 into the
merge → one buffer, delete the merge).  That is the scatter-packing item on the
roadmap, with FFT decimation (radix-2/4 even-odd stage writes) as the motivating
workload.

## 4. Proposed order of work

| step | what | kind | cost |
|-----:|------|------|------|
| 1 | `DV_RESHAPE` C lowering (zero-copy dims rewrite) | gap fix | small |
| 2 | A/B demo test: `cat_reduce` vs `gather_ravel`, same values, count helper calls | evidence | small |
| 3 | Rewrite the FFT levels' `value of catenate X` → gather + reshape (source) | uses today's IR | small |
| 4 | `\|\|`-chain peephole (n-ary catenate) | peephole | small |
| 5 | forall shaped extents + `at` (deferred earlier; unlocks offset-DPS in foralls) | feature | medium |
| 6 | Scatter packing: affine disjointness + fanout-gated merge deletion | analysis | large |
| 7 | Uniqueness/refcount (general in-place legality net) | analysis + runtime | large |

Steps 1–4 remove the quadratic behavior from the FFT with no new analysis
machinery.  Steps 5–6 are the build-in-place ending; step 7 is the
update-in-place branch and benefits everything else (subscript updates
included).

## 5. Copy-cost summary for one FFT level (size-N streams, `packs` iterations)

| scheme | bytes copied per stream |
|--------|------------------------|
| today: catenate-reduce + `\|\|` chain | O(N·packs) + 3·O(N) re-copies |
| after steps 1–4 (gather+ravel, n-ary concat) | 2·O(N) (once into quarter, once into merge) |
| after step 6 (packing) | O(N) (each element written once, in place) |

## 6. Inlining vs. a DPS calling convention (crossing the Pack_j boundary)

Would inlining Pack_j help?  Yes — but only *our* rewriter, not the C compiler:

- **Inlining does not let clang fold the memcpys.**  Even fully inlined, the
  chain is `malloc(a+b); memcpy×2; malloc(a+b+c); memcpy×2; ...` — distinct
  heap objects of different sizes with intervening stores.  The redundancy is
  semantic (always-copy), not syntactic; it must be folded in our IR.
- **Inlining removes the call boundary that hides the producer from the
  rewriter.**  With Pack_j's gathers and the consuming catenate in one graph,
  the DPS rewrite is an intra-graph edge rewiring (point the gather's stores at
  the final buffer + offset).

The two classical ways to move a destination across a call boundary:

1. **Inline** — dissolve the boundary.  Viable here (small call tree), costs
   code size.
2. **DPS calling convention** — keep the boundary, change the ABI: qualifying
   callees grow hidden `(dest, offset)` parameters and build in place.  This is
   exactly what OSC's IF2 buffers were — why build-in-place lived at the
   IF1→IF2 lowering, not in the source.

Purity makes option 2 unusually cheap in this compiler: **every array output is
fresh by construction** (always-copy), so no escape/alias analysis is needed
before handing a callee a destination.  The per-function summary reduces to
"which outputs are arrays, and is their size an affine function of the
arguments" — size arithmetic only.

Within one function, the `||` forest is flattened by a left-spine leaf walk —
the same shape as the existing `flatten_cross` (to_if1.ml:1199), and the
resurrection of a concat-folding BFS that existed in an earlier incarnation of
this work.  No such folding survives in the current tree: `Concat_exp (a, b)`
lowers strictly pairwise (to_if1.ml:8804).

## 7. Worked example: levelB_i as returns-tree packing

levelB_i separates the three roles exactly:

- **Roots** (must materialize): `xre_i, xim_i` — the function's observable
  outputs.  Results are not intermediates; two allocations are the floor.
- **Essential stores** (cannot go away): `fft_4_2`'s 8 outputs per `k` — every
  result element is produced exactly once.  Only their ADDRESS is negotiable.
- **Pure shuffle** (all removable): the outer `catenate` over `j` (chunk
  stride `4·cards`), the `||` quarter permutation within a chunk, and the
  inner order-preserving gathers.  Their composition is affine address
  arithmetic:

```
are(j,k) -> xre_i[ j*4*cards + 0*cards + k ]
cre(j,k) -> xre_i[ j*4*cards + 1*cards + k ]
bre(j,k) -> xre_i[ j*4*cards + 2*cards + k ]
dre(j,k) -> xre_i[ j*4*cards + 3*cards + k ]      (+ im mirror)
```

**The pass**: visit the RETURNS from the roots down; flatten the catenate/`||`
forest (leaf-spine walk); assign each leaf its affine slice of the root; push
the (buffer, offset) destinations down into the enclosed loops' returns
clauses.  Layout information flows TOP-DOWN (roots dictate to leaves), where
today's code builds BOTTOM-UP (leaves materialize, shuffles copy upward).
Result: one j×k nest, 8 computations + 8 affine stores per iteration, 2
allocations, zero intermediate buffers.  The codegen target for a
destination-carrying leaf is the forall scatter (`at [offset + ..]`) — step 5
of §4 is what this pass EMITS.

Two boundaries of the transformation:

- **Level-to-level fusion is impossible in principle**, not just across the
  function boundary: the next level reads `xre[k+p0..p3]` — a global shuffle.
  A butterfly stage needs the whole previous level materialized.  So "2 buffers
  per level" is the packing pass's true optimum.
- **The last win belongs to uniqueness, not packing**: `old xre_i` dies when
  the new level is built (fanout 1 into the next iteration of the level loop),
  so refcount/liveness lets the for-initial PING-PONG two buffers total — the
  classic in-place FFT double-buffer.  Packing: O(N·packs) -> O(N) copies per
  level.  Uniqueness: 2·levels -> 2 allocations.
