# Forall Lowering Spec — Sisal 2.0 decoupled scatter/gather

The target model for lowering Sisal `for … returns … end for` to IF1.

**Sources.** SISAL 2.0 Language Manual (`sisal_2_0.pdf`, Ch 6 "For Expressions",
§6.1 Control and §6.2 Result Values — esp. **§6.2.3 "Array of"**; printed
pp 48–56). Feo, *Arrays in Sisal* (`arrays_in_sisal.pdf`, pp 7–8). See also
`forall_symtab_notes.md`, `forall_lowering_workitems.md`,
`forall_array_dv_lowering.md`.

---

## 1. The model: scatter and gather are DECOUPLED

Sisal 1.2 **couples** work-scatter and result-gather — the range generator
dictates the result's order, size, and structure. Feo calls this "one flaw …
results in confusion and programming errors" (the transpose mistake).

Sisal 2.0 **decouples** them:

- the **generator** (the `for`-top) governs **scatter** — it enumerates the
  index space;
- the **returns clause** (the `for`-bottom) governs **gather** — it assembles
  the results and says *where* each iteration's value lands.

The returns clause carries its own **size-descriptor** (ranks + sizes) and
**`at`** (placement). The generator never touches them. That separation is the
whole point.

---

## 2. Grammar (Sisal 2.0 manual, Ch 6)

### 2.1 Control / SCATTER — the `for`-top (§6.1)

```
in-exp-list ::= in-exp [ dot   in-exp ]…           -- zip
              | in-exp [ cross in-exp ]…            -- cartesian
in-exp      ::= value-id in expression [ at [ index-id-list ] ]   -- array/stream scatter
              | value-id in [ triplet ]                            -- range scatter
triplet     ::= [ lo ] .. [ hi ] [ .. stride ]
                  -- lo default 1; hi default ±inf (sign of stride); stride default 1, never 0
index-id-list ::= { .. | value-id } [ , { .. | value-id } ]…
```

- **`dot`** = zip: all in-exps must yield the **same** number of values; indices
  paired (`[1,3],[2,4]`).
- **`cross`** = Cartesian/outer product: lengths need **not** match; all pairs
  (`[1,3],[1,4],[2,3],[2,4]`). Body order is left-to-right (first in-exp is the
  **outer** loop). A later cross axis may reference an earlier index
  (`j in [i..4]`).
- **`at` on the scatter** introduces *scatter indices* = the index positions of
  the scattered values. For an n-D array scatter, supply one `value-id` or empty
  triplet per scattered dimension (`for X in A at [I,..,..]` scatters planes; `I`
  is the first-dim index; an absent `at` scatters all dimensions).

### 2.2 Result / GATHER — the `for`-bottom (§6.2)

```
for-bottom ::= returns return-exp [ , return-exp ]… end { for | while | until | do }
return-exp ::= array [ [ size-descriptor ] ] of expression [ filter | at [ at-exp [, at-exp]… ] ]
             | stream of expression [ filter ]
             | expression [ filter ]            -- "last value" / predefined reduction
             | suffix ( value-id )
filter     ::= when expression | unless expression
```

- **size-descriptor** = triplets giving the result's dimensions. Default lower
  bound 1; **upper bound optional** (omitted ⇒ extent taken from the contributing
  values); stride always 1; no named triplets; no distributed/carried names in
  the size expressions.

---

## 3. `array of` shape rules (§6.2.3) — the decoupling knobs

The packaging order (absent `at`) equals body-execution order. Then:

- **Default — no descriptor or a 1-D descriptor ⇒ rank-1, regardless of `cross`.**
  `for i in [1..2] cross j in [3..4] returns array of i*j` builds the flat 1-D
  `[3,4,6,8]` (lower bound 1). This is the **changed default** vs Sisal 1.2 (the
  generator no longer dictates result rank). Contributing values may be any type
  (ragged arrays OK for 1-D).
- **Descriptor rank == number of scatter dims ⇒** each scatter dim becomes a
  result dim (extent = number of values).
  `for x in A at [i,j] returns array[0..,0..] of g(x,k)` → 2-D, extents from #i, #j.
- **Descriptor rank n > k scatter dims ⇒** the first k dims come from the scatter
  extents; the last n−k come from the contributing values' extents (which must be
  (n−k)-dimensional with identical extents).
  `returns array[0..,0..,1..,1..] of g(x,k)`.
- **Iteration control + carried values ⇒** contributing values must be
  (descriptor−1)-dimensional and the same size; the first dim's extent = number
  of iterations, the rest from the contributing expressions.

### `at` (placement)

A position specifier — one and only one value per result position. **`at`
requires a full size-descriptor with ALL upper bounds present** (not optional
here), and the number of position parts must match the result rank.

- `returns array[4..7] of I*10 at [4+I-1]` → result lower bound 4.
- `returns array[1..2,1..2] of V at [I,..]` → place each body vector into a row.
- **Transpose — the canonical win of decoupling:**
  `for i in 1,n cross j in 1,m returns array[1..m,1..n] of X[j,i] at [j,i]`
  → an m×n result by **placement**, immune to generator order. (The coupled
  Sisal 1.2 form gives the wrong n×m.)

### Filters and defaults

- **Masking (`when`/`unless`)** is **not** allowed with `at` or a size-descriptor
  — only on 1-D arrays — to preserve rectangularity (= the flat `array_dv` model).
- **Default value:** no descriptor ⇒ empty array if the body never runs; with a
  descriptor ⇒ an error value.

---

## 4. Target IF1 structure — recursive GENERATOR + flat BODY + recursive RETURNS

The decoupling realized in IF1. Each for-all is **one** GENERATOR + **one** BODY
+ **one** RETURNS. The GENERATOR and RETURNS each carry **their own** nesting; the
body is flat.

```
FORALL
  GENERATOR   (recursive — SCATTER: enumerate the index space;
               nests one level per scatter axis)
       RANGEGEN / SCATTER [axis 0]
         (nested) GENERATOR
            RANGEGEN / SCATTER [axis 1] …
       exposes the index tuple (i, j, …) + bounds upward, BY NAME

  BODY        (single, flat — the per-point value expression; reads i, j;
               never nests)

  RETURNS     (recursive — GATHER: assemble the result;
               nests one level per RESULT dimension)
       GATHER [dim 0]
         (nested) RETURNS
            GATHER [dim 1] …
       consumes the `at` placement indices + the body value
```

- GENERATOR and RETURNS are **mirrors**, but their nesting depths are
  **independent**: the returns' depth = the size-descriptor's rank, which may
  differ from the scatter rank (see §3, case 3).
- **`dot`** is the same skeleton with the generator/returns nesting collapsed to a
  single **zipped** level (axes advance in lockstep). **`cross`** uses cartesian
  nesting (outer/inner counting). Zip-vs-cartesian is a property of the
  **generator**; result rank + placement are a property of the **returns**.
- Because every index crosses a boundary **by name** out of a single generator,
  the cross-scope node-id aliasing of the nested-FORALL form cannot arise, and the
  body slot is always a real `BODY` (no nested `FORALL`).

---

## 5. Mapping to `array_dv` (flat arrays)

Sisal 2.0 flat arrays == our **`array_dv`** (dope vector: rank, dims, lower
bounds, contiguous data). Default `array_dv of` over `cross` flattens to rank-1
(§3 default); multidimensional needs a size-descriptor. A for-all must never
build `array_dv[array_dv]` — normalize to one rank-N flat DV. See
`nested_array_dv_invariant` (memory).

---

## 6. Current state vs. target (migration)

**Today:** `cross` is lowered as **nested FORALLs** (a whole forall in the body
slot), not a nested generator/returns. The single/inner (base-case) path is
name-driven and clean; the recursive (cross) path was the old, awkward one.

**Done on this branch:**
- RETURNS gather index = the classified placement (fixes `at`);
- range bounds `lb`/`ub` land on RETURNS;
- retired the positional gen→body wiring (phantom body port);
- fixed the nested-`cross` `I`/`J` alias: re-bind generator outputs to the
  generator compound `gn`, and recurse against the re-bound `forall_gr`;
- de-duped the generator install into `add_generator_to` (proven byte-identical
  across all 360 corpus IF1 files).

**TODO toward this spec:**
- recursive **GENERATOR** (nest sub-generators; keep one body + one returns)
  replacing the nested-FORALL form;
- recursive **RETURNS** (nested gathers) driven by the size-descriptor;
- parse and honor the returns **size-descriptor** and **`at`** (ranks / sizes /
  placement);
- backend: lower the nested generator/returns into a **rank-k loop nest**
  (today the nested `FORALL` body slot makes `lower_forall` `failwith "no BODY"`).

See `project_array_roadmap` (memory): Phase 1 = get Sisal 1.2 solid; Phase 2 =
the Sisal 2.0 decoupled scatter/gather described here.
