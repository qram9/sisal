# Forall Lowering — Work Items

Tracking doc for the mechanical forall (generator / body / returns) lowering to C.

Goal: lower array-building `forall` loops mechanically (no heuristics, no
positional assumptions) by reading the IF1 structure — generator nodes drive
the loop, body produces named per-iteration values, returns gathers drive the
store. See also `forall_spec.md` (the target Sisal 2.0 model: recursive
generator + flat body + recursive returns, decoupled scatter/gather),
`forall_symtab_notes.md`, `forall_array_dv_lowering.md`.

## Done

- [x] **Generator publishes its outputs as named boundary outputs** (loop var,
      range bounds `lb`/`ub`), `val_def != 0` rule. (commit `ad39bd5`)
- [x] **Relay body results into RETURNS** by name: body outputs named
      `__forall_body_k` (bound to the body compound), imported into the RETURNS
      in-list; `body_inputs` pragma records the port range. (commit `ad39bd5`)
- [x] **Drop `get_ports_unified`** from the forall BODY and RETURNS graphs.
      (commits `ad39bd5`, `d1e41fb`)
- [x] **RANGEGEN exposes 3 output ports**: 0 = induction var, 1 = lower bound,
      2 = upper bound. Reverse symtab lookup `(RANGEGEN, 0/1/2)` -> `(I, lb, ub)`.
      (commit `d653d77`)
- [x] **Generator outputs defined by the generator compound** (`val_def = gn`),
      not the `__0` input boundary — symmetric with body results
      (`__forall_body_k -> (bx, k)`). (commit `d1e41fb`)
- [x] **Backend loop-var binding driven off generator nodes**: RANGEGEN out 0/1/2
      = `lb+idx`/`lb`/`ub` (per axis -> dot); DV_SCATTER out 0/>=1 =
      `A.data[idx]`/`A.lower_bound+idx`. (commit `d1e41fb`)
- [x] **Per-axis lower bound for `dot`** (each axis uses its own `lb`).
      (commit `d1e41fb`)
- [x] **RETURNS gather index = the classified placement (not `axis_name`).**
      The returns now imports the placement coordinate found by NODE+PORT
      (`RANGEGEN:0`, or `DV_SCATTER`/`ASCATTER:port>=1` for `at`), laying the
      `gn:placement -> returns:gather-index` edge. Fixes the `at` case, where
      `axis_name` (the `In_exp` name) was wrongly the element `X`; for at3 the
      `DV_GATHER` index is now `I` (`gn:0`), not `X`. Range/`for x in A` (no
      `at`) unchanged (fall back to `axis_name` only when no classified
      placement exists). `to_if1.ml` `build_forloop`.
- [x] **Range bounds `lb`/`ub` land on RETURNS too.** Since `I` is bound as the
      induction var together with its `lb`/`ub` (RANGEGEN:1/2, one pair per
      `dot` axis), the returns now also imports those bounds (classified by
      NODE+PORT) as boundary inputs bound to the generator compound — so the
      mechanical store has `lb`/`ub` in scope for `result[I - lb]` and sizing
      `ub - lb + 1`. Order is load-bearing: placement@0, body relay@1.., then
      `lb`/`ub` appended on later ports (no internal gather edge; available to
      the backend). f1 → lb@2/ub@3; dot2 → both pairs @2..5. `to_if1.ml`.

Verified: f1 `[1..5]`, at3 `[10 40 90]`, dot (incl. distinct lower bounds),
decldef body — all correct; dv suite 12 groups pass / 4 pre-existing fails.

## Open

- [ ] **No shadowing — all names must be unique.** Every subgraph output is
      bound twice (once in its own subgraph, once in the enclosing forall), and
      each relayed name must be **brand-new** — never seen before in the parent
      or local symtab. Mint fresh unique temps at both levels (e.g. `__temp__K`
      in the subgraph, `__temp_forall__Body0` in the forall) so the C lowering is
      a plain per-output assignment with no cross-scope binding logic. Applies to
      generator, body, and returns outputs alike. (Current registration does an
      unconditional `SM.add`, which can shadow a pre-existing name — to fix.)
      See `forall_symtab_notes.md`.
- [ ] **Name body & returns outputs locally, then relay** — symmetric with the
      generator. Each body output and each returns output must first be a name in
      its own subgraph's local symtab, then relayed to the forall under a fresh
      unique temp bound to the subgraph compound. (Today `__forall_body_k` is
      minted directly in the forall, not first named in the body; returns outputs
      aren't named-then-relayed yet.) See `forall_symtab_notes.md`.
- [ ] **DV_DIMENSION shape-source is overloaded.** In the `array_dv` RETURNS,
      the returns axis import feeds *both* the `DV_GATHER` index *and*
      `DV_DIMENSION:0` (which wants the source `array_dv` to copy its shape) off
      the same input port — so `DV_DIMENSION` gets the placement scalar, not the
      source array. Pre-existing and benign today (the backend sizes the result
      from the generator extent via `alloc_empty`, not from `DV_DIMENSION`), but
      the shape source should be a distinct input (the source array) once the
      store is driven mechanically off the gather. Was `X`, now `I` after the
      placement fix — equally wrong for the shape; harmless because unused.
- [ ] **RETURNS store: multi-output, mechanical.** Drive the store from the
      RETURNS gather nodes + `__forall_body_k` relays (one array per gather),
      retiring the `body_elem_port` type heuristic and the single-output
      assumption. Test: `returns array_dv of i, array_dv of i*i`.
- [x] **Retire positional generator->body wiring.** Removed `add_edge gn 0 bx
      next_bx` and the `wire_streams` gen:p -> bx:(p-1) loop. They duplicated the
      name-driven import (`wire_all_syms_to_compound bx`), and because the import
      had already filled bx:0, the duplicate `gn:0` landed on a free port (bx:1)
      -- a phantom body input the backend materialized as an unused
      default-typed (`float`) variable (`v_BODY_..._n__0_p1_o`). The name import
      reads each subgraph's boundary in-list and is sufficient/authoritative.
      Fixed the phantom for decldef bodies (body1) and `at` loops (at3, was a
      `p2_o` float); dv suite still 12/4. `to_if1.ml` `build_forloop`.
- [ ] **Retire `wire_all_syms_to_compound`** in favour of explicit edges from the
      forall symtab (deferred).
- [ ] **`lower_simple` materialize RANGEGEN outputs 1/2** (`lb`/`ub`) so the
      backend can read them off the ports rather than following input edges
      (the purer node-driven form).

## Backlog

### Toward the `forall_spec.md` target (recursive generator + recursive returns)

- [x] **`cross` I/J alias fixed** in the current nested-FORALL form (re-bind
      generator outputs to `gn` + recurse against re-bound `forall_gr`); inner
      body now computes `i*j`. IF1 verified line by line. (The nested-FORALL
      *shape* is still the old form — see the restructure items below.)
- [ ] **Recursive GENERATOR** — replace nested FORALLs with one generator that
      nests sub-generators (one level per scatter axis) and exposes the full index
      tuple by name to a single body + single returns. Moves the recursion from
      `build_forloop` into the generator builder. (`forall_spec.md` §4.)
- [ ] **Recursive RETURNS** — mirror of the generator: nested gathers, one level
      per *result* dimension (depth = the size-descriptor rank, independent of
      scatter rank). Kills the empty-in-list `add_return_gr` outer-returns path;
      everything name-driven like the base case. (`forall_spec.md` §4.)
- [ ] **Returns size-descriptor + `at`** — parse and honor `array[[size-desc]] of
      expr [at [at-exp…]]`: ranks/sizes from the descriptor, placement from `at`;
      default bare `array of` flattens to rank-1 even over `cross`. Enables the
      transpose-by-placement idiom. (`forall_spec.md` §3.)
- [ ] **Backend nested lowering** — lower the nested generator/returns into a
      rank-k loop nest (today the nested `FORALL` body slot makes `lower_forall`
      `failwith "no BODY"`).

### Other

- [ ] **Masks** (`when` / `unless`) — gather mask port. (Disallowed with `at`/
      size-descriptor per spec §3 — 1-D only, to keep results rectangular.)
- [ ] **Reduce** (`value of [reduction]`) — mechanical path (currently special-
      cased: argmax/argmin/sum/product/least/greatest).
- [ ] **Parallel emit**: make the loop strategy a single pluggable point
      (serial -> GCD `dispatch_apply` / `vectorize` pragma / Metal); default GCD
      over OpenMP on darwin. Pick per-loop via a cost heuristic later.
- [ ] Front-end diagnostic for case-insensitive self-shadow (`for a in A`).
