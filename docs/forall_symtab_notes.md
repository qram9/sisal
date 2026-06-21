# Forall Symtab Notes

Expected symtab situation for the generator, body, and returns subgraphs and
their enclosing forall.

## Binding principle (generator, body, returns alike)

- **Every subgraph output is bound twice:**
  1. inside the subgraph that defines it — a name in that subgraph's local symtab;
  2. in the enclosing forall — a name in the forall's local symtab, with
     `val_def =` the subgraph's **compound node** (generator node / body node /
     returns node), never the forall's boundary node.
- **No shadowing is allowed — all names must be unique.** Each relayed output
  gets a **brand-new name** that was never bound before, in neither the parent
  nor the local symtab.
  - Example: a source `K := I` makes the body define `K`, and `K` is bound to a
    body output. In theory this output also gets a fresh, never-seen temp inside
    the body — say `__temp__K` — and the forall gets its own fresh temp — say
    `__temp_forall__Body0`.
- **This makes C lowering trivial — no cross-scope binding logic.** Because the
  names are unique, the subgraph lowering only needs to assign, inside its own
  block:

  ```c
  __temp_forall__Body0 = __temp__K;
  ```

  `__temp_forall__Body0` is declared in the enclosing (forall) scope, so once the
  subgraph's scope closes the enclosing graph already sees the value. No name can
  clash, so we never have to reconcile bindings across the subgraph/parent
  boundary.

## Generator subgraph

- Suppose we have `for i in 1, m dot j in 1, n`.
- Then, in the **generator's local symtab**, we will have:
  - `i` and `j` (the induction variables);
  - the newly added lower-bound and upper-bound temporary variables, bound to
    `m` and `n`.
- The **forall** encloses the generator.
- The **forall's local symtab** will hold copies of these variables (brand-new
  unique names, no shadowing):
  - In theory the names can be the same, but we must take care not to shadow any
    existing names in the forall — so each relayed output uses a fresh unique
    name.
- The `val_def` of these names will be the **generator node**, not the forall's
  boundary node.

## Body subgraph

- Suppose `for i in 1, m dot j in 1, n returns array_dv of i*j` (optionally with
  body lets, e.g. `K := i*j`).
- Then, in the **body's local symtab**, we will have:
  - `i` and `j` (and, for element/`at` loops, the elements and `at` indices) as
    **imported inputs** — `val_def = 0` (the body boundary), `def_port =` the
    body input port;
  - any **body-internal `:=` locals** (e.g. `K`), each a named node defined in
    the body;
  - **a local-symtab name for each body output** — just like the generator, the
    body must name every one of its outputs. If the output is `K`, it also gets a
    brand-new unique temp `__temp__K`.
- The **forall** encloses the body.
- The **forall's local symtab** will hold the body's outputs as fresh unique
  temps — `__temp_forall__Body0`, one per return clause.
- The `val_def` of these names will be the **body node** (body compound), not the
  forall's boundary node.
- Lowering: inside the body block emit `__temp_forall__Body0 = __temp__K;`.

## Returns subgraph

- Continuing `... returns array_dv of i*j` (one return clause; multiple clauses
  → one gather each).
- The **returns subgraph** contains one **gather** per clause; each gather reads:
  - an **index / placement** input (the axis — the induction variable today; an
    arbitrary placement expression under Sisal 2.0);
  - a **value** input (the body result relayed in).
- Then, in the **returns' local symtab**, we will have:
  - the imported inputs (axis/placement, value) named with `val_def = 0` (the
    returns boundary) on their input ports;
  - **a local-symtab name for each returns output** — just like the generator
    and body, the returns must name every one of its outputs (each gathered
    array), with a brand-new unique temp.
- The **forall's local symtab** will hold the returns outputs as fresh unique
  temps, one per clause.
- The `val_def` of these names will be the **returns node** (returns compound),
  not the forall's boundary node.
- Lowering: inside the returns block emit `__temp_forall__Ret0 = <returns local
  output temp>;`.

## Summary

All three subgraphs follow the same shape — **name every output locally, then
relay it to the forall under a fresh unique name bound to the subgraph's
compound** — and **no name is ever shadowed**, which is what lets the C lowering
be a plain per-output assignment with no cross-scope binding logic.
