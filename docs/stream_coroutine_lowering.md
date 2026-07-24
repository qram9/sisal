# Stream Lowering via C++20 Coroutines

How Sisal `stream[T]` values are compiled to C++. Read this together with
`docs/loop_behavior_comparison.md`, which defines the `for initial` gather
semantics that the stream lowering must reproduce.

---

## 1. Why coroutines

A Sisal stream is a lazily-produced, single-consumption-friendly sequence.
Earlier we lowered streams to an eager ring buffer (`sisal_stream_t` with
`head`/`tail`/`capacity` and an 8-byte slot stride). That model forced every
producer to materialize the whole sequence up front and was the source of a
stride-mismatch bug (elements written at an 8-byte slot stride but read back at
the element's natural stride). It also could not express a producer that yields
"one more" lazily (`addh`/`addl`) without copying.

Streams now lower to a **C++20 coroutine generator**, `sisal_generator<T>`
(defined in `runtime/sisal_runtime.h`). A stream-producing Sisal loop becomes a
coroutine that `co_yield`s each element; consumers pull elements on demand. This
matches the lazy semantics directly and removes all manual slot arithmetic — the
generator's own accessors are the only way elements are read.

---

## 2. The runtime type: `sisal_generator<T>`

```
runtime/sisal_runtime.h
```

Key pieces:

- **`promise_type`** — `initial_suspend()` returns `std::suspend_always`, so the
  coroutine is **lazy**: constructing the generator runs *no* body code; the
  first element is produced only on the first `resume()`. `yield_value` stashes
  the yielded value in `current_value`.

- **Shared `State`** — holds the `std::coroutine_handle`, an `initiated` flag,
  and a **memoizing `std::vector<T> buffer`**. `State` is held through a
  `std::shared_ptr`, so **copies of a generator share one underlying coroutine
  and one buffer**. The handle is `.destroy()`ed when the last copy dies.

- **Pull-on-demand + memoization** — `ensure_initiated`, `advance`, `current`,
  `is_empty_pred`, `get_size`, and `sisal_stream_get` all resume the coroutine
  as needed and push each freshly-yielded value into `buffer`. Because values
  are buffered, re-reading an index is cheap, `rest` is just *copy + bump the
  per-copy `index`*, and a generator can be consumed more than once.

- **`SizeHelper size`** — a member object exposing `.size` on a generator. On use
  it runs the coroutine **to completion** (buffering everything) and returns the
  count, with implicit conversions and `==` overloads so `S.size` reads like an
  array's `.size` field. NOTE: touching `.size` (or `sisal_stream_get`) forces
  the producer to completion, so the current lowering is **eager over any input
  stream** it iterates. This is correct for finite streams (the sieve) but would
  need rework to keep a genuinely infinite input lazy.

- **Stream API on the generator** — `sisal_stream_first` (= `current`),
  `sisal_stream_rest` (copy + advance index; persistent/functional, shares the
  buffer), `sisal_stream_empty_pred`, `sisal_stream_get(g, k)` (random index),
  `sisal_stream_empty<T>()` (an empty generator). `sisal_stream_addh`/`addl` are
  **themselves coroutines** that re-`co_yield` the source then the new element
  (or vice-versa) — they build a *new lazy stream* rather than mutate a buffer.

---

## 3. The backend: how a stream-returning loop is emitted

`src/to_apple/apple_lower.ml`. Two loop forms produce streams; both wrap the
loop body in an **immediately-invoked lambda coroutine** whose return type is the
generator:

```cpp
res = [ /* params */ ]() -> sisal_generator<int32_t> {
    ... loop with co_yield ...
}( /* args */ );
```

### 3a. `for initial ... returns stream of X` (`lower_for_initial`)

A per-iteration `co_yield X` plus a preheader seed `co_yield`, reproducing the
`for initial` gather rules from `docs/loop_behavior_comparison.md`:

- **Rule 1** — the `initial` seed is `co_yield`ed once before the guard, so it is
  gathered even on a zero-trip loop.
- **Rule 2** — the body computes the new carry and `co_yield`s it *before* the
  guard is re-tested, so the final out-of-bounds value (the one that fails the
  test) is gathered.

Example — `Integers` (`for initial I:=3; while I<Limit-1 repeat I:=old I+2;
returns stream of I`) yields `3` (seed), then `5,7,…` and the final out-of-bounds
value: `Integers(15) = 3 5 7 9 11 13 15`, `Integers(30) = 3 … 27 29`, zero-trip
`Integers(4) = [3]`.

### 3b. `for X in S returns stream of E [unless mask]` (`lower_forall`)

A forall over a source (array or stream). The generator level emits a counted
loop and reads each element through the generator accessor — **never** through
raw `.data` indexing:

```cpp
for (int32_t __k = 0; __k < (int32_t)S.size; __k++) {
    I = sisal_stream_get<int32_t>(S, __k);   // coroutine accessor, no stride math
    ... compute mask ...
    if (mask) co_yield(E);                    // masked stream gather
}
```

Example — `Filter(S,M) = for I in S returns stream of I unless mod(I,M)=0`
drops multiples of `M`.

---

## 4. THE load-bearing gotcha: capture lifetime

A lambda that contains `co_yield` is a coroutine, and **its captures live in the
closure object, not the coroutine frame.** With an immediately-invoked lambda:

```cpp
res = [=]() -> sisal_generator<int> { ... uses LIMIT ... }();   // WRONG
```

the closure temporary is destroyed the instant the call returns — which is at
`initial_suspend`, *before any body code runs*. On the next `resume()`, every
captured variable (`LIMIT`, an input stream `S`, …) is **dangling**. The
observed symptom was a loop that produced only its seed and then reported
`done`, because the guard `I < LIMIT-1` was reading garbage.

**Fix (both wrapper sites):** forward every free enclosing variable as a
**by-value coroutine parameter**. Coroutine *parameters* are copied into the
coroutine frame and live exactly as long as the coroutine:

```cpp
res = [](auto v_g1_n__0_LIMIT) -> sisal_generator<int> { ... }(v_g1_n__0_LIMIT);  // RIGHT
```

`auto` params sidestep having to reconstruct each variable's C type — deduction
from the argument gives the exact type, and by-value means a frame copy.

`collect_free_coro_vars` (top-level in `apple_lower.ml`) computes the free set:
walk the body's C-AST, collect referenced identifiers, subtract those declared
inside the body. The collector keys on the compiler's naming convention — **every
generated variable is `v_`-prefixed** — so type-name ids emitted as `C.Id`
(`int32_t`, `sisal_generator<int32_t>`) and `__`-prefixed loop counters are
naturally excluded, and function names (the string in `C.Call`) are never `Id`
nodes to begin with. The same helper is used by both `lower_forall` (§3b) and
`lower_for_initial` (§3a).

Caveat: the collector only sees *structured* C-AST. If a loop body ever emits a
`C.Raw` string that references an enclosing `v_` variable, that reference is
invisible to the collector and would dangle again. Keep stream-loop bodies free
of `Raw` references to enclosing vars (or extend the collector to scan `Raw`).

---

## 5. End-to-end reference: Sieve of Eratosthenes

`test/e2e/stream_sieve_dv.sis` composes all three pieces — `Integers` (§3a),
`Filter` (§3b), and a `main` post-test (`repeat … until stream_empty`) loop that
carries a stream. `Sieve(20) = 2 3 5 7 11 13 17 19`; larger limits include the
final out-of-bounds integer when it is prime (`Sieve(30)` includes `29`) because
`Integers` generates it per Rule 2 and it survives filtering.

Tests (all in the dv e2e suite): `stream_simple_dv` (a stream literal),
`stream_loop_dv` (a forall stream), `stream_integers_dv` (a `for initial`
stream, with a reference model of Rules 1+2), and `stream_sieve_dv` (the full
composition).
