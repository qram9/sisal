# Splitting `dv_run_all.cpp`

Status: **PROPOSAL.** Nothing moved yet. Grounded in measurements taken
2026-08-15 against `dv_run_all.cpp` at 22,548 lines / 379 groups / 386 test
functions.

---

## 1. Why

**Compile cost, measured.** The harness translation unit alone — no generated
code, no link — takes **633 ms** for one group. Sisal codegen for a `.sis` is
**10 ms** by comparison. The runner rebuilds that TU once per group, so the
suite pays 379 x 633 ms ~= **240 s of CPU** compiling test functions that are
`#ifdef`-ed out. At 14 workers that is ~17 s of the ~100 s wall time, and it
scales linearly with every group added.

**Findability.** 386 test functions in one file. Nothing indicates where a
group's assertions live except grep.

**The census problem.** A reference implementation written inline in a test body
is structurally indistinguishable from a hardcoded constant — same file, same
indentation, no marker. That is precisely why classifying "which groups have a
reference" has been unreliable: a heuristic can only guess, and hand-reading
22.5k lines is the only certain method. Splitting does not fix this by itself,
but it gives each group a home where a `*_ref.h` can sit next to it and be
visible in a directory listing.

---

## 2. Why it is safe

The structure makes this close to mechanical:

- **1136 `#ifdef TEST_*` blocks**, and the runner compiles with **exactly one**
  `-DTEST_<MACRO>` (`run_dv_e2e.sh:52`). Everything else in the file is
  preprocessed away already.
- The file has four clean strata:

  | lines | content |
  |---|---|
  | 1–23 | includes (system, 5 `*_ref.h`, `dv_rank8_slices_harness.h`) |
  | 24–~2070 | `extern "C"` declaration blocks, one `#ifdef` per group |
  | ~2076–2290 | shared helpers: `check`, `make_*`, `ai`/`ad`/`af`/`ab`, `near_*` |
  | ~2290–21270 | the 386 test functions, one `#ifdef` per group |
  | 21271–22549 | `main()` — 387 dispatch blocks |

- Because only one macro is ever defined, **duplicate type names across groups
  are already legal and stay legal**. `struct FUNC_MAIN_results` is redefined in
  many blocks (`TEST_FEO_FFT_DV` and `TEST_FEO_FFT` both define it); only one
  is ever active. Grouping several such blocks into one part file changes
  nothing, since still only one is active per compile.

---

## 3. Hazards, and how each is handled

1. **Shared helpers.** `check` (and the pass/fail counters it updates),
   `make_int_arr`, `ai`, `near_d` and friends sit at top level and are used by
   most tests. They must move to a common header, not be duplicated — the
   counters in particular must remain a single definition.
2. **`main()` must exist exactly once per binary.** Put it in the common header
   as a thin body that calls `run_active_test()`, and have each part define
   `run_active_test()` containing only its own groups' dispatch chain. One part
   is compiled per build, so exactly one definition exists.
3. **The runner must find the right part.** `run_dv_e2e.sh` uses a single
   `${HARNESS}` variable, so this is a one-line change. Prefer deriving the part
   by grep (`grep -l "test_<name> (" test/e2e/harness/dv_part_*.cpp`) over a
   hand-maintained manifest, so it cannot drift; cache the mapping in a
   generated file for speed.
4. **The parallel runner** (`run_dv_e2e_parallel.py`) parses `run_group` lines
   out of the `.sh`. If the `run_group` signature is left unchanged, it needs no
   edit — another reason to derive the part rather than add an argument.
5. **`positive.t` and cram** are untouched: they only compile `.sis` to IF1 and
   never reference the harness.

---

## 4. The split protocol

The invariant at every step: **the suite's per-group output is byte-identical to
what it was before the split.** Not "still 379 passing" — identical text, so a
check that silently stopped running is caught.

**Step 0 — golden.** Capture per-group stdout for all 379 groups into
`test/e2e/golden/<GROUP>.txt`. This is the only thing that makes the rest
verifiable, and it is worth keeping afterwards as a regression baseline.

**Step 1 — extract the common header.** Move includes + shared helpers +
`main()` into `test/e2e/harness/dv_harness.h`; `dv_run_all.cpp` includes it and
otherwise stays whole. Re-run, diff against golden. This step alone must be
green before any partitioning — it is where the helper/counter mistakes surface.

**Step 2 — halve, verify, repeat.** Split the test functions (with their
matching extern blocks and dispatch entries) into two files at an `#ifdef`
boundary. Re-run, diff against golden. Then split each half. Continue:

```
1 -> 2 -> 4 -> 8 -> 16 -> 32 parts
386 test fns / 32 ~= 12 per part
```

Stop at 32 (~12 each) or 26 (~15 each); either satisfies the target. Five
halvings, each a separate commit, each verified against the same golden.

**Why halving rather than one 26-way cut:** if the output diverges, the culprit
is confined to the one file just split, and the previous commit is a known-good
state to bisect from. A single 26-way cut gives no such bracket — a broken
helper reference or a dropped dispatch entry would have to be hunted across the
whole tree at once.

**Step 3 — order.** Group order in the suite output changes if parts are
enumerated differently. Either keep `run_group` order authoritative in the `.sh`
(preferred — it is already the order the goldens were captured in), or sort both
sides before diffing.

---

## 5. Target layout

```
test/e2e/harness/
    dv_harness.h        includes, shared helpers, counters, main()
    dv_part_01.cpp      externs + tests + run_active_test() for ~12 groups
    ...
    dv_part_32.cpp
    parts.index         generated: GROUP -> part file
test/e2e/golden/
    <GROUP>.txt         captured stdout, the split's invariant
test/e2e/*_ref.h        reference implementations (5 today)
```

`dv_run_all.cpp` disappears at the end of step 2, not before.

---

## 6. Expected payoff

- Harness TU per group drops from ~22.5k lines to ~700–900 (its own tests plus
  the shared header). Compile should fall from 633 ms toward ~150 ms, cutting
  roughly 180 s of the suite's CPU and ~13 s of its wall time.
- Adding a group touches one small file instead of a 22.5k-line one, which also
  removes a standing merge-conflict surface.
- Each part becomes the natural home for that group's `*_ref.h`, so "does this
  group have a reference?" becomes answerable by looking rather than by
  classifying.

## 7. What this does not do

It does not make the suite end-to-end in the sense of compiling a Sisal program
to an executable and checking what it prints. The generated code is a library of
`extern "C"` functions and the harness supplies `main()`; that stays true after
the split. It also does not by itself write any missing references — it only
makes their absence visible.
