# `for initial` — does the seed contribute? (survey + current state)

Status: current as of 2026-08-07. Companion to `loop_behavior_comparison.md`,
which states the rules; this file records which RETURNS forms actually obey
them, what was measured, and what is still outstanding.

---

## 1. The rule

The `initial` clause is **`body_0`** — the first element of every carried
value's history — and it therefore contributes to every RETURNS form.

Sisal 90 User's Guide §5.5 (`~/work/oldsisal/oldsisal/draft.pdf`, p56) gives the
execution order as `first_iteration; guard1; body1; returns1; …` and states that
"since the FIRST ITERATION always executes, the expression NEVER returns default
reduction values." So a zero-trip `value of X` is the seed, a zero-trip gather
is `[seed]`, and a zero-trip reduction is the seed rather than the reduction's
identity.

Sisal 2.0's Ch6 rules (initial values do not contribute; zero-trip last-value is
an error value; reductions give the identity) govern its *different*
`for..while..do` construct, which has no first-iteration concept. They do not
apply here — see `sisal_2_0_ch6.md` §6.1.2.

Only a **carry** has a `body_0`. A body temporary has no value at the seed, and
Sisal 1.2 does not admit one in RETURNS at all (OSC: `****ERROR Value name 'k'
undefined`). That distinction is load-bearing below.

---

## 2. Survey

Measured with seed `i := 10`, guard `i < 13`, body `i := old i + 1` — so the
body values are `11 12 13` — and cross-checked against OSC 13.0.3 (build recipe
in memory: prebuilt tree under `~/work/oldsisal/oldsisal/saved`, copy `bin` and
`lib/*` to a short dir, `TMPDIR=/tmp ./bin/osc -o prog prog.sis`; the banner
goes to stderr, so stdout line 1 is the first result).

| RETURNS form | result | seed | ours = OSC |
|---|---|---|---|
| `value of i` | `13` | n/a (last value) | yes |
| `value of sum i` | `46` = 10+11+12+13 | yes | yes |
| `value of product / greatest / least` | — | yes | yes |
| bare `array_dv of i` | `10 11 12 13` | yes | yes |
| `stream of i` | `10 11 12 13` | yes | yes |
| `array_dv(4) of i` (declared extent, scalar carry) | `10 11 12 13` | yes | our extension |
| `array_dv(3) of i*2` (an **expression**) | `22 24 26` | no — correct | 1.2 rejects the form |
| `array_dv(3) of r` (**array-valued** carry) | `2 4 3 6 0 0` | **no — gap** | — |

The zero-trip reduction rows are the decisive evidence, because there the seed
and the reduction identity differ:

| zero-trip loop | ours | OSC | identity (if the seed were skipped) |
|---|---|---|---|
| `i := 10; while i < 5`, `value of sum i` | 10 | 10 | 0 |
| `i := 7; while i < 5`, `value of product i` | 7 | 7 | 1 |
| `i := 99; while i < 3`, `value of greatest i` | 99 | 99 | — |
| `i := 10; while i < 5`, `array_dv of i` | `[10]` | `[10]` | `[]` |
| `i := 10; while i < 5`, `stream of i` | `[10]` | `[10]` | `[]` |

---

## 3. The declared extent is a SIZE DESCRIPTOR

`array_dv(n) of X` declares the size of the RESULT: slot 0 is the seed and the
loop fills `1..n-1`. Sisal 2.0 spells the same idea `array [size-descriptor] of`.

The extent exists for loops whose trip count the compiler cannot derive —
`m := old m * 4`, `while ~found & (i < array_size(period))`, psa's
`while to = from`. For those there is no compile-time count, which is why a
mismatch between the declared size and the actual iteration count is detectable
only at runtime. Declaring the extent is best practice generally, not only when
inference fails.

Before 2026-08-06 this form was the ONLY one in the compiler where the initial
clause did not contribute, and it did not merely exclude the seed — it
fabricated:

```
array_dv(3) of i,  0 trips  ->  0 0 0        while `value of` and bare gather gave 10
array_dv(5) of i,  3 trips  ->  11 12 13 0 0
array_dv(2) of i,  3 trips  ->  11 12        the third store went PAST the allocation, exit 0
```

Fixed in `1090500`: the scalar shaped gather now emits the same `body_0` tick
the bare path always had. Migration was 11 declared extents over 8 files
(`loop5`, `loop11s`, `loop17` ×3, `loop20`, `loop23s`, `mr_forinit`,
`shaped_gather`, `simple_fwdsweep` ×2), each `+1`, with each C reference
emitting its seed as element 0. Several read better afterwards: `loop5` and
`loop11s` now gather the whole `X[1..n]` rather than `X[2..n]`, and `loop23s`'s
`array_addh` lands the recurrence at its natural column indices instead of
shifted down one.

---

## 4. Where it lives

`src/backend/cpp/cpp_lower.ml`, the for-initial gather lowering:

- **bare path** — sizes itself from the TEST compare (`if is_carry then inc
  trip_count else trip_count`) and emits `@ if is_carry then store'` in the
  preheader. Has always done this.
- **scalar shaped path** — now `@ if is_carry then scalar_store`, the change in
  `1090500`.
- **array-element shaped path** — deliberately does NOT, see below.
- **streams** — a preheader `co_yield` plus a per-iteration one; see
  `stream_coroutine_lowering.md` §3a.

`slot` is `ctr++` in all non-placement cases, so the seed naturally takes slot 0
and the loop continues from 1.

---

## 5. Outstanding

Both remaining items are on the same runtime helper, and neither is a semantics
question any more.

**1. Array-valued carries do not collect their seed.**

```sisal
for initial i := 1; r := row(1);
while i < 3 repeat i := old i + 1; r := row(old i + 1);
returns array_dv(3) of r end for
```

gives `[2,4 | 3,6 | 0,0]` — the seed row `row(1) = [1,2]` is missing and the
third declared slot is never written, so it reads as a fabricated zero row.
`sisal_array_shaped_store` allocates lazily off the first element it sees, so a
preheader store leaves the descriptor empty; adding the tick there made
feo_fft's twiddle carries come out `size=0`, so it was reverted with the reason
recorded in the code. This is also why `feo_fft_parts2` gathers one row rather
than two.

**2. Trip count ≠ declared extent is unguarded, in both directions.**

- `trips > extent` — the store walks past the allocation. Silent heap
  corruption, exit 0.
- `trips < extent` — the tail keeps whatever `alloc_empty` left. The array is
  the size the user declared, so nothing downstream can tell the slots were
  never filled.

Since the extent exists precisely for loops with no derivable count, a runtime
check is the only check that can ever exist for the case the feature was built
for. Precedent for the shape: `35c5848`'s always-on carry-gather size assert.
Related: we have no runtime subscript checking at all — OSC reports
`ARRAY SUBSCRIPT VIOLATION [HIGH]` with function, line and index where we read
or write past a buffer silently.

---

## 6. Coverage

`forinit_shadow_dv`, `simple_backsub_dv`, `simple_fwdsweep_dv`, `firsttrue_dv`,
`shaped_gather_dv`, `mr_forinit_dv`, `loop5/11s/17/20/23s_dv`, `feo_fft_parts2`,
`zerotrip_expr_dv`, `forinit_history_dv`. All execute the generated C and
compare against a reference computed in the harness — compiling clean is not a
test, and `test/positive.t` / the `test/unit/*.sis` corpus only check that IF1
is emitted.
