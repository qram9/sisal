# `for initial` — does the seed contribute? (cases, measurements, current state)

Status: current as of 2026-08-07. Companion to `loop_behavior_comparison.md`,
which states the rules; this file records the cases that were run, what each
produced here and under OSC 13.0.3, and what is still outstanding.

Every program below is complete and runnable. OSC recipe: a prebuilt tree
exists at `~/work/oldsisal/oldsisal/saved` — copy `bin` and `lib/*` into a short
directory, then `TMPDIR=/tmp ./bin/osc -o prog prog.sis`. `TMPDIR` is
load-bearing: the default macOS tempdir blows the frontend's 127-char total
command-line limit and `if1ld` dies with `CAN'T OPEN <tmp>.if1` *after* the
frontend reports 0 errors. The `SISAL 1.2 V13_0_3` banner goes to **stderr**, so
stdout line 1 is the first result. For OSC, `array_dv` becomes `array` and
`double` becomes `double_real`.

---

## 1. The rule

The `initial` clause is **`body_0`** — the first element of every carried
value's history — and it therefore contributes to every RETURNS form.

Sisal 90 User's Guide §5.5 (`~/work/oldsisal/oldsisal/draft.pdf`, p56) gives the
execution order as `first_iteration; guard1; body1; returns1; …` and states that
"since the FIRST ITERATION always executes, the expression NEVER returns default
reduction values". So a zero-trip `value of X` is the seed, a zero-trip gather
is `[seed]`, and a zero-trip reduction is the seed rather than the reduction's
identity.

Sisal 2.0's Ch6 rules (initial values do not contribute; zero-trip last-value is
an error value; reductions give the identity) govern its *different*
`for..while..do` construct, which has no first-iteration concept. They do not
apply here — see `sisal_2_0_ch6.md` §6.1.2.

Only a **carry** has a `body_0`. A body temporary has no value at the seed, and
Sisal 1.2 does not admit one in RETURNS at all (OSC: `****ERROR Value name 'k'
undefined`). That distinction is load-bearing in case D below.

---

## 2. Case A — every form on one loop

Seed `i := 10`, guard `i < 13`, body `i := old i + 1`, so the body values are
`11 12 13`.

```sisal
define Main
type Ints = array_dv[integer];
function row(k : integer returns Ints)
  for j in 1, 2 returns array_dv of j * k end for
end function
function Main(returns integer, Ints, Ints, integer, Ints, Ints)
  let
    fv   := for initial i := 10; while i < 13 repeat i := old i + 1;
            returns value of i end for;
    decl := for initial i := 10; while i < 13 repeat i := old i + 1;
            returns array_dv(4) of i end for;
    bare := for initial i := 10; while i < 13 repeat i := old i + 1;
            returns array_dv of i end for;
    red  := for initial i := 10; while i < 13 repeat i := old i + 1;
            returns value of sum i end for;
    expr := for initial i := 10; while i < 13 repeat i := old i + 1;
            returns array_dv(3) of i * 2 end for;
    arr  := for initial i := 1; r := row(1);
            while i < 3 repeat i := old i + 1; r := row(old i + 1);
            returns array_dv(3) of r end for
  in fv, decl, bare, red, expr, arr end let
end function
```

Measured:

```
value of i                   13
array_dv(4) of i    [decl]   size=4 : 10 11 12 13
array_dv of i       [bare]   size=4 : 10 11 12 13
value of sum i               46
array_dv(3) of i*2  [expr]   size=3 : 22 24 26
array_dv(3) of r    [array carry]  size=6 : 2 4 3 6 0 0
```

`decl`, `bare` and `red` take the seed. `expr` does not, and should not — it
gathers an expression, not a carry. `arr` does not, and should — see §6.

---

## 3. Case B — zero-trip, where the seed and the default differ

```sisal
define Main
type Ints = array_dv[integer];
function Main(returns integer, Ints, Ints)
  let
    fv   := for initial i := 10; while i < 5 repeat i := old i + 1;
            returns value of i end for;
    bare := for initial i := 10; while i < 5 repeat i := old i + 1;
            returns array_dv of i end for;
    decl := for initial i := 10; while i < 5 repeat i := old i + 1;
            returns array_dv(3) of i end for
  in fv, bare, decl end let
end function
```

Measured, after `1090500`:

```
value of i = 10
bare     size=1: 10
decl(3)  size=3: 10 0 0
```

`value of` and the bare gather give the seed. `decl(3)` places the seed at slot
0 and leaves the two slots the extent over-declared unwritten — see §6, item 2.
Before `1090500` `decl(3)` gave `0 0 0`: no seed and three fabricated slots.

---

## 4. Case C — reductions, including the zero-trip cases

These are the decisive ones: skipping the seed would give the reduction's
**identity**, which is a different number from the seed.

```sisal
define Main
function Main(returns integer, integer, integer, integer, integer, integer)
  let
    s   := for initial i := 10; while i < 13 repeat i := old i + 1;
           returns value of sum i end for;
    p   := for initial i := 2;  while i < 4  repeat i := old i + 1;
           returns value of product i end for;
    zs  := for initial i := 10; while i < 5  repeat i := old i + 1;
           returns value of sum i end for;
    zp  := for initial i := 7;  while i < 5  repeat i := old i + 1;
           returns value of product i end for;
    g   := for initial i := 99; while i < 3  repeat i := old i + 1;
           returns value of greatest i end for;
    l   := for initial i := 1;  while i < 4  repeat i := old i + 1;
           returns value of least i end for
  in s, p, zs, zp, g, l end let
end function
```

| expression | history | ours | OSC | with seed | without (identity) |
|---|---|---|---|---|---|
| `sum i` | 10,11,12,13 | 46 | 46 | 46 | 36 |
| `product i` | 2,3,4 | 24 | 24 | 24 | 12 |
| `sum i`, zero-trip | 10 | 10 | 10 | 10 | **0** |
| `product i`, zero-trip | 7 | 7 | 7 | 7 | **1** |
| `greatest i`, zero-trip | 99 | 99 | 99 | 99 | — |
| `least i` | 1,2,3,4 | 1 | 1 | 1 | 2 |

---

## 5. Case D — streams

```sisal
define Main
type IStream = stream[integer];
function Main(returns IStream, IStream)
  let
    run := for initial i := 10; while i < 13 repeat i := old i + 1;
           returns stream of i end for;
    zt  := for initial i := 10; while i < 5 repeat i := old i + 1;
           returns stream of i end for
  in run, zt end let
end function
```

```
ours   running = 10 11 12 13      zero-trip = 10
OSC    [ 1,4: 10 11 12 13 ]       [ 1,1: 10 ]
```

The codegen states the intent outright — two `co_yield`s, one in the preheader
for the seed and one per iteration (`stream_coroutine_lowering.md` §3a).

---

## 6. Case E — declared extent vs actual trip count

```sisal
define Main
type Ints = array_dv[integer];
function Main(returns Ints, Ints, Ints)
  let
    exact := for initial i := 10; while i < 13 repeat i := old i + 1;
             returns array_dv(4) of i end for;
    over  := for initial i := 10; while i < 13 repeat i := old i + 1;
             returns array_dv(6) of i end for;
    under := for initial i := 10; while i < 13 repeat i := old i + 1;
             returns array_dv(2) of i end for
  in exact, over, under end let
end function
```

```
exact  size=4: 10 11 12 13
over   size=6: 10 11 12 13 0 0     two slots NEVER WRITTEN, silently
under  size=2: 10 11               the remaining stores went PAST the buffer, exit 0
```

Neither direction is guarded. See §8, item 2.

---

## 7. Summary table

| RETURNS form | seed contributes | ours = OSC |
|---|---|---|
| `value of X` | yes | yes |
| `value of sum / product / greatest / least X` | yes | yes |
| bare `array_dv of X` | yes | yes |
| `stream of X` | yes | yes |
| `array_dv(n) of X`, scalar carry | yes (since `1090500`) | our extension, no counterpart |
| `array_dv(n) of <expression>` | no — correct, no `body_0` | 1.2 rejects the form outright |
| `array_dv(n) of X`, **array-valued** carry | **no — outstanding** | — |

---

## 8. The declared extent is a SIZE DESCRIPTOR

`array_dv(n) of X` declares the size of the RESULT: slot 0 is the seed and the
loop fills `1..n-1`. Sisal 2.0 spells the same idea `array [size-descriptor] of`.

The extent exists for loops whose trip count the compiler cannot derive —
`m := old m * 4`, `while ~found & (i < array_size(period))`, psa's
`while to = from`. For those there is no compile-time count, which is why a
mismatch between the declared size and the actual iteration count is detectable
only at runtime. Declaring the extent is best practice generally, not only where
inference fails.

Migration in `1090500`: 11 declared extents over 8 files (`loop5`, `loop11s`,
`loop17` ×3, `loop20`, `loop23s`, `mr_forinit`, `shaped_gather`,
`simple_fwdsweep` ×2), each `+1`, with each C reference emitting its seed as
element 0. Several read better afterwards — `loop5` and `loop11s` now gather the
whole `X[1..n]` rather than `X[2..n]`, and `loop23s`'s `array_addh` lands the
recurrence at its natural column indices instead of shifted down one.

---

## 9. Where it lives

`src/backend/cpp/cpp_lower.ml`, the for-initial gather lowering:

- **bare path** — sizes itself from the TEST compare (`if is_carry then inc
  trip_count else trip_count`) and emits `@ if is_carry then store'` in the
  preheader. Has always done this.
- **scalar shaped path** — now `@ if is_carry then scalar_store`; the change in
  `1090500`.
- **array-element shaped path** — deliberately does NOT; §10 item 1.
- **streams** — preheader `co_yield` plus a per-iteration one.

`slot` is `ctr++` in all non-placement cases, so the seed naturally takes slot 0
and the loop continues from 1.

---

## 10. Outstanding

Both are on the same runtime helper, and neither is a semantics question any
more.

**1. Array-valued carries do not collect their seed.** Case A's `arr` gives
`[2,4 | 3,6 | 0,0]`: the seed row `row(1) = [1,2]` is missing and the third
declared slot is never written. `sisal_array_shaped_store` allocates lazily off
the first element it sees, so a preheader store leaves the descriptor empty —
adding the tick there made feo_fft's twiddle carries come out `size=0`, so it
was reverted with the reason recorded in the code. This is also why
`feo_fft_parts2` gathers one row rather than two.

**2. Trip count ≠ declared extent is unguarded, in both directions** (case E).
`trips > extent` walks past the allocation — silent heap corruption, exit 0.
`trips < extent` leaves whatever `alloc_empty` returned, and the array is the
size the user declared, so nothing downstream can tell. Since the extent exists
precisely for loops with no derivable count, a runtime check is the only check
that can ever exist for the case the feature was built for. Precedent:
`35c5848`'s always-on carry-gather size assert.

Related: we have no runtime subscript checking at all. OSC reports
`ARRAY SUBSCRIPT VIOLATION [HIGH]` with function, line and offending index where
we read or write past a buffer silently.

---

## 11. Coverage

`forinit_shadow_dv`, `simple_backsub_dv`, `simple_fwdsweep_dv`, `firsttrue_dv`,
`shaped_gather_dv`, `mr_forinit_dv`, `loop5/11s/17/20/23s_dv`, `feo_fft_parts2`,
`zerotrip_expr_dv`, `forinit_history_dv`. All execute the generated C and compare
against a reference computed in the harness — compiling clean is not a test, and
`test/positive.t` / the `test/unit/*.sis` corpus only check that IF1 is emitted.
