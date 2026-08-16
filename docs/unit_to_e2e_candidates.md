# Unit tests still promotable to e2e

Survey date: 2026-08-15, against 291 `test/unit/*.sis` and 383 `test/e2e/*.sis`.
Suite at the time: 381 groups green.

Regenerate the raw list with the script at the bottom.

## Method, and what the numbers mean

A unit test counts as **covered** if `test/e2e` holds a file with the same stem,
the stem plus `_dv`, or the stem minus `_dv` (names are matched case-folded,
since Sisal identifiers are case-insensitive). That leaves **105 uncovered files
that compile clean**.

105 is not the number of promotable tests. It is an upper bound, and most of the
gap is explained by three buckets that are not worth promoting as they stand.
The earlier figure of ~36 in this session came from applying the
self-containment filter below; both numbers are right, they answer different
questions. Prefer to quote the bucketed count.

## Not promotable as they stand

**Needs external functions (~45 files).** A non-empty `global` list other than
the math intrinsics means the program calls something no `.sis` in the tree
defines — `IsMember`, `Remove_Edge`, `Choose_Random`, `paraffin`, `slab`,
`cdfcreate`. The e2e harness links one generated TU; there is nothing to bind
those to. Math intrinsics (`sqrt`, `sin`, `cos`, `log10`, `atan`) do NOT count,
they are implicit. Promoting one of these means either supplying the missing
function in C or pulling in the file that defines it.

**Parser/AST fixtures (~10 files).** `rest_ast`, `reset_ast`, `scan1`, `scan2`,
`simple_tests`, `sisal_tests_by_section`, `monolith`, `types`, `fails`, `bad`.
These exist to be *parsed*; several are deliberately malformed or are a grab bag
of unrelated fragments. `positive.t` already covers what they are for. There is
no single answer to check.

**A `_dv` suffix does not mean it is ported.** `newgauss_dv` declares
`RealMatrix = array[RealVector]` — a plain array of DV rows. Plain `array` is not
allowed at all; the target is `array_dv` throughout, with the cons-list/union
idiom reserved for data that genuinely cannot share one rectangle. So
`newgauss_dv` is not a shortcut to promoting `newgauss`, even though it compiles
clean. Check the type declarations, not the filename.

**A dotted filename is underscored on promotion.** `lu.piv` -> `lu_piv_dv`,
`lu.npiv` -> `lu_npiv_dv`, `feo.fft` -> `feo_fft`. All three are ALREADY in e2e;
a matcher that does not fold `.` to `_` reports them as uncovered. The script
below folds them.

**Already covered in substance.** `lu` (e2e has `lu_piv_dv` and `lu_npiv_dv`),
`gaussj` / `gaussj_1` (e2e has six Gauss-Jordan variants), `sieve` / `sieve_v2`,
`uprime1` / `uprime2`, `queens` / `newqueens`, `zbuffer1` / `zbuffer2`,
`scan1` / `scan2`, `simple` / `simple2a` — pick one of each pair, not both.

**Linear solvers are already well covered.** `lu_npiv_dv` and `lu_piv_dv` both
check against `hilbref::lu_solve`, and six Gauss-Jordan variants are in e2e. Do
not add another solver for the sake of solving; see the newgauss note below for
what it would actually add.

## The actionable list

Self-contained (no non-math `global`), a computable answer, and a reference that
can be written from a definition rather than from our own output.

### Ready — small, obvious reference

| test | lines | what it exercises | reference |
|---|---|---|---|
| `test_forall_cross` | 7 | cross-product generator | nested C loops |
| `test_forall_dot` | 7 | dot (zip) generator | single C loop |
| `test_forall_simple` | 7 | one-level gather | C loop |
| `builtin_mat` | 40 | matrix builtins | `laref::` |
| `builtin_vec` | 83 | vector builtins | `laref::`, `ewref::` |
| `gen_extent` | 34 | generator extents | closed form |
| `bubble` | 37 | bubble sort | `std::sort`, ordering + multiset apart |
| `quicksort1` | 27 | a third partition scheme | `std::sort` |
| `scat` | 50 | scatter placement | C loop with explicit indices |
| `sizable_dv_deep` | 24 | nested sizable array_dv | closed form |

### Worth doing, needs a port first

| test | lines | blocker | reference |
|---|---|---|---|
| ~~`newgauss`~~ | — | **ALREADY DONE** — e2e `newgauss_dv`. See below. | — |
| ~~`gaussj`~~ | — | **ALREADY DONE** — e2e `gaussj_dv_rr` | — |
| `fft` | 37 | array-of-arrays; math globals are fine | `fftref::` |
| `test_8queens` / `queens` | 22 / 58 | ragged solution list -> cons-list idiom | count solutions: 92 for n=8 |
| ~~`sieve`~~ | — | **ALREADY DONE** — e2e `stream_uprime2_dv` | — |
| `life` | 99 | `ranf`/`rans` are external | C LCG matching the Sisal one, or a fixed board |
| `LegPoly` | 168 | none known (math globals only) | `legref::` already exists |
| `Gauss` | 139 | none known | quadrature nodes/weights from the definition |

`newgauss` was the intended third promotion of this batch and was deferred, not
rejected: the port is real work, and rushing it would produce a test whose
reference was fitted to whatever the compiler emitted.

## newgauss was ALREADY PORTED — read this before planning any promotion

`newgauss` is in e2e as **`newgauss_dv`** (renamed 2026-08-15 from
`stand_alone_gauss_dv`, which is what it was called when the name-based survey
missed it). `test/unit/newgauss.sis` and `test/unit/stand_alone_gauss.sis` are
the same program — identical function set, 7/7 — so one group covers both.

This was missed because the survey matched **filenames**, and a port may be
renamed to anything. Ten entries in the original list were already covered:

| listed as uncovered | actually in e2e as |
|---|---|
| `newgauss` | `newgauss_dv` (was `stand_alone_gauss_dv`) |
| `gaussj`, `gaussj_1` | `gaussj_dv_rr` |
| `sieve`, `sieve_v2`, `uprime1`, `uprime2` | `stream_uprime2_dv` |
| `p16final` | `hilbert_dv` |
| `sbatcher` | `seqbatcher_dv` |
| `outs2` | `outs_dv` |

Three more (`lu.piv`, `lu.npiv`, `feo.fft`) were missed by the dot-to-underscore
rename. **Always run the content check in the script below before starting a
port** — it compares the set of function names, which a rename cannot hide.

## What the existing newgauss_dv already establishes (do not re-derive)

Its header documents the design conclusions this file previously stated as open
questions, and one of them corrects a plausible-but-wrong plan:

- The triangle needs **no list**. "Lists are for raggedness whose extent is a
  property of the DATA — a `when`/`unless` gather — not for a triangle whose
  shape is known from n."
- The block is kept **full n x n**, NOT shrinking. An earlier attempt kept the
  shrinking block and produced inf/nan: a flat rank-2 dope has one `lower_bound`
  per AXIS, so per-ROW offsets cannot be represented. A probe of a single
  uniform block with one origin does work, which makes this trap easy to walk
  into by generalising from it.
- The unused triangle carries the ORIGINAL values, not zeros — harmless, since
  `solve_down` reads `l[j,i]` only for `j < i` and `solve_up` reads `u[i,j]`
  only for `j >= i`.
- The oracle is a round trip: solve `A x = A e_m` for every unit vector, so the
  result must be the IDENTITY. That exercises factorisation and both
  substitutions together. Inputs are Vandermonde, i.e. ill-conditioned enough
  for the check to bite. Holds exactly for n = 2..5.

## Linear algebra coverage, for reference

`lu_npiv_dv` and `lu_piv_dv` (solve, checked against `hilbref::lu_solve`),
`newgauss_dv` (factor + both substitutions, round-trip identity), and six
Gauss-Jordan variants. Adding another solver adds little; prefer candidates that
exercise something structurally new.

## Historical: the array_dv probe (2026-08-15)

`reduce`, the core of the program, was transliterated to plain `array_dv` and run
against a C reference for one elimination step on a 4x4. Result: **values match,
and the origins are exactly what the shrinking-block formulation needs** —

```
row  : rank=1 dims=4    lb=1
mult : rank=1 dims=3    lb=2
next : rank=2 dims=3x3  lb=[2,2]        (i = 1)
```

So both things the port depends on hold: a rank-2 gather `for j in i+1,n /
for k in i+1,n` carries `lower_bound = [i+1, i+1]` per dimension through to C,
and the row slice `b[i, ..]` works on it. All four `array_setl` calls in the
original are therefore unnecessary.

**The one function that is not a transliteration is `factor`.** It gathers
`array of col` / `array of row` across iterations, and those rows have different
lengths at each step (`n-i` and `n-i+1`) — a ragged gather, which is exactly what
`array_dv` will not express. The fix is NOT a list; it is to pad to the dense L/U
layout so every row has length `n`:

```
next[j,k] := if j > i and k > i then b[j,k] - mult[j]*row[k] else b[j,k] end if
```

with `mult` and `row` generated over `1, n` and zero outside the active range.
The padding is not a workaround: L is unit lower triangular and U is upper
triangular, so those zeros are the true values, and n-by-n triangular factors are
how the mathematics presents them anyway. The ragged form was the optimisation.

**Pad only what `factor` gathers.** `col` and `row` need it; the block `next`
does NOT — it is uniformly square `(n-i)x(n-i)` at every step and is already
array_dv-clean. Keep it shrinking, with its non-1 origins. Flattening it to full
size as well would be slightly easier to write but would discard the only case in
the suite exercising a rank-2 `array_dv` with a non-1 lower bound on BOTH
dimensions, which the probe above proved works and which nothing else covers.

So: `factor` returns two n-by-n `array_dv`s laid out exactly like
`hilbref::lu_solve` (direct element-for-element comparison, no repacking), while
`reduce` keeps the shrinking block. That is the whole of the remaining work.

Note when writing the harness: `real` lowers to **`float`** (4 bytes, type_id 8),
not `double`. Feeding `double` gives uninitialised garbage that looks like a
compiler bug and is not one.

## Rules that apply to every promotion

1. Rewrite to `array_dv` **first**, everywhere. Plain `array` is not acceptable,
   including as an outer container holding `array_dv` rows. Rank is a runtime
   property of the dope vector, so a rank-2 matrix is declared by its ELEMENT
   type (`type Matrix = array_dv[real]`) and the rank comes from nesting the
   gathers — see `test/e2e/matmul_dv.sis`.
   Only when the data genuinely cannot share one rectangle does the
   cons-list/union idiom apply (see the Mt/Cons/Hd/Tl examples in e2e).
   Triangular shapes such as the L/U factors are NOT such a case: they pack into
   a dense square with the unused corner left zero.
   `array_setl` calls usually vanish in the port — a gather preserves its
   generator's origin, so `for j in i+1, n` already yields `lower_bound = i+1`,
   per dimension.
2. A reference written from the operation's definition, in C where practical, so
   it doubles later as a performance baseline. Never a constant copied out of our
   own output.
3. Where a test can fail two independent ways — a sort mis-ordering vs. losing an
   element — assert them separately.
4. Inputs that produce `0/0` or a division by zero get **changed**, not guarded
   and not pinned.
5. Register at all five points: `extern` decl, test fn, dispatch,
   `run_group` in `run_dv_e2e.sh`, `test/positive.t`. Then
   `python3 test/e2e/split_harness.py 32` and re-baseline `test/e2e/golden/`.

## Regenerating this list

Two checks, and BOTH are needed. The name check alone reported 13 already-covered
tests as candidates; the content check catches renames the name check cannot.

```python
import os, re, subprocess

def fns(p):
    """Function names DEFINED in a file.  Strip Sisal comments first -- matching
    the bare word `function` also hits prose like 'this function factors...',
    which silently poisons the comparison."""
    out = set()
    for ln in open(p, errors='ignore'):
        m = re.match(r'\s*function\s+(\w+)\s*\(', ln.split('%')[0], re.I)
        if m:
            out.add(m.group(1).lower())
    return frozenset(out)

E = {f[:-4].lower() for f in os.listdir('test/e2e') if f.endswith('.sis')}
EF = {}
for f in os.listdir('test/e2e'):
    if f.endswith('.sis'):
        k = fns('test/e2e/' + f)
        if len(k) >= 3:
            EF.setdefault(k, []).append(f)

def by_name(n):
    # .replace('.','_'): dotted unit names are underscored on promotion
    # (lu.piv -> lu_piv_dv, feo.fft -> feo_fft).
    b = n.lower().replace('.', '_')
    return b in E or b + '_dv' in E or re.sub(r'_dv$', '', b) in E

def by_content(n):
    """A port may be renamed to ANYTHING (newgauss -> stand_alone_gauss_dv), so
    compare function sets.  >0.8 Jaccard = same program."""
    k = fns(f'test/unit/{n}.sis')
    if len(k) < 3:
        return None
    for ek, ev in EF.items():
        if len(k & ek) / len(k | ek) > 0.8:
            return ev[0]
    return None

MATH = {'sqrt','sin','cos','log','log10','atan','acos','exp','SIN','COS','SQRT',
        'ACOS','SINR','COSR','ACOSR','LOG','Sin','Cos','Sqrt'}
for n in sorted(f[:-4] for f in os.listdir('test/unit') if f.endswith('.sis')):
    if by_name(n):
        continue
    dup = by_content(n)
    if dup:
        print(f'{n:28} COVERED (renamed) by test/e2e/{dup}')
        continue
    p = f'test/unit/{n}.sis'
    if subprocess.run(['./_build/install/default/bin/sisal', p, '--c=/dev/null'],
                      capture_output=True).returncode:
        continue
    s = open(p).read()
    g = [m for m in re.findall(r'^\s*global\s+(\w+)', s, re.M) if m not in MATH]
    print(f'{n:28} {len(s.splitlines()):4} lines  needs:{",".join(g) or "-"}')
```
