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

**Already covered in substance.** `newgauss_dv` vs `newgauss`, `lu` / `lu.piv` /
`lu.npiv`, `gaussj` / `gaussj_1`, `sieve` / `sieve_v2`, `uprime1` / `uprime2`,
`queens` / `newqueens`, `zbuffer1` / `zbuffer2`, `scan1` / `scan2`,
`simple` / `simple2a` — pick one of each pair, not both.

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
| `newgauss` | 228 | `array[RealVector]` -> rank-2; `array_setl` re-basing throughout; exports `factor`/`solve_down`/`solve_up`, no `main` | `hilbref::lu_solve`; check `A*x == b` |
| `gaussj` | 166 | same array-of-arrays rewrite | residual check |
| `lu` | 41 | array-of-arrays | reconstruct `L*U == A` |
| `fft` | 37 | array-of-arrays; math globals are fine | `fftref::` |
| `test_8queens` / `queens` | 22 / 58 | ragged solution list -> cons-list idiom | count solutions: 92 for n=8 |
| `sieve` | 52 | none known | primes below N |
| `life` | 99 | `ranf`/`rans` are external | C LCG matching the Sisal one, or a fixed board |
| `LegPoly` | 168 | none known (math globals only) | `legref::` already exists |
| `Gauss` | 139 | none known | quadrature nodes/weights from the definition |

`newgauss` was the intended third promotion of this batch and was deferred, not
rejected: the port is real work, and rushing it would produce a test whose
reference was fitted to whatever the compiler emitted.

## Rules that apply to every promotion

1. Rewrite to `array_dv` **first**. If `array_dv` genuinely does not fit, that is
   a discussion, not a workaround.
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

```python
import os, re, subprocess
u = {f[:-4] for f in os.listdir('test/unit') if f.endswith('.sis')}
e = {f[:-4].lower() for f in os.listdir('test/e2e') if f.endswith('.sis')}
cov = lambda n: (n.lower() in e or n.lower() + '_dv' in e
                 or re.sub(r'_dv$', '', n.lower()) in e)
MATH = {'sqrt','sin','cos','log','log10','atan','acos','exp','SIN','COS','SQRT',
        'ACOS','SINR','COSR','ACOSR','LOG','Sin','Cos','Sqrt'}
for n in sorted(u):
    if cov(n):
        continue
    p = f'test/unit/{n}.sis'
    if subprocess.run(['./_build/install/default/bin/sisal', p, '--c=/dev/null'],
                      capture_output=True).returncode:
        continue
    s = open(p).read()
    g = [m for m in re.findall(r'^\s*global\s+(\w+)', s, re.M) if m not in MATH]
    print(f'{n:28} {len(s.splitlines()):4} lines  needs:{",".join(g) or "-"}')
```
