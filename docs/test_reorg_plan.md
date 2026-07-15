# Test Directory Reorganization Plan

Status: **PLAN ONLY — no files moved yet.** Execute after the current
`forall-extent-rework` lands (tree currently has 30 untracked `.sis` + ~395
untracked `.if1` debug dumps).

Grounded in an actual run of `bash test/run_dv_e2e.sh` (see "Empirical basis").

---

## 1. Empirical basis (what the run told us)

- **`.if1` files are NOT goldens.** Only the `.t` cram files hold expected output
  (inline). 395 of 396 `.if1` files are untracked side-effect dumps → gitignore,
  do not move.
- **e2e is tiny and self-contained.** `run_dv_e2e.sh` emits each `.sis` to an
  ephemeral `/tmp/*.cpp`, links it against the single harness `dv_run_all.cpp`
  (which holds every assertion in `#ifdef TEST_XXX` blocks), runs it, checks exit
  code. The generated `.cpp` never persists.
- **`*_dv.sis` is not the e2e set.** 30 of 31 `*_dv` files are never executed by
  the harness; they are compile-only → they stay in `unit/`.
- Last run: **18 groups pass, 4 "fail" = 4 dead references** (no `.sis` exists).

## 2. The 18 e2e stems (the entire `e2e/` payload)

Executed + asserted by `dv_run_all.cpp`:

```
dv_agreement        dv_lifted_arith     dv_intrinsics       dv_broadcast_complex
dv_compress_test    dv_broadcast_numpy  forall_cpu          negate_dv
dv_forall_reduce    dv_bulk_basic       dv_innerproduct     for_initial_e2e
gaussj_parts(*)     gaussj_dv_rr(*)     swaploop(*)         gen_extent
broadcast_parts     if_cond
```

`(*)` = currently **untracked** WIP — `git add` these as part of the reorg commit.

Dead references to **remove** from `run_dv_e2e.sh` (no `.sis` exists):
`dv_abs_demo  dv_shl  dv_test_subset  dv_forall_basic`

## 3. Target structure

Keep `dune` and the `.t` cram files at `test/` root (avoids relative-path
gymnastics in cram sandboxes). Only create `unit/` and `e2e/`.

```
test/
  dune                      # cram rule (globs updated, see §5)
  positive.t errors.t limitations.t
  com_defines globals types ranf.h types.h   # shared deps, stay at root
  unit/                     # ~350 tracked .sis — compile -> IF1 only
    apl/                    # apl_*.sis (8)        clean sub-bucket
    <everything else flat>  # incl. the 30 compile-only *_dv.sis
  e2e/                      # executed tests
    run_dv_e2e.sh
    dv_run_all.cpp          # the harness (assertions live here)
    <the 18 stem .sis>
    harness/                # orphan/manual drivers, not in run_dv_e2e.sh
      matmul_harness.cpp  verify_numpy_broadcast_harness.cpp
      test_verify_numpy_broadcast.cpp  main_mixed.cpp  main.c  union0.c
```

## 4. Move commands (use `git mv` to preserve history)

```sh
cd test
mkdir -p unit/apl e2e/harness

# e2e payload (15 tracked + 3 untracked stems)
for s in dv_agreement dv_lifted_arith dv_intrinsics dv_broadcast_complex \
         dv_compress_test dv_broadcast_numpy forall_cpu negate_dv \
         dv_forall_reduce dv_bulk_basic dv_innerproduct for_initial_e2e \
         gen_extent broadcast_parts if_cond; do git mv "$s.sis" e2e/; done
git add gaussj_parts.sis gaussj_dv_rr.sis swaploop.sis   # untracked WIP
git mv gaussj_parts.sis gaussj_dv_rr.sis swaploop.sis e2e/  # after add, or just mv
git mv run_dv_e2e.sh dv_run_all.cpp e2e/
git mv matmul_harness.cpp verify_numpy_broadcast_harness.cpp \
       test_verify_numpy_broadcast.cpp main_mixed.cpp main.c union0.c e2e/harness/

# apl sub-bucket
git mv apl_*.sis unit/apl/

# everything else tracked -> unit/  (all remaining *.sis)
git ls-files '*.sis' | grep -vE '^(e2e|unit)/' | xargs -I{} git mv {} unit/
```

## 5. Edits required after the move

**`test/dune`** — globs must reach into subdirs:
```diff
- (glob_files *.sis)
+ (glob_files_rec *.sis)
```
(`glob_files_rec` recurses; keep the `*.h`, `*.sish`, `com_defines`, `globals`,
`types` deps as-is at root.)

**`test/positive.t`, `test/errors.t`** — bare `sisal foo.sis` → `sisal unit/foo.sis`
(and `unit/apl/foo.sis` for apl). Mechanical:
```sh
# in positive.t: prefix each compiled file with its new dir
#   sisal basic.sis   ->  sisal unit/basic.sis
#   sisal apl_map.sis ->  sisal unit/apl/apl_map.sis
```
Verify with `dune test` (cram diffs expected output; paths in golden text such as
`in file: foo.sis` may need updating too — check the `errors.t` expected strings).

**`test/e2e/run_dv_e2e.sh`**:
- `HARNESS="${REPO}/test/dv_run_all.cpp"` → `"${REPO}/test/e2e/dv_run_all.cpp"`
- `"${SISAL}" "${REPO}/test/${stem}.sis"` → `"${REPO}/test/e2e/${stem}.sis"`
- Delete the 4 dead `run_group` lines (§2).
- Strip the `--dv` 3rd arg from every `run_group` (no-op since the flag was removed).

## 6. Validation checklist

1. `dune build` clean.
2. `dune test` (cram) clean — confirms unit path rewrites are correct.
3. `bash test/e2e/run_dv_e2e.sh` → still **18 groups pass, 0 fail** (4 "fails"
   gone now that dead refs are removed).
4. `git status` shows only renames (+ 3 new WIP stems) — no content churn.
5. Add `test/**/*.if1` to `.gitignore` so debug dumps stop showing as untracked.

## 7. Open question for later

Whether the 30 compile-only `*_dv.sis` should eventually gain `dv_run_all.cpp`
assertions and graduate to `e2e/`. For now they are unit (compile→IF1) because
nothing executes them.
