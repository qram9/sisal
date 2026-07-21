# Project-Scoped Rules for git_sisal

- **E2E Testing**: Always run the parallel end-to-end regression test script `python3 test/e2e/run_dv_e2e_parallel.py` instead of the sequential bash script `test/e2e/run_dv_e2e.sh`. The parallel runner compiles and executes all test groups concurrently, which is significantly faster.
