# Sisal-to-Silicon (Apple) Test Suite

This directory contains tests optimized for **Apple Silicon (M4 Max)**. The compiler backend (`To_apple`) translates Sisal source code into strictly-typed C++ using Apple's native parallel and math frameworks.

## Core Components

1.  **`sisal_runtime.h`**: Defines the `sisal_array_t` (Dope Vector) structure and links to Apple's **Accelerate.framework** for AMX/vDSP acceleration.
2.  **`test_runner.cpp`**: A C++ test harness that exercises generated functions (e.g., Newton-Raphson Square Root).
3.  **`run_test.sh`**: An automation script that handles the end-to-end compilation and execution cycle.

## How to Run

To run the Newton-Raphson Square Root test on silicon:

```bash
cd test/silicon
./run_test.sh ../for_initial.sis
```

## Silicon Features Verified

- [x] **Iterative Loops**: Functional `while` / `do-while` loops with recurrence state updates.
- [x] **Strict Typing**: All variables explicitly typed (no `auto`) for silicon predictability.
- [x] **Hardware Acceleration**: Automatic linkage to `Accelerate.framework` for convolution and vector math.
- [x] **Parallel Orchestration**: Grand Central Dispatch (`dispatch_apply`) ready for `FORALL` loops.
