# Sisal 2.0 Compiler (`git_sisal`)

A modern optimizing compiler and C++23 code generator for **Sisal 2.0**, introducing rank-polymorphic dense arrays (dope vectors), side-effect monad ordering, and dataflow IR graph transformations.

---

## Key Features & Language Innovations

1. **Dense Dope-Vectored Arrays (`array_dv`)**:
   - Originally, SISAL 1.2 implemented arrays in a ragged/nested sense, using build-in-place or update-in-place analysis to recover performance.
   - To support high-performance APL/NumPy-style dense multi-dimensional array operations, `array_dv` introduces rank-polymorphic dope-vector descriptors (strides, shape, offset).
   - Operations like slicing, reshaping, broadcasting, and transposing are zero-copy descriptor transformations.
   - C++ lowering targets modern C++23 with BLAS/Accelerate acceleration for dense matrix operations.

2. **Ragged Arrays & Algebraic Lists**:
   - For irregular data structures where raggedness is required, list-like patterns use standard algebraic `union` types (`Cons` / `Nil`), providing ergonomic functional list processing.

3. **Side-Effect Sequencing via Monad Ordering**:
   - Reconciles pure functional dataflow graph optimizations (IF1) with deterministic IO (`printf`, `cout`, `cerr`).
   - Monad control ports automatically insert prepass ordering edges between side-effecting nodes while leaving pure dataflow nodes 100% parallelizable.

4. **Pattern Matching & Wildcard Bindings**:
   - Supports don't-care wildcard (`_`) bindings across all `decldef` contexts (`let`, `:=`, tuple patterns, loops, `let rec`).
   - Tuple pattern bindings resolve via IF1 `MULTIARITY` nodes during AST lowering.

5. **Range Indexing & Slicing (`..`)**:
   - Concise APL/NumPy-style range slicing syntax (e.g., `A[1..5, 2..8]`) lowered directly into zero-copy dope-vector descriptor operations.

6. **First-Class Tuple Types**:
   - Composite tuple types and multi-value returns (`let x, y, z := ...`) supported natively throughout compiler AST and IF1 IR lowerings.

---

## Pending Items & Future Roadmap

- **Higher-Order Functions (Runtime Values)**:
  - Extend function types (`FUNCTION_TYPE`) from compile-time inlined constructs into first-class runtime function pointers and closures passed as parameters into functions.
- **APL Combinators**:
  - Full combinator library (`MAP`, `FOLDL`, `SCAN`, `EACH`) with general lambda expressions.
- **Einstein Summation (`EINSUM`) Lowering**:
  - Direct translation of `EINSUM` notation to optimized tensor library backends (BLAS, LAPACK, cuTENSOR).
- **Railway Error Monad Pipeline**:
  - Generalizing Monad Control types (`PRINTF_TY`, `COUT_TY`, `CERR_TY`) into a unified Railway Monad error handling and IO system.
- **GPU Performance & Library Acceleration**:
  - GPU offloading for dense matrix and vector kernels using CUDA, CUTLASS, and Apple Accelerate/vDSP.

---

## Installation & Environment Setup

### Prerequisites

- **OCaml**: `>= 4.14.0` (or OCaml 5.x)
- **OPAM**: OCaml Package Manager
- **C++ Compiler**: `clang++` supporting C++20/C++23
- **Python**: `python3` (for parallel E2E test harness execution)

### 1. Install OCaml & OPAM Dependencies

```bash
# Initialize OPAM switch if needed
opam switch create 4.14.2
eval $(opam env)

# Install required packages
opam install dune menhir re
```

Or install dependencies directly using `opam pin`:
```bash
opam pin add . -y
```

---

## Building the Compiler

Build the project using `dune`:

```bash
# Build the compiler executable
dune build

# Run static analysis check
dune build @check
```

The compiled `sisal` binary will be produced at:
`_build/install/default/bin/sisal`

---

## Usage

### Compile a Sisal Source File to C++

```bash
./_build/install/default/bin/sisal path/to/program.sis --c=output.cpp
```

### Compile & Execute Generated C++ Code

```bash
clang++ -std=c++23 -O3 -I runtime output.cpp -o program
./program
```

---

## Running Tests

Run the parallel end-to-end regression suite (compiles and runs 408 test groups concurrently):

```bash
python3 test/e2e/run_dv_e2e_parallel.py
```

---

## Documentation

Comprehensive design specifications and architecture notes are located in the [`docs/`](file:///Users/ramshankar/work/fromgit/git_sisal/docs) directory:
- [IF1 to C Architecture](file:///Users/ramshankar/work/fromgit/git_sisal/docs/if1_to_c_architecture.md)
- [Rank Polymorphism & Dope Vectors](file:///Users/ramshankar/work/fromgit/git_sisal/docs/Rank_Polymorphism_Complete_Guide.md)
- [Stream Coroutines & Lowering](file:///Users/ramshankar/work/fromgit/git_sisal/docs/stream_coroutine_lowering.md)

---

## Authors & Contributors

- **Ram** (Lead Architect & Developer)
- **Antigravity AI (Google DeepMind)**
- **Claude and Gemini** (AI Pair Programming Contributors)

---

## License

See [LICENSE](file:///Users/ramshankar/work/fromgit/git_sisal/LICENSE).
