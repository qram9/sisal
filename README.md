# Sisal 2.0 Compiler (`git_sisal`)

A modern optimizing compiler and C++23 code generator for **Sisal 2.0**, introducing rank-polymorphic dense arrays (dope vectors), side-effect monad ordering, Einstein summation, stream coroutines, structural IR deduplication, and dataflow graph transformations.

---

## Key Features & Language Innovations

1. **Dense Dope-Vectored Arrays (`array_dv`)**:
   - Originally, SISAL 1.2 implemented arrays in a ragged/nested sense, using build-in-place or update-in-place analysis to recover performance.
   - To support high-performance APL/NumPy-style dense multi-dimensional array operations, `array_dv` introduces rank-polymorphic dope-vector descriptors (strides, shape, offset).
   - Operations like slicing (`A[1..5, 2..8]`), reshaping, broadcasting, and transposing are zero-copy descriptor transformations.
   - C++ lowering targets modern C++23 with Apple Accelerate / BLAS acceleration for dense matrix operations.

2. **Einstein Summation (`EINSUM`) & Contraction Engine**:
   - Built-in `EINSUM` notation parser (`einsum_lower.ml`) supporting general multi-tensor contractions (e.g., `EINSUM("ij,jk->ik", A, B)`).
   - Lowers directly to BLAS/LAPACK `cblas_dgemm` / `cblas_sgemm` matrix calls.

3. **APL-Style Array Combinators**:
   - Native support for array combinators: `MAP`, `FOLDL`, `SCAN`, `EACH`, `REDUCE`, `REDUCE_AXIS`, `REDUCE_RANGE`, `ROTATE`, `TAKE`, `DROP`, `SLICE`, `COMPRESS`, `RAVEL`, and `STENCIL`.

4. **Coroutines & Stream Pipeline Processing**:
   - First-class stream processing (`stream_t`) with coroutine generators (`STREAM_SIEVE`, `STREAM_INTEGERS`, `STREAM_GURD`) lowered into zero-overhead stateful C++ iterators.

5. **Side-Effect Sequencing via Monad Ordering**:
   - Reconciles pure functional dataflow graph optimizations (IF1) with deterministic IO (`printf`, `cout`, `cerr`).
   - Monad control ports automatically insert prepass ordering edges (`PRINTF_TY`, `COUT_TY`, `CERR_TY`) between side-effecting nodes while leaving pure dataflow nodes 100% parallelizable.

6. **Pattern Matching & Wildcard Bindings**:
   - Supports don't-care wildcard (`_`) bindings across all `decldef` contexts (`let`, `:=`, tuple patterns, loops, `let rec`).
   - Tuple pattern bindings resolve via IF1 `MULTIARITY` nodes during AST lowering.

7. **AoS / SoA Memory Layout Transformations**:
   - Flexible memory layout support for Array of Structures (AoS) and Structure of Arrays (SoA) layout transformations (`NUCLEIC_SOA`, `REC_SOA`).

8. **IR Structural Type Deduplication**:
   - Automated IR graph pass (`cleanup.ml`) computing structural equivalence classes for type IDs, deduplicating identical types and re-linking edge types to canonical leader IDs.

9. **Copy-on-Write Reference Counting**:
   - Runtime descriptor management (`runtime/sisal_runtime.h`) with automatic reference counting (`ref_count`) and copy-on-write allocations for array descriptors.

10. **Interactive HTML Graph Visualizer**:
    - Embedded visualizer exporting interactive, colorized HTML graph diagrams (`export_debug_html`) at key compilation milestones (AST lowering, IR optimization, and C translation).

11. **Ragged Arrays & Algebraic Lists**:
    - For irregular data structures where raggedness is required, list-like patterns use standard algebraic `union` types (`Cons` / `Nil`), providing ergonomic functional list processing.

---

## Pending Items & Future Roadmap

- **Higher-Order Functions (Runtime Values)**:
  - Extend function types (`FUNCTION_TYPE`) from compile-time inlined constructs into first-class runtime function pointers and closures passed as values into functions.
- **Railway Error Monad Pipeline**:
  - Generalizing Monad Control types (`PRINTF_TY`, `COUT_TY`, `CERR_TY`) into a unified Railway Monad exception and IO pipeline.
- **GPU Kernel Offloading & Acceleration**:
  - Expanding Apple Accelerate / BLAS integration into dedicated CUDA and CUTLASS GPU kernel generation.

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
- [EINSUM Lowering & Subscripts](file:///Users/ramshankar/work/fromgit/git_sisal/docs/einsum.md)
- [Stream Coroutines & Lowering](file:///Users/ramshankar/work/fromgit/git_sisal/docs/stream_coroutine_lowering.md)

---

## Authors & Contributors

- **Ram** (Lead Architect & Developer)
- **Antigravity AI (Google DeepMind)**
- **Claude and Gemini** (AI Pair Programming Contributors)

---

## License

See [LICENSE](file:///Users/ramshankar/work/fromgit/git_sisal/LICENSE).
