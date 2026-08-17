# Sisal 2.0 Compiler (`git_sisal`)

A modern optimizing compiler and C++23 code generator for **Sisal 2.0**, introducing rank-polymorphic dense arrays (dope vectors), side-effect monad ordering, Einstein summation, stream coroutines, structural IR deduplication, and dataflow graph transformations.

---

## Key Features & Language Innovations

1. **Novel C++23 Dope-Vector Runtime (`sisal_runtime.h`)**:
   - Built from scratch to support rank-polymorphic multi-dimensional dense arrays (`array_dv`) lowered directly to the C/C++ `sisal_array_t` descriptor struct.
   - **`sisal_array_t` C Representation**: Encapsulates dynamic shape, stride, and offset arrays alongside element pointer and reference count (`ref_count`).
   - **Zero-Copy Descriptor Transformations**: Slicing (`A[1..5, 2..8]`), reshaping, broadcasting, and transposition operate in $O(1)$ time by manipulating `sisal_array_t` stride/offset metadata without copying underlying element buffers.
   - **Copy-on-Write (COW) Memory Management**: Reference-counted buffer management (`ref_count`) ensures safe functional updates while avoiding unneeded data duplication.
   - **Hardware BLAS Acceleration**: Direct memory layout alignment with BLAS/LAPACK (`cblas_dgemm`, `cblas_sgemm`, `cblas_dgemv`) via Apple Accelerate / OpenBLAS.
   - Originally, SISAL 1.2 implemented arrays in a ragged/nested sense, using build-in-place or update-in-place analysis. `array_dv` lowered to `sisal_array_t` provides modern NumPy/APL dense array capabilities while maintaining Sisal's functional guarantees.

2. **Einstein Summation (`EINSUM`) & Contraction Engine**:
   - Built-in `EINSUM` notation parser (`einsum_lower.ml`) supporting general multi-tensor contractions (e.g., `EINSUM("ij,jk->ik", A, B)`).
   - Lowers directly to BLAS/LAPACK `cblas_dgemm` / `cblas_sgemm` matrix calls.

3. **APL-Style Array Combinators**:
   - Native support for array combinators: `MAP`, `FOLDL`, `SCAN`, `EACH`, `REDUCE`, `REDUCE_AXIS`, `REDUCE_RANGE`, `ROTATE`, `TAKE`, `DROP`, `SLICE`, `COMPRESS`, `RAVEL`, and `STENCIL`.

4. **Coroutines & Stream Pipeline Processing**:
   - First-class stream processing (`stream_t`) with coroutine generators (`STREAM_SIEVE`, `STREAM_INTEGERS`, `STREAM_GURD`) lowered into zero-overhead stateful C++ iterators.

5. **Small Vector & Fixed Matrix Intrinsics (`float2`, `float4`, `mat2`, `mat4`)**:
   - First-class fixed-size SIMD vector types (`float2`, `float3`, `float4`, `int2`, `int4`) and matrix types (`mat2`, `mat3`, `mat4`).
   - Mapped directly to CPU SIMD vector registers (ARM Neon, x86 AVX-512) and GPU compute shader vector primitives.
   - Built-in hardware math intrinsics: matrix-matrix products (`mat2 * mat2`), matrix-vector transformations (`mat2 * float2`), inner products, and elementwise math (`mat_abs`, `mat_sqrt`, `mat_sin`).

6. **Side-Effect Sequencing via Monad Ordering**:
   - Reconciles pure functional dataflow graph optimizations (IF1) with deterministic IO (`printf`, `cout`, `cerr`).
   - Monad control ports automatically insert prepass ordering edges (`PRINTF_TY`, `COUT_TY`, `CERR_TY`) between side-effecting nodes while leaving pure dataflow nodes 100% parallelizable.

6. **Pattern Matching & Wildcard Bindings**:
   - Supports don't-care wildcard (`_`) bindings across all `decldef` contexts (`let`, `:=`, tuple patterns, loops, `let rec`).
   - Tuple pattern bindings resolve via IF1 `MULTIARITY` nodes during AST lowering.

7. **AoS / SoA Memory Layout Transformations**:
   - Flexible memory layout support for Array of Structures (AoS) and Structure of Arrays (SoA) layout transformations (`NUCLEIC_SOA`, `REC_SOA`).

8. **IR Structural Type Deduplication**:
   - Automated IR graph pass (`cleanup.ml`) computing structural equivalence classes for type IDs, deduplicating identical types and re-linking edge types to canonical leader IDs.

9. **Interactive HTML Graph Visualizer**:
   - Embedded visualizer exporting interactive, colorized HTML graph diagrams (`export_debug_html`) at key compilation milestones (AST lowering, IR optimization, and C translation).

11. **Ragged Arrays & Algebraic Lists**:
    - For irregular data structures where raggedness is required, list-like patterns use standard algebraic `union` types (`Cons` / `Nil`), providing ergonomic functional list processing.

---

## Pending Items & Future Roadmap

- **Copy-on-Write (COW) & Reference Count Lifetime Management**:
  - Full static liveness analysis and runtime COW reference-counting (`sisal_array_consume_replace`) to perform automatic in-place array updates when `ref_count == 1` vs copy-on-write when arrays are shared.
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
