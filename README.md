# Sisal-2026 Compiler (`git_sisal`)

A modern optimizing compiler and C++23 code generator for **Sisal-2026**, introducing rank-polymorphic dense arrays (dope vectors), side-effect monad ordering, Einstein summation, stream coroutines, structural IR deduplication, and dataflow graph transformations.

📖 **[Read the Complete Sisal-2026 Tutorial & Reference Guide](docs/sisal_2026_tutorial.md)**

---

## Key Features & Language Innovations

1. **Novel C++23 Dope-Vector Runtime & Broadcasting Engine (`sisal_runtime.h`)**:
   - **APL & NumPy Heritage**: Brings dense rank-polymorphic multi-dimensional arrays (`array_dv`) into Sisal-2026, continuing an architectural lineage originating in **APL** (Iverson, 1962) and perfected in **NumPy**, **PyTorch**, and **JAX**. (See 📘 **[Rank Polymorphism: A Complete Guide](docs/Rank_Polymorphism_Complete_Guide.md)**).
   - **Natural Fit for Single-Assignment Semantics**: Dope-vector metadata operations (slicing `A[1..5, 2..8]`, reshaping, transposition) fit naturally into single-assignment dataflow languages as $O(1)$ constant-time metadata views. Combined with Copy-on-Write (CoW) reference counting, `array_dv` provides 100% single-assignment immutability guarantees alongside native C/C++ execution performance.
   - **Right-Aligned Trailing Axis Broadcasting**: Built-in array broadcasting matching NumPy/JAX rules via `conform_check` and `sisal_dv_offset_at`. Axis sizes of 1 are expanded to match target shape using zero-copy `stride = 0` metadata, incurring zero element byte copies and zero allocation overhead.
   - **No `array_dv[array_dv[...]]`**: All vectors (1D), matrices (2D), and tensors ($N$-D) use the single flat type **`array_dv[T]`**. Dynamic rank is a runtime metadata property of `sisal_array_t`.
   - **`sisal_array_t` C Representation**: Encapsulates dynamic shape, stride, and offset arrays alongside element pointer and reference count (`ref_count`).
   - **Hardware BLAS Acceleration**: Direct memory layout alignment with BLAS/LAPACK (`cblas_dgemm`, `cblas_sgemm`, `cblas_dgemv`) via Apple Accelerate / OpenBLAS.
   ```sisal
   % Zero-copy slicing & rank-polymorphic dope vectors
   A := array_dv [1: 10, 20, 30, 40, 50];
   SubSlice := A[2..4]; % O(1) view metadata shift, zero data copy
   M := Matrix + Vector % Zero-copy stride-0 broadcast addition
   ```

2. **Einstein Summation (`EINSUM`) & Contraction Engine**:
   - Built-in `EINSUM` notation parser (`einsum_lower.ml`) supporting general multi-tensor contractions (e.g., `EINSUM("ij,jk->ik", A, B)`).
   - Fast-paths lower directly to BLAS/LAPACK `cblas_dgemm` / `cblas_dgemv` matrix/vector calls and $O(1)$ stride swaps.
   - General Einstein subscripts lower to `If1.EINSUM_NODE` multi-index tensor contraction loops.
   - See 📘 **[Einstein Summation (`EINSUM`) Lowering & Support Guide](docs/einsum_lowering_guide.md)**.
   ```sisal
   % Matrix Multiplication via Tensor Contraction
   C := EINSUM("ij,jk->ik", MatrixA, MatrixB)
   ```

3. **APL-Style Bulk Operations Battery (58 Primitives)**:
   - Native support for 58 whole-array (APL-style) bulk operations: `MAP`, `FOLDL`, `FOLDR`, `SCAN`, `CUMSUM`, `CUMPROD`, `SUM`, `PRODUCT`, `LEAST`, `GREATEST`, `MEAN`, `VARIANCE`, `STDDEV`, `NORM`, `TAKE`, `DROP`, `ROTATE`, `REVERSE`, `COMPRESS`, `SORT`, `ARGMAX`, `ARGMIN`, `GRADE_UP`, `GRADE_DOWN`, `NONZERO`, `WHERE`, `CONCAT`, `TILE`, `PAD`, `STENCIL`, `INNERPRODUCT`, `OUTERPRODUCT`, `RAVEL`, `EXPAND`, `SQUEEZE`, `PERMUTE`, `ANY`, `ALL`, and 0-based `REDUCE_AXIS` reductions.
   - See 📘 **[Bulk Operations & Whole-Array Primitives Reference](docs/bulk_ops_reference.md)**.
   ```sisal
   Doubled := MAP(A, function(x) x * 2 end function);
   Total   := REDUCE(A, +);
   Shifted := ROTATE(A, 1)
   ```

4. **C++20 Stackless Stream Coroutines (`co_yield`)**:
   - Streams (`stream[T]`) compile directly into **C++20 stackless coroutines (`sisal_generator<T>`)**.
   - **Zero-Allocation Pipeline**: Producers yield elements on-demand into consumers via `co_yield`, allowing compiler Heap Allocation Elision Optimization (HALO) to inline coroutine frames directly onto the stack.
   - **Ultra-Fast Switches**: User-space context transitions run in **2–5 nanoseconds** (30x–100x faster than kernel/ucontext thread switches).
   - See 📘 **[Cooperative Coroutine Streams Design](docs/coroutine_streams_design.md)** and 📘 **[Stream Coroutine Lowering Architecture](docs/stream_coroutine_lowering.md)**.
   ```sisal
   Numbers := STREAM_INTEGERS(1, 100);
   Primes  := STREAM_SIEVE(Numbers) % Evaluated lazily via C++20 co_yield
   ```

5. **Small Vector & Fixed Matrix Intrinsics (`float2`, `float4`, `mat2`, `mat4`)**:
   - First-class fixed-size SIMD vector types (`float2`, `float3`, `float4`, `int2`, `int4`) and matrix types (`mat2`, `mat3`, `mat4`).
   - Mapped directly to CPU SIMD vector registers (ARM Neon, x86 AVX-512) and GPU compute shader vector primitives.
   - Built-in hardware math intrinsics: matrix-matrix products (`mat2 * mat2`), matrix-vector transformations (`mat2 * float2`), inner products, and elementwise math (`mat_abs`, `mat_sqrt`, `mat_sin`).
   ```sisal
   v := float4(1.0, 2.0, 3.0, 4.0);
   m := mat2(1.0, 0.0, 0.0, 1.0);
   p := m * float2(5.0, 6.0) % Fast SIMD vector transform
   ```

6. **Side-Effect Sequencing via Monad Ordering & `printf` Support**:
   - Reconciles pure functional dataflow graph optimizations (IF1) with deterministic IO (`printf`, `cout`, `cerr`).
   - `printf` calls can be freely inserted into code for logging and debugging with **guaranteed execution ordering**.
   - Monad control ports automatically insert prepass ordering edges (`PRINTF_TY`, `COUT_TY`, `CERR_TY`) between side-effecting nodes, ensuring strict, deterministic output ordering while keeping pure dataflow nodes 100% parallelizable.
   ```sisal
   let
     _ := printf("Processing value: %d\n", input_val);
     result := HeavyComputation(input_val);
     _ := printf("Computed result: %d\n", result)
   in
     result
   end let
   ```

7. **Pattern Matching & Wildcard Bindings**:
   - Supports don't-care wildcard (`_`) bindings across all `decldef` contexts (`let`, `:=`, tuple patterns, loops, `let rec`).
   - Tuple pattern bindings resolve via IF1 `MULTIARITY` nodes during AST lowering.
   ```sisal
   let
     first, _, third := GetThreeTuple();
     _ := IgnoreSideEffect()
   in
     first + third
   end let
   ```

8. **AoS / SoA Memory Layout Transformations**:
   - Flexible memory layout support for Array of Structures (AoS) and Structure of Arrays (SoA) layout transformations (`NUCLEIC_SOA`, `REC_SOA`).
   ```sisal
   type ParticleAoS = record[ x, y, z : real ];
   type ParticleSoA = record[ x, y, z : array_dv[real] ];
   ```

9. **Interactive HTML Graph Visualizer**:
   - Embedded visualizer exporting interactive, colorized HTML graph diagrams (`export_debug_html`) at key compilation milestones (AST lowering, IR optimization, and C translation).

10. **Algebraic Lists for Irregular / Ragged Patterns**:
    - Legacy `array` syntax is **not available in Sisal-2026**; all dense multi-dimensional arrays use **`array_dv`**. For irregular or ragged structures, use standard algebraic `union` types (`Cons` / `Nil`), providing ergonomic functional list processing.
    ```sisal
    type IntList = union[ nil_tag: null; cons_tag: record[ head: integer; tail: IntList ] ]
    ```

11. **First-Class Higher-Order Functions (HOFs) & Closures**:
    - **First-Class Function Values**: Functions can be passed as arguments, returned from procedures, bound to `let` variables, and stored in algebraic data structures (`union` lists).
    - **Environment Variable Capture (Closures)**: Inner functions capture single or multiple scalar variables (`x`, `multiplier`, `offset`) and outer functions across surrounding lexical scopes.
    - **Control-Flow Scope Integration**: Captured functions resolve cleanly inside `if-then-else` expressions, `for-initial` / `for-repeat` loop bodies, and `tagcase` pattern matches.
    - **Direct & Mutual Recursion**: Full support for self-referential procedures (`HeapSort`, `DispatchAll`), mutual recursion (`LETREC_SCOPE_DV`), and recursive algebraic list dispatch.
    - **Direct Multi-Assignment Tuple Swapping**: Zero-copy variable swapping (`A_swap, B_swap := B, A` and `A, B := B, A`) executes via direct 24-byte descriptor pointer assignments ($O(1)$ constant time).
    ```sisal
    type IntOp = function( integer returns integer );

    function Main( x : integer returns integer )
      function AddX( y : integer returns integer )
        y + x % Environment capture of outer scalar 'x'
      end function

      let
        % Higher-Order Function call & Direct Tuple Swap
        res := ApplyTwice( AddX, 10 );
        A, B := B, A % Zero-copy O(1) descriptor swap
      in
        res
      end let
    end function
    ```

12. **Static Liveness Analysis & Copy-on-Write (CoW)**:
    - **Topological Edge Liveness (`scan_edge_liveness`)**: Topologically sorts dataflow graphs (`topo_sort gr`) and tracks output port consumer fanout (`scan_fanout`), identifying exact last-use boundary edges (`EdgeFreeMap`).
    - **Copy-on-Write Memory Safety**: Assignments (`B := A`) copy only 24-byte struct descriptors (`data` pointer, rank, size). Mutating operations (`B[i] := v`) automatically update in-place if `B` is unshared (last-use) or trigger CoW allocation if `A` is still live elsewhere.
    ```sisal
    let
      A := array [1: 10, 20, 30];
      B := A;
      B2 := B[1: 999] % Automatic CoW if A is live, or in-place update if A is dead
    in
      A, B2
    end let
    ```

---

## Sisal C++ Runtime vs. Python NumPy Architecture

| Feature / Dimension | Sisal C++ (`sisal_array_t`) | Python NumPy (`numpy.ndarray`) |
| :--- | :--- | :--- |
| **Variable Assignment (`B := A`)** | **Zero-Copy Stack Struct**: Copies a 24-byte C struct (`data` pointer, rank, size). $O(1)$ constant time. | **Zero-Copy Reference**: Binds a Python object reference (`PyArrayObject*`) pointing to shared heap memory. |
| **Mutation & Safety** | **Pure Functional Immutability (CoW)**: Performs **in-place update** if `A` is dead (last-use), or **automatic CoW copy** if `A` is live elsewhere. | **Mutable by Default**: Modifying `b[0]` mutates `a` when `b = a` or `b = a[:]`. Requires manual `.copy()` calls to avoid side-effects. |
| **Broadcasting Engine** | **Built-in `conform_check`**: Implements exact right-aligned trailing axis broadcasting rules matching NumPy/JAX. | Standard `np.broadcast_arrays` rules ($d_A = d_B$, $d_A=1$, or $d_B=1$). |
| **Execution Performance** | **Compiled Native C++23**: Native machine code compiled via `clang++`/`g++`. Loop nests (`forall`) are vectorizable by LLVM without GIL locks. | **Interpreted / C-Extension**: Fast for C primitives, but encounters Python interpreter / GIL overhead on explicit loops. |
| **Python Interoperability** | **Zero-Copy C Export**: Flat `data` pointer can be wrapped directly by `pybind11::array_t` without memory copying. | Standard Python data science ecosystem. |

---

## Pending Items & Future Roadmap

- **Monadic Linear State Threading**:
  - Linear state threading (`op : Array -> (Result, Array)`) to guarantee 100% in-place updates without dynamic reference checks.
- **Lazy Layout Transformations**:
  - Virtualizing stride/offset transformations for `TRANSPOSE`, `RESHAPE`, and `REVERSE` to fuse directly into downstream `forall` loops without intermediate buffer allocations.
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

### Code Coverage Tracking (`bisect_ppx`)

To collect code coverage statistics across the compiler while executing all 408 end-to-end regression tests:

```bash
# 1. Run parallel E2E tests with coverage tracking
mkdir -p _coverage
BISECT_FILE=$(pwd)/_coverage/bisect python3 test/e2e/run_dv_e2e_parallel.py

# 2. View terminal coverage summary
bisect-ppx-report summary --per-file --coverage-path _coverage/

# 3. Generate HTML coverage report
bisect-ppx-report html --coverage-path _coverage/ -o _coverage/html/
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
