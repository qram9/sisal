# Sisal-2026 Language Tutorial & Reference Guide

Welcome to the **Sisal-2026 Language Tutorial**. This guide is inspired by the classic Lawrence Livermore National Laboratory (LLNL) & University of East Anglia (UEA) Sisal tutorial (*John R. W. Glauert, John Feo, Tom DeBoni*), updated and expanded to cover all modern **Sisal-2026** features in the `git_sisal` optimizing compiler and C++23 runtime.

---

## Table of Contents

1. [Introduction to Sisal-2026 & Dataflow Parallelism](#1-introduction-to-sisal-2026--dataflow-parallelism)
2. [Expression Syntax, Scalar Types & Monadic `printf`](#2-expression-syntax-scalar-types--monadic-printf)
3. [User-Defined Types & Rank-Polymorphic Dense Arrays (`array_dv`)](#3-user-defined-types--rank-polymorphic-dense-arrays-array_dv)
4. [APL-Style Combinators & Einstein Summation (`EINSUM`)](#4-apl-style-combinators--einstein-summation-einsum)
5. [Parallel Loops (`forall`) & Reductions](#5-parallel-loops-forall--reductions)
6. [Sequential Loops (`for initial`) & Zero-Copy Tuple Swapping](#6-sequential-loops-for-initial--zero-copy-tuple-swapping)
7. [First-Class Higher-Order Functions (HOFs) & Closures](#7-first-class-higher-order-functions-hofs--closures)
8. [SIMD Small Vectors (`float4`) & Fixed Matrix Intrinsics (`mat2`)](#8-simd-small-vectors-float4--fixed-matrix-intrinsics-mat2)
9. [Coroutines & Stream Pipeline Processing](#9-coroutines--stream-pipeline-processing)
10. [Static Liveness Analysis, Copy-on-Write (CoW) & NumPy Comparison](#10-static-liveness-analysis-copy-on-write-cow--numpy-comparison)

---

## 1. Introduction to Sisal-2026 & Dataflow Parallelism

**Sisal** (*Streams and Iteration in a Single Assignment Language*) is a single-assignment dataflow language designed for high-performance parallel computing. 

### Core Principles & Architectural Heritage:
- **Single Assignment / Immutability**: Values are immutable once defined. Variables represent values, not memory locations.
- **Implicit Parallelism**: Because functions have no side-effects, independent dataflow expressions execute concurrently automatically.
- **APL & NumPy Heritage**: Sisal-2026 introduces **dense rank-polymorphic dope-vector arrays (`array_dv`)**, continuing an architectural lineage originating in **APL** (Iverson, 1962) and perfected in modern computing via **NumPy**, **PyTorch**, and **JAX**.
- **Natural Fit for Single-Assignment Semantics**: Dope-vector metadata operations (slicing `A[i, ..]`, reshaping, transposition) fit naturally into single-assignment dataflow languages as $O(1)$ constant-time metadata views. Combined with Copy-on-Write (CoW) reference counting, `array_dv` provides 100% single-assignment immutability guarantees alongside native C/C++ execution performance—eliminating the need to rely on compiler static analysis passes (*build-in-place* / *update-in-place*) to infer layout intentions.
- **Sisal-2026 Innovations**: First-class higher-order functions (closures), Einstein summation (`EINSUM`), hardware SIMD intrinsics (`float4`, `mat2`), stream coroutines, and side-effect monad ordering.

---

## 2. Expression Syntax, Scalar Types & Monadic `printf`

Sisal supports basic scalar types: `integer`, `real`, `double`, `boolean`, `character`.

> 💡 **Floating-Point Literal Exponent Notation**:
> - Exponents with `e` or `E` (e.g. `1.0e-5`, `3.14e0`) denote single-precision **`real`** values (`float`).
> - Exponents with `d` or `D` (e.g. `1.0d-5`, `2.718281828459d0`) denote double-precision **`double`** values (`double`).
>
> ⚠️ **Strict Type Safety**:
> Sisal-2026 is strictly statically typed. Binary operators cannot mix distinct scalar types without explicit conversion (e.g., `double(i) + d` or `real(count)`). Implicit type coercion is forbidden.

### Basic Arithmetic & Strict Type Conversion
```sisal
function MixedArithmetic( i : integer; d : double returns double )
  % ERROR: i + d  (Implicit mixing of integer and double is forbidden!)

  % CORRECT: Explicitly promote i to double before addition
  double(i) + d
end function

function Calculate( a, b : integer returns integer )
  if a > b then
    (a + b) * 2
  else
    (b - a) / 2
  end if
end function
```

### Side-Effect Sequencing via Monad Ordering & `printf`
Sisal-2026 reconciles pure functional dataflow graphs with deterministic I/O logging using two primary idioms:
1. **Wildcard Binding (`_ := printf(...)`)**: Discards output return when logging status.
2. **Value Pass-Through Assignment (`res := printf("%d\n", val)`)**: Evaluates and returns the primary argument value after printing, enabling inline logging without temporary variables.

```sisal
let
  % 1. Wildcard binding pattern
  _ := printf("Starting computation for input val=%d\n", input_val);
  
  % 2. Value pass-through pattern (prints result and binds it to result)
  result := printf("Completed computation: result=%d\n", HeavyCompute(input_val))
in
  result
end let
```
*Note: The compiler automatically inserts monad control ports (`PRINTF_TY`) to order log calls in strict **lexicographic order** while leaving pure dataflow nodes 100% parallelizable.*

---

## 3. User-Defined Types & Rank-Polymorphic Dense Arrays (`array_dv`)

Arrays in Sisal-2026 are dense multi-dimensional structures represented by the `sisal_array_t` dope vector.

> ⚠️ **First Edition Language Note**:
> In the First Edition of Sisal-2026, the legacy `array` syntax is **not supported**. All multi-dimensional arrays are exclusively represented using **`array_dv`** (dense dope vectors). Support for legacy `array` representations may be evaluated in future editions of the language. If irregular or ragged structures are required in Edition 1, use algebraic recursive union types (`union [ nil_tag: null; cons_tag: record [ head: ...; tail: ... ] ]`) as demonstrated in [Section 7](#7-first-class-higher-order-functions-hofs--closures).
>
> 💡 **Rank-Polymorphic Dope Vector Principle**:
> `array_dv[T]` represents a flat multi-dimensional dope vector (`sisal_array_t`). The rank (1D vector, 2D matrix, 3D tensor) is a dynamic runtime property of the dope vector. Therefore, nested types like `array_dv[array_dv[T]]` are **invalid**. Matrices and higher-dimensional tensors are declared simply as **`array_dv[T]`**.
>
> 💡 **Design Philosophy: Not a Weakness, But a Strength**:
> Sisal-2026 removes the need for compiler optimization passes to guess layout intentions between ragged vs. dense arrays. Dense multi-dimensional computations explicitly use `array_dv[T]`, while irregular patterns use algebraic recursive union types. We believe this explicit division is not a weakness, but rather a strength: it eliminates compiler ambiguity and gives programmers transparent, predictable control over vectorization and performance.

> [!NOTE]
> For an in-depth reference on static rank polymorphism, prefix agreement, unification, and dynamic shape inference in Sisal-2026, read the complete guide:
> 📘 **[Rank Polymorphism: A Complete Guide](Rank_Polymorphism_Complete_Guide.md)**

### Array Construction & Indexing
Array literal syntax `array_dv [1: v1, v2, ...]` creates a **flat 1D vector**. To construct a multi-dimensional matrix, initialize a flat 1D vector literal and apply `reshape`:

```sisal
type IntArray = array_dv [ integer ];

function MatrixDemo( returns IntArray, integer )
  let
    % 1D Vector literal (6 elements)
    Flat := array_dv [1: 10, 20, 30, 40, 50, 60];
    
    % Reshape flat 1D vector into 2x3 rank-2 Matrix
    M := reshape(Flat, 2, 3);
    
    % Coordinate indexing M[2, 1] returns scalar integer (40)
    val := M[2, 1]
  in
    M, val
  end let
end function
```

### Zero-Copy Slicing ($O(1)$ Metadata Shift)
Slicing an array creates a zero-copy **View** without allocating memory or copying elements:

```sisal
let
  A := array_dv [1: 10, 20, 30, 40, 50];
  SubSlice := A[2..4] % Returns [20, 30, 40] in O(1) time
in
  SubSlice
end let
```

---

## 4. APL-Style Bulk Operations & Einstein Summation (`EINSUM`)

Sisal-2026 provides native whole-array (APL-style) bulk operations and Einstein summation for high-performance mathematical modeling.

> [!NOTE]
> For a complete reference of all 58 whole-array bulk operations (reductions, scans, statistical functions, axis reductions, sorting, and structural manipulators), see:
> 📘 **[Bulk Operations & Whole-Array Primitives Reference](bulk_ops_reference.md)**

### Array Combinators
```sisal
Doubled := MAP(A, function(x) x * 2 end function);
Total   := REDUCE(A, +);
Shifted := ROTATE(A, 1);
MaxVal  := REDUCE_AXIS(Matrix, max, 1)
```

### Tensor Contraction with `EINSUM`
Matrix multiplication and general multi-tensor contractions map directly to hardware BLAS (`cblas_dgemm`):

```sisal
% Matrix Multiplication (C = A x B)
C := EINSUM("ij,jk->ik", MatrixA, MatrixB)

% Batched Tensor Contraction
T := EINSUM("bij,bjk->bik", TensorA, TensorB)
```

> [!NOTE]
> For complete compiler lowering pipelines, parser grammars, BLAS fast-paths, and test suite details, see:
> 📘 **[Einstein Summation (`EINSUM`) Lowering & Support Guide](einsum_lowering_guide.md)**

---

## 5. Parallel Loops (`forall`) & Reductions

The `forall` construct expresses data-parallel execution across arrays or index ranges.

### Parallel Vector Multiplication
```sisal
function ScaleVector( A : array_dv[real]; factor : real returns array_dv[real] )
  for x in A
  returns array_dv of x * factor
  end for
end function
```

### Cross-Product & Reductions
```sisal
function MatrixVectorMult( M : array_dv[real]; V : array_dv[real] returns array_dv[real] )
  for row in M
    dot_product := for x in row at i
                     val := x * V[i]
                   returns value of sum val
                   end for
  returns array_dv of dot_product % Elevates 1D row dot-products into a rank-2 result array_dv
  end for
end function
```

---

## 6. Sequential Loops (`for initial`) & Zero-Copy Tuple Swapping

Sequential loops carry state across iterations via `for initial ... repeat`.

> [!NOTE]
> For a detailed technical comparison of `for initial` loop semantics, initial seed evaluation rules, and comparisons with C/Fortran loops, see:
> 📘 **[Sisal `for initial` Loop Behavior & C/Fortran Comparison](loop_behavior_comparison.md)**
> 📘 **[Sisal `for initial` Seed Evaluation Semantics](for_initial_seed_semantics.md)**

### Iterative Convergence Loop
```sisal
function Factorial( n : integer returns integer )
  for initial
    i := 1;
    acc := 1
  while i <= n repeat
    i := old i + 1;
    acc := old acc * old i
  returns value of acc
  end for
end function
```

### Zero-Copy Multi-Assignment Tuple Swapping
Swapping variables or loop states (`A, B := B, A`) executes as an $O(1)$ 24-byte descriptor swap with zero memory copying:

```sisal
for initial
  A := initial_A;
  B := initial_B
repeat
  % Zero-copy descriptor pointer swap
  A, B := old B, old A
while ...
```

---

## 7. First-Class Higher-Order Functions (HOFs) & Closures

Sisal-2026 supports first-class functions, nested procedures, lexical environment closures, and recursive list dispatch.

### Closures & Variable Capture
Nested functions capture variables from enclosing outer scopes:

```sisal
type IntOp = function( integer returns integer );

function ApplyTwice( f : IntOp; val : integer returns integer )
  f( f( val ) )
end function

function Main( x : integer returns integer )
  function AddX( y : integer returns integer )
    y + x % Environment capture of outer scalar 'x'
  end function

  let
    res := ApplyTwice( AddX, 10 ) % Returns 10 + x + x
  in
    res
  end let
end function
```

### Functions Stored in Algebraic Data Structures
Functions can be stored in recursive `union` lists and dispatched dynamically:

```sisal
type FuncList = union[ nil_tag: null; cons_tag: record[ head: IntOp; tail: FuncList ] ];

function DispatchAll( lst : FuncList; val : integer returns integer )
  tagcase cell := lst
  tag nil_tag:  val
  tag cons_tag:
    let
      f := cell.head;
      nxt := f( val )
    in
      DispatchAll( cell.tail, nxt )
    end let
  end tagcase
end function
```

---

## 8. SIMD Small Vectors (`float4`) & Fixed Matrix Intrinsics (`mat2`)

Sisal-2026 maps fixed-size vectors directly to CPU SIMD registers (ARM Neon, x86 AVX-512) and GPU vector types.

```sisal
function TransformPoints( p : float4; m : mat2 returns float4 )
  let
    v1 := float2(p.x, p.y);
    v2 := m * v1 % Fast hardware SIMD matrix-vector product
  in
    float4(v2.x, v2.y, p.z, p.w)
  end let
end function
```

---

## 9. Coroutines, Stream Processing & Array Broadcasting

### C++20 Stackless Stream Coroutines (`co_yield`)
In Sisal-2026, streams (`stream[T]`) are lowered directly to native **C++20 stackless coroutines (`sisal_generator<T>`)**. Unlike traditional eager pipelines that allocate large intermediate ring-buffers or POSIX stackful context switches (`swapcontext`), Sisal-2026 stream producers yield elements on-demand into consumer loops via `co_yield`:

- **Zero-Allocation Pipeline**: The C++ compiler applies Heap Allocation Elision Optimization (HALO) to inline coroutine frames directly onto the caller's stack frame.
- **Ultra-Fast Context Switches**: Context transitions execute purely in user space via basic register jumps in **2–5 nanoseconds** (30x–100x faster than kernel/ucontext thread switches).
- **Infinite Stream Evaluation**: Streams can represent unbounded mathematical sequences (e.g. Sieve of Eratosthenes) evaluated on-demand without memory overflow.

```sisal
% Demand-driven prime sieve coroutine pipeline
function PrimeGenerator( limit : integer returns stream[integer] )
  let
    S      := STREAM_INTEGERS(2, limit);
    Primes := STREAM_SIEVE(S)
  in
    Primes % Consumer loop pulls elements lazily via C++20 co_yield
  end let
end function
```

> [!NOTE]
> For complete compiler transformation details and coroutine promise definitions, see:
> 📘 **[Cooperative Coroutine Streams Design](coroutine_streams_design.md)**
> 📘 **[Stream Coroutine Lowering Architecture](stream_coroutine_lowering.md)**

---

### Array Broadcasting & Stride-0 Axis Expansion
Sisal-2026 implements built-in right-aligned trailing axis broadcasting (matching NumPy / JAX rules) via `conform_check` and `sisal_dv_offset_at` in `runtime/sisal_runtime.h`.

When operating on arrays of unequal dimensions (e.g., adding a 1D vector `V` to a 2D matrix `M`):
1. **Right-Aligned Axis Matching**: The smaller rank array is right-aligned against the larger array's shape.
2. **Dimension Compatibility**: For each dimension pair `(da, db)`, axes are compatible if `da == db` or `da == 1` or `db == 1`.
3. **Zero-Copy Stride-0 Expansion**: Dimensions of size 1 are expanded to match target shape by setting `stride = 0`. Evaluating element offsets (`linear_offset += coords[axis] * stride`) incurs zero element byte copies and zero allocation overhead.

```sisal
% Broadcast a 1D bias vector B [3] across a 2D matrix M [5, 3]
function AddBias( M : array_dv[real]; B : array_dv[real] returns array_dv[real] )
  M + B % Zero-copy stride-0 broadcast addition
end function
```

---

## 10. Static Liveness Analysis, Copy-on-Write (CoW) & NumPy Comparison

### Static Liveness Analysis (`scan_edge_liveness`)
The compiler analyzes dataflow edge liveness to identify the **last topological use** of every array:
- **`B := A` Assignment**: Copies only the 24-byte descriptor (`B.data = A.data`). Zero element bytes copied.
- **Mutating Operations (`B[i] := v`)**:
  - **Shared (Both A and B Live)**: Allocates a new buffer (`malloc` + `memcpy`) to protect `A`'s immutability.
  - **Unshared (Last-Use / Dead A)**: Updates in-place inside `B.data` without memory allocation.

### Architectural Comparison: Sisal C++ vs. Python NumPy

| Feature / Dimension | Sisal C++ (`sisal_array_t`) | Python NumPy (`numpy.ndarray`) |
| :--- | :--- | :--- |
| **Variable Assignment (`B := A`)** | **Zero-Copy Stack Struct**: Copies a 24-byte C struct (`data` pointer, rank, size). $O(1)$ constant time. | **Zero-Copy Reference**: Binds a Python object reference (`PyArrayObject*`) pointing to shared heap memory. |
| **Mutation & Safety** | **Pure Functional Immutability (CoW)**: Performs **in-place update** if `A` is dead (last-use), or **automatic CoW copy** if `A` is live elsewhere. | **Mutable by Default**: Modifying `b[0]` mutates `a` when `b = a` or `b = a[:]`. Requires manual `.copy()` calls to avoid side-effects. |
| **Broadcasting Engine** | **Built-in `conform_check`**: Implements exact right-aligned trailing axis broadcasting rules matching NumPy/JAX. | Standard `np.broadcast_arrays` rules ($d_A = d_B$, $d_A=1$, or $d_B=1$). |
| **Execution Performance** | **Compiled Native C++23**: Native machine code compiled via `clang++`/`g++`. Loop nests (`forall`) are vectorizable by LLVM without GIL locks. | **Interpreted / C-Extension**: Fast for C primitives, but encounters Python interpreter / GIL overhead on explicit loops. |
| **Python Interoperability** | **Zero-Copy C Export**: Flat `data` pointer can be wrapped directly by `pybind11::array_t` without memory copying. | Standard Python data science ecosystem. |

---

### Case Study: Gauss-Jordan Elimination (Sisal 1.2 vs. Sisal-2026)

For a complete, step-by-step comparative analysis of matrix solving, row slicing (`A[i, ..]`), scalar indexing (`A[i, j]`), and zero-copy row swapping, read the dedicated case study:
📘 **[Gauss-Jordan Elimination: Sisal 1.2 vs. Sisal-2026 Case Study](gauss_jordan_comparison.md)**

---

## Compiling & Running Sisal Programs

To compile a Sisal source file (`program.sis`) to a C++ binary using `git_sisal`:

```bash
# 1. Compile Sisal source to C++23 code
dune exec src/main.exe -- --c=output.cpp program.sis

# 2. Compile C++ output with clang++ / g++
clang++ -O3 -std=c++23 -I./runtime output.cpp -o program

# 3. Execute native binary
./program
```

To run the complete parallel E2E test suite across all 417 test groups:
```bash
python3 test/e2e/run_dv_e2e_parallel.py
```
