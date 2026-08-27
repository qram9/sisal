# Sisal 2.0 Language Tutorial & Reference Guide

Welcome to the **Sisal 2.0 Language Tutorial**. This guide is inspired by the classic Lawrence Livermore National Laboratory (LLNL) & University of East Anglia (UEA) Sisal tutorial (*John R. W. Glauert, John Feo, Tom DeBoni*), updated and expanded to cover all modern **Sisal 2.0** features in the `git_sisal` optimizing compiler and C++23 runtime.

---

## Table of Contents

1. [Introduction to Sisal 2.0 & Dataflow Parallelism](#1-introduction-to-sisal-20--dataflow-parallelism)
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

## 1. Introduction to Sisal 2.0 & Dataflow Parallelism

**Sisal** (*Streams and Iteration in a Single Assignment Language*) is a pure functional programming language designed for high-performance parallel computing. 

### Core Principles:
- **Single Assignment / Immutability**: Values are immutable once defined. Variables represent values, not memory locations.
- **Implicit Parallelism**: Because functions have no side-effects, independent dataflow expressions execute concurrently automatically.
- **Sisal 2.0 Innovations**: Introduced dense rank-polymorphic dope-vector arrays (`array_dv`), first-class higher-order functions (closures), Einstein summation (`EINSUM`), hardware SIMD intrinsics (`float4`, `mat2`), stream coroutines, and side-effect monad ordering.

---

## 2. Expression Syntax, Scalar Types & Monadic `printf`

Sisal supports basic scalar types: `integer`, `real`, `double`, `boolean`, `character`.

### Basic Arithmetic & Conditional Expressions
```sisal
function Calculate( a, b : integer returns integer )
  if a > b then
    (a + b) * 2
  else
    (b - a) / 2
  end if
end function
```

### Side-Effect Sequencing via Monad Ordering & `printf`
Sisal 2.0 reconciles pure functional dataflow graphs with deterministic I/O logging. `printf` calls can be freely inserted into code with **guaranteed execution sequence**:

```sisal
let
  _ := printf("Starting computation for input val=%d\n", input_val);
  result := HeavyCompute(input_val);
  _ := printf("Completed computation: result=%d\n", result)
in
  result
end let
```
*Note: The compiler automatically inserts monad control ports (`PRINTF_TY`) to order log calls sequentially while leaving pure dataflow nodes 100% parallelizable.*

---

## 3. User-Defined Types & Rank-Polymorphic Dense Arrays (`array_dv`)

Arrays in Sisal 2.0 are dense multi-dimensional structures represented by the `sisal_array_t` dope vector.

### Array Construction & Indexing
```sisal
type IntArray = array [ integer ];

function ArrayDemo( returns IntArray, integer )
  let
    A := array [1: 10, 20, 30, 40, 50];
    val := A[3] % Returns 30
  in
    A, val
  end let
end function
```

### Zero-Copy Slicing ($O(1)$ Metadata Shift)
Slicing an array creates a zero-copy **View** without allocating memory or copying elements:

```sisal
let
  A := array [1: 10, 20, 30, 40, 50];
  SubSlice := A[2..4] % Returns [20, 30, 40] in O(1) time
in
  SubSlice
end let
```

---

## 4. APL-Style Combinators & Einstein Summation (`EINSUM`)

Sisal 2.0 provides native array combinators and Einstein summation for high-performance mathematical modeling.

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

---

## 5. Parallel Loops (`forall`) & Reductions

The `forall` construct expresses data-parallel execution across arrays or index ranges.

### Parallel Vector Multiplication
```sisal
function ScaleVector( A : array[real]; factor : real returns array[real] )
  for x in A
  returns array of x * factor
  end for
end function
```

### Cross-Product & Reductions
```sisal
function MatrixVectorMult( M : array[array[real]]; V : array[real] returns array[real] )
  for row in M
    dot_product := for x in row at i
                     val := x * V[i]
                   returns value of sum val
                   end for
  returns array of dot_product
  end for
end function
```

---

## 6. Sequential Loops (`for initial`) & Zero-Copy Tuple Swapping

Sequential loops carry state across iterations via `for initial ... repeat`.

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

Sisal 2.0 supports first-class functions, nested procedures, lexical environment closures, and recursive list dispatch.

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

Sisal 2.0 maps fixed-size vectors directly to CPU SIMD registers (ARM Neon, x86 AVX-512) and GPU vector types.

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

## 9. Coroutines & Stream Pipeline Processing

Streams represent continuous sequences of values processed lazily via coroutine generators.

```sisal
function PrimeGenerator( limit : integer returns stream[integer] )
  let
    S := STREAM_INTEGERS(2, limit);
    Primes := STREAM_SIEVE(S)
  in
    Primes
  end let
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
