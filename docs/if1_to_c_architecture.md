# IF1 to C-AST: The "First to Silicon" Architecture

This document outlines the architectural plan for lowering Sisal's IF1 intermediate representation to a modern, OCaml-native C Abstract Syntax Tree (C-AST). 

The primary goal of this bridge is **"First to Silicon"**—leveraging standard C compilers (Clang/GCC) to automatically map high-level parallel constructs to multi-core CPUs and SIMD units (AVX2, AVX-512, NEON) without the complexity of a raw assembly or LLVM IR backend.

---

## 1. High-Level Compiler Pipeline

The Sisal compiler pipeline transitions from the graph-based dataflow of IF1 to the structured, imperative control flow of C.

```mermaid
graph TD
    A[Sisal Source] -->|Parser| B(AST)
    B -->|Frontend| C{IF1 Graph}
    
    subgraph "IF1 Optimizations"
        C --> D[Constant Folding]
        C --> E[Railway Monad / Error Handling]
        C --> F[Loop Invariant Code Motion]
    end
    
    subgraph "IF1 to C-AST Lowering"
        D & E & F --> G[Strip Mining & Vectorization]
        G --> H[Task / Thread Extraction]
        H --> I{OCaml C-AST}
    end
    
    subgraph "Code Generation"
        I --> J[C99 Code Generator]
        J --> K[out.c]
        K --> L((Clang / GCC))
        L -.-> M[AVX2 / NEON / Multi-core Silicon]
    end
```

---

## 2. The OCaml C-AST Design

The Python-based `c_ast` is ported to a strongly-typed OCaml Algebraic Data Type (ADT). This ensures memory safety, pattern-matching capabilities, and seamless integration with the existing IF1 lowering passes.

Crucially, this ADT introduces **First-Class Pragmas** and **Vector Types** to support modern hardware.

```ocaml
(* docs/code_snippets/c_ast_types.ml *)

type qualifier = Const | Volatile | Restrict

type c_type = 
  | Basic of string                       (* e.g., "int", "float", "double" *)
  | Pointer of c_type * qualifier list    (* e.g., float *restrict *)
  | Array of c_type * int option          (* e.g., int a[10] *)
  | Vector of c_type * int                (* SIMD: __attribute__((vector_size(N))) *)
  | Struct of string * (string * c_type) list

type expr = 
  | Id of string
  | LitInt of int
  | LitFloat of float
  | BinOp of binary_op * expr * expr
  | Call of string * expr list
  | Deref of expr                         (* *ptr *)
  | AddrOf of expr                        (* &var *)
  | Index of expr * expr                  (* arr[i] *)
  | Cast of c_type * expr

type stmt = 
  | Decl of c_type * string * expr option
  | Expr of expr
  | For of stmt * expr * expr * stmt list
  | If of expr * stmt list * stmt list
  | Return of expr
  | Pragma of string                      (* e.g., "omp parallel for simd" *)
  | Compound of stmt list
```

---

## 3. Mapping IF1 to Silicon

### 3.1 Data Parallelism: The `FORALL` Node

Sisal's `FORALL` loops are embarrassingly parallel. The translation targets **OpenMP** for multi-threading across cores and **Clang Vector Extensions** for SIMD lane execution.

**Translation Strategy:**
1.  Identify the `FORALL` boundaries and reduction operators (e.g., `SUM`, `PRODUCT`).
2.  Emit a `Pragma("omp parallel for simd reduction(+:...)")`.
3.  Emit a standard `For` loop in the C-AST.

```mermaid
graph LR
    subgraph "IF1 Graph"
        A[FORALL Node] -->|Generator| B(1 .. N)
        A -->|Body| C(A[i] + B[i])
        A -->|Returns| D(ARRAY_OF)
    end
    
    subgraph "C-AST"
        E[Pragma: omp parallel for simd]
        F[For i = 1 to N]
        G[C[i] = A[i] + B[i]]
        E --> F
        F --> G
    end
    
    A ==> E
```

### 3.2 Task Parallelism: Recursion & `Let Rec`

GPU and strict SIMD models struggle with recursion. For CPUs, we utilize **Work-Stealing** deques to execute divide-and-conquer Sisal algorithms. To ensure performance on Apple Silicon and portability to Linux, we avoid Intel TBB and instead use a dual-backend approach.

**Translation Strategy:**
1.  Detect `Let_rec` or heavy function invocations.
2.  Emit a platform-agnostic `SISAL_SPAWN` and `SISAL_SYNC` macro.
3.  The runtime header (`sisal_task.h`) maps these to:
    *   **macOS:** Grand Central Dispatch (`dispatch_group_async`).
    *   **Linux/Windows:** OpenMP Tasks (`#pragma omp task`).

```mermaid
sequenceDiagram
    participant Main as Main Thread
    participant Pool as Task Pool (GCD/OMP)
    
    Main->>Pool: SISAL_SPAWN(QuickSort_Left)
    Main->>Pool: SISAL_SPAWN(QuickSort_Right)
    Note over Pool: Idle cores (P/E clusters) steal tasks<br/>from the global/local deques
    Pool-->>Main: SISAL_SYNC()
    Main->>Main: Merge Results
```

### 3.3 The "Railway Monad" in C

IF1 uses a "Railway Monad" to handle errors (e.g., Division by Zero, Out of Bounds) safely before executing a loop. In C, this maps to predicated execution or early exits.

*   **Scalar Context:** Translated to standard `if (error) { goto error_handler; }`.
*   **Vector Context (SIMD):** OpenMP/SIMD cannot easily `goto` out of a lane. The compiler must hoist the error check *outside* the SIMD loop or use **Masked Operations**.

```c
// Example of Hoisted Error Check generated by C-AST
int err = check_bounds(A, N);
if (err) return ERROR_OUT_OF_BOUNDS;

#pragma omp parallel for simd
for (int i = 0; i < N; i++) {
    // Safe to execute blindly in SIMD
    C[i] = A[i] / B[i]; 
}
```

---

## 4. Next Steps for Implementation

1.  **Initialize `src/c_ast/`**: Create the OCaml modules (`c_ast.ml`, `c_ast_print.ml`) for the ADT defined above.
2.  **The Lowering Pass (`src/to_c/`)**: Create a visitor that walks the IF1 graph and instantiates `c_ast` nodes.
3.  **Memory Model Definition**: Define how Sisal Arrays (and their dope vectors) map to C `structs` to ensure zero-copy views and efficient SIMD gathers.
