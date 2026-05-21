# Rank Polymorphism: A Complete Guide

## What Is Rank Polymorphism?

**TL;DR:** Rank polymorphism lets you write a function once for scalars, and it **automatically works on arrays of any dimension** (vectors, matrices, tensors, etc.) without explicit loops.

---

## The Big Idea

### Example: Linear Interpolation

**Write once (for scalars):**
```apl
lerp ← {(1-⍵)×⍺ + ⍵×⍵}  (* APL syntax *)
```

**Works on everything:**
```apl
3 lerp 0.5 7      (* scalars → scalar: 5.0 *)
3 lerp 0.5 [7 9]  (* scalar + vector → vector: [5.0 6.0] *)
3 lerp 0.5 [[7 9] [2 4]]  (* scalar + matrix → matrix *)
[1 2] lerp 0.5 [7 9]      (* vector + vector → vector *)
(* ...and so on for any rank! *)
```

**The magic:** You never wrote a loop! The language **automatically** breaks arrays into cells, applies the scalar operation, and reconstructs the result.

---

## Core Concepts

### Rank

**Rank = Number of dimensions**

```
0: Scalar        42
1: Vector        [1 2 3]
2: Matrix        [[1 2]
                  [3 4]]
3: 3D Tensor     [[[1 2] [3 4]]
                  [[5 6] [7 8]]]
```

### Shape

**Shape = Size of each dimension**

```
Scalar:     shape = []        (no dimensions)
[1 2 3]:    shape = [3]       (3 elements)
[[1 2]
 [3 4]]:    shape = [2 2]     (2 rows, 2 cols)
```

### Cells and Frames

**When applying a function:**
- **Cells:** The pieces the function actually operates on
- **Frame:** The structure built around the cells

**Example:** `add : scalar × scalar → scalar`

Applied to matrices:
```
[[1 2]     [[10 20]       [[11 22]
 [3 4]]  +  [30 40]]   =   [33 44]]

Frame: [2 2]  (iterate over 2×2 grid)
Cells: rank 0 (scalars)

Breaks down to:
1 + 10 = 11
2 + 20 = 22
3 + 30 = 33
4 + 40 = 44
```

---

## The Lifting Mechanism

### How Rank Polymorphism Works

**1. Determine expected cell rank**
```ocaml
(* Function signature includes cell rank *)
scalar_add : ⟨0⟩ int × ⟨0⟩ int → ⟨0⟩ int
              ↑             ↑         ↑
              expected rank 0 cells
```

**2. Break arguments into cells**
```
Argument: [[1 2] [3 4]]  (rank 2)
Expected: rank 0 cells
→ Break into: [1, 2, 3, 4]  (4 scalar cells)

Frame shape: [2 2]
```

**3. Apply function to each cell**
```
Cell 1: 1 + 10 = 11
Cell 2: 2 + 20 = 22
Cell 3: 3 + 30 = 33
Cell 4: 4 + 40 = 44
```

**4. Reconstruct with frame shape**
```
Result cells: [11, 22, 33, 44]
Frame shape: [2 2]
→ [[11 22] [33 44]]
```

---

## Type System

### Remora's Dependent Type System

**Justin Slepak (2014) - First static type system for rank polymorphism**

**Array Type:**
```ocaml
type array_ty = 
  | Array of shape * element_ty

type shape = 
  | Shape of int list        (* Known shape: [2 3] *)
  | ShapeVar of var          (* Unknown shape: 'n *)
  | ShapeExpr of shape_expr  (* Computed: n + 1 *)
```

**Function Type with Rank:**
```ocaml
(* Π notation - dependent product *)
∀(n : Nat). Array[n] int → Array[n] int
             ↑              ↑
             shape variable  same shape in output

(* Cell rank annotation *)
add : ⟨0⟩ int × ⟨0⟩ int → ⟨0⟩ int
      ↑
      operates on rank-0 cells
```

### Shape Compatibility

**Prefix Agreement Rule (APL/J)**

Shapes agree if one is a prefix of the other:

```
[2 3]   and [2 3 4]   → Compatible (prefix [2 3])
[2 3]   and [2]       → Compatible (prefix [2])
[2 3]   and [3 4]     → INCOMPATIBLE

Result shape: longest shape
```

**Example:**
```
Scalar + Matrix:
  []  +  [2 3]  → result: [2 3]
  
Vector + Matrix:
  [3] +  [2 3]  → result: [2 3]
  
Incompatible:
  [3] +  [2 4]  → ERROR (not prefix agreement)
```

---

## Unification for Rank Polymorphism

### The Problem

**Standard unification:**
```ocaml
int ~ int  ✓
int ~ bool ✗
'a ~ int   (* bind 'a = int *)
```

**Rank-polymorphic unification:**
```ocaml
Array[2 3] int ~ Array[2 3] int  ✓
Array['n] int  ~ Array[5] int    (* bind 'n = 5 *)
Array[2 3] int ~ Array[2 3 4] int  (* Lifting? *)
```

### Extended Unification Rules

**Rule 1: Exact Shape Match**
```ocaml
unify (Array[s1] t1) (Array[s2] t2) =
  unify_shape s1 s2 >>= fun () ->
  unify t1 t2
```

**Rule 2: Shape Variable Binding**
```ocaml
unify (Array[ShapeVar 'n] t) (Array[Shape [2 3]] t) =
  bind 'n [2 3]
```

**Rule 3: Prefix Agreement (Limited Rank Polymorphism)**
```ocaml
unify_with_lifting (Array[s1] t1) (Array[s2] t2) =
  if is_prefix s1 s2 || is_prefix s2 s1 then
    let result_shape = longer_of s1 s2 in
    Ok (Array[result_shape] t1)
  else
    Error "Shape mismatch"
```

---

## Implementation for SISAL

### Limited Rank Polymorphism (Practical Subset)

**Goal:** Support most useful cases without full dependent types

### Phase 1: Shape-Annotated Arrays

**Extend type system:**
```ocaml
type sisal_type =
  | INTEGER
  | REAL
  | BOOLEAN
  | Array of shape_constraint * sisal_type
  | ShapeVar of string  (* 'n, 'm, etc. *)

type shape_constraint =
  | Fixed of int list        (* [2 3 4] *)
  | Variable of string       (* 'n *)
  | AtLeast of int           (* rank >= 2 *)
  | Any                      (* any rank *)
```

**Function signatures:**
```sisal
(* Scalar function - cell rank 0 *)
FUNCTION add(x, y : integer) RETURNS integer
  TYPE: ⟨0⟩ int × ⟨0⟩ int → ⟨0⟩ int

(* Lifts automatically to: *)
  ∀ shape. Array[shape] int × Array[shape] int → Array[shape] int

(* Vector dot product - cell rank 1 *)
FUNCTION dot(a, b : array[n] real) RETURNS real
  TYPE: ⟨1⟩ Array[n] real × ⟨1⟩ Array[n] real → ⟨0⟩ real

(* Matrix multiply - cell rank 2 *)
FUNCTION matmul(A, B : array[n m] real) RETURNS array[n m] real
  TYPE: ⟨2⟩ Array[n m] real × ⟨2⟩ Array[m k] real → ⟨2⟩ Array[n k] real
```

### Phase 2: Unification Algorithm

**Extended unification with lifting:**

```ocaml
let rec unify_rank_polymorphic graph ty1 ty2 =
  match (ty1, ty2) with
  
  (* Base types *)
  | (INTEGER, INTEGER) -> return graph
  | (REAL, REAL) -> return graph
  
  (* Exact array match *)
  | (Array (s1, elem1), Array (s2, elem2)) ->
      let* graph = unify_shape s1 s2 graph in
      unify_rank_polymorphic graph elem1 elem2
  
  (* Scalar + Array = Array (broadcast) *)
  | (scalar, Array (shape, elem)) 
  | (Array (shape, elem), scalar) when is_scalar scalar ->
      let* graph = unify_rank_polymorphic graph scalar elem in
      return (Array (shape, elem), graph)
  
  (* Array lifting (prefix agreement) *)
  | (Array (s1, elem1), Array (s2, elem2)) ->
      match compute_lifted_shape s1 s2 with
      | Some result_shape ->
          let* graph = unify_rank_polymorphic graph elem1 elem2 in
          return (Array (result_shape, elem1), graph)
      | None ->
          Error (Printf.sprintf 
            "Shape mismatch: %s and %s"
            (string_of_shape s1)
            (string_of_shape s2))
  
  | _ -> Error "Type mismatch"

(* Shape unification *)
and unify_shape s1 s2 graph =
  match (s1, s2) with
  | (Fixed dims1, Fixed dims2) ->
      if dims1 = dims2 then return graph
      else Error "Fixed shape mismatch"
  
  | (Variable v, Fixed dims) ->
      bind_shape_var v dims graph
  
  | (Variable v1, Variable v2) ->
      if v1 = v2 then return graph
      else bind_shape_var v1 (Variable v2) graph
  
  | (AtLeast n, Fixed dims) ->
      if List.length dims >= n then return graph
      else Error "Rank too small"
  
  | (Any, _) | (_, Any) ->
      return graph
  
  | _ -> Error "Shape constraint mismatch"

(* Compute lifted shape (prefix agreement) *)
let compute_lifted_shape s1 s2 =
  match (s1, s2) with
  | (Fixed dims1, Fixed dims2) ->
      if is_prefix dims1 dims2 then Some (Fixed dims2)
      else if is_prefix dims2 dims1 then Some (Fixed dims1)
      else None
  
  | (Variable v, Fixed dims) -> Some (Fixed dims)
  | (Fixed dims, Variable v) -> Some (Fixed dims)
  
  | (Any, s) | (s, Any) -> Some s
  
  | _ -> None
```

### Phase 3: Type Checking with Lifting

**Example: Checking vector + matrix**

```sisal
LET 
  v := [1, 2, 3]           (* shape: [3] *)
  m := [[1, 2, 3],         (* shape: [2 3] *)
        [4, 5, 6]]
IN
  v + m                    (* What's the type? *)
END LET
```

**Type checking:**
```ocaml
(* 1. Infer types *)
v : Array[3] int
m : Array[2 3] int

(* 2. Check operator *)
(+) : ⟨0⟩ int × ⟨0⟩ int → ⟨0⟩ int

(* 3. Determine frame shape *)
Frame for v: [3]
Frame for m: [2 3]

(* 4. Check prefix agreement *)
is_prefix [3] [2 3]? NO
is_prefix [2 3] [3]? NO
ERROR: Shape mismatch

(* Correct version: *)
v + m[0]  (* [3] + [3] → [3] ✓ *)
```

**Valid lifting:**
```sisal
LET
  s := 5              (* shape: [] *)
  v := [1, 2, 3]      (* shape: [3] *)
  m := [[1, 2, 3],    (* shape: [2 3] *)
        [4, 5, 6]]
IN
  s + m               (* [] + [2 3] → [2 3] ✓ *)
END LET
```

---

## Examples

### Example 1: Scalar Function Lifting

**Define scalar operation:**
```sisal
FUNCTION square(x : real) RETURNS real
  x * x
END FUNCTION

TYPE: ⟨0⟩ real → ⟨0⟩ real
```

**Automatic lifting:**
```sisal
square(5.0)              (* 25.0 *)
square([1.0, 2.0, 3.0])  (* [1.0, 4.0, 9.0] *)
square([[1.0, 2.0],      (* [[1.0, 4.0],
         [3.0, 4.0]])       [9.0, 16.0]] *)
```

**Type checking:**
```ocaml
(* Input: Array[3] real *)
square : ⟨0⟩ real → ⟨0⟩ real

Frame shape: [3]
Cell rank: 0
Apply square to each cell: [square(1.0), square(2.0), square(3.0)]
Result: Array[3] real
```

### Example 2: Vector Dot Product

**Define vector operation:**
```sisal
FUNCTION dot(a, b : array[n] real) RETURNS real
  SUM(a * b)  (* element-wise multiply, then sum *)
END FUNCTION

TYPE: ⟨1⟩ Array[n] real × ⟨1⟩ Array[n] real → ⟨0⟩ real
```

**Lifting to matrices:**
```sisal
(* Matrix of vectors *)
LET
  rows := [[1.0, 2.0, 3.0],
           [4.0, 5.0, 6.0]]    (* shape: [2 3] *)
  
  v := [1.0, 0.0, 1.0]         (* shape: [3] *)
IN
  dot(rows, v)  (* Apply dot to each row *)
                (* Result: [4.0, 10.0]  shape: [2] *)
END LET
```

**Type checking:**
```ocaml
rows : Array[2 3] real
v    : Array[3] real

dot : ⟨1⟩ Array[n] real × ⟨1⟩ Array[n] real → ⟨0⟩ real

(* Determine cells *)
rows cells: rank 1, shape [3]  (each row)
v cells:    rank 1, shape [3]  (whole vector)

(* Frame *)
Frame for rows: [2]  (2 rows)
Frame for v:    []   (scalar frame, broadcast)

Result: [2] (vector of 2 scalars)
```

### Example 3: Matrix Operations

**Matrix transpose (rank 2):**
```sisal
FUNCTION transpose(m : array[n m] real) RETURNS array[m n] real
  (* Implementation *)
END FUNCTION

TYPE: ⟨2⟩ Array[n m] real → ⟨2⟩ Array[m n] real
```

**Lifting to 3D:**
```sisal
LET
  batch := [[[1, 2],     (* shape: [2 2 2] *)
             [3, 4]],
            
            [[5, 6],
             [7, 8]]]
IN
  transpose(batch)  (* Transpose each matrix *)
                    (* Result: [2 2 2] with each matrix transposed *)
END LET
```

---

## Limited Implementation Strategy

### What to Support

**Level 1: Scalar Lifting (Easy) ✅**
- Scalar functions automatically work on arrays
- All arithmetic operators
- Comparison operators

**Level 2: Prefix Broadcasting (Medium) ✅**
- Scalar + Array → Array
- Vector + Matrix → Matrix (if compatible)
- Automatic shape checking

**Level 3: Explicit Cell Rank (Advanced) ⚠️**
- Functions declare expected cell rank
- Manual lifting for vector/matrix operations
- Shape inference

**Level 4: Full Rank Polymorphism (Hard) ❌**
- Arbitrary cell ranks
- Complex shape inference
- Dependent types

### Recommended: Levels 1-2

**This gives you 80% of the power with 20% of the complexity.**

---

## Concrete Implementation

### Step 1: Extend IF1 Types

```ocaml
(* Current IF1 *)
type if1_ty =
  | INTEGRAL
  | REAL
  | Array_ty of int  (* just element type ID *)
  | ...

(* Extended IF1 *)
type if1_ty =
  | INTEGRAL
  | REAL
  | Array_ty of {
      shape : shape_ty;
      elem_ty : int;
      cell_rank : int;  (* For lifting *)
    }
  | ShapeVar of string
  | ...

type shape_ty =
  | FixedShape of int list
  | VarShape of string
  | AnyShape
  | AtLeastRank of int
```

### Step 2: Shape Checking

```ocaml
let check_prefix_agreement s1 s2 =
  match (s1, s2) with
  | (FixedShape d1, FixedShape d2) ->
      let len1 = List.length d1 in
      let len2 = List.length d2 in
      let prefix = min len1 len2 in
      let p1 = List.take prefix d1 in
      let p2 = List.take prefix d2 in
      if p1 = p2 then
        Ok (if len1 > len2 then s1 else s2)
      else
        Error "Shapes incompatible"
  
  | (AnyShape, s) | (s, AnyShape) -> Ok s
  
  | _ -> Error "Cannot determine compatibility"
```

### Step 3: Automatic Lifting

```ocaml
let lift_operation op arg1 arg2 graph =
  match (get_type arg1 graph, get_type arg2 graph) with
  
  (* Scalar op scalar → scalar *)
  | (INTEGRAL, INTEGRAL) ->
      simple_binop op arg1 arg2 graph
  
  (* Scalar op array → array (broadcast) *)
  | (INTEGRAL, Array_ty {shape; elem_ty; _}) 
      when is_integral_id elem_ty ->
      let (result_node, _), graph = 
        create_lifted_op op arg1 arg2 shape graph 
      in
      ((result_node, 0, array_ty_id), graph)
  
  (* Array op array → check shapes, lift *)
  | (Array_ty a1, Array_ty a2) ->
      let* result_shape = 
        check_prefix_agreement a1.shape a2.shape 
      in
      let (result_node, _), graph =
        create_lifted_op op arg1 arg2 result_shape graph
      in
      ((result_node, 0, result_array_ty_id), graph)
  
  | _ -> Error "Type mismatch in operation"
```

### Step 4: IF1 Lowering

```sisal
(* Source *)
LET
  v := [1, 2, 3]
  s := 5
IN
  v + s
END LET

(* Lowers to *)
Node 1: LITERAL [1, 2, 3]   (* Array[3] int *)
Node 2: LITERAL 5            (* int *)
Node 3: BROADCAST_SCALAR     (* Replicate 5 to shape [3] *)
  Input 0: Node 2, Port 0    (scalar)
  Input 1: Node 1, Port 0    (shape provider)
  Output 0: Array[3] int

Node 4: ELEMENT_WISE_ADD
  Input 0: Node 1, Port 0
  Input 1: Node 3, Port 0
  Output 0: Array[3] int
```

---

## Performance Considerations

### Optimizations

**1. Shape Information at Compile Time**
```ocaml
(* Known shapes → no runtime checks *)
Array[2 3] int + Array[2 3] int
  → Direct vectorized add (6 elements)

(* Unknown shapes → runtime check needed *)
Array[n] int + Array[m] int
  → Runtime shape comparison, then add
```

**2. Loop Fusion**
```sisal
square(square(v))

(* Fuse into single loop instead of two passes *)
FOR i IN 1..n DO
  result[i] := (v[i] * v[i]) * (v[i] * v[i])
END FOR
```

**3. Vectorization**
```c
/* Generated C with SIMD *)
for (int i = 0; i < n; i += 4) {
  __m256 a = _mm256_load_ps(&arr1[i]);
  __m256 b = _mm256_load_ps(&arr2[i]);
  __m256 c = _mm256_add_ps(a, b);
  _mm256_store_ps(&result[i], c);
}
```

---

## Summary

### What Is Rank Polymorphism?

**Functions automatically work on arrays of any dimension** by:
1. Breaking arrays into cells of the expected rank
2. Applying the function to each cell
3. Reconstructing the result with the frame shape

### Why It's Powerful

✅ **Write less code** - One function works everywhere
✅ **No explicit loops** - Iteration is implicit
✅ **Composable** - Functions combine naturally
✅ **Optimizable** - Compiler sees iteration structure

### Limited Implementation for SISAL

**Recommended Subset:**

1. **Scalar lifting** - Scalar operations auto-lift to arrays
2. **Prefix broadcasting** - Compatible shapes auto-align
3. **Static shape checking** - Catch errors at compile time

**Implementation:**
```ocaml
(* Extend types *)
Array_ty of {shape; elem_ty; cell_rank}

(* Unification with lifting *)
unify_with_prefix_agreement

(* Code generation *)
generate_lifted_operation
```

**This gives 80% of rank polymorphism's power with manageable complexity!**

---

## References

1. **Slepak, Shivers, Manolios (2014).** "An Array-Oriented Language with Static Rank Polymorphism." ESOP 2014.
   - First static type system for rank polymorphism

2. **Slepak (2019).** "The Semantics of Rank Polymorphism." arXiv:1907.00509
   - Complete formal semantics

3. **Iverson (1962).** "A Programming Language" 
   - Original APL notation

4. **Gibbons & Loregian (2019).** "A Unified Framework for Rank Polymorphism" 
   - Naperian functors approach

5. **Keller et al. (2010).** "Regular, Shape-Polymorphic Parallel Arrays in Haskell."
   - Haskell's Repa library

**Your approach for SISAL: Start with levels 1-2 (scalar lifting + broadcasting). This is proven, practical, and gives huge wins.** ✅

---

## Addendum: The `array_dv` Subscript Problem and the Static vs Dynamic Design Question

*Recorded 2026-05-21. This section captures a design study and the critical questions it raised for the Sisal compiler specifically.*

---

### The Concrete Problem in the Sisal Compiler

The Sisal `array_dv` type carries rank at runtime in a descriptor but erases it at compile time. The type `array_dv[double_real]` is the same whether the array is rank-1, rank-2, or rank-N. This creates a fundamental ambiguity at every subscript site.

When the compiler sees `A[i]` and `A : array_dv[double_real]`, it must emit one of two IR operations:

```
DV_ELEMENT   → output type: double_real        (scalar; A has runtime rank 1)
DV_RANK_DEC  → output type: array_dv[double_real]  (row slice; A has runtime rank ≥ 2)
```

These are **different types** in the IR. The compiler must choose at compile time but the rank is only in the runtime descriptor. The existing code defaults to `DV_ELEMENT` everywhere, which is wrong when A is rank-2.

**Concrete case from `gaussj_dv_improved.sis`:**

```sisal
function idfamax( A: OneD; n: integer returns integer )
  for i in 1, n returns value of argmax abs(A[i]) end for
end function
```

Here `A[i]` on a rank-1 array should be `DV_ELEMENT` (scalar). But:

```sisal
let row := dv_row(A, i)  % row is rank-1 slice of rank-2 A
in idfamax(row, n)
```

Inside `idfamax`, `A[i]` is now on the rank-1 `row` — still `DV_ELEMENT`. Correct. But in:

```sisal
A2, B2 := Compute(n, Icol, A1, B1)
```

where `Compute` accesses `Ain[i, j]` — two-index form, so the first index gives `DV_RANK_DEC` (row) and the second gives `DV_ELEMENT` (element). The compiler handles the two-index case correctly. The ambiguity only bites on single-index access of a potentially high-rank array.

---

### Resolution Contexts: Where the Compiler Can Infer the Right Operation

Three sources can resolve the ambiguity, in order of reliability:

**1. Callee parameter type (Remora-style)**

When `A[i]` is passed as argument `k` to a typed function, the function's declared parameter type for position `k` resolves it:

```sisal
idfamax(row, n)   % idfamax's param A: OneD = array_dv[double_real]
                  % → row passed as OneD → DV_RANK_DEC (row is array)
abs(row[imax])    % abs expects double_real scalar
                  % → row[imax] is DV_ELEMENT
```

The callee's `Function_ty(arg_fst, ret_ty, name)` is already in the IF1 typemap. `arg_fst` is a `Tuple_ty` chain of parameter type IDs — the same structure as `ret_ty` which is already walked by `fold_ret_ty_lis`. Walking `arg_fst` with the same function gives the ordered parameter types.

**2. Let-binding declared type (SaC-style)**

```sisal
let Abar : array_dv[double_real] = A[i]
```

The declared type is `Compound_type(Sisal_dv Double_real)` in `Decl_with_type`. It is available in `bind_exp_to_decl` as `atyp` but currently arrives *after* the RHS is lowered (used only to check, raising `Sem_error` if wrong). The fix is to pass it *before* lowering as a hint.

For the multi-binding form:

```sisal
let ABar : array_dv, BBar : array_dv = A[i], B[i]
```

The `Decl_tuple_with_type` case already pairs each name with its declared type via `List.fold_left2`. The hint just needs to reach `do_simple_exp`.

**3. Binary operator sibling (HM-style, lateral)**

```sisal
ABar + BBar[j]   % ABar : array_dv → BBar[j] should also be array_dv
```

Lower left side first, use its output type as a hint when lowering right. This is **not safe to apply in `bin_exp` generally** — see Critical Questions below.

---

### The Dispatch Machinery Must Be Preserved

The existing `lift_binop_forall` / `emit_dv_conform_check` code already implements full NumPy-style runtime rank-polymorphic broadcast:

```
DV_NUM_RANK(A) → rank_A           % runtime rank of each operand
max_rank = max(rank_A, rank_B)
for i in 1..max_rank:             % compute broadcast shape
  d_A = if idx_A >= 1 then DV_DIMENSION(A, idx_A).size else 1
  d_B = if idx_B >= 1 then DV_DIMENSION(B, idx_B).size else 1
  shape[i] = max(d_A, d_B)        % NumPy broadcasting rule
total = product(shape)
for i in 0..total-1:              % linear element scan
  off_A = DV_OFFSET_AT(A, i, shape)
  val_A = DV_LOAD_LINEAR(A, off_A)
  ... op ...
result_flat[i] = val_A op val_B
DV_RESHAPE_BY_SHAPE(result_flat, shape)  % restore rank
```

The dispatch path is **entirely driven by the IR types of already-lowered operands** (`is_dv_array_ty qq1`, `is_dv_array_ty qq2`). If rank inference correctly resolves `A[i]` to `DV_RANK_DEC` (output `array_dv`), `qq1` becomes `Array_dv` and the conform_check path fires. This is the correct result — rank inference *enables* the broadcast path rather than bypassing it.

The generated `body_elem` `Array_ref(__LFA, [__LFI])` inside `lift_binop_forall` is constructed after lowering and lives in a fresh forall scope with no type annotation context — it falls back to `DV_ELEMENT` (scalar element scan), which is correct for a linear index.

---

### The Radical Alternative: Always DV_RANK_DEC (the APL Model)

**Question raised:** What if `DV_ELEMENT` always returns `array_dv` instead of a scalar — i.e., subscripting always rank-reduces, and rank-1 arrays subscripted give rank-0 `array_dv` (a scalar wrapped in an array)?

This would eliminate the compile-time ambiguity entirely. Every `A[i]` emits `DV_RANK_DEC`. The output type is always `array_dv[T]`. No inference step needed.

**Effect on dispatch:** Both operands of `+` would always be `array_dv`, so `bin_exp` always routes to `lift_binop_forall` → DV+DV conform_check. The conform_check handles rank-0+rank-N broadcasting correctly (max_rank = N, rank-0 broadcasts to all). The DV+DV path is unaffected.

**Where it breaks:** The DV+scalar path in `lift_binop_forall` (when one operand is `array_dv` and the other is a literal like `2.0 : double_real`) iterates via `ARRAY_LIML`/`ARRAY_LIMH` on the DV operand. For a rank-0 `array_dv`, these are undefined — a rank-0 array has no axis to take limits from, and `Array_ref(rank0_array, [i])` would attempt DV_RANK_DEC on rank-0, giving rank-(-1).

**Fix:** Either (a) define `ARRAY_LIML`/`ARRAY_LIMH` for rank-0 to return 0/0 (one element, linear index 0), or (b) wrap scalar literals in rank-0 `array_dv` too, so every value is `array_dv` and only the DV+DV conform_check path ever fires. Option (b) is the full APL model. Option (a) is a small runtime special-case.

**This is implementable with changes to C lowering only** — no changes to the IF1 IR, no type inference pass, no new compiler phases.

---

### Why Remora and SaC Chose Static Analysis Instead

If the dynamic/runtime approach works and is simpler, why do the major static systems go the other route? Their stated reasons:

**Remora (Slepak, Shivers, Manolios — ESOP 2014):**
- APL's implicit iteration structure is "too dynamic for good static compilation." The control structure — which axes loop, which are cells — is derived from runtime values, making it invisible to the compiler.
- Static types make the frame/cell decomposition explicit at compile time, enabling specialization and optimization.
- Shape errors are caught at compile time rather than producing wrong results silently at runtime.

**SaC (Grelck, Scholz):**
- Shape inference is an **"essential prerequisite"** for intermediate array elimination. Their With-loop folding merges adjacent comprehensions into a single pass, eliminating temporary allocations. Without known shapes, the compiler cannot determine whether two loops iterate over the same domain.
- Measured **2–14× speedups** specifically from this optimization.
- Goal: APL expressiveness at Fortran performance. The dynamic route cannot reach Fortran performance.

**Futhark:**
- GPU architectures require static shape knowledge for memory allocation at kernel launch. Dynamic dispatch is architecturally infeasible on GPU.

---

### The Critical Question for Sisal: Intermediate Allocation

SaC's argument is the one that directly applies to Sisal's numerical workloads. Consider the inner loop of Gauss-Jordan:

```sisal
v := Ain[i, j] - (Ain[i, pvtrow] / pvtele) * Ain[pvtrow, j]
```

**With the always-DV_RANK_DEC (dynamic) approach:**
- `Ain[i, pvtrow]` → rank-0 `array_dv` → **heap allocation** for one double
- `/ pvtele` → DV+DV conform_check → shape computation, linear forall, reshape → **heap allocation**
- `* Ain[pvtrow, j]` → same → **heap allocation**
- `-` → same → **heap allocation**

This inner loop runs N² times. For N=1000, that is 4 million heap round-trips for what should be four scalar floating-point instructions.

**With static inference (DV_ELEMENT resolves correctly to `double_real`):**
- All four operations are direct FP arithmetic on registers. No allocation.

**The escape hatch:** If rank-0 `array_dv` can live on the stack (or in a register) rather than the heap — which is possible if the runtime treats rank-0 as a special case and the compiler can prove rank-0 statically — the allocation overhead goes away. This is what the lightweight rank inference step buys: for cases where context reveals the result is scalar (function expects `double_real`, let-binding declares `double_real`), emit `DV_ELEMENT` → scalar in a register. For genuinely unknown cases, emit `DV_RANK_DEC` → pay the allocation cost.

---

### Design Decision Record

| Approach | Compile complexity | Runtime cost | Correctness |
|---|---|---|---|
| Always `DV_ELEMENT` (current) | None | None | Wrong for rank-2+ subscripts |
| Always `DV_RANK_DEC` (APL model) | None (C lowering only) | Heap allocation per scalar subscript | Correct |
| Lightweight context inference | Small (3 hint sources) | Scalar where inferrable, heap otherwise | Correct |
| Full static shape inference (SaC) | Large (full inference pass) | None for scalar paths | Correct + optimal |

**Chosen direction:** Lightweight context inference first — threading an `expected_ty option` hint through `do_simple_exp` from three sources (callee param type, let-binding declared type, binary op sibling). The always-DV_RANK_DEC model is a valid fallback for cases where inference cannot resolve the ambiguity, provided the C runtime handles rank-0 `array_dv` correctly.

**Open question:** Whether rank-0 `array_dv` should be heap-allocated (current `sisal_array_t` model) or stack-allocated as a special case. The answer determines whether the dynamic fallback is acceptable for inner-loop numerical code.

**Deferred: compile-time hint-based unification for performance.**
Beyond correctness, compile-time rank hints could enable dead code elimination and other optimizations in the generated C — for example, knowing a subscript is always scalar allows the compiler to skip the conform_check branch entirely. The argument for this is valid. However, without a solid performance baseline and profiling data to show where time is actually spent, the added compiler complexity is not justified. This is deferred until performance analysis identifies it as a real bottleneck.

---

### Summary of Key Findings

1. `A[i]` on `array_dv` is ambiguous at compile time. The correct operation depends on the runtime rank of `A`.
2. Three context sources can resolve it at compile time without a full inference pass.
3. The existing NumPy-style conform_check broadcast machinery is correct and complete — rank inference enables it, not bypasses it.
4. Making `DV_ELEMENT` always return `array_dv` (always rank-reduce) is correct and requires only C lowering changes, but incurs heap allocation for every scalar subscript in numerical inner loops.
5. SaC/Remora chose static inference primarily to eliminate intermediate array allocations and enable loop fusion — not for safety alone.
6. The lightweight inference approach covers the common cases (function args, let-binding types) and avoids the allocation problem for inferrable scalar contexts.
