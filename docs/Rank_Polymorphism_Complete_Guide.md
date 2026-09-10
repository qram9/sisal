# Rank Polymorphism in Sisal-2026: Complete Architecture & Developer Guide

## 1. Executive Summary & Context

**Rank polymorphism** allows functions written for scalar values or low-dimensional inputs to **automatically apply to multi-dimensional dense arrays of any rank** (vectors, matrices, 3D/4D tensors) without writing explicit loops.

In **Sisal-2026**, rank polymorphism is integrated into the core type system and C++23 runtime execution engine via **dense dope vectors (`array_dv[T]`)**.

---

## 2. Why Sisal-2026 Adopted Rank Polymorphism

### Legacy Sisal 1.2 / 2.0 Limitation (Nested Ragged Arrays)
In historical Sisal 1.2 and Sisal 2.0, multi-dimensional arrays were represented as nested ragged pointer structures:
```sisal
% Legacy Sisal 1.2 syntax (Obsolete in Sisal-2026)
type Matrix = array[array[real]];
```
This legacy representation caused three major issues:
1. **Memory Fragmentation & Pointer Chasing**: Each matrix row was a separate heap buffer.
2. **Complex Compiler Pass Overhead**: Inferring update-in-place optimization opportunities across nested pointer arrays required static analysis passes.
3. **Explicit Loop Boilerplate**: Simple matrix-vector arithmetic required nested parallel `forall` loops.

### The Sisal-2026 Solution (`array_dv[T]`)
Sisal-2026 unifies all dense arrays under the single flat parameterized type **`array_dv[T]`**:
- **Dynamic Rank Metadata**: The rank (1D vector, 2D matrix, $N$-D tensor) is a dynamic property of the dope vector metadata (`sisal_array_t`).
- **No `array_dv[array_dv[T]]`**: Nested dope vector declarations are forbidden. All arrays are flat contiguous memory buffers.
- **Array Literal Construction**: Literal bracket notation `array_dv [1: v1, v2, ...]` creates a **flat 1D vector**. Multi-dimensional matrices are created by reshaping a flat vector (`reshape(Flat, rows, cols)`) or via parallel `forall` loop gather reductions.
- **Zero-Copy Slicing ($O(1)$)**: Slicing (`A[1..5, 2..8]`) creates a constant-time metadata view shift without element byte copying.

> 💡 **Design Philosophy: Not a Weakness, But a Strength**
> By explicitly separating dense tensor computing (`array_dv[T]`) from irregular or ragged data structures (algebraic recursive union types `union [ nil_tag: null; cons_tag: ... ]`), Sisal-2026 removes the need for compiler optimization passes to guess layout intentions. We believe this explicit control is not a weakness, but rather a profound strength: it eliminates compiler ambiguity, guarantees $O(1)$ zero-copy view metadata shifts, and gives developers predictable, transparent control over hardware performance.

---

## 3. Core Mechanics & Definitions

### Rank & Shape
- **Rank**: Number of dimensions.
  - Scalar: Rank 0
  - Vector: Rank 1
  - Matrix: Rank 2
  - Tensor: Rank $N$
- **Shape**: List of axis sizes.
  - Scalar: `[]`
  - Vector `[10, 20, 30]`: `[3]`
  - Matrix $2 \times 3$: `[2, 3]`

---

## 4. Sisal-2026 Code Examples

### Example 1: Matrix-Vector & Matrix-Scalar Expressions

Rank polymorphism operates directly on built-in operators (`+`, `-`, `*`, `/`) and functions taking `array_dv[T]` arguments mixed with scalar values:

```sisal
function TransformAndScale( M : array_dv[real]; V : array_dv[real]; s : real returns array_dv[real] )
  let
    % M is a 2D Matrix of Shape [2, 3]
    % V is a 1D Vector of Shape [3]
    % s is a scalar real (0D)

    % 1. Matrix + Vector broadcast addition -> returns Shape [2, 3]
    M_plus_V := M + V;

    % 2. Matrix-Scalar broadcast multiplication -> returns Shape [2, 3]
    Scaled := M_plus_V * s;

    % 3. Combined inline rank-polymorphic expression
    Result := (M * s) + V
  in
    Result
  end let
end function
```

### Example 2: Single Subscript (`M[i]`) vs. Coordinate Indexing (`M[i, j]`) vs. Explicit Slicing (`M[i, ..]`)

In Sisal-2026:
- **Single-subscript indexing `M[i]` ALWAYS returns a scalar value `T`**. On a 2D matrix `M`, `M[i]` performs **linear (flat 1D) indexing** into the underlying contiguous memory buffer as if `M` were a single row.
- **Coordinate indexing `M[i, j]`** accesses the scalar element at 2D coordinate $(i, j)$.
- **Explicit Range Slicing `M[i, ..]`** extracts Row $i$ as a 1D vector slice view.

```sisal
function IndexVsSliceDemo( M : array_dv[real] returns real, real, array_dv[real] )
  let
    % 1. Linear Flat Indexing: M[5] returns the 5-th scalar element in flat memory
    flat_elem := M[5];

    % 2. Coordinate Indexing: M[2, 3] returns the scalar element at row 2, col 3
    elem := M[2, 3];

    % 3. Explicit Row Slice: M[2, ..] extracts Row 2 as a 1D Vector view
    row := M[2, ..]
  in
    flat_elem, elem, row
  end let
end function
```

> 💡 **Why `M[i]` ALWAYS Returns a Scalar**:
> In legacy ragged array languages (`array[array[T]]`), `M[i]` returned a 1D row array pointer. In Sisal-2026 (`array_dv[T]`), `M[i]` treats `M` as a flat 1D buffer and returns the $i$-th scalar element. To extract a 1D vector slice, you explicitly write `M[i, ..]`. This design eliminates static type checking ambiguity and IR lowering conflict (`DOPE_VECTOR_ELEMENT` vs `DOPE_VECTOR_SLICE`).

---

### Example 2: Zero-Copy Slicing + Rank-Polymorphic Addition

```sisal
function SliceBroadcastDemo( returns array_dv[real] )
  let
    % 4x4 Matrix
    M := array_dv [1: [1.0, 2.0, 3.0, 4.0],
                      [5.0, 6.0, 7.0, 8.0],
                      [9.0, 10.0, 11.0, 12.0],
                      [13.0, 14.0, 15.0, 16.0]];
                      
    % Zero-copy slicing: extract Sub-matrix [2..3, 1..2] -> Shape [2, 2]
    Sub := M[2..3, 1..2];
    
    % Rank reduction: extract Row 2 -> Shape [4]
    Row := M[2, 1..4]
  in
    Sub + Row % Automatic broadcasting!
  end let
end function
```

---

## 5. Right-Aligned Trailing Axis Broadcasting Rules

Sisal-2026 follows NumPy and PyTorch right-aligned trailing axis broadcasting rules:

When evaluating binary operator $A \oplus B$:
1. **Right Alignment**: Align dimensions from right (trailing axis) to left.
2. **Dimension Agreement**: Two dimensions $d$ are compatible if:
   - `shape_A[d] == shape_B[d]`
   - `shape_A[d] == 1` or `shape_B[d] == 1`
3. **Zero-Copy Stride-0 Expansion**: If a dimension has size $1$, the compiler expands it by setting `stride[d] = 0`. This allows elements to be reused without allocating extra memory or making byte copies.

---

## 6. Compiler & Runtime Implementation Details

### C++23 Runtime Dope Vector (`sisal_array_t`)
```cpp
struct sisal_array_t {
    void* data;          // Contiguous element buffer
    int32_t rank;        // Dynamic dimension count
    int32_t total_elems; // Total element count
    int32_t elem_size;   // Size of type T in bytes
    int32_t ref_count;   // Copy-on-Write reference count
    int32_t* shape;      // Axis sizes
    int32_t* stride;     // Axis byte strides
    int32_t offset;      // Element offset
};
```

### Stride-0 Indexing Function (`sisal_dv_offset_at`)
```cpp
inline int32_t sisal_dv_offset_at(const sisal_array_t* arr, int32_t flat_idx) {
    int32_t offset = arr->offset;
    int32_t rem = flat_idx;
    for (int32_t i = 0; i < arr->rank; ++i) {
        int32_t dim_size = arr->shape[i];
        int32_t coord = rem / arr->stride_mod[i];
        rem %= arr->stride_mod[i];
        // Stride 0 zeroes out offset increment for broadcast dimensions!
        offset += coord * arr->stride[i];
    }
    return offset;
}
```

---

## 7. Architectural Comparison Matrix

| Feature | Legacy Sisal 1.2 / 2.0 | Sisal-2026 (`array_dv`) |
| :--- | :--- | :--- |
| **Type Representation** | `array[array[T]]` (ragged) | `array_dv[T]` (flat dope vector) |
| **Memory Buffer** | Fragmented pointer arrays | Contiguous memory block |
| **Slicing Complexity** | $O(N)$ memory allocation & copy | $O(1)$ constant time metadata shift |
| **Broadcasting** | Manual nested loops | Automatic right-aligned stride-0 |
| **Immutability Guarantee** | Compiler static update pass | Native Copy-on-Write (`ref_count`) |
| **BLAS Integration** | Difficult / manual | Native (`cblas_dgemm`) |
