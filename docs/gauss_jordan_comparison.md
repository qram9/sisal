# Gauss-Jordan Elimination: Sisal 1.2 vs. Sisal-2026 Case Study

This document provides a detailed comparative case study of **Gauss-Jordan Elimination with Partial Pivoting** implemented in **Sisal 1.2** (legacy ragged array model) versus **Sisal-2026** (`git_sisal` flat dope-vector model).

---

## 1. Executive Summary & Comparison Table

| Language Feature | Sisal 1.2 (Legacy Model) | Sisal-2026 (`git_sisal`) | Impact in Sisal-2026 |
| :--- | :--- | :--- | :--- |
| **Matrix Type (`TwoD`)** | `type TwoD = array[array[double]]` *(Relied on compiler build-in-place optimizations)* | `type TwoD = array_dv[double]` *(Explicit language primitive)* | **User-Directed Flat Dope Vector**: No reliance on compiler optimization passes. User explicitly chooses flat `array_dv` for matrices. |
| **Memory Layout** | Ragged pointer tree *(OSC compiler attempted in-place flattening)* | Flat C-contiguous row-major block (`sisal_array_t`) | **Guaranteed Flat Layout**: 100% contiguous memory layout guaranteed by type definition, enabling SIMD and BLAS acceleration. |
| **Row Extraction** | `row_i := A[i]` | `row_i := A[i, ..]` *(rank-reducing slice)* | **Zero-Copy View**: $O(1)$ metadata shift without copying buffer bytes. |
| **Scalar Indexing** | `val := A[i, j]` *(sugar for `A[i][j]` 2-level dereference)* | `val := A[i, j]` *(flat stride calculation)* | **$O(1)$ Direct Offset**: Evaluates to scalar via direct `data[i * s0 + j * s1]` calculation without pointer chasing. |
| **Row Swapping** | `A[i: A[j]; j: A[i]]` | `A[i: A[j, ..]; j: A[i, ..]]` *(dope swap)* | **$O(1)$ Zero-Copy Swap**: Swaps row descriptors in constant time with CoW. |
| **Matrix Assembly** | `returns array of Arow` | `returns array_dv of Arow` *(rank elevation)* | **Flat Assembly**: Elevates 1D row slices into a single contiguous rank-2 matrix `array_dv[double]`. |

---

## 2. Sisal-2026 Implementation (`gaussj1_dv.sis`)

Below is the complete, high-performance **Sisal-2026** implementation of Gauss-Jordan Elimination with partial pivoting:

```sisal
% Gauss-Jordan Elimination Solver in Sisal-2026 (git_sisal)
define Main, idfamax, idfmax, GetPivot, Compute

type Onei = array_dv[integer];
type OneD = array_dv[double];
type TwoD = array_dv[double]; % Single flat rank-2 dope vector

% Find index of maximum absolute element in a 1D row vector
function idfamax( A: OneD; n: integer returns integer )
  for initial
    i := 2;
    max_idx := 1;
  while ( i <= n ) repeat
    i := old i + 1;
    max_idx := if abs(A[old i]) > abs(A[old max_idx]) then old i else old max_idx end if;
  returns value of max_idx
  end for
end function

% Find index of maximum element
function idfmax( A: OneD; n: integer returns integer )
  for initial
    i := 2;
    max_idx := 1;
  while ( i <= n ) repeat
    i := old i + 1;
    max_idx := if A[old i] > A[old max_idx] then old i else old max_idx end if;
  returns value of max_idx
  end for
end function

% Select pivot row and pivot column using rank-reducing row slices (A[i, ..])
function GetPivot( n: integer; A: TwoD; PIVR: Onei returns integer, integer )
  let cols, maxs :=
    for i in 1, n
      col, max := if PIVR[i] = 0 then
                    let
                      row_i := A[i, ..];          % O(1) Rank-reducing row slice (1D vector)
                      imax  := idfamax(row_i, n);
                    in
                      imax, abs(A[i, imax])      % Scalar index A[i, imax]
                    end let
                  else
                    0, -1.0d0
                  end if
    returns array_dv of col
            array_dv of max
    end for;
  in
    let irow := idfmax(maxs, n);
    in
      cols[irow], irow
    end let
  end let
end function

% Perform row reduction for pivot step
function Compute( n, pvtrow: integer; Ain: TwoD; Bin: OneD returns TwoD, OneD )
  let pvtele := Ain[pvtrow, pvtrow] % 2D Scalar index
  in
    for i in 1, n
      Arow, Bele := if i = pvtrow then
                      for j in 1, n
                      returns array_dv of Ain[i, j] / pvtele
                      end for,
                      Bin[i] / pvtele
                    else
                      let multiplier := Ain[i, pvtrow] / pvtele;
                      in
                        for j in 1, n
                        returns array_dv of Ain[i, j] - multiplier * Ain[pvtrow, j]
                        end for,
                        Bin[i] - multiplier * Bin[pvtrow]
                      end let
                    end if
    returns array_dv of Arow % Transparent Rank Elevation: 1D Arow -> Rank-2 TwoD matrix
            array_dv of Bele
    end for
  end let
end function

% Main iterative Gauss-Jordan loop (uses sequential state transition `for initial ... repeat`)
% See detailed notes on for initial semantics: loop_behavior_comparison.md & for_initial_seed_semantics.md
function Main( n: integer; Ain: TwoD; Bin: OneD returns OneD )
  for initial
    I    := 0;
    A, B := Ain, Bin;
    PIVR := array_fill(1, n, 0)
  while I < n repeat
    I := old I + 1;
    Icol, Irow := GetPivot(n, old A, old PIVR);
    A1, B1 := if ( Icol ~= Irow ) then
                % Zero-copy row descriptor swapping using row slices
                old A[Icol: old A[Irow, ..]; Irow: old A[Icol, ..]],
                old B[Icol: old B[Irow]; Irow: old B[Icol]]
              else
                old A, old B
              end if;
    PIVR := old PIVR[Icol: 1];
    A, B := Compute(n, Icol, A1, B1)
  returns value of B
  end for
end function
```

---

## 3. Detailed Step-by-Step Contrast

### Step 1: Type Declarations (`TwoD`)
- **Sisal 1.2**:
  ```sisal
  type TwoD = array[array[double]] % Ragged array of 1D array handles
  ```
  In Sisal 1.2, `TwoD` is a 1D array of pointers. Each row is independently allocated on the heap.
- **Sisal-2026**:
  ```sisal
  type TwoD = array_dv[double] % Flat rank-2 dope vector
  ```
  In Sisal-2026, `TwoD` is a single contiguous row-major block in memory managed by a 24-byte `sisal_array_t` descriptor.

---

### Step 2: Row Extraction in `GetPivot`
- **Sisal 1.2**:
  ```sisal
  row_i := A[i]; % Dereferences pointer A[i] -> returns array[double]
  ```
  Incurred a pointer dereference `*(*(A + i))`.
- **Sisal-2026**:
  ```sisal
  row_i := A[i, ..]; % O(1) rank-reducing slice
  ```
  Creates a 1D view of row `i` in $O(1)$ constant time by adjusting metadata offsets (`offset = i * stride0`). Zero element bytes are copied.

---

### Step 3: Scalar Indexing
- **Sisal 1.2**:
  ```sisal
  pvtele := Ain[pvtrow, pvtrow]; % Syntactic sugar for Ain[pvtrow][pvtrow]
  ```
  In Sisal 1.2, multi-index comma syntax `Ain[i, j]` was supported as syntactic sugar for `Ain[i][j]`, evaluating to a scalar via two separate pointer lookups `*(*(Ain + i) + j)`.
- **Sisal-2026**:
  ```sisal
  pvtele := Ain[pvtrow, pvtrow]; % Native multi-index calculation
  ```
  Evaluates to a scalar directly by calculating flat memory index: `data[pvtrow * stride0 + pvtrow * stride1]` with zero pointer indirection.

---

### Step 4: Row Swapping in `Main`
- **Sisal 1.2**:
  ```sisal
  old A[Icol: old A[Irow]; Irow: old A[Icol]]
  ```
  Swapped pointers in the top-level pointer array.
- **Sisal-2026**:
  ```sisal
  old A[Icol: old A[Irow, ..]; Irow: old A[Icol, ..]]
  ```
  Swaps row view descriptors in $O(1)$ constant time. If `old A` is no longer used elsewhere, Copy-on-Write (CoW) updates the matrix in-place.

---

### Step 5: Matrix Assembly & Transparent Rank Elevation in `Compute`
- **Sisal 1.2**:
  ```sisal
  returns array of Arow % Assembles array of row pointers
  ```
  Constructed a new top-level array of pointers pointing to separately allocated row arrays.
- **Sisal-2026**:
  ```sisal
  returns array_dv of Arow % Transparent Rank Elevation
  ```
  The compiler's type engine (`to_if1.ml`) detects that `Arow` is already a 1D `array_dv[double]`. Instead of building a nested structure, it transparently elevates the output to a single, contiguous rank-2 matrix `array_dv[double]`.

---

## 4. Performance & Language Design Philosophy

1. **APL & NumPy Heritage in a Single-Assignment Setting**:
   - Dense rank-polymorphic dope-vector arrays (`array_dv`) follow a proven architectural lineage originating in **APL** (Iverson, 1962) and perfected in modern computing by **NumPy**, **PyTorch**, and **JAX**.
   - For complete theoretical details on static rank polymorphism, prefix agreement, and shape inference, see 📘 **[Rank Polymorphism: A Complete Guide](Rank_Polymorphism_Complete_Guide.md)**.
   - Rather than relying on compiler analysis passes (*build-in-place* / *update-in-place*) to discover or attempt to flatten array layouts, Sisal-2026 makes dense multi-dimensional dope vectors a first-class language primitive (`array_dv`).
2. **Natural Fit for Single-Assignment Dataflow Semantics**:
   - Dope-vector metadata operations (slicing `A[i, ..]`, reshaping, transposition) fit naturally into single-assignment dataflow languages as $O(1)$ constant-time metadata views.
   - Combined with Copy-on-Write (CoW) reference counting, `array_dv` provides 100% single-assignment immutability guarantees alongside native C/C++ execution performance.
3. **Predictable L1/L2 Cache Locality & Hardware Acceleration**:
   - Storing all matrix entries contiguously in row-major order guarantees L1/L2 cache locality, enabling LLVM SIMD auto-vectorization (AVX-512 / Neon FMA) and BLAS matrix acceleration (`cblas_dgemm`).
