# Sisal-2026 Optimizer Roadmap & Wishlist Matrix

This document explicitly separates **currently implemented compiler features** from **planned optimizer roadmap items and language wishlists**.

---

## Implemented vs. Planned Feature Matrix

| Feature / Optimization Area | Status | Authoritative Verification Source |
| :--- | :--- | :--- |
| **Rank-Polymorphic `array_dv`** | Implemented & Verified | `test/e2e/dv_rank8_slices.sis`, `test/e2e/reshape_matmul_dv.sis` |
| **Standard `EINSUM` (`"ij,jk->ik"`)** | Implemented (BLAS lowering) | `test/e2e/transformer_gqa_swiglu.sis`, `test/e2e/dv_matmul.sis` |
| **Reference Counting Copy Elimination** | Implemented & Verified | `test/e2e/array_copy_liveness_dv.sis`, `docs/fft_copy_elimination_report.md` |
| **Hand-Fused Transformer Blocks** | Implemented & Verified | `test/e2e/transformer_all_dv.sis` (`TRANSFORMER_ALL_DV` 423/423 PASS) |
| **Automatic IF1 Loop Fusion Pass** | **Planned Roadmap Item** | Section 1 below |
| **EINSUM Contraction Path DP** | **Planned Roadmap Item** | Section 2 below |
| **GEMM Epilogue Activation Fusion** | **Planned Roadmap Item** | Section 3 below |
| **Tiled EINSUM Subscript Syntax** | **Planned Wishlist Item** | Section 7 below (`EINSUM("((i 32) (j 64)) ...")`) |

---


## 1. Loop Fusion (IF1 Graph Pass)
- **Description**: Fuse consecutive `Forall` loop nodes that operate over matching generator domains (e.g., Softmax `MaxS`, `ExpS`, `SumExp`, `P` normalization).
- **Goal**: Replace intermediate array allocations ($O(N)$ memory) with scalar register pass pipelines ($O(1)$ L1 cache temporary storage).
- **Status**: Target optimization pass (currently baseline compiles to separate loop passes).

---

## 2. Einsum Dynamic Programming Contraction Path Optimization
- **Description**: Analyze multi-tensor `EINSUM` contraction chains and apply dynamic programming matrix-chain parenthesization.
- **Goal**: Automatically find optimal contraction order to reduce FLOP complexity (from $O(N^4)$ down to optimal $O(N^3)$) before delegating to BLAS routines.
- **Status**: Target optimizer pass roadmap item.

---

## 3. Einsum & GEMM Epilogue Fusion
- **Description**: Fuse elementwise activation functions (SiLU, GELU, ReLU, bias additions) directly into matrix multiplication outputs.
- **Goal**: Avoid round-tripping output matrices through main memory before applying activations (e.g., SwiGLU `silu(X @ W1) * (X @ W3)`).
- **Status**: Proposal documented in `docs/gpu_tiling_and_cutlass_proposal.md`.

---

## 4. Advanced Copy Elimination & Deforestation
- **Description**: Extend runtime update-in-place reference counting to eliminate copy operations across complex control flow and FFT/array re-ordering passes.
- **Goal**: Achieve zero memory copying across complex pipeline stages.
- **Status**: Documented in `docs/fft_copy_elimination_report.md`.

---

## 5. Subscript Slicing & Strided View Lowering
- **Description**: Lower sub-array slicing operations (`A[i_start:i_end, j_start:j_end]`) to zero-copy strided view descriptors instead of copying memory blocks.
- **Goal**: Enable zero-copy slicing for rank-polymorphic tensors.
- **Status**: Planned in `docs/subscript_slicing_plan.md`.

---

## 6. GPU Tiling & Kernel Codegen
- **Description**: Automatically tile 2D/3D `for` loops and map them to CUDA/Metal thread blocks.
- **Goal**: Deliver high-performance GPU tensor code generation for multi-dimensional `array_dv` operations.
- **Status**: Documented in `docs/gpu_tiling_and_cutlass_proposal.md`.

---

## 7. Tiled EINSUM Subscript & Unified Permutation Notation (Wishlist Item)
- **Description**: Extend the `EINSUM` format string to natively encode tensor contraction math, L1/L2 cache tiling, and loop permutation in a single unified bracketed expression (e.g. `EINSUM("((i 32) (j 64)) ((j 64) (k 16)) -> (i 32) (k 16) (j 64)", A, B)`).
- **Goal**:
  - Eliminate the need for separate imperative schedule/transformation scripts.
  - Bracket nesting depth directly represents tile/cache hierarchy depth: `i` (flat), `(i 32)` (L2 tile), `((i 128) 8)` (L2/L1 micro-tile).
  - Left-to-right ordering of terms on the RHS output side (`->`) uniquely dictates the execution loop nesting and permutation order without extra keywords.
- **Status**: Planned optimizer wishlist feature.

### Lowering Walkthrough: Untiled vs. Tiled (k in Middle)

#### 1. Naive Untiled Lowering (`EINSUM("ik, kj -> ij")` $\to$ $i \to j \to k$ order)
```fortran
! Naive Lowering: Reduction k in innermost position (Strided access on B, high cache misses)
DO i = 1, M
   DO j = 1, N
      sum_val = 0.0d0
      DO k = 1, K
         sum_val = sum_val + A(i, k) * B(k, j)
      END DO
      C(i, j) = sum_val
   END DO
END DO
```

#### 2. Interchanged Lowering ($k$ as Middle Loop $\to$ $i \to k \to j$ order)
```fortran
! Interchanged: k in middle position (Scalar broadcast of A, unit-stride for B and C)
DO i = 1, M
   DO k = 1, K                       ! k is MIDDLE loop!
      a_val = A(i, k)                ! Load once into register
      DO j = 1, N                    ! Innermost loop over j
         C(i, j) = C(i, j) + a_val * B(k, j)
      END DO
   END DO
END DO
```

#### 3. Tiled Lowering with $k$ in Middle (`EINSUM("((i 32) (j 64)) ((j 64) (k 16)) -> (i 32) (k 16) (j 64)")`)
```fortran
! Tiled & Interchanged: i_tile -> k_tile -> j_tile -> i_elem -> k_elem -> j_elem
DO i_tile = 1, M, 32
   DO k_tile = 1, K, 16                 ! k_tile is MIDDLE tile loop!
      DO j_tile = 1, N, 64
         
         ! Inner Micro-kernel (L1 Cache / Vector Registers)
         DO i_elem = i_tile, MIN(i_tile + 31, M)
            DO k_elem = k_tile, MIN(k_tile + 15, K)   ! k_elem is MIDDLE element loop!
               a_val = A(i_elem, k_elem)
               
               !DIR$ SIMD (Vectorized unit-stride loop over j_elem)
               DO j_elem = j_tile, MIN(j_tile + 63, N)
                  C(i_elem, j_elem) = C(i_elem, j_elem) + a_val * B(k_elem, j_elem)
               END DO
            END DO
         END DO

      END DO
   END DO
END DO
```

#### 4. 3D Batched MatMul & 4D Attention Lowering Example (`EINSUM("b ((m 32) (k 16)) (b ((k 16) (n 64))) -> b (m 32) (k 16) (n 64)")`)
```fortran
! 3D Batched MatMul with Parallel Batch (b) & Middle k Loop
!$OMP PARALLEL DO COLLAPSE(2) PRIVATE(m_elem, k_elem, n_elem, a_val)
DO b = 1, B
   DO m_tile = 1, M, 32
      DO k_tile = 1, K, 16                 ! k_tile is MIDDLE tile loop!
         DO n_tile = 1, N, 64
            
            ! Inner Micro-kernel (Fits 100% in L1 Cache)
            DO m_elem = m_tile, MIN(m_tile + 31, M)
               DO k_elem = k_tile, MIN(k_tile + 15, K)   ! k_elem is MIDDLE element loop!
                  a_val = A(b, m_elem, k_elem)
                  
                  !DIR$ SIMD
                  DO n_elem = n_tile, MIN(n_tile + 63, N)
                     C(b, m_elem, n_elem) = C(b, m_elem, n_elem) + a_val * B(b, k_elem, n_elem)
                  END DO
               END DO
            END DO

         END DO
      END DO
   END DO
END DO
!$OMP END PARALLEL DO
```

For 4D Transformer Attention ($Q \cdot K^T$ with Batch $b$, Heads $h$, Sequence $s$, Head Dim $d$):
```sisal
Scores := EINSUM("b h ((s 64) (d 16)) (b h ((k 64) (d 16))) -> b h (s 64) (d 16) (k 64)", Q, K)
```
Lowered to parallel threads over $(b, h)$, outer tiles over Query sequence $(s)$, **head dimension $d$ reduced in middle registers**, and Key sequence $(k)$ streamed with unit-stride vector memory access.

#### 5. Higher-Order Epilogue & Pre-Processing Fusion inside `EINSUM` (Wishlist Item)
Rather than introducing a separate keyword, `EINSUM` itself is extended to support on-the-fly higher-order function (HOF) fusion for pre-processing loads and post-processing stores directly in the subscript string using bound function names:

```sisal
let
  SwiGLU := function(gate, up : double returns double) (gate / (1.0d0 + exp(-gate))) * up end function;
in
  Hidden := EINSUM(
    % Bound function SwiGLU applied directly inside (h 64) tile bracket on store!
    "((s 32) (h 64)) ((h 64) (d 16)), ((s 32) (h 64)) ((h 64) (d 16)) -> (s 32) (d 16) ((h 64) SwiGLU)",
    SwiGLU, X, W1, X, W2
  )
end let
```
This unifies (1) tensor contraction math, (2) L1/L2 cache tiling, (3) loop interchange, (4) pre-processing load HOFs, and (5) post-processing store HOFs **all directly inside `EINSUM`** with zero extra language keywords!

#### 6. Related Work & Novelty Analysis


- **NumPy / PyTorch `einsum`**: Uses standard Einstein notation (`"ik,kj->ij"`). Expresses contraction math declaratively, but has **zero syntax for loop tiling, cache block sizes, or execution loop ordering**.
- **Halide (Ragan-Kelley et al., PLDI 2013) & TVM (Chen et al., OSDI 2018)**: Pioneered the decoupling of computation algorithm from execution schedule. However, scheduling is imperative and separate from the math expression (e.g. `s.tile(i, i_out, i_in, 32).reorder(i_out, k_out, j_out)` in an external Python script).
- **Einops (Rozenberg, ICLR 2022)**: Provides index rearrangement syntax (`"b (h w) -> b h w"`), but focuses exclusively on spatial array reshaping and tensor broadcasting—**cannot specify contraction reductions, cache block sizes, or SIMD loop order**.
- **Tensor Comprehensions (Vasilache et al., FAIR 2018) & TACO (Kjolstad et al., OOPSLA 2017)**: Uses polyhedral compiler infrastructure (ISL) to discover tile sizes automatically during compilation. No inline syntax exists for the developer to specify tile bounds directly in the string.
- **Sisal 2026 Novelty**:
  1. **Purely Functional Inline Scheduling**: Unifies math definition and hardware loop schedule in a single functional string expression.
  2. **Zero-Keyword Positional Ordering**: The position of bracketed terms on the RHS of `->` dictates outer/inner loop nesting and loop interchange (e.g. `-> (i 32) (k 16) (j 64)` places $k$ in the middle).
  3. **Cache Depth Mapping**: Bracket depth corresponds 1-to-1 to physical memory levels: `i` (flat DRAM), `(i 32)` (L2 Cache), `((i 128) 8)` (L1 / Vector Register).

---

> **Disclaimer**: This document is a work in progress. To inspect the current active state of the compiler's optimization capabilities, transformation passes, and generated runtime code, please consult the test definitions, generated artifacts, and test execution output in `test/e2e/`.



