# Interprocedural Provided Variant Pass & Topological Liveness Architecture

## 1. Overview
This document describes the compiler architecture for **Interprocedural Array Allocation Promotion (Provided Variant Strategy)**, **Topological Edge Liveness Analysis**, and **Single-Assignment In-Place Memory Safety** in the Sisal compiler backend.

---

## 2. Interprocedural Provided Variant Strategy

### 2.1 Concept
When a procedure `BAR(p1, p2, ...)` allocates internal return/intermediate arrays whose sizes depend **only on formal parameters or constants**, it is classified as a **Candidate Callee**. For candidate procedures, the compiler generates two C entrypoints:

1. **Provided Variant Entrypoint (`func_BAR_provided`):**
   ```cpp
   extern "C" sisal_array_t func_BAR_provided(int32_t N, sisal_array_t *prov_res) {
       // Computes results directly into *prov_res (0 heap allocations!)
       ...
       return *prov_res;
   }
   ```
2. **Backward-Compatible Wrapper Entrypoint (`func_BAR`):**
   ```cpp
   extern "C" sisal_array_t func_BAR(int32_t N) {
       sisal_array_t prov_res_local = sisal_array_empty();
       return func_BAR_provided(N, &prov_res_local);
   }
   ```

### 2.2 Caller Call-Site Optimization
When a caller loop invokes a candidate procedure `BAR` on iteration $k$, the caller pre-allocates the destination pointer `prov_res` in the pre-header outside the loop and invokes `func_BAR_provided(args, &prov_res)` inside the loop, eliminating **$N_{\text{steps}}$ heap allocations**.

---

## 3. Pure Structural Candidate Selection (`check_is_candidate_callee`)

To strictly target candidate functions without name-based or string-matching rules:

* **Single Return Array:** The procedure must return a single output port of type `sisal_array_t` (`Array_dv` / `Array_ty`).
* **Parameter Invariance:** Traces all internal array allocation size edges in the callee's IF1 graph `sub_gr`. An allocation size is parameter-invariant if its dataflow slice depends **only on Node 0** (formal procedure parameters) or constant literals.
* **Non-Candidates Untouched:** Functions returning scalars, multi-return structs, or non-parameter-invariant allocations remain standard C functions without `_provided` wrappers.

---

## 4. Single-Assignment Deep-Copy & In-Place Safety Rules

### 4.1 Decision Matrix: Copy of Dope Vector vs Complete `memcpy`

| Scenario | Operation | Memory Allocation | Safety Condition |
| :--- | :--- | :--- | :--- |
| **Read-Only Alias** | `B := A` | **0 `malloc`s, 0 `memcpy`s** | `B` is only read |
| **Contiguous Row Extraction** | `B := A[i, 1..N]` | **0 `malloc`s, 0 `memcpy`s** | `sisal_dv_rank_reduce` advances `B.data` pointer |
| **Last-Use In-Place Update** | `B[i] := v` | **0 `malloc`s, 0 `memcpy`s** | `A` is dead (`edge_free_map`) |
| **Live Value Mutation Hazard** | `B[i] := v` | **Alloc new buffer + `memcpy`** | `A` has future topological readers |

### 4.2 Topological Edge Liveness (`scan_edge_liveness`)
Computes topological node execution order and fanout counts for every graph scope. It identifies the **exact last topological reader** of an array `A`, marking the edge in `edge_free_map` so that downstream operations modify `A` in-place only after all readers have completed.

---

## 5. Architectural Roadmap

1. **Pre-allocated Chained Concatenations (`||`):** Pre-allocate total destination buffer size in the pre-header scope once, turning each iteration's concatenation into a direct store into the pre-allocated slice.
2. **Lazy List Scheduling:** Re-order topological schedules in long declaration chains (e.g., `ricard_dv`) to delay array mutations until after all readers complete, maximizing in-place buffer reuse.
