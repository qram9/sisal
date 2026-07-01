# Design Plan: Arbitrary Subscript Slicing (`A[.., j]`)

This document outlines the final design and implementation to support arbitrary slicing (e.g., column slicing `A[.., j]` or mixed slicing `A[i, .., j]`) on dope-vector arrays in Sisal.

---

## 1. The Subscript Load Rule & Exception

### The Standard Subscript Load Rule
In the current OCaml compiler frontend (`to_if1.ml`), subscripts on arrays compile down to **scalar element loads** (i.e. `DV_ELEMENT` or `AELEMENT`), reducing the rank to 0. 

### The Slicing Exception
Slicing is a direct exception to this rule. When a slice `:` (or `..` in Sisal) is present, the subscript operation must **not** compile to a scalar load. Instead:
1. It must return a new, **dope-vector view (`array_dv`)** or a copy of the subset.
2. The output rank must be equal to the number of sliced dimensions (e.g. 1D for `A[.., j]` or `A[i, ..]`).
3. We must preserve type safety by validating that the output type is indeed `array_dv` of the same element type, matching the remaining rank.

---

## 2. OCaml Frontend Lowering Design (`to_if1.ml`)

We represent subscripting as a single, flat `DV_RANK_REDUCE` operation with a **variable number of input ports** mapping to the subscript dimensions of the array.

```
                  ┌─────────────────┐
                  │ DV_RANK_REDUCE  │
                  └──────┬──┬──┬────┘
     Input Array ────────┘  │  │  └─────── Dimension N spec (2 ports)
                             │  └────────── Dimension 1 spec (2 ports)
                             └───────────── Dimension 0 spec (2 ports)
```

Each dimension $k$ is represented by exactly **2 ports**:
1. **Flag Port**: `1` if indexed (concrete index), `0` if sliced (`..`).
2. **Val Port**: The index expression (if Flag = `1`) or the axis index literal (if Flag = `0`).

---

## 3. C Backend Codegen (`apple_lower.ml`)

For a `DV_RANK_REDUCE` node:
- If it has exactly 1 subscript spec port (the original binary node `DV_RANK_REDUCE(A, i)`), we map it directly to the optimal `sisal_dv_rank_reduce(e1, e2)` runtime function.
- If it has more than 1 spec port, it is a slicing node, and we map it to the variadic `sisal_dv_slice` runtime function, forwarding a compound literal `(int32_t[]){ flag0, val0, flag1, val1, ... }` spec array.

---

## 4. Runtime Implementation (`sisal_runtime.h`)

We implement `sisal_dv_slice` to compute the sliced view dynamically:
- **Contiguous Check**: A slice is contiguous if and only if all indexed dimensions precede all sliced/kept dimensions.
- **Zero-Copy View**: If contiguous (e.g. row slice `A[i, ..]`), we compute the pointer offset and return a zero-copy view of the array data.
- **Contiguous Copying**: If non-contiguous (e.g. column slice `A[.., j]`), we allocate a new contiguous data buffer and copy the sliced elements using a multi-dimensional coordinate mapping loop. This ensures that all subsequent index operations (`A[i]`) continue to work seamlessly without complex stride logic in codegen.

```cpp
inline sisal_array_t sisal_dv_slice(sisal_array_t a, const int32_t* spec, int32_t spec_rank) {
    sisal_array_t res = a;
    
    uint64_t strides[8];
    uint64_t current_stride = a.size;
    for (int i = 0; i < (int)a.rank; i++) {
        int32_t dim_size = (a.dims[i] > 0) ? (int32_t)a.dims[i] : (int32_t)current_stride;
        current_stride = (dim_size > 0) ? (current_stride / (uint64_t)dim_size) : 0;
        strides[i] = current_stride;
    }
    
    uint64_t offset = 0;
    uint32_t new_rank = 0;
    int limit = (spec_rank < (int)a.rank) ? spec_rank : (int)a.rank;
    
    bool contiguous = true;
    bool seen_slice = false;
    for (int i = 0; i < limit; i++) {
        int32_t is_indexed = spec[2 * i];
        if (is_indexed) {
            if (seen_slice) {
                contiguous = false;
            }
        } else {
            seen_slice = true;
        }
    }
    
    if (contiguous) {
        for (int i = 0; i < limit; i++) {
            int32_t is_indexed = spec[2 * i];
            int32_t val        = spec[2 * i + 1];
            if (is_indexed) {
                offset += (uint64_t)(val - (int32_t)a.lower_bound[i]) * strides[i];
            } else {
                res.dims[new_rank] = a.dims[val];
                res.lower_bound[new_rank] = a.lower_bound[val];
                new_rank++;
            }
        }
        for (int i = limit; i < (int)a.rank; i++) {
            res.dims[new_rank] = a.dims[i];
            res.lower_bound[new_rank] = a.lower_bound[i];
            new_rank++;
        }
        for (uint32_t i = new_rank; i < 8; i++) {
            res.dims[i] = 0;
            res.lower_bound[i] = 1;
        }
        size_t esz = sisal_elem_size(a.type_id);
        res.data = (char*)a.data + offset * esz;
        res.rank = new_rank;
        uint64_t new_size = 1;
        for (uint32_t i = 0; i < new_rank; i++) {
            new_size *= (res.dims[i] > 0 ? res.dims[i] : 1);
        }
        res.size = (new_rank == 0) ? 1 : new_size;
        return res;
    } else {
        for (int i = 0; i < limit; i++) {
            int32_t is_indexed = spec[2 * i];
            int32_t val        = spec[2 * i + 1];
            if (!is_indexed) {
                res.dims[new_rank] = a.dims[val];
                res.lower_bound[new_rank] = a.lower_bound[val];
                new_rank++;
            }
        }
        for (int i = limit; i < (int)a.rank; i++) {
            res.dims[new_rank] = a.dims[i];
            res.lower_bound[new_rank] = a.lower_bound[i];
            new_rank++;
        }
        for (uint32_t i = new_rank; i < 8; i++) {
            res.dims[i] = 0;
            res.lower_bound[i] = 1;
        }
        res.rank = new_rank;
        uint64_t new_size = 1;
        for (uint32_t i = 0; i < new_rank; i++) {
            new_size *= (res.dims[i] > 0 ? res.dims[i] : 1);
        }
        res.size = (new_rank == 0) ? 1 : new_size;
        
        size_t esz = sisal_elem_size(a.type_id);
        size_t slot = (esz > 8 ? esz : 8);
        res.data = malloc(res.size * slot);
        res.ref_count = 1;
        
        uint64_t dst_idx = 0;
        int64_t coords[8];
        for (int i = 0; i < 8; i++) {
            coords[i] = res.lower_bound[i];
        }
        
        while (dst_idx < res.size) {
            int64_t src_coords[8] = {0};
            int r_idx = 0;
            for (int i = 0; i < (int)a.rank; i++) {
                if (i < limit) {
                    int32_t is_indexed = spec[2 * i];
                    int32_t val        = spec[2 * i + 1];
                    if (is_indexed) {
                        src_coords[i] = val;
                    } else {
                        src_coords[i] = coords[r_idx++];
                    }
                } else {
                    src_coords[i] = coords[r_idx++];
                }
            }
            
            uint64_t src_offset = 0;
            for (int i = 0; i < (int)a.rank; i++) {
                src_offset += (uint64_t)(src_coords[i] - a.lower_bound[i]) * strides[i];
            }
            
            memcpy((char*)res.data + dst_idx * slot, (char*)a.data + src_offset * esz, esz);
            dst_idx++;
            
            for (int d = (int)new_rank - 1; d >= 0; d--) {
                coords[d]++;
                if (coords[d] < res.lower_bound[d] + res.dims[d]) {
                    break;
                }
                coords[d] = res.lower_bound[d];
            }
        }
        
        return res;
    }
}
