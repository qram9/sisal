# Sisal Dope-Vector Runtime: Rank-Aware Block Operations

This document provides a detailed overview of the algorithms and implementation mechanics behind the Sisal runtime's **rank-aware block operations** under the Dope-Vector (DV) representation. Specifically, it documents [sisal_dv_replace_slice](file:///Users/ramshankar/work/fromgit/git_sisal/runtime/sisal_runtime.h#L686-L697) and [sisal_array_adjust](file:///Users/ramshankar/work/fromgit/git_sisal/runtime/sisal_runtime.h#L290-L302).

---

## 1. Dope-Vector Layout (`sisal_array_t`)

A multi-dimensional `array_dv` in Sisal is represented as a single flat memory block wrapped in a metadata header. The metadata tracks up to 8 dimensions dynamically at runtime:

```cpp
typedef struct {
    void*    data;             // Pointer to the flat contiguous elements buffer
    uint64_t size;             // Total flat count of scalar elements (product of all dimensions)
    int64_t  lower_bound[8];   // Index lower limits per axis (e.g., lower_bound[0] = row start index)
    int64_t  dims[8];          // Dimensions / extents per axis (e.g., dims[0] = row count)
    int64_t  stride[8];        // Strides along each axis (for element stepping)
    uint8_t  rank;             // Current rank (number of dimensions)
    uint32_t type_id;          // Elem type (double, float, int32, etc.)
} sisal_array_t;
```

---

## 2. Slab & Stride Mechanics

For an array of rank $k > 1$, a **slab** (or row slice) represents the sub-array along the trailing $(k-1)$ dimensions.

```
       Matrix (Rank 2) 4 x 3
       ┌───────────┬───────────┬───────────┐
Row 0: │  data[0]  │  data[1]  │  data[2]  │  ◄── 1D Slab (size = 3)
       ├───────────┼───────────┼───────────┤
Row 1: │  data[3]  │  data[4]  │  data[5]  │
       ├───────────┼───────────┼───────────┤
Row 2: │  data[6]  │  data[7]  │  data[8]  │
       ├───────────┼───────────┼───────────┤
Row 3: │  data[9]  │  data[10] │  data[11] │
       └───────────┴───────────┴───────────┘
```

The size of a single trailing slab is calculated dynamically:
$$\text{slab\_size} = \frac{\text{size}}{\text{dims}[0]}$$

* **For Rank-1 (1D)**: $\text{dims}[0] = \text{size}$, so $\text{slab\_size} = 1$ (the slab is a single scalar element).
* **For Rank-2 (2D)**: $\text{slab\_size} = \frac{\text{size}}{\text{rows}} = \text{columns}$ (the slab is a 1D row).
* **For Rank-3 (3D)**: $\text{slab\_size} = \text{rows} \times \text{columns}$ (the slab is a 2D matrix slice).

---

## 3. Algorithm: `sisal_dv_replace_slice` (Slab Replacement)

Replaces an entire trailing slab at a specified index along the leading axis.

### Implementation
```cpp
inline sisal_array_t sisal_dv_replace_slice(sisal_array_t a, int32_t idx, sisal_array_t slice) {
    sisal_array_t res = a;
    size_t esz = sisal_elem_size(a.type_id);
    size_t slot = (esz > 8 ? esz : 8);
    int32_t dim0 = (a.dims[0] > 0) ? (int32_t)a.dims[0] : (int32_t)a.size;
    uint64_t slice_size = (dim0 > 0) ? (a.size / (uint64_t)dim0) : 0;
    res.data = malloc(a.size * slot);
    memcpy(res.data, a.data, a.size * slot);
    memcpy((char*)res.data + (uint64_t)(idx - (int32_t)a.lower_bound[0]) * slice_size * esz,
           slice.data, slice_size * esz);
    return res;
}
```

### Steps:
1. **Compute Element Size ($esz$)**: Determined dynamically via `type_id`.
2. **Retrieve leading dimension ($dim0$)**: Falls back to `size` if the array is empty or flat.
3. **Compute `slice_size` (Slab elements count)**: Total flat size divided by row count ($dim0$).
4. **Allocate & Copy base array**: Clones $A$ into a fresh output memory slot.
5. **Calculate Target Offset**:
   $$\text{offset} = (\text{idx} - \text{lower\_bound}[0]) \times \text{slice\_size} \times esz$$
6. **Overwrite memory block**: Copies the data of the replacement `slice` directly to the calculated offset in the new array.

---

## 4. Algorithm: `sisal_array_adjust` (Leading-Axis Adjustment)

Extracts a contiguous window of slabs along the leading axis (e.g. slicing rows `lo..hi` out of a matrix).

### Implementation
```cpp
inline sisal_array_t sisal_array_adjust(sisal_array_t a, int64_t lo, int64_t hi) {
    size_t esz = sisal_elem_size(a.type_id);
    int64_t rows = (hi >= lo) ? (hi - lo + 1) : 0;
    int64_t dim0 = (a.dims[0] > 0) ? a.dims[0] : (int64_t)a.size;
    int64_t slice = (dim0 > 0) ? ((int64_t)a.size / dim0) : 1;
    int64_t n_elems = rows * slice;
    sisal_array_t res = sisal_array_alloc_empty(a.rank, a.type_id, (uint64_t)n_elems);
    res.lower_bound[0] = lo;
    for (int k = 1; k < (int)a.rank; k++) { res.dims[k] = a.dims[k]; res.lower_bound[k] = a.lower_bound[k]; }
    res.dims[0] = rows;
    memcpy(res.data, (char*)a.data + (uint64_t)(lo - a.lower_bound[0]) * slice * esz, (uint64_t)n_elems * esz);
    return res;
}
```

### Steps:
1. **Determine Rows Count**: Calculates the sliced rows count: $\text{rows} = \text{hi} - \text{lo} + 1$.
2. **Compute Slice Stride**: Calculated as $\text{slice} = \text{size} / \text{dims}[0]$.
3. **Compute Output size**: Calculated as $\text{n\_elems} = \text{rows} \times \text{slice}$.
4. **Copy Metadata**: Sets the new leading lower bound $\text{lower\_bound}[0] = \text{lo}$ and new $\text{dims}[0] = \text{rows}$, while inheriting trailing dimension extents.
5. **Slice Memory Block**: Copies the sub-block starting at offset:
   $$\text{start\_offset} = (\text{lo} - \text{lower\_bound}[0]) \times \text{slice} \times esz$$
   for a length of $\text{n\_elems} \times esz$ bytes.
