#ifndef SISAL_RUNTIME_H
#define SISAL_RUNTIME_H

#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <math.h>
#include <stdarg.h>
#include <dispatch/dispatch.h>
#ifdef __APPLE__
#  include <Accelerate/Accelerate.h>
#else
#  include <cblas.h>
#endif

typedef struct {
    void* data;
    uint64_t size;
    int32_t rank;
    int32_t type_id;
    int32_t ref_count;
    /* Authoritative element byte size, set at allocation (the compiler knows
       sizeof statically).  0 = unset -> fall back to the type_id switch.
       type_id is an IF1 typemap id the runtime cannot interpret beyond the
       preloaded scalars; this field carries the one fact helpers need across
       the compiler/runtime boundary explicitly. */
    uint32_t elem_bytes;
    /* One descriptor triple per rank: (start, size, stride).
       - lower_bound[k] = start of axis k (the Sisal lower bound)
       - dims[k]        = extent of axis k  (ub - lb + 1)
       - stride[k]      = byte stride to step one index along axis k
       lower_bound[0] keeps the meaning of the old scalar lower_bound, so rank-1
       paths are unchanged.  Folding lb into a virtual origin is a later step. */
    int64_t lower_bound[8];
    int64_t dims[8];
    int64_t stride[8];
} sisal_array_t;

template<typename T, typename S>
inline T sisal_cast_dispatch(S s) { 
  return (T)s; 
}

// Specializations for sisal_array_t
template<> inline int32_t sisal_cast_dispatch<int32_t, sisal_array_t>(sisal_array_t s) { 
    return (int32_t)s.size; 
}
template<> inline float sisal_cast_dispatch<float, sisal_array_t>(sisal_array_t s) { return (float)s.size; }
template<> inline double sisal_cast_dispatch<double, sisal_array_t>(sisal_array_t s) { return (double)s.size; }
template<> inline uint64_t sisal_cast_dispatch<uint64_t, sisal_array_t>(sisal_array_t s) { return (uint64_t)s.size; }
template<> inline sisal_array_t sisal_cast_dispatch<sisal_array_t, sisal_array_t>(sisal_array_t s) { return s; }

// Scalar-to-array hacks — preserve value in .size and .dims[0] so the roundtrip
// SISAL_CAST(int32_t, SISAL_CAST(sisal_array_t, x)) == x
template<> inline sisal_array_t sisal_cast_dispatch<sisal_array_t, float>(float s) {
    sisal_array_t a = {}; a.size = (uint64_t)(s > 0 ? (uint64_t)s : 0);
    a.rank = 1; a.ref_count = 1;
    a.dims[0] = (int64_t)(s > 0 ? (int64_t)s : 0); return a;
}
template<> inline sisal_array_t sisal_cast_dispatch<sisal_array_t, double>(double s) {
    sisal_array_t a = {}; a.size = (uint64_t)(s > 0 ? (uint64_t)s : 0);
    a.rank = 1; a.ref_count = 1;
    a.dims[0] = (int64_t)(s > 0 ? (int64_t)s : 0); return a;
}
template<> inline sisal_array_t sisal_cast_dispatch<sisal_array_t, int32_t>(int32_t s) {
    sisal_array_t a = {}; a.size = (uint64_t)(s > 0 ? s : 0);
    a.rank = 1; a.ref_count = 1;
    a.dims[0] = (int64_t)s; return a;
}

#define SISAL_CAST(T, val) sisal_cast_dispatch<T>(val)

inline int32_t sisal_dv_dimension(int32_t dim, sisal_array_t a) {
  if (dim >= 0 && dim < a.rank) return (int32_t)a.dims[dim];
  return (int32_t)a.size;
}

/* Leading-axis conformance guard for `A dot B` (any op iterating two array_dv
   together).  Returns true iff A and B agree on every axis under trailing (numpy)
   alignment: per aligned axis the extents must be equal or one of them 1 (a
   missing leading axis counts as 1).  This is the single intrinsic the front end
   inserts as a guard -- `if sisal_dv_conform(A,B) then <forall> else error` --
   replacing the synthesized per-axis conform forall. */
inline bool sisal_dv_conform(sisal_array_t a, sisal_array_t b) {
  int ra = (int)a.rank, rb = (int)b.rank;
  int mr = ra > rb ? ra : rb;
  for (int k = 0; k < mr; k++) {
    int ia = k - (mr - ra);            /* 0-based axis into a (trailing-aligned) */
    int ib = k - (mr - rb);
    int da = (ia >= 0 && ia < ra) ? (int)a.dims[ia] : 1;
    int db = (ib >= 0 && ib < rb) ? (int)b.dims[ib] : 1;
    if (!(da == db || da == 1 || db == 1)) return false;
  }
  return true;
}

inline int32_t sisal_dv_dimension(int32_t dim, int32_t val) { return val; }

inline int32_t sisal_dv_offset_at(sisal_array_t a, int32_t idx, sisal_array_t shape) {
    // shape is a 1D int32 array: shape.data[i] = size of dimension i
    // shape.size = number of dimensions (MR)
    int32_t* sh_data = (int32_t*)shape.data;
    int32_t ndim = (int32_t)shape.size;

    int32_t coords[8] = {0};
    int32_t remaining = idx;
    // Un-flatten result index into per-axis coords (Row-major)
    for (int i = ndim - 1; i >= 0; i--) {
        int32_t d = sh_data[i];
        if (d <= 0) d = 1;
        coords[i] = remaining % d;
        remaining /= d;
    }

    int32_t linear_offset = 0;
    int32_t current_a_stride = 1;
    int rank_diff = ndim - (int)a.rank;

    // Re-flatten into source array 'a' index, applying broadcast (dim==1 → always 0)
    for (int i = (int)a.rank - 1; i >= 0; i--) {
        int res_axis = i + rank_diff;
        int32_t a_dim = (a.dims[i] > 0) ? (int32_t)a.dims[i]
                      : (a.rank == 1)    ? (int32_t)a.size
                      : 1;
        if (res_axis >= 0 && a_dim > 1) {
            linear_offset += coords[res_axis] * current_a_stride;
        }
        current_a_stride *= a_dim;
    }
    return linear_offset;
}

#ifdef SISAL_CUSTOM_ELEM_SIZE
size_t sisal_elem_size(int32_t type_id);
#else
static inline size_t sisal_elem_size(int32_t type_id) {
    switch (type_id) {
        case 1: case 5: case 6: case 8: return 4;  /* bool/int/int32/float */
        case 4: case 7: return 8;                   /* double/int64 */
        default: return sizeof(sisal_array_t);
    }
}
#endif

/* Element size of an ARRAY VALUE: prefer the authoritative per-array
   elem_bytes (set at allocation); the type_id switch is only the legacy
   fallback -- its default conflates "unknown id" with "descriptor-sized",
   which is right for boxed arrays and wrong for records. */
static inline size_t sisal_esz(sisal_array_t a) {
    return a.elem_bytes ? (size_t)a.elem_bytes : sisal_elem_size(a.type_id);
}

/* Explicit element size (records and anything the type_id switch cannot
   know): the compiler passes sizeof(...) at the call site. */
inline sisal_array_t sisal_array_alloc_sized(int32_t rank, int32_t type_id,
                                             uint64_t size, size_t esz) {
  sisal_array_t a;
  a.data = malloc(size * (esz > 8 ? esz : 8));
  a.size = size;
  a.type_id = type_id;
  a.ref_count = 1;
  a.elem_bytes = (uint32_t)esz;
  a.rank = rank;
  for (int i=0; i<8; i++) { a.lower_bound[i] = 1; a.dims[i] = 0; a.stride[i] = 0; }
  if (rank == 1) a.dims[0] = (int64_t)size;
  return a;
}

inline sisal_array_t sisal_array_alloc_empty(int32_t rank, int32_t type_id, uint64_t size) {
  return sisal_array_alloc_sized(rank, type_id, size, sisal_elem_size(type_id));
}

/* Zeroed descriptor (data NULL, size 0) -- the "no element yet" seed for an
   array-valued forall reduction accumulator. */
inline sisal_array_t sisal_array_empty(void) { sisal_array_t a = {}; return a; }

/* For-initial gather of ARRAY-valued elements (`returns array_dv of w` where w is
   itself an array): FLATTEN, don't box.  Append val's buffer to acc, growing the
   leading dim by 1.  Empty acc seeds from val.  Grows per REAL iteration, so it's
   correct for any induction (incl. multiplicative), and avoids the nested
   array_dv[array_dv[..]] a boxed store would produce.  The element's rank is a
   RUNTIME quantity read off its dope: result rank = val.rank + 1, inner dims
   copied from val (assumes uniform elements). */
inline void sisal_copy_inner_dims(sisal_array_t* res, sisal_array_t val) {
    for (int i = 0; i < (int)val.rank && i < 7; i++) res->dims[i + 1] = val.dims[i];
    /* rank-1 vals from casts/views may carry dims[0]=0 with size set */
    if (val.rank == 1 && res->dims[1] == 0) res->dims[1] = (int64_t)val.size;
}
inline sisal_array_t sisal_array_concat_grow(sisal_array_t acc, sisal_array_t val) {
    size_t esz = sisal_esz(val);
    if (acc.data == NULL) {
        sisal_array_t res = sisal_array_alloc_sized(val.rank + 1, val.type_id, val.size, sisal_esz(val));
        res.dims[0] = 1;
        sisal_copy_inner_dims(&res, val);
        if (val.size) memcpy(res.data, val.data, (size_t)val.size * esz);
        return res;
    }
    uint64_t newsize = acc.size + val.size;
    sisal_array_t res = acc;
    res.data = malloc((size_t)(newsize ? newsize : 1) * (esz > 8 ? esz : 8));
    if (acc.size) memcpy(res.data, acc.data, (size_t)acc.size * esz);
    if (val.size) memcpy((char*)res.data + (size_t)acc.size * esz, val.data, (size_t)val.size * esz);
    res.size = newsize;
    res.rank = val.rank + 1;
    res.dims[0] = acc.dims[0] + 1;
    sisal_copy_inner_dims(&res, val);
    return res;
}

/* Shaped for-initial gather of ARRAY-valued elements (`returns array_dv(n) of w`
   where w is itself an array): place val's buffer in slot `idx` of a result
   preallocated to `ext` leading slots.  The element byte size AND rank are
   runtime values read off val's dope, so allocation happens lazily on the first
   call (leading dim = declared extent, remaining dims = val's own).  Exact
   preallocation -- no per-iteration growth -- and correct for any induction. */
inline sisal_array_t sisal_array_shaped_store(sisal_array_t acc, sisal_array_t val,
                                              int64_t ext, int64_t idx) {
    size_t esz = sisal_esz(val);
    if (acc.data == NULL) {
        uint64_t total = (uint64_t)(ext > 0 ? ext : 0) * val.size;
        acc = sisal_array_alloc_sized(val.rank + 1, val.type_id, total, sisal_esz(val));
        acc.dims[0] = ext;
        for (int i = 0; i < (int)val.rank && i < 7; i++) acc.dims[i + 1] = val.dims[i];
    }
    if (idx >= 0 && idx < acc.dims[0] && val.size)
        memcpy((char*)acc.data + (size_t)idx * (size_t)val.size * esz,
               val.data, (size_t)val.size * esz);
    return acc;
}

/* One elementwise reduction step for an array-VALUED forall reduction
   (`value of sum/product/greatest/least <array>`).  op: 0=sum(+) 1=product(*)
   2=greatest(max) 3=least(min).  An empty acc means this is the first element ->
   return a fresh copy of val; otherwise op(acc, val) elementwise into a new buffer
   (always-copy).  Shape/dims/lower_bound inherited from the operands. */
inline sisal_array_t sisal_array_ereduce(sisal_array_t acc, sisal_array_t val, int op) {
    if (acc.data == NULL || acc.size == 0) {
        size_t esz = sisal_esz(val);
        sisal_array_t res = val;
        res.data = malloc(val.size * (esz > 8 ? esz : 8));
        memcpy(res.data, val.data, (size_t)val.size * esz);
        return res;
    }
    size_t esz = sisal_esz(acc);
    sisal_array_t res = acc;
    res.data = malloc(acc.size * (esz > 8 ? esz : 8));
    memcpy(res.data, acc.data, (size_t)acc.size * esz);
    uint64_t n = acc.size < val.size ? acc.size : val.size;
#define SISAL_EREDUCE_LOOP(T)                                                   \
    do { T* r = (T*)res.data; T* v = (T*)val.data;                              \
         for (uint64_t k = 0; k < n; k++)                                       \
             r[k] = op == 0 ? (T)(r[k] + v[k]) : op == 1 ? (T)(r[k] * v[k])     \
                  : op == 2 ? (r[k] > v[k] ? r[k] : v[k])                       \
                            : (r[k] < v[k] ? r[k] : v[k]); } while (0)
    switch (acc.type_id) {
        case 4:  SISAL_EREDUCE_LOOP(double);  break;
        case 5:  SISAL_EREDUCE_LOOP(float);   break;
        case 7:  SISAL_EREDUCE_LOOP(int64_t); break;
        default: SISAL_EREDUCE_LOOP(int32_t); break;  /* int32/int/bool */
    }
#undef SISAL_EREDUCE_LOOP
    return res;
}

inline sisal_array_t sisal_array_replace_i32(sisal_array_t a, int64_t idx, int32_t val) {
    int64_t liml = a.lower_bound[0];
    int64_t dim0 = (a.dims[0] > 0) ? a.dims[0] : (int64_t)a.size;
    int64_t limh = liml + dim0 - 1;

    if (idx == limh + 1) {
        sisal_array_t res = sisal_array_alloc_sized(a.rank, a.type_id, a.size + 1, sisal_esz(a));
        res.lower_bound[0] = a.lower_bound[0];
        res.dims[0] = dim0 + 1;
        for (int i = 1; i < a.rank; i++) { res.dims[i] = a.dims[i]; res.lower_bound[i] = a.lower_bound[i]; }
        memcpy(res.data, a.data, a.size * 4);
        ((int32_t*)res.data)[a.size] = val;
        return res;
    } else if (idx == liml - 1) {
        sisal_array_t res = sisal_array_alloc_sized(a.rank, a.type_id, a.size + 1, sisal_esz(a));
        res.lower_bound[0] = a.lower_bound[0] - 1;
        res.dims[0] = dim0 + 1;
        for (int i = 1; i < a.rank; i++) { res.dims[i] = a.dims[i]; res.lower_bound[i] = a.lower_bound[i]; }
        memcpy((int32_t*)res.data + 1, a.data, a.size * 4);
        ((int32_t*)res.data)[0] = val;
        return res;
    } else {
        sisal_array_t res = a;
        res.data = malloc(a.size * 8);
        memcpy(res.data, a.data, a.size * 8);
        ((int32_t*)res.data)[idx - a.lower_bound[0]] = val;
        return res;
    }
}
inline sisal_array_t sisal_array_replace_f32(sisal_array_t a, int64_t idx, float val) {
    int64_t liml = a.lower_bound[0];
    int64_t dim0 = (a.dims[0] > 0) ? a.dims[0] : (int64_t)a.size;
    int64_t limh = liml + dim0 - 1;

    if (idx == limh + 1) {
        sisal_array_t res = sisal_array_alloc_sized(a.rank, a.type_id, a.size + 1, sisal_esz(a));
        res.lower_bound[0] = a.lower_bound[0];
        res.dims[0] = dim0 + 1;
        for (int i = 1; i < a.rank; i++) { res.dims[i] = a.dims[i]; res.lower_bound[i] = a.lower_bound[i]; }
        memcpy(res.data, a.data, a.size * 4);
        ((float*)res.data)[a.size] = val;
        return res;
    } else if (idx == liml - 1) {
        sisal_array_t res = sisal_array_alloc_sized(a.rank, a.type_id, a.size + 1, sisal_esz(a));
        res.lower_bound[0] = a.lower_bound[0] - 1;
        res.dims[0] = dim0 + 1;
        for (int i = 1; i < a.rank; i++) { res.dims[i] = a.dims[i]; res.lower_bound[i] = a.lower_bound[i]; }
        memcpy((float*)res.data + 1, a.data, a.size * 4);
        ((float*)res.data)[0] = val;
        return res;
    } else {
        sisal_array_t res = a;
        res.data = malloc(a.size * 8);
        memcpy(res.data, a.data, a.size * 8);
        ((float*)res.data)[idx - a.lower_bound[0]] = val;
        return res;
    }
}
inline sisal_array_t sisal_array_replace_f64(sisal_array_t a, int64_t idx, double val) {
    int64_t liml = a.lower_bound[0];
    int64_t dim0 = (a.dims[0] > 0) ? a.dims[0] : (int64_t)a.size;
    int64_t limh = liml + dim0 - 1;

    if (idx == limh + 1) {
        sisal_array_t res = sisal_array_alloc_sized(a.rank, a.type_id, a.size + 1, sisal_esz(a));
        res.lower_bound[0] = a.lower_bound[0];
        res.dims[0] = dim0 + 1;
        for (int i = 1; i < a.rank; i++) { res.dims[i] = a.dims[i]; res.lower_bound[i] = a.lower_bound[i]; }
        memcpy(res.data, a.data, a.size * 8);
        ((double*)res.data)[a.size] = val;
        return res;
    } else if (idx == liml - 1) {
        sisal_array_t res = sisal_array_alloc_sized(a.rank, a.type_id, a.size + 1, sisal_esz(a));
        res.lower_bound[0] = a.lower_bound[0] - 1;
        res.dims[0] = dim0 + 1;
        for (int i = 1; i < a.rank; i++) { res.dims[i] = a.dims[i]; res.lower_bound[i] = a.lower_bound[i]; }
        memcpy((double*)res.data + 1, a.data, a.size * 8);
        ((double*)res.data)[0] = val;
        return res;
    } else {
        sisal_array_t res = a;
        res.data = malloc(a.size * 8);
        memcpy(res.data, a.data, a.size * 8);
        ((double*)res.data)[idx - a.lower_bound[0]] = val;
        return res;
    }
}
inline sisal_array_t sisal_array_replace_arr(sisal_array_t a, int64_t idx, sisal_array_t val) {
    int64_t liml = a.lower_bound[0];
    int64_t dim0 = (a.dims[0] > 0) ? a.dims[0] : (int64_t)a.size;
    int64_t limh = liml + dim0 - 1;
    size_t esz = sizeof(sisal_array_t);

    if (idx == limh + 1) {
        sisal_array_t res = sisal_array_alloc_sized(a.rank, a.type_id, a.size + 1, sisal_esz(a));
        res.lower_bound[0] = a.lower_bound[0];
        res.dims[0] = dim0 + 1;
        for (int i = 1; i < a.rank; i++) { res.dims[i] = a.dims[i]; res.lower_bound[i] = a.lower_bound[i]; }
        memcpy(res.data, a.data, a.size * esz);
        ((sisal_array_t*)res.data)[a.size] = val;
        return res;
    } else if (idx == liml - 1) {
        sisal_array_t res = sisal_array_alloc_sized(a.rank, a.type_id, a.size + 1, sisal_esz(a));
        res.lower_bound[0] = a.lower_bound[0] - 1;
        res.dims[0] = dim0 + 1;
        for (int i = 1; i < a.rank; i++) { res.dims[i] = a.dims[i]; res.lower_bound[i] = a.lower_bound[i]; }
        memcpy((char*)res.data + esz, a.data, a.size * esz);
        ((sisal_array_t*)res.data)[0] = val;
        return res;
    } else {
        sisal_array_t res = a;
        res.data = malloc(a.size * esz);
        memcpy(res.data, a.data, a.size * esz);
        ((sisal_array_t*)res.data)[idx - a.lower_bound[0]] = val;
        return res;
    }
}


/* ADDH: append `val` at the high end -> new array of size+1 (lower_bound kept). */
inline sisal_array_t sisal_array_addh_i32(sisal_array_t a, int32_t val) {
    sisal_array_t res = sisal_array_alloc_sized(a.rank, a.type_id, a.size + 1, sisal_esz(a));
    res.lower_bound[0] = a.lower_bound[0];
    memcpy(res.data, a.data, a.size * 8);
    ((int32_t*)res.data)[a.size] = val;
    return res;
}
inline sisal_array_t sisal_array_addh_f32(sisal_array_t a, float val) {
    sisal_array_t res = sisal_array_alloc_sized(a.rank, a.type_id, a.size + 1, sisal_esz(a));
    res.lower_bound[0] = a.lower_bound[0];
    memcpy(res.data, a.data, a.size * 8);
    ((float*)res.data)[a.size] = val;
    return res;
}
inline sisal_array_t sisal_array_addh_f64(sisal_array_t a, double val) {
    sisal_array_t res = sisal_array_alloc_sized(a.rank, a.type_id, a.size + 1, sisal_esz(a));
    res.lower_bound[0] = a.lower_bound[0];
    memcpy(res.data, a.data, a.size * 8);
    ((double*)res.data)[a.size] = val;
    return res;
}
/* array_dv addh where the appended value is itself an array: rank-polymorphic
   splice along axis 0.  B is a SLAB (rank == a.rank-1, B == a's trailing dims) -> the
   leading dim grows by 1; or a STACK (rank == a.rank, trailing dims agree) -> leading
   dim grows by b.dims[0].  Trailing dims are inherited from A; data is A's flat buffer
   with B's flat buffer appended.  (Numpy `concatenate`-along-axis-0 semantics.) */
inline sisal_array_t sisal_array_addh_arr(sisal_array_t a, sisal_array_t b) {
    size_t esz = sisal_esz(a);
    int64_t add_rows = (b.rank == a.rank) ? (b.dims[0] > 0 ? b.dims[0] : 1) : 1;
    int64_t b_elems = (int64_t)b.size;
    sisal_array_t res = sisal_array_alloc_sized(a.rank, a.type_id, a.size + (uint64_t)b_elems, sisal_esz(a));
    res.lower_bound[0] = a.lower_bound[0];
    for (int k = 1; k < (int)a.rank; k++) { res.dims[k] = a.dims[k]; res.lower_bound[k] = a.lower_bound[k]; }
    res.dims[0] = a.dims[0] + add_rows;
    memcpy(res.data, a.data, a.size * esz);
    memcpy((char*)res.data + (uint64_t)a.size * esz, b.data, (uint64_t)b_elems * esz);
    return res;
}

inline sisal_array_t sisal_array_catenate(sisal_array_t acc, sisal_array_t val) {
    /* empty val is the identity: without this, addh_arr would still bump
       dims[0] by one phantom (zero-element) row/slot, leaving dims[0]
       inconsistent with size (zero-trip loops produce empty descriptors). */
    if (val.data == NULL || val.size == 0) return acc;
    if (acc.data == NULL || acc.size == 0) {
        size_t esz = sisal_esz(val);
        sisal_array_t res = val;
        res.data = malloc(val.size * (esz > 8 ? esz : 8));
        memcpy(res.data, val.data, (size_t)val.size * esz);
        return res;
    }
    return sisal_array_addh_arr(acc, val);
}

inline sisal_array_t sisal_array_build_double(int64_t lb, int count, const double* elems) {
    sisal_array_t res = sisal_array_alloc_empty(1, 4, (uint64_t)count);
    res.lower_bound[0] = lb;
    res.dims[0] = count;
    memcpy(res.data, elems, (size_t)count * sizeof(double));
    return res;
}
inline sisal_array_t sisal_array_build_i32(int64_t lb, int count, const int32_t* elems) {
    sisal_array_t res = sisal_array_alloc_empty(1, 6, (uint64_t)count);
    res.lower_bound[0] = lb;
    res.dims[0] = count;
    memcpy(res.data, elems, (size_t)count * sizeof(int32_t));
    return res;
}
/* Generic array-literal builder: element type known statically at the call
   site (T), type_id recorded for the dope, elem_bytes = sizeof(T) so helpers
   agree with the typed-pointer writers. */
template<typename T>
inline sisal_array_t sisal_array_build_elems(int64_t lb, int count, const T* elems, int32_t type_id) {
    sisal_array_t res = sisal_array_alloc_sized(1, type_id, (uint64_t)count, sizeof(T));
    res.lower_bound[0] = lb;
    res.dims[0] = count;
    if (count > 0) memcpy(res.data, elems, (size_t)count * sizeof(T));
    return res;
}

inline sisal_array_t sisal_array_build_arr(int64_t lb, int count, const sisal_array_t* elems) {
    int32_t elem_rank = elems[0].rank;
    int32_t type_id = elems[0].type_id;
    size_t esz = sisal_elem_size(type_id);
    uint64_t total_size = 0;
    for (int i = 0; i < count; i++) {
        total_size += elems[i].size;
    }
    sisal_array_t res = sisal_array_alloc_empty(elem_rank + 1, type_id, total_size);
    res.lower_bound[0] = lb;
    res.dims[0] = count;
    for (int k = 0; k < elem_rank; k++) {
        res.dims[k + 1] = elems[0].dims[k];
        res.lower_bound[k + 1] = elems[0].lower_bound[k];
    }
    char* ptr = (char*)res.data;
    for (int i = 0; i < count; i++) {
        uint64_t sz = elems[i].size * esz;
        memcpy(ptr, elems[i].data, sz);
        ptr += sz;
    }
    return res;
}

/* FILL(lo, hi, val): new array indexed [lo..hi] (size hi-lo+1), every element = val. */
inline sisal_array_t sisal_array_fill_i32(int64_t lo, int64_t hi, int32_t val) {
    int64_t n = (hi >= lo) ? (hi - lo + 1) : 0;
    sisal_array_t res = sisal_array_alloc_empty(1, 6, (uint64_t)n);
    res.lower_bound[0] = lo;
    for (int64_t k = 0; k < n; k++) ((int32_t*)res.data)[k] = val;
    return res;
}
inline sisal_array_t sisal_array_fill_f32(int64_t lo, int64_t hi, float val) {
    int64_t n = (hi >= lo) ? (hi - lo + 1) : 0;
    sisal_array_t res = sisal_array_alloc_empty(1, 8, (uint64_t)n);
    res.lower_bound[0] = lo;
    for (int64_t k = 0; k < n; k++) ((float*)res.data)[k] = val;
    return res;
}
inline sisal_array_t sisal_array_fill_f64(int64_t lo, int64_t hi, double val) {
    int64_t n = (hi >= lo) ? (hi - lo + 1) : 0;
    sisal_array_t res = sisal_array_alloc_empty(1, 4, (uint64_t)n);
    res.lower_bound[0] = lo;
    for (int64_t k = 0; k < n; k++) ((double*)res.data)[k] = val;
    return res;
}
inline sisal_array_t sisal_array_fill_arr(int64_t lo, int64_t hi, sisal_array_t val) {
    int64_t n = (hi >= lo) ? (hi - lo + 1) : 0;
    sisal_array_t res = sisal_array_alloc_sized(1, val.type_id, (uint64_t)n, sisal_esz(val));
    res.lower_bound[0] = lo;
    for (int64_t k = 0; k < n; k++) ((sisal_array_t*)res.data)[k] = val;
    return res;
}

template <typename T>
inline sisal_array_t sisal_array_fill_rec(int64_t lo, int64_t hi, T val, int32_t type_id) {
    int64_t n = (hi >= lo) ? (hi - lo + 1) : 0;
    sisal_array_t res = sisal_array_alloc_sized(1, type_id, (uint64_t)n, sizeof(T));
    res.lower_bound[0] = lo;
    for (int64_t k = 0; k < n; k++) ((T*)res.data)[k] = val;
    return res;
}

/* ADDL: prepend `val` at the low end -> size+1, val at index 0, A shifted up,
   lower_bound-1.  Mirror of ADDH (8-byte slot convention). */
inline sisal_array_t sisal_array_addl_i32(sisal_array_t a, int32_t val) {
    sisal_array_t res = sisal_array_alloc_sized(a.rank, a.type_id, a.size + 1, sisal_esz(a));
    res.lower_bound[0] = a.lower_bound[0] - 1;
    ((int32_t*)res.data)[0] = val;
    memcpy((char*)res.data + 8, a.data, a.size * 8);
    return res;
}
inline sisal_array_t sisal_array_addl_f32(sisal_array_t a, float val) {
    sisal_array_t res = sisal_array_alloc_sized(a.rank, a.type_id, a.size + 1, sisal_esz(a));
    res.lower_bound[0] = a.lower_bound[0] - 1;
    ((float*)res.data)[0] = val;
    memcpy((char*)res.data + 8, a.data, a.size * 8);
    return res;
}
inline sisal_array_t sisal_array_addl_f64(sisal_array_t a, double val) {
    sisal_array_t res = sisal_array_alloc_sized(a.rank, a.type_id, a.size + 1, sisal_esz(a));
    res.lower_bound[0] = a.lower_bound[0] - 1;
    ((double*)res.data)[0] = val;
    memcpy((char*)res.data + 8, a.data, a.size * 8);
    return res;
}
inline sisal_array_t sisal_array_addl_arr(sisal_array_t a, sisal_array_t b) {
    /* prepend B (a slab/stack) at the low end -- rank-poly mirror of addh_arr */
    size_t esz = sisal_esz(a);
    int64_t add_rows = (b.rank == a.rank) ? (b.dims[0] > 0 ? b.dims[0] : 1) : 1;
    int64_t b_elems = (int64_t)b.size;
    sisal_array_t res = sisal_array_alloc_sized(a.rank, a.type_id, a.size + (uint64_t)b_elems, sisal_esz(a));
    res.lower_bound[0] = a.lower_bound[0] - add_rows;
    for (int k = 1; k < (int)a.rank; k++) { res.dims[k] = a.dims[k]; res.lower_bound[k] = a.lower_bound[k]; }
    res.dims[0] = a.dims[0] + add_rows;
    memcpy(res.data, b.data, (uint64_t)b_elems * esz);
    memcpy((char*)res.data + (uint64_t)b_elems * esz, a.data, a.size * esz);
    return res;
}

/* ADJUST: re-bounded subrange A[lo..hi] along the LEADING axis -- a window of
   (hi-lo+1) slabs.  Rank-aware: for rank-1 a slab is one element; for rank-k it is a
   trailing (k-1)-D slab (slice = product of trailing dims).  Result dims[0]=hi-lo+1,
   trailing dims inherited, lower_bound[0]=lo. */
inline sisal_array_t sisal_array_adjust(sisal_array_t a, int64_t lo, int64_t hi) {
    size_t esz = sisal_esz(a);
    int64_t rows = (hi >= lo) ? (hi - lo + 1) : 0;
    int64_t dim0 = (a.dims[0] > 0) ? a.dims[0] : (int64_t)a.size;
    int64_t slice = (dim0 > 0) ? ((int64_t)a.size / dim0) : 1;
    int64_t n_elems = rows * slice;
    sisal_array_t res = sisal_array_alloc_sized(a.rank, a.type_id, (uint64_t)n_elems, sisal_esz(a));
    res.lower_bound[0] = lo;
    for (int k = 1; k < (int)a.rank; k++) { res.dims[k] = a.dims[k]; res.lower_bound[k] = a.lower_bound[k]; }
    res.dims[0] = rows;
    memcpy(res.data, (char*)a.data + (uint64_t)(lo - a.lower_bound[0]) * slice * esz, (uint64_t)n_elems * esz);
    return res;
}

inline sisal_array_t sisal_array_setl(sisal_array_t a, int64_t lb) {
    sisal_array_t res = a;
    res.lower_bound[0] = lb;
    return res;
}

inline sisal_array_t sisal_array_reshape_by_shape(sisal_array_t a, sisal_array_t shape) {
    sisal_array_t res = a;
    res.rank = (int32_t)shape.size;
    int32_t* sh_data = (int32_t*)shape.data;
    for (int i = 0; i < res.rank && i < 8; i++) {
        res.dims[i] = sh_data[i];
    }
    return res;
}

inline sisal_array_t sisal_array_add(sisal_array_t a, sisal_array_t b) {
    sisal_array_t res = sisal_array_alloc_sized(a.rank, a.type_id, a.size, sisal_esz(a));
    for (int i=0; i<a.rank; i++) res.dims[i] = a.dims[i];
    double* da = (double*)a.data;
    double* db = (double*)b.data;
    double* dr = (double*)res.data;
    for (uint64_t i=0; i<a.size; i++) dr[i] = da[i] + db[i];
    return res;
}

inline sisal_array_t sisal_array_sub(sisal_array_t a, sisal_array_t b) {
    sisal_array_t res = sisal_array_alloc_sized(a.rank, a.type_id, a.size, sisal_esz(a));
    for (int i=0; i<a.rank; i++) res.dims[i] = a.dims[i];
    double* da = (double*)a.data;
    double* db = (double*)b.data;
    double* dr = (double*)res.data;
    for (uint64_t i=0; i<a.size; i++) dr[i] = da[i] - db[i];
    return res;
}

inline sisal_array_t sisal_array_mul(sisal_array_t a, sisal_array_t b) {
    sisal_array_t res = sisal_array_alloc_sized(a.rank, a.type_id, a.size, sisal_esz(a));
    for (int i=0; i<a.rank; i++) res.dims[i] = a.dims[i];
    double* da = (double*)a.data;
    double* db = (double*)b.data;
    double* dr = (double*)res.data;
    for (uint64_t i=0; i<a.size; i++) dr[i] = da[i] * db[i];
    return res;
}

inline float sisal_array_reduce_sum(sisal_array_t a) {
    float s = 0;
    float* d = (float*)a.data;
    for(uint64_t i=0; i<a.size; i++) s += d[i];
    return s;
}

inline int32_t sisal_array_reduce_int_product(sisal_array_t a) {
    int32_t p = 1;
    int32_t* d = (int32_t*)a.data;
    for(uint64_t i=0; i<a.size; i++) p *= d[i];
    return p;
}

inline float sisal_array_reduce_float_product(sisal_array_t a) {
    float p = 1.0f; float* d = (float*)a.data;
    for(uint64_t i=0; i<a.size; i++) p *= d[i]; return p;
}
inline double sisal_array_reduce_double_sum(sisal_array_t a) {
    double s = 0.0; double* d = (double*)a.data;
    for(uint64_t i=0; i<a.size; i++) s += d[i]; return s;
}
inline int32_t sisal_array_reduce_int_sum(sisal_array_t a) {
    int32_t s = 0; int32_t* d = (int32_t*)a.data;
    for(uint64_t i=0; i<a.size; i++) s += d[i]; return s;
}
inline double sisal_array_reduce_double_product(sisal_array_t a) {
    double p = 1.0; double* d = (double*)a.data;
    for(uint64_t i=0; i<a.size; i++) p *= d[i]; return p;
}
inline float sisal_array_reduce_least(sisal_array_t a) {
    float* d = (float*)a.data; float v = a.size ? d[0] : 0.0f;
    for(uint64_t i=1; i<a.size; i++) if(d[i]<v) v=d[i]; return v;
}
inline double sisal_array_reduce_double_least(sisal_array_t a) {
    double* d = (double*)a.data; double v = a.size ? d[0] : 0.0;
    for(uint64_t i=1; i<a.size; i++) if(d[i]<v) v=d[i]; return v;
}
inline int32_t sisal_array_reduce_int_least(sisal_array_t a) {
    int32_t* d = (int32_t*)a.data; int32_t v = a.size ? d[0] : 0;
    for(uint64_t i=1; i<a.size; i++) if(d[i]<v) v=d[i]; return v;
}
inline float sisal_array_reduce_greatest(sisal_array_t a) {
    float* d = (float*)a.data; float v = a.size ? d[0] : 0.0f;
    for(uint64_t i=1; i<a.size; i++) if(d[i]>v) v=d[i]; return v;
}
inline double sisal_array_reduce_double_greatest(sisal_array_t a) {
    double* d = (double*)a.data; double v = a.size ? d[0] : 0.0;
    for(uint64_t i=1; i<a.size; i++) if(d[i]>v) v=d[i]; return v;
}
inline int32_t sisal_array_reduce_int_greatest(sisal_array_t a) {
    int32_t* d = (int32_t*)a.data; int32_t v = a.size ? d[0] : 0;
    for(uint64_t i=1; i<a.size; i++) if(d[i]>v) v=d[i]; return v;
}

/* INNERPRODUCT: full APL/numpy dot semantics, row-major, any ranks.
   Contract last axis of A with second-to-last axis of B (last if B rank-1).
   Result shape = A.shape[:-1] + B.shape[:-2] + B.shape[-1:]
   Result rank  = rankA + rankB - 2  (minimum 1, dot product wraps in size-1).

   Implementation:
     A is logically (M, K) where M = prod(A.shape[:-1]), K = A.shape[-1].
     B rank-1: GEMV → result shape A.shape[:-1]
     B rank-2: GEMM → result shape A.shape[:-1] + (N,)
     B rank>2: L batched GEMMs, L = prod(B.shape[:-2]), scattered into result.
   BLAS (float/double) or loop (int32). */
inline sisal_array_t sisal_array_innerproduct(sisal_array_t a, sisal_array_t b) {
    int ar = a.rank, br = b.rank, tid = a.type_id;

    /* contraction axis sizes */
    int64_t Ka = (ar >= 1) ? a.dims[ar-1] : (int64_t)a.size;
    int64_t Kb = (br <= 1) ? (int64_t)b.size : b.dims[br-2];
    if (Ka != Kb) {
        fprintf(stderr, "innerproduct: axis mismatch A[%d]=%lld B[%d]=%lld\n",
                ar-1, (long long)Ka, br<=1?0:br-2, (long long)Kb);
        return sisal_array_alloc_empty(1, tid, 0);
    }
    int K = (int)Ka;

    /* M = prod(A.shape[:-1]),  N = B.shape[-1],  L = prod(B.shape[:-2]) */
    int64_t M = 1; for (int i=0; i<ar-1; i++) M *= a.dims[i];
    int64_t N = (br >= 1) ? b.dims[br-1] : 1;
    int64_t L = 1; for (int i=0; i<br-2; i++) L *= b.dims[i];
    int Mint=(int)M, Nint=(int)N, Lint=(int)L;

    /* result rank and shape */
    int rr = (ar-1) + (br >= 2 ? br-1 : 0);
    if (rr < 1) rr = 1;
    int64_t rs = (br >= 2) ? M*L*N : (M > 0 ? M : 1);
    sisal_array_t r = sisal_array_alloc_empty(rr, tid, (uint64_t)rs);
    { int di=0;
      for (int i=0; i<ar-1; i++) r.dims[di++] = a.dims[i];   /* A.shape[:-1] */
      if (br >= 2) {
        for (int i=0; i<br-2; i++) r.dims[di++] = b.dims[i]; /* B.shape[:-2] */
        r.dims[di++] = N;                                      /* B.shape[-1]  */
      }
      if (di == 0) r.dims[0] = 1; }

    /* K=0: no contraction terms, result is all zeros */
    if (K == 0) { memset(r.data, 0, (size_t)rs * sisal_elem_size(tid)); return r; }

    /* --- dispatch --- */
    if (br <= 1) {
        /* A_flat(M,K) @ b(K) → r(M)  via GEMV */
        int Mv = Mint > 0 ? Mint : 1;
        if (tid==4)
            cblas_dgemv(CblasRowMajor,CblasNoTrans,Mv,K,1.0,
                        (double*)a.data,K,(double*)b.data,1,0.0,(double*)r.data,1);
        else if (tid==6) {
            int32_t *da=(int32_t*)a.data,*db=(int32_t*)b.data,*dr=(int32_t*)r.data;
            for(int m=0;m<Mv;m++){int32_t s=0;for(int k=0;k<K;k++)s+=da[m*K+k]*db[k];dr[m]=s;}
        } else
            cblas_sgemv(CblasRowMajor,CblasNoTrans,Mv,K,1.0f,
                        (float*)a.data,K,(float*)b.data,1,0.0f,(float*)r.data,1);

    } else if (L == 1) {
        /* A_flat(M,K) @ B(K,N) → r(M,N)  via GEMM */
        if (tid==4)
            cblas_dgemm(CblasRowMajor,CblasNoTrans,CblasNoTrans,Mint,Nint,K,
                        1.0,(double*)a.data,K,(double*)b.data,Nint,0.0,(double*)r.data,Nint);
        else if (tid==6) {
            int32_t *da=(int32_t*)a.data,*db=(int32_t*)b.data,*dr=(int32_t*)r.data;
            for(int m=0;m<Mint;m++) for(int j=0;j<Nint;j++){
                int32_t s=0;for(int k=0;k<K;k++)s+=da[m*K+k]*db[k*Nint+j];dr[m*Nint+j]=s;}
        } else
            cblas_sgemm(CblasRowMajor,CblasNoTrans,CblasNoTrans,Mint,Nint,K,
                        1.0f,(float*)a.data,K,(float*)b.data,Nint,0.0f,(float*)r.data,Nint);

    } else {
        /* B has batch dims (L>1): L separate GEMMs, scatter into r[m,l,j].
           B[l] starts at l*K*N; result[m,l,j] = m*L*N + l*N + j (non-contiguous). */
        size_t esz = (tid==4)?sizeof(double):(tid==6)?sizeof(int32_t):sizeof(float);
        void* tmp = malloc((size_t)Mint*(size_t)Nint*esz);
        for (int l=0; l<Lint; l++) {
            if (tid==4) {
                double *da=(double*)a.data, *db_l=(double*)b.data+l*K*Nint;
                cblas_dgemm(CblasRowMajor,CblasNoTrans,CblasNoTrans,Mint,Nint,K,
                            1.0,da,K,db_l,Nint,0.0,(double*)tmp,Nint);
                double *dt=(double*)tmp, *dr=(double*)r.data;
                for(int m=0;m<Mint;m++) for(int j=0;j<Nint;j++)
                    dr[m*Lint*Nint+l*Nint+j] = dt[m*Nint+j];
            } else if (tid==6) {
                int32_t *da=(int32_t*)a.data,*db_l=(int32_t*)b.data+l*K*Nint,*dr=(int32_t*)r.data;
                for(int m=0;m<Mint;m++) for(int j=0;j<Nint;j++){
                    int32_t s=0;for(int k=0;k<K;k++)s+=da[m*K+k]*db_l[k*Nint+j];
                    dr[m*Lint*Nint+l*Nint+j]=s;}
            } else {
                float *da=(float*)a.data, *db_l=(float*)b.data+l*K*Nint;
                cblas_sgemm(CblasRowMajor,CblasNoTrans,CblasNoTrans,Mint,Nint,K,
                            1.0f,da,K,db_l,Nint,0.0f,(float*)tmp,Nint);
                float *dt=(float*)tmp, *dr=(float*)r.data;
                for(int m=0;m<Mint;m++) for(int j=0;j<Nint;j++)
                    dr[m*Lint*Nint+l*Nint+j] = dt[m*Nint+j];
            }
        }
        free(tmp);
    }
    return r;
}

/* REVERSE: return a copy with elements in reverse order */
inline sisal_array_t sisal_array_reverse(sisal_array_t a) {
    sisal_array_t res = sisal_array_alloc_sized(a.rank, a.type_id, a.size, sisal_esz(a));
    for (int i = 0; i < 8; i++) res.lower_bound[i] = a.lower_bound[i];
    int32_t* src = (int32_t*)a.data; int32_t* dst = (int32_t*)res.data;
    for (uint64_t i = 0; i < a.size; i++) dst[i] = src[a.size - 1 - i];
    return res;
}

/* ROTATE(a, n): circular LEFT shift by n (APL `n rotate A`); negative n rotates
   right.  dst[i] = src[(i + n) mod N].  Type-generic via element size. */
inline sisal_array_t sisal_array_rotate(sisal_array_t a, int32_t n) {
    sisal_array_t res = sisal_array_alloc_sized(a.rank, a.type_id, a.size, sisal_esz(a));
    for (int i = 0; i < 8; i++) res.lower_bound[i] = a.lower_bound[i];
    int64_t N = (int64_t)a.size;
    if (N == 0) return res;
    size_t esz = sisal_esz(a);
    int64_t sh = (((int64_t)n % N) + N) % N;          /* normalise to [0, N) */
    char* src = (char*)a.data; char* dst = (char*)res.data;
    for (int64_t i = 0; i < N; i++)
        memcpy(dst + i * esz, src + ((i + sh) % N) * esz, esz);
    return res;
}

/* SLICE(a, lo, hi): the contiguous sub-range a[lo..hi] (Sisal 1-based, inclusive),
   re-based to lower_bound 1.  Type-generic. */
inline sisal_array_t sisal_array_slice(sisal_array_t a, int32_t lo, int32_t hi) {
    int64_t count = (int64_t)hi - (int64_t)lo + 1;
    if (count < 0) count = 0;
    sisal_array_t res = sisal_array_alloc_sized(a.rank, a.type_id, (uint64_t)count, sisal_esz(a));
    res.lower_bound[0] = 1;
    if (count == 0) return res;
    size_t esz = sisal_esz(a);
    int64_t off = (int64_t)lo - a.lower_bound[0];      /* 0-based start in `a` */
    if (off < 0) off = 0;
    memcpy((char*)res.data, (char*)a.data + off * esz, (size_t)count * esz);
    return res;
}

/* element i of `a` is non-zero?  (per the array's element type) */
static inline bool sisal_elem_is_nonzero(sisal_array_t a, uint64_t i) {
    switch (a.type_id) {
        case 4: return ((double*)a.data)[i] != 0.0;
        case 8: return ((float*)a.data)[i] != 0.0f;
        case 7: return ((int64_t*)a.data)[i] != 0;
        default: return ((int32_t*)a.data)[i] != 0;   /* int / bool */
    }
}

/* NONZERO(a): the 1-based indices (int array) of the non-zero elements of a. */
inline sisal_array_t sisal_array_nonzero(sisal_array_t a) {
    uint64_t count = 0;
    for (uint64_t i = 0; i < a.size; i++) if (sisal_elem_is_nonzero(a, i)) count++;
    sisal_array_t res = sisal_array_alloc_empty(1, 6, count);   /* int32 indices */
    res.lower_bound[0] = 1;
    int32_t* out = (int32_t*)res.data;
    uint64_t k = 0;
    for (uint64_t i = 0; i < a.size; i++)
        if (sisal_elem_is_nonzero(a, i)) out[k++] = (int32_t)(i + a.lower_bound[0]);
    return res;
}

/* WHERE(cond, a, b): elementwise select -- result[i] = cond[i] ? a[i] : b[i].
   cond is a bool array; result takes a's type/shape.  Type-generic. */
inline sisal_array_t sisal_array_where(sisal_array_t cond, sisal_array_t a, sisal_array_t b) {
    sisal_array_t res = sisal_array_alloc_sized(a.rank, a.type_id, a.size, sisal_esz(a));
    for (int i = 0; i < 8; i++) { res.lower_bound[i] = a.lower_bound[i]; res.dims[i] = a.dims[i]; }
    size_t esz = sisal_esz(a);
    bool* m = (bool*)cond.data;
    char* ad = (char*)a.data; char* bd = (char*)b.data; char* rd = (char*)res.data;
    for (uint64_t i = 0; i < a.size; i++)
        memcpy(rd + i * esz, (m[i] ? ad : bd) + i * esz, esz);
    return res;
}

/* write `fill` (a double, converted to the array's element type) into res[i] */
static inline void sisal_elem_set_d(sisal_array_t res, int64_t i, double fill) {
    switch (res.type_id) {
        case 4: ((double*)res.data)[i] = fill; break;
        case 8: ((float*)res.data)[i] = (float)fill; break;
        case 7: ((int64_t*)res.data)[i] = (int64_t)fill; break;
        default: ((int32_t*)res.data)[i] = (int32_t)fill; break;
    }
}

/* PERMUTE(a, nperm, d0, d1, ...): reorder axes -- result axis k = source axis
   d[k] (0-based).  PERMUTE(A,2,1,0) transposes a rank-2 array.  Type-generic,
   general rank (<= 8). */
inline sisal_array_t sisal_array_permute(sisal_array_t a, int32_t nperm, ...) {
    int perm[8];
    va_list ap; va_start(ap, nperm);
    for (int i = 0; i < nperm && i < 8; i++) perm[i] = va_arg(ap, int);
    va_end(ap);
    int R = (int)a.rank;
    sisal_array_t res = sisal_array_alloc_sized(a.rank, a.type_id, a.size, sisal_esz(a));
    size_t esz = sisal_esz(a);
    if (nperm != R || R <= 1) {           /* nothing to do -> plain copy */
        for (int i = 0; i < 8; i++) { res.dims[i] = a.dims[i]; res.lower_bound[i] = a.lower_bound[i]; }
        memcpy(res.data, a.data, (size_t)a.size * esz);
        return res;
    }
    for (int k = 0; k < R; k++) { res.dims[k] = a.dims[perm[k]]; res.lower_bound[k] = a.lower_bound[perm[k]]; }
    int64_t sstr[8], rstr[8];
    sstr[R-1] = 1; rstr[R-1] = 1;
    for (int k = R - 2; k >= 0; k--) { sstr[k] = sstr[k+1] * a.dims[k+1]; rstr[k] = rstr[k+1] * res.dims[k+1]; }
    for (uint64_t idx = 0; idx < res.size; idx++) {
        int64_t rem = (int64_t)idx, slin = 0;
        for (int k = 0; k < R; k++) { int64_t c = rem / rstr[k]; rem %= rstr[k]; slin += c * sstr[perm[k]]; }
        memcpy((char*)res.data + (int64_t)idx * esz, (char*)a.data + slin * esz, esz);
    }
    return res;
}

/* PAD(a, lo, hi, fill): prepend `lo` and append `hi` copies of `fill`.
   result = [fill x lo] ++ a ++ [fill x hi].  `fill` arrives as a double and is
   converted to a's element type. */
inline sisal_array_t sisal_array_pad(sisal_array_t a, int32_t lo, int32_t hi, double fill) {
    if (lo < 0) lo = 0;
    if (hi < 0) hi = 0;
    int64_t N = (int64_t)a.size;
    int64_t total = (int64_t)lo + N + (int64_t)hi;
    sisal_array_t res = sisal_array_alloc_sized(a.rank, a.type_id, (uint64_t)total, sisal_esz(a));
    res.lower_bound[0] = 1;
    size_t esz = sisal_esz(a);
    for (int64_t i = 0; i < total; i++) {
        if (i < lo || i >= lo + N) sisal_elem_set_d(res, i, fill);
        else memcpy((char*)res.data + i * esz, (char*)a.data + (i - lo) * esz, esz);
    }
    return res;
}

/* SORT: return a sorted copy (ascending, element-size 4 bytes assumed) */
#include <algorithm>
inline sisal_array_t sisal_array_sort(sisal_array_t a) {
    sisal_array_t res = sisal_array_alloc_sized(a.rank, a.type_id, a.size, sisal_esz(a));
    for (int i = 0; i < 8; i++) res.lower_bound[i] = a.lower_bound[i];
    int32_t* src = (int32_t*)a.data; int32_t* dst = (int32_t*)res.data;
    for (uint64_t i = 0; i < a.size; i++) dst[i] = src[i];
    std::sort(dst, dst + a.size);
    return res;
}

/* COMPRESS: returns elements of `data` where `mask` (bool array) is true */
/* COMPRESS: keep the slabs of `data` whose mask flag is true.  A slab is one
   element for rank-1 data, one axis-0 row for rank>1 (the mask indexes axis
   0 either way).  Byte-true (esz), so it works for any element type. */
inline sisal_array_t sisal_array_compress(sisal_array_t mask, sisal_array_t data) {
    size_t esz = sisal_esz(data);
    uint64_t slab = (data.rank > 1 && data.dims[0] > 0)
                        ? data.size / (uint64_t)data.dims[0] : 1;
    uint64_t count = 0;
    bool* m = (bool*)mask.data;
    for (uint64_t i = 0; i < mask.size; i++) if (m[i]) count++;
    sisal_array_t res =
        sisal_array_alloc_sized(data.rank, data.type_id, count * slab, esz);
    res.lower_bound[0] = 1;
    res.dims[0] = (int64_t)count;
    for (int k = 1; k < (int)data.rank; k++) {
        res.dims[k] = data.dims[k];
        res.lower_bound[k] = data.lower_bound[k];
    }
    char* dst = (char*)res.data;
    const char* src = (const char*)data.data;
    for (uint64_t i = 0; i < mask.size; i++) {
        if (m[i]) {
            memcpy(dst, src + i * slab * esz, slab * esz);
            dst += slab * esz;
        }
    }
    return res;
}

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
        size_t esz = sisal_esz(a);
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
        
        size_t esz = sisal_esz(a);
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

/* DV_RANK_REDUCE: zero-copy view fixing dimension 0 at 1-based index idx.
   Returns a sisal_array_t with rank-1 less, data pointer advanced to the slice. */
inline sisal_array_t sisal_dv_rank_reduce(sisal_array_t a, int32_t idx) {
    sisal_array_t res = a;
    if (a.rank <= 0) return a;
    int32_t dim0 = (a.dims[0] > 0) ? (int32_t)a.dims[0] : (int32_t)a.size;
    uint64_t slice_size = (dim0 > 0) ? (a.size / (uint64_t)dim0) : 0;
    size_t esz = sisal_esz(a);
    res.data = (char*)a.data + (uint64_t)(idx - (int32_t)a.lower_bound[0]) * slice_size * esz;
    res.rank = a.rank - 1;
    res.size = (a.rank == 1) ? 1 : slice_size;
    for (int i = 0; i < 7; i++) { res.lower_bound[i] = a.lower_bound[i + 1]; res.dims[i] = a.dims[i + 1]; }
    res.lower_bound[7] = 1;
    res.dims[7] = 0;
    return res;
}

inline sisal_array_t sisal_array_get_row(sisal_array_t a, int32_t offset) {
    return sisal_dv_rank_reduce(a, (int32_t)a.lower_bound[0] + offset);
}

/* DV_RANK_REPLACE: functional copy of `a` with the rank-(N-1) slab at 1-based
   leading index `idx` overwritten by `slice`'s contiguous data. Mirrors
   sisal_dv_rank_reduce's offset math (slab byte offset = (idx-lb)*slice_size*esz). */
inline sisal_array_t sisal_dv_replace_slice(sisal_array_t a, int32_t idx, sisal_array_t slice) {
    sisal_array_t res = a;
    size_t esz = sisal_esz(a);
    size_t slot = (esz > 8 ? esz : 8);
    int32_t dim0 = (a.dims[0] > 0) ? (int32_t)a.dims[0] : (int32_t)a.size;
    uint64_t slice_size = (dim0 > 0) ? (a.size / (uint64_t)dim0) : 0;
    res.data = malloc(a.size * slot);
    memcpy(res.data, a.data, a.size * slot);
    
    int64_t row_off = (int64_t)(idx - (int32_t)a.lower_bound[0]) * slice_size;
    int64_t col_off = slice.lower_bound[0] - a.lower_bound[1];
    int64_t total_off = row_off + col_off;
    
    uint64_t copy_size = slice.size;
    if (col_off + (int64_t)copy_size > (int64_t)slice_size) {
        copy_size = slice_size - col_off;
    }
    
    memcpy((char*)res.data + total_off * esz, slice.data, copy_size * esz);
    return res;
}

// Math wrappers — generated code calls these by mangled name
static inline float  func__SABS__F__F(float x)    { return fabsf(x); }
static inline double func__SABS__D__D(double x)   { return fabs(x); }
static inline float  func__SSQRT__F__F(float x)   { return sqrtf(x); }
static inline double func__SSQRT__D__D(double x)  { return sqrt(x); }
static inline float  func__SSIN__F__F(float x)    { return sinf(x); }
static inline double func__SSIN__D__D(double x)   { return sin(x); }
static inline float  func__SCOS__F__F(float x)    { return cosf(x); }
static inline double func__SCOS__D__D(double x)   { return cos(x); }
static inline float  func__STAN__F__F(float x)    { return tanf(x); }
static inline double func__STAN__D__D(double x)   { return tan(x); }
static inline float  func__SASIN__F__F(float x)   { return asinf(x); }
static inline double func__SASIN__D__D(double x)  { return asin(x); }
static inline float  func__SACOS__F__F(float x)   { return acosf(x); }
static inline double func__SACOS__D__D(double x)  { return acos(x); }
static inline float  func__SATAN__F__F(float x)   { return atanf(x); }
static inline double func__SATAN__D__D(double x)  { return atan(x); }
static inline float  func__SSINH__F__F(float x)   { return sinhf(x); }
static inline double func__SSINH__D__D(double x)  { return sinh(x); }
static inline float  func__SCOSH__F__F(float x)   { return coshf(x); }
static inline double func__SCOSH__D__D(double x)  { return cosh(x); }
static inline float  func__STANH__F__F(float x)   { return tanhf(x); }
static inline double func__STANH__D__D(double x)  { return tanh(x); }
static inline float  func__SLOG__F__F(float x)    { return logf(x); }
static inline double func__SLOG__D__D(double x)   { return log(x); }
static inline float  func__SLOG10__F__F(float x)  { return log10f(x); }
static inline double func__SLOG10__D__D(double x) { return log(x); }
static inline float  func__SEXP__F__F(float x)    { return expf(x); }
static inline double func__SEXP__D__D(double x)   { return exp(x); }
static inline int32_t func__SFLOOR__F__I(float x)  { return (int32_t)floorf(x); }
static inline int64_t func__SFLOOR__D__L(double x) { return (int64_t)floor(x); }
static inline int32_t func__STRUNC__F__I(float x)  { return (int32_t)x; }
static inline int64_t func__STRUNC__D__L(double x) { return (int64_t)x; }
static inline int32_t func__SMOD__II__I(int32_t a, int32_t b) { return a % b; }
static inline int64_t func__SMOD__LL__L(int64_t a, int64_t b) { return a % b; }

/* integer abs */
static inline int32_t func__SABS__I__I(int32_t x) { return x < 0 ? -x : x; }
static inline int64_t func__SABS__L__L(int64_t x) { return x < 0 ? -x : x; }

/* max / min (a,b) -> larger/smaller */
static inline int32_t func__SMAX__II__I(int32_t a, int32_t b) { return a > b ? a : b; }
static inline int32_t func__SMIN__II__I(int32_t a, int32_t b) { return a < b ? a : b; }
static inline float   func__SMAX__FF__F(float a, float b)     { return a > b ? a : b; }
static inline float   func__SMIN__FF__F(float a, float b)     { return a < b ? a : b; }
static inline double  func__SMAX__DD__D(double a, double b)   { return a > b ? a : b; }
static inline double  func__SMIN__DD__D(double a, double b)   { return a < b ? a : b; }

/* exp(base, n): two-arg form is POWER base^n (Sisal `exp` = exponentiation). */
static inline float   func__SEXP__FI__F(float base, int32_t n)  { return powf(base, (float)n); }
static inline double  func__SEXP__DI__D(double base, int32_t n) { return pow(base, (double)n); }

/* etothe(x) = e^x (C exp).  One-arg Sisal `exp` is routed to ETOTHE by to_if1, so
   this is what one-arg exponential lowers to. */
static inline float   func__SETOTHE__F__F(float x)  { return expf(x); }
static inline double  func__SETOTHE__D__D(double x) { return exp(x); }

#endif
