#ifndef SISAL_RUNTIME_H
#define SISAL_RUNTIME_H

#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <math.h>
#include <stdarg.h>
#include <dispatch/dispatch.h>

typedef struct {
    void* data;
    uint64_t size;
    int32_t rank;
    int32_t type_id;
    int32_t ref_count;
    int64_t lower_bound;
    int64_t dims[8];
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

// Scalar-to-array hacks
template<> inline sisal_array_t sisal_cast_dispatch<sisal_array_t, float>(float s) { sisal_array_t a = { NULL, 0, 1, 0, 1, 0, {0} }; return a; }
template<> inline sisal_array_t sisal_cast_dispatch<sisal_array_t, double>(double s) { sisal_array_t a = { NULL, 0, 1, 0, 1, 0, {0} }; return a; }
template<> inline sisal_array_t sisal_cast_dispatch<sisal_array_t, int32_t>(int32_t s) { sisal_array_t a = { NULL, 0, 1, 0, 1, 0, {0} }; return a; }

#define SISAL_CAST(T, val) sisal_cast_dispatch<T>(val)

inline int32_t sisal_dv_dimension(int32_t dim, sisal_array_t a) {
  if (dim >= 0 && dim < a.rank) return (int32_t)a.dims[dim];
  return (int32_t)a.size;
}

inline int32_t sisal_dv_dimension(int32_t dim, int32_t val) { return val; }

inline int32_t sisal_dv_offset_at(sisal_array_t a, int32_t idx, sisal_array_t shape) {
    int32_t coords[8] = {0};
    int32_t remaining = idx;
    // Un-flatten result index (Row-major)
    for (int i = (int)shape.rank - 1; i >= 0; i--) {
        int32_t d = (int32_t)shape.dims[i];
        if (d <= 0) d = 1;
        coords[i] = remaining % d;
        remaining /= d;
    }
    
    int32_t linear_offset = 0;
    int32_t current_a_stride = 1;
    int rank_diff = (int)shape.rank - (int)a.rank;
    
    // Flatten for source array 'a' (Row-major)
    for (int i = (int)a.rank - 1; i >= 0; i--) {
        int res_axis = i + rank_diff;
        if (res_axis >= 0) {
            if (a.dims[i] > 1) {
                linear_offset += coords[res_axis] * current_a_stride;
            }
        }
        current_a_stride *= (int32_t)a.dims[i];
    }
    return linear_offset;
}

inline sisal_array_t sisal_array_alloc_empty(int32_t rank, int32_t type_id, uint64_t size) {
  sisal_array_t a;
  a.data = malloc(size * 8); 
  a.size = size;
  a.lower_bound = 1;
  a.type_id = type_id;
  a.ref_count = 1;
  a.rank = rank;
  for (int i=0; i<8; i++) a.dims[i] = 0;
  return a;
}

inline sisal_array_t sisal_array_setl(sisal_array_t a, int64_t lb) {
    sisal_array_t res = a;
    res.lower_bound = lb;
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
    sisal_array_t res = sisal_array_alloc_empty(a.rank, a.type_id, a.size);
    for (int i=0; i<a.rank; i++) res.dims[i] = a.dims[i];
    double* da = (double*)a.data;
    double* db = (double*)b.data;
    double* dr = (double*)res.data;
    for (uint64_t i=0; i<a.size; i++) dr[i] = da[i] + db[i];
    return res;
}

inline sisal_array_t sisal_array_sub(sisal_array_t a, sisal_array_t b) {
    sisal_array_t res = sisal_array_alloc_empty(a.rank, a.type_id, a.size);
    for (int i=0; i<a.rank; i++) res.dims[i] = a.dims[i];
    double* da = (double*)a.data;
    double* db = (double*)b.data;
    double* dr = (double*)res.data;
    for (uint64_t i=0; i<a.size; i++) dr[i] = da[i] - db[i];
    return res;
}

inline sisal_array_t sisal_array_mul(sisal_array_t a, sisal_array_t b) {
    sisal_array_t res = sisal_array_alloc_empty(a.rank, a.type_id, a.size);
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

// Stubs for remaining reducers
inline float sisal_array_reduce_float_product(sisal_array_t a) { return 1.0f; }
inline double sisal_array_reduce_double_sum(sisal_array_t a) { return (double)sisal_array_reduce_sum(a); }
inline int32_t sisal_array_reduce_int_sum(sisal_array_t a) { return (int32_t)sisal_array_reduce_sum(a); }
inline double sisal_array_reduce_double_product(sisal_array_t a) { return 1.0; }
inline float sisal_array_reduce_least(sisal_array_t a) { return 0.0f; }
inline double sisal_array_reduce_double_least(sisal_array_t a) { return 0.0; }
inline int32_t sisal_array_reduce_int_least(sisal_array_t a) { return 0; }
inline float sisal_array_reduce_greatest(sisal_array_t a) { return 0.0f; }
inline double sisal_array_reduce_double_greatest(sisal_array_t a) { return 0.0; }
inline int32_t sisal_array_reduce_int_greatest(sisal_array_t a) { return 0; }

#endif
