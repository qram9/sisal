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

// Scalar-to-array hacks — preserve value in .size and .dims[0] so the roundtrip
// SISAL_CAST(int32_t, SISAL_CAST(sisal_array_t, x)) == x
template<> inline sisal_array_t sisal_cast_dispatch<sisal_array_t, float>(float s) {
    sisal_array_t a = { NULL, (uint64_t)(s > 0 ? (uint64_t)s : 0), 1, 0, 1, 0, {0} };
    a.dims[0] = (int64_t)(s > 0 ? (int64_t)s : 0); return a;
}
template<> inline sisal_array_t sisal_cast_dispatch<sisal_array_t, double>(double s) {
    sisal_array_t a = { NULL, (uint64_t)(s > 0 ? (uint64_t)s : 0), 1, 0, 1, 0, {0} };
    a.dims[0] = (int64_t)(s > 0 ? (int64_t)s : 0); return a;
}
template<> inline sisal_array_t sisal_cast_dispatch<sisal_array_t, int32_t>(int32_t s) {
    sisal_array_t a = { NULL, (uint64_t)(s > 0 ? s : 0), 1, 0, 1, 0, {0} };
    a.dims[0] = (int64_t)s; return a;
}

#define SISAL_CAST(T, val) sisal_cast_dispatch<T>(val)

inline int32_t sisal_dv_dimension(int32_t dim, sisal_array_t a) {
  if (dim >= 0 && dim < a.rank) return (int32_t)a.dims[dim];
  return (int32_t)a.size;
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

static inline size_t sisal_elem_size(int32_t type_id) {
    switch (type_id) {
        case 1: case 5: case 6: return 4;
        case 7: return 8;
        default: return sizeof(sisal_array_t);
    }
}

inline sisal_array_t sisal_array_alloc_empty(int32_t rank, int32_t type_id, uint64_t size) {
  sisal_array_t a;
  size_t esz = sisal_elem_size(type_id);
  a.data = malloc(size * (esz > 8 ? esz : 8));
  a.size = size;
  a.lower_bound = 1;
  a.type_id = type_id;
  a.ref_count = 1;
  a.rank = rank;
  for (int i=0; i<8; i++) a.dims[i] = 0;
  if (rank == 1) a.dims[0] = (int64_t)size;
  return a;
}

inline sisal_array_t sisal_array_replace_i32(sisal_array_t a, int64_t idx, int32_t val) {
    sisal_array_t res = a;
    res.data = malloc(a.size * 8);
    memcpy(res.data, a.data, a.size * 8);
    ((int32_t*)res.data)[idx - a.lower_bound] = val;
    return res;
}
inline sisal_array_t sisal_array_replace_f32(sisal_array_t a, int64_t idx, float val) {
    sisal_array_t res = a;
    res.data = malloc(a.size * 8);
    memcpy(res.data, a.data, a.size * 8);
    ((float*)res.data)[idx - a.lower_bound] = val;
    return res;
}
inline sisal_array_t sisal_array_replace_f64(sisal_array_t a, int64_t idx, double val) {
    sisal_array_t res = a;
    res.data = malloc(a.size * 8);
    memcpy(res.data, a.data, a.size * 8);
    ((double*)res.data)[idx - a.lower_bound] = val;
    return res;
}
inline sisal_array_t sisal_array_replace_arr(sisal_array_t a, int64_t idx, sisal_array_t val) {
    sisal_array_t res = a;
    size_t esz = sizeof(sisal_array_t);
    res.data = malloc(a.size * esz);
    memcpy(res.data, a.data, a.size * esz);
    ((sisal_array_t*)res.data)[idx - a.lower_bound] = val;
    return res;
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

/* INNERPRODUCT: rank-polymorphic (APL/numpy semantics, row-major).
   rank-1 x rank-1 -> rank-1 array of size 1 (scalar wrapped)
   rank-2 x rank-2 -> rank-2 array (matmul)
   Caller extracts scalar via _f32/_f64/_i32 wrappers when needed. */
inline sisal_array_t sisal_array_innerproduct(sisal_array_t a, sisal_array_t b) {
    if (a.rank == 1 && b.rank == 1) {
        /* dot product: sum(a[i]*b[i]) packed into a single-element array */
        sisal_array_t r = sisal_array_alloc_empty(1, a.type_id, 1);
        r.dims[0] = 1;
        if (a.type_id == 4) { /* double */
            double s = 0.0; double* da=(double*)a.data; double* db=(double*)b.data;
            for (uint64_t i=0;i<a.size;i++) s+=da[i]*db[i];
            ((double*)r.data)[0] = s;
        } else if (a.type_id == 6) { /* int32 */
            int32_t s = 0; int32_t* da=(int32_t*)a.data; int32_t* db=(int32_t*)b.data;
            for (uint64_t i=0;i<a.size;i++) s+=da[i]*db[i];
            ((int32_t*)r.data)[0] = s;
        } else { /* float (type_id==8) and fallback */
            float s = 0.0f; float* da=(float*)a.data; float* db=(float*)b.data;
            for (uint64_t i=0;i<a.size;i++) s+=da[i]*db[i];
            ((float*)r.data)[0] = s;
        }
        return r;
    } else if (a.rank == 2 && b.rank == 2) {
        /* matmul: C[i,j] = sum_k A[i,k]*B[k,j], row-major */
        int64_t M=a.dims[0], K=a.dims[1], N=b.dims[1];
        sisal_array_t r = sisal_array_alloc_empty(2, a.type_id, (uint64_t)(M*N));
        r.dims[0]=M; r.dims[1]=N;
        if (a.type_id == 4) {
            double* da=(double*)a.data; double* db=(double*)b.data; double* dr=(double*)r.data;
            for(int64_t i=0;i<M;i++) for(int64_t j=0;j<N;j++) {
                double s=0.0; for(int64_t k=0;k<K;k++) s+=da[i*K+k]*db[k*N+j];
                dr[i*N+j]=s; }
        } else if (a.type_id == 6) {
            int32_t* da=(int32_t*)a.data; int32_t* db=(int32_t*)b.data; int32_t* dr=(int32_t*)r.data;
            for(int64_t i=0;i<M;i++) for(int64_t j=0;j<N;j++) {
                int32_t s=0; for(int64_t k=0;k<K;k++) s+=da[i*K+k]*db[k*N+j];
                dr[i*N+j]=s; }
        } else {
            float* da=(float*)a.data; float* db=(float*)b.data; float* dr=(float*)r.data;
            for(int64_t i=0;i<M;i++) for(int64_t j=0;j<N;j++) {
                float s=0.0f; for(int64_t k=0;k<K;k++) s+=da[i*K+k]*db[k*N+j];
                dr[i*N+j]=s; }
        }
        return r;
    } else {
        /* unsupported rank combination: return empty */
        return sisal_array_alloc_empty(1, a.type_id, 0);
    }
}
/* Scalar-extracting wrappers: extract result[0] and free the temp array */
inline float   sisal_array_innerproduct_f32(sisal_array_t a, sisal_array_t b) {
    sisal_array_t r = sisal_array_innerproduct(a, b);
    float v = r.data ? ((float*)r.data)[0] : 0.0f;
    if (r.data) free(r.data); return v;
}
inline double  sisal_array_innerproduct_f64(sisal_array_t a, sisal_array_t b) {
    sisal_array_t r = sisal_array_innerproduct(a, b);
    double v = r.data ? ((double*)r.data)[0] : 0.0;
    if (r.data) free(r.data); return v;
}
inline int32_t sisal_array_innerproduct_i32(sisal_array_t a, sisal_array_t b) {
    sisal_array_t r = sisal_array_innerproduct(a, b);
    int32_t v = r.data ? ((int32_t*)r.data)[0] : 0;
    if (r.data) free(r.data); return v;
}

/* REVERSE: return a copy with elements in reverse order */
inline sisal_array_t sisal_array_reverse(sisal_array_t a) {
    sisal_array_t res = sisal_array_alloc_empty(a.rank, a.type_id, a.size);
    res.lower_bound = a.lower_bound;
    int32_t* src = (int32_t*)a.data; int32_t* dst = (int32_t*)res.data;
    for (uint64_t i = 0; i < a.size; i++) dst[i] = src[a.size - 1 - i];
    return res;
}

/* SORT: return a sorted copy (ascending, element-size 4 bytes assumed) */
#include <algorithm>
inline sisal_array_t sisal_array_sort(sisal_array_t a) {
    sisal_array_t res = sisal_array_alloc_empty(a.rank, a.type_id, a.size);
    res.lower_bound = a.lower_bound;
    int32_t* src = (int32_t*)a.data; int32_t* dst = (int32_t*)res.data;
    for (uint64_t i = 0; i < a.size; i++) dst[i] = src[i];
    std::sort(dst, dst + a.size);
    return res;
}

/* COMPRESS: returns elements of `data` where `mask` (bool array) is true */
inline sisal_array_t sisal_array_compress(sisal_array_t mask, sisal_array_t data) {
    uint64_t count = 0;
    bool* m = (bool*)mask.data;
    for (uint64_t i = 0; i < mask.size; i++) if (m[i]) count++;
    sisal_array_t res = sisal_array_alloc_empty(data.rank, data.type_id, count);
    res.lower_bound = 1;
    uint64_t out = 0;
    for (uint64_t i = 0; i < mask.size; i++) {
        if (m[i]) { ((float*)res.data)[out++] = ((float*)data.data)[i]; }
    }
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

#endif
