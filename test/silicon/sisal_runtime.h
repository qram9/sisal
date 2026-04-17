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
    int64_t lower_bound;
    int32_t ref_count;
    int32_t type_id;
} sisal_array_t;

// Unified memory allocation (4KB aligned for Apple Silicon Zero-Copy)
inline sisal_array_t sisal_alloc_unified(uint64_t byte_size) {
    sisal_array_t arr = {0};
    void* ptr = NULL;
    if (posix_memalign(&ptr, 4096, byte_size) != 0) {
        return arr;
    }
    memset(ptr, 0, byte_size);
    arr.data = ptr;
    arr.size = 0;
    arr.lower_bound = 1; // Default Sisal
    arr.ref_count = 1;
    arr.type_id = 0;
    return arr;
}

inline sisal_array_t sisal_array_alloc_empty(int32_t dims, int32_t type_id, uint64_t size) {
    uint64_t element_size = (type_id == 1) ? 8 : 4; // 1: double, others: float/int
    sisal_array_t arr = sisal_alloc_unified(size * element_size);
    arr.size = size;
    arr.type_id = type_id;
    return arr;
}

inline sisal_array_t sisal_array_create(int64_t lb, int32_t type_id, int32_t n, ...) {
    sisal_array_t arr = sisal_array_alloc_empty(1, type_id, n);
    arr.lower_bound = lb;
    va_list args;
    va_start(args, n);
    if (type_id == 0 || type_id == 3) { // float/bool
        float* d = (float*)arr.data;
        for (int i = 0; i < n; ++i) d[i] = (float)va_arg(args, double);
    } else if (type_id == 1) { // double
        double* d = (double*)arr.data;
        for (int i = 0; i < n; ++i) d[i] = va_arg(args, double);
    } else { // int
        int32_t* d = (int32_t*)arr.data;
        for (int i = 0; i < n; ++i) d[i] = va_arg(args, int32_t);
    }
    va_end(args);
    return arr;
}

inline sisal_array_t sisal_array_fill(int64_t lb, int32_t size, double val) {
    sisal_array_t arr = sisal_array_alloc_empty(1, 0, size); // assume real
    arr.lower_bound = lb;
    float* d = (float*)arr.data;
    for (int i = 0; i < size; ++i) d[i] = (float)val;
    return arr;
}

inline float sisal_array_reduce_sum(sisal_array_t A) {
    float* a = (float*)A.data;
    float sum = 0;
    for(uint64_t i=0; i<A.size; ++i) sum += a[i];
    return sum;
}

inline float sisal_array_reduce_product(sisal_array_t A) {
    float* a = (float*)A.data;
    float prod = 1.0f;
    for(uint64_t i=0; i<A.size; ++i) prod *= a[i];
    return prod;
}

inline float sisal_array_reduce_least(sisal_array_t A) {
    float* a = (float*)A.data;
    if (A.size == 0) return 0;
    float res = a[0];
    for(uint64_t i=1; i<A.size; ++i) if (a[i] < res) res = a[i];
    return res;
}

inline float sisal_array_reduce_greatest(sisal_array_t A) {
    float* a = (float*)A.data;
    if (A.size == 0) return 0;
    float res = a[0];
    for(uint64_t i=1; i<A.size; ++i) if (a[i] > res) res = a[i];
    return res;
}

inline sisal_array_t sisal_array_concat(sisal_array_t A, sisal_array_t B) {
    sisal_array_t res = sisal_array_alloc_empty(1, A.type_id, A.size + B.size);
    res.lower_bound = A.lower_bound;
    uint64_t esize = (A.type_id == 1) ? 8 : 4;
    memcpy(res.data, A.data, A.size * esize);
    memcpy((char*)res.data + A.size * esize, B.data, B.size * esize);
    return res;
}

inline sisal_array_t sisal_array_addh(sisal_array_t A, double val) {
    sisal_array_t res = sisal_array_alloc_empty(1, A.type_id, A.size + 1);
    res.lower_bound = A.lower_bound;
    uint64_t esize = (A.type_id == 1) ? 8 : 4;
    memcpy(res.data, A.data, A.size * esize);
    if (A.type_id == 0) ((float*)res.data)[A.size] = (float)val;
    else if (A.type_id == 1) ((double*)res.data)[A.size] = val;
    else ((int32_t*)res.data)[A.size] = (int32_t)val;
    return res;
}

// Metal Placeholder for M4 Max
extern "C" inline void sisal_gpu_vector_add(sisal_array_t A, sisal_array_t B, sisal_array_t Out) {
    float* a = (float*)A.data;
    float* b = (float*)B.data;
    float* out = (float*)Out.data;
    uint64_t n = A.size;
    for(uint64_t i=0; i<n; ++i) {
        out[i] = a[i] + b[i];
    }
}

#endif
