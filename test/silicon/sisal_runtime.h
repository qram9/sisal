#ifndef SISAL_RUNTIME_H
#define SISAL_RUNTIME_H

#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
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
    uint64_t element_size = (type_id == 0) ? 4 : 8; // simplified
    sisal_array_t arr = sisal_alloc_unified(size * element_size);
    arr.size = size;
    arr.type_id = type_id;
    return arr;
}

inline sisal_array_t sisal_array_create(int64_t lb, int32_t type_id, int32_t n, ...) {
    sisal_array_t arr = sisal_array_alloc_empty(1, type_id, n);
    arr.lower_bound = lb;
    return arr;
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
