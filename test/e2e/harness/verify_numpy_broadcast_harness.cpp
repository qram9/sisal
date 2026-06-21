#include <stdio.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>
#include <vector>
#include <iostream>
#include "sisal_runtime.h"

// Generated code's result structs
struct TEST_MULTI_OP_results {
  sisal_array_t res_0;
  float res_1;
  float res_2;
};
struct TEST_UNIT_EXPANSION_results {
  sisal_array_t res_0;
  float res_1;
};
struct TEST_TRAILING_results {
  sisal_array_t res_0;
  float res_1;
};

extern "C" {
    struct TEST_MULTI_OP_results TEST_MULTI_OP(sisal_array_t A, sisal_array_t B);
    sisal_array_t TEST_SCALAR_BROADCAST(double S, sisal_array_t M);
    struct TEST_UNIT_EXPANSION_results TEST_UNIT_EXPANSION(sisal_array_t A, sisal_array_t B);
    struct TEST_TRAILING_results TEST_TRAILING(sisal_array_t A, sisal_array_t B);
}

static int g_pass = 0, g_fail = 0;

// REFERENCE IMPLEMENTATIONS
// These implement the logic of verify_numpy_broadcast.sis manually.

// 1. test_trailing reference: [2, 3] + [3] -> [2, 3]
std::vector<double> test_trailing_ref(const std::vector<double>& A, const std::vector<double>& B) {
    std::vector<double> res(6);
    for (int i = 0; i < 2; i++) {
        for (int j = 0; j < 3; j++) {
            res[i * 3 + j] = A[i * 3 + j] + B[j];
        }
    }
    return res;
}

// 2. test_unit_expansion reference: [2, 1] + [1, 3] -> [2, 3]
std::vector<double> test_unit_expansion_ref(const std::vector<double>& A, const std::vector<double>& B) {
    std::vector<double> res(6);
    for (int i = 0; i < 2; i++) {
        for (int j = 0; j < 3; j++) {
            res[i * 3 + j] = A[i] + B[j]; // A[i][0] + B[0][j]
        }
    }
    return res;
}

// 3. test_scalar_broadcast reference: S + [2, 2] -> [2, 2]
std::vector<double> test_scalar_broadcast_ref(double S, const std::vector<double>& M) {
    std::vector<double> res(4);
    for (int i = 0; i < 4; i++) res[i] = S + M[i];
    return res;
}

// 4. test_multi_op reference: (A + B) * 2.0 - A
std::vector<double> test_multi_op_ref(const std::vector<double>& A, const std::vector<double>& B) {
    std::vector<double> res(4);
    for (int i = 0; i < 4; i++) res[i] = (A[i] + B[i]) * 2.0 - A[i];
    return res;
}

// Helper to create a fake dope vector with rank and shape
static sisal_array_t make_dv(int rank, std::vector<int64_t> shape, const std::vector<double>& data) {
    uint64_t total_size = 1;
    for (auto s : shape) total_size *= s;
    
    sisal_array_t a = sisal_array_alloc_empty(1, 1, total_size);
    a.rank = rank;
    a.size = total_size;
    a.lower_bound = 1;
    for (int i = 0; i < rank; i++) a.dims[i] = shape[i];
    
    double* d = (double*)a.data;
    for (uint64_t i = 0; i < total_size; i++) d[i] = data[i];
    return a;
}

static void check_array(const char* test, sisal_array_t got, const std::vector<double>& want) {
    if (got.size != want.size()) {
        printf("  FAIL %s: size mismatch (got %llu, want %zu)\n", test, got.size, want.size());
        g_fail++; return;
    }
    double* d = (double*)got.data;
    bool match = true;
    for (size_t i = 0; i < want.size(); i++) {
        if (fabs(d[i] - want[i]) > 1e-7) {
            if (match) printf("  FAIL %s:\n", test);
            printf("    [%zu] got %.4f want %.4f\n", i, d[i], want[i]);
            match = false;
        }
    }
    if (match) {
        printf("  PASS %s\n", test);
        g_pass++;
    } else {
        g_fail++;
    }
}

int main() {
    printf("--- verify_numpy_broadcast.sis: Generated vs Reference ---\n\n");

    // 1. TEST_TRAILING
    {
        std::vector<double> A_data = {1.0, 2.0, 3.0, 4.0, 5.0, 6.0};
        std::vector<double> B_data = {10.0, 20.0, 30.0};
        sisal_array_t A = make_dv(2, {2, 3}, A_data);
        sisal_array_t B = make_dv(1, {3}, B_data);
        
        struct TEST_TRAILING_results r = TEST_TRAILING(A, B);
        std::vector<double> want = test_trailing_ref(A_data, B_data);
        check_array("TEST_TRAILING", r.res_0, want);
    }

    // 2. TEST_UNIT_EXPANSION
    {
        std::vector<double> A_data = {1.0, 2.0};
        std::vector<double> B_data = {10.0, 20.0, 30.0};
        sisal_array_t A = make_dv(2, {2, 1}, A_data);
        sisal_array_t B = make_dv(2, {1, 3}, B_data);
        
        struct TEST_UNIT_EXPANSION_results r = TEST_UNIT_EXPANSION(A, B);
        std::vector<double> want = test_unit_expansion_ref(A_data, B_data);
        check_array("TEST_UNIT_EXPANSION", r.res_0, want);
    }

    // 3. TEST_SCALAR_BROADCAST
    {
        double S = 100.0;
        std::vector<double> M_data = {1.0, 2.0, 3.0, 4.0};
        sisal_array_t M = make_dv(2, {2, 2}, M_data);
        
        sisal_array_t r = TEST_SCALAR_BROADCAST(S, M);
        std::vector<double> want = test_scalar_broadcast_ref(S, M_data);
        check_array("TEST_SCALAR_BROADCAST", r, want);
    }

    // 4. TEST_MULTI_OP
    {
        std::vector<double> A_data = {1.0, 2.0, 3.0, 4.0};
        std::vector<double> B_data = {10.0, 20.0, 30.0, 40.0};
        sisal_array_t A = make_dv(2, {2, 2}, A_data);
        sisal_array_t B = make_dv(2, {2, 2}, B_data);
        
        struct TEST_MULTI_OP_results r = TEST_MULTI_OP(A, B);
        std::vector<double> want = test_multi_op_ref(A_data, B_data);
        check_array("TEST_MULTI_OP", r.res_0, want);
    }

    printf("\nTests passed: %d, Tests failed: %d\n", g_pass, g_fail);
    return g_fail == 0 ? 0 : 1;
}
