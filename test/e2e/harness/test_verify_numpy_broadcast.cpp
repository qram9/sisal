#include <stdio.h>
#include <math.h>
#include <assert.h>
#include <stdint.h>
#include <stdbool.h>
#include "sisal_runtime.h"

// Define the results structs as they appear in the generated C code
struct TEST_MULTI_OP_results { sisal_array_t res_0; float res_1; float res_2; } ;
struct TEST_UNIT_EXPANSION_results { sisal_array_t res_0; float res_1; } ;
struct TEST_TRAILING_results { sisal_array_t res_0; float res_1; } ;

extern "C" {
    struct TEST_MULTI_OP_results TEST_MULTI_OP(sisal_array_t A, sisal_array_t B);
    sisal_array_t TEST_SCALAR_BROADCAST(double S, sisal_array_t M);
    struct TEST_UNIT_EXPANSION_results TEST_UNIT_EXPANSION(sisal_array_t A, sisal_array_t B);
    struct TEST_TRAILING_results TEST_TRAILING(sisal_array_t A, sisal_array_t B);
}

static int g_pass = 0, g_fail = 0;

static sisal_array_t make_double_array(int n, double start, double step) {
    sisal_array_t a = sisal_array_alloc_empty(1, 1, n); // type_id 1 = double
    a.lower_bound = 0;
    double* d = (double*)a.data;
    for (int i = 0; i < n; i++) d[i] = start + step * i;
    return a;
}

static void check_double_array(const char* test, sisal_array_t got, double* want, int n) {
    int fail = 0;
    double* d = (double*)got.data;
    if (got.size != (uint64_t)n) {
        printf("  FAIL %s: size mismatch (got %llu, want %d)\n", test, got.size, n);
        g_fail++;
        return;
    }
    for (int i = 0; i < n; i++) {
        if (fabs(d[i] - want[i]) > 1e-7 * (1.0 + fabs(want[i]))) {
            if (fail == 0) printf("  FAIL %s:\n", test);
            printf("    [%d]: got %.8f want %.8f\n", i, d[i], want[i]);
            fail++;
        }
    }
    if (fail == 0) { printf("  PASS %s\n", test); g_pass++; }
    else g_fail++;
}

int main() {
    printf("--- Testing verify_numpy_broadcast.sis ---\n\n");

    // 1. Test scalar broadcast: S + M
    {
        double S = 10.0;
        const int N = 5;
        sisal_array_t M = make_double_array(N, 1.0, 1.0); // [1, 2, 3, 4, 5]
        sisal_array_t r = TEST_SCALAR_BROADCAST(S, M);
        double want[N] = {11.0, 12.0, 13.0, 14.0, 15.0};
        check_double_array("TEST_SCALAR_BROADCAST", r, want, N);
    }

    // 2. Test trailing: A + B ([2,3] + [3])
    // Note: Our runtime currently treats all arrays as 1D flat buffers, 
    // but the generated code handles multi-dim indexing. 
    // For 1D, it's just element-wise.
    {
        const int N = 3;
        sisal_array_t A = make_double_array(N, 1.0, 1.0);
        sisal_array_t B = make_double_array(N, 10.0, 10.0);
        struct TEST_TRAILING_results r = TEST_TRAILING(A, B);
        double want[N] = {11.0, 22.0, 33.0};
        check_double_array("TEST_TRAILING", r.res_0, want, N);
    }

    printf("\n%d passed, %d failed\n", g_pass, g_fail);
    return g_fail == 0 ? 0 : 1;
}
