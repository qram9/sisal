#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>
#include <sisal_runtime.h>

extern "C" sisal_array_t func_MAIN(sisal_array_t A, sisal_array_t B, int32_t N);

int g_pass = 0;
int g_fail = 0;

void check(const char* name, bool cond) {
    if (cond) {
        printf("  PASS  %s\n", name);
        g_pass++;
    } else {
        printf("  FAIL  %s\n", name);
        g_fail++;
    }
}

sisal_array_t make_matrix(int32_t* data, int32_t rows, int32_t cols) {
    sisal_array_t a = sisal_array_alloc_empty(2, 4, rows * cols);
    a.dims[0] = rows;
    a.dims[1] = cols;
    a.lower_bound[0] = 1;
    a.lower_bound[1] = 1;
    memcpy(a.data, data, rows * cols * sizeof(int32_t));
    return a;
}

int32_t get_elem(sisal_array_t a, int32_t i, int32_t j) {
    int32_t rows = a.dims[0];
    int32_t cols = a.dims[1];
    return ((int32_t*)a.data)[(i-1) * cols + (j-1)];
}

void test_matmul() {
    printf("=== Group: Matmul DV ===\n");
    
    // 2x2 Matrix A: [1 2; 3 4]
    int32_t dataA[] = {1, 2, 3, 4};
    sisal_array_t a = make_matrix(dataA, 2, 2);
    
    // 2x2 Matrix B: [5 6; 7 8]
    int32_t dataB[] = {5, 6, 7, 8};
    sisal_array_t b = make_matrix(dataB, 2, 2);
    
    // Result should be:
    // [ (1*5+2*7) (1*6+2*8) ] = [ 19 22 ]
    // [ (3*5+4*7) (3*6+4*8) ] = [ 43 50 ]
    
    sisal_array_t r = func_MAIN(a, b, 2);
    
    check("matmul rank", r.rank == 2);
    check("matmul dims[0]", r.dims[0] == 2);
    check("matmul dims[1]", r.dims[1] == 2);
    check("matmul[1,1]=19", get_elem(r, 1, 1) == 19);
    check("matmul[1,2]=22", get_elem(r, 1, 2) == 22);
    check("matmul[2,1]=43", get_elem(r, 2, 1) == 43);
    check("matmul[2,2]=50", get_elem(r, 2, 2) == 50);
}

int main(void) {
    printf("=== Matmul test harness ===\n");
    test_matmul();
    printf("\n--- Summary: %d passed, %d failed ---\n", g_pass, g_fail);
    return (g_fail > 0) ? 1 : 0;
}
