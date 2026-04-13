#include <stdio.h>
#include <assert.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>
#include "sisal_runtime.h"

// Signature for forall_negate.sis
extern "C" sisal_array_t MAIN_GPU(int32_t n);

void test_parallel_negate() {
    printf("--- Testing Parallel FORALL Negate (GCD) ---\n");
    int32_t test_n = 10;
    
    printf("Calling MAIN_GPU(%d)...\n", test_n);
    sisal_array_t result = MAIN_GPU(test_n);
    
    printf("Array (Negated): Size %llu, LB %d\n", result.size, result.lower_bound);
    
    float* data = (float*)result.data;
    printf("Contents (Parallel): ");
    for(int i=0; i<3; ++i) printf("%f ", data[i]);
    printf("\n");
    
    if (result.size > 0 && data[0] <= 0.0f) {
        printf("SUCCESS: Parallel FORALL executed on CPU Clusters.\n");
    } else {
        printf("FAILURE: Parallel execution failed or data incorrect.\n");
    }
}

int main() {
    printf("Sisal-to-Silicon Parallel Test on M4 Max\n");
    test_parallel_negate();
    return 0;
}
