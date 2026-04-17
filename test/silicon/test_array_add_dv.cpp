#include <stdio.h>
#include <assert.h>
#include <stdint.h>
#include <stdbool.h>
#include <math.h>
#include "sisal_runtime.h"

// Signature for the generated Sisal function
extern "C" sisal_array_t MAIN(sisal_array_t a, sisal_array_t b);

void print_array(const char* name, sisal_array_t arr) {
    printf("%s: [", name);
    float* data = (float*)arr.data;
    for (uint64_t i = 0; i < arr.size; i++) {
        printf("%.1f%s", data[i], (i == arr.size - 1) ? "" : ", ");
    }
    printf("] (size=%llu, lb=%lld)\n", arr.size, arr.lower_bound);
}

int main() {
    printf("--- Testing array_add_dv.sis: Parallel Vector Addition ---\n\n");

    const int N = 10;
    
    // Create input arrays using our new RAII runtime
    sisal_array_t A = sisal_array_alloc_empty(1, 0, N);
    sisal_array_t B = sisal_array_alloc_empty(1, 0, N);
    A.lower_bound = 0;
    B.lower_bound = 0;

    float* dataA = (float*)A.data;
    float* dataB = (float*)B.data;

    for (int i = 0; i < N; i++) {
        dataA[i] = (float)(i + 1);    // 1, 2, 3...
        dataB[i] = (float)((i + 1) * 10); // 10, 20, 30...
    }

    print_array("Input A", A);
    print_array("Input B", B);

    // Call the generated Sisal logic
    printf("\nCalling Sisal MAIN...\n");
    sisal_array_t Sum = MAIN(A, B);

    print_array("Result Sum", Sum);

    // Verification
    int fails = 0;
    float* dataSum = (float*)Sum.data;
    for (int i = 0; i < N; i++) {
        float want = dataA[i] + dataB[i];
        if (fabs(dataSum[i] - want) > 1e-6) {
            printf("ERROR at index %d: got %.1f, want %.1f\n", i, dataSum[i], want);
            fails++;
        }
    }

    if (fails == 0) {
        printf("\nSUCCESS: Array addition verified.\n");
    } else {
        printf("\nFAILURE: %d mismatches found.\n", fails);
    }

    // Notice: We don't call free()! std::shared_ptr inside Sum, A, and B 
    // will automatically reclaim the memory when we exit main().

    return (fails == 0) ? 0 : 1;
}
