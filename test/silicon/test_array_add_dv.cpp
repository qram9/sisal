#include <stdio.h>
#include <assert.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>
#include "sisal_runtime.h"

extern "C" sisal_array_t MAIN(sisal_array_t a, sisal_array_t b);

void test_array_add_dv() {
    printf("--- Testing Array Add DV ---\n");
    
    float val_a[] = {10.0, 20.0, 30.0};
    float val_b[] = {1.0, 2.0, 3.0};
    
    sisal_array_t a = sisal_array_create(0, 0, 3, 10.0, 20.0, 30.0);
    sisal_array_t b = sisal_array_create(0, 0, 3, 1.0, 2.0, 3.0);
    
    printf("Calling MAIN...\n");
    sisal_array_t res = MAIN(a, b);
    
    float* data = (float*)res.data;
    printf("Result: [%f, %f, %f]\n", data[0], data[1], data[2]);
    
    if (fabs(data[0] - 11.0f) < 1e-5 && fabs(data[1] - 22.0f) < 1e-5 && fabs(data[2] - 33.0f) < 1e-5) {
        printf("SUCCESS: array_add_dv worked.\n");
    } else {
        printf("FAILURE: array_add_dv failed.\n");
    }
}

int main() {
    test_array_add_dv();
    return 0;
}
