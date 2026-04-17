#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include "sisal_runtime.h"

// Generated SISAL function
extern "C" sisal_array_t DVFILL(int32_t lo, int32_t hi, int32_t v);

// C reference: fill array_dv[lo..hi] with v
static sisal_array_t ref_dvfill(int32_t lo, int32_t hi, int32_t v) {
    int32_t count = hi - lo + 1;
    if (count <= 0) count = 0;
    sisal_array_t a = sisal_array_alloc_empty(1, 2, (uint64_t)count);
    a.lower_bound = (int64_t)lo;
    int32_t *p = (int32_t *)a.data;
    for (int32_t i = 0; i < count; i++) p[i] = v;
    return a;
}

static int check(const char *label, int32_t lo, int32_t hi, int32_t v) {
    sisal_array_t got = DVFILL(lo, hi, v);
    sisal_array_t ref = ref_dvfill(lo, hi, v);

    int count = hi - lo + 1;
    if (count < 0) count = 0;

    if (got.size != ref.size) {
        printf("FAIL %s: size got=%llu ref=%llu\n", label,
               (unsigned long long)got.size, (unsigned long long)ref.size);
        return 1;
    }
    if (got.lower_bound != ref.lower_bound) {
        printf("FAIL %s: lower_bound got=%lld ref=%lld\n", label,
               (long long)got.lower_bound, (long long)ref.lower_bound);
        return 1;
    }
    int32_t *gp = (int32_t *)got.data;
    int32_t *rp = (int32_t *)ref.data;
    for (int i = 0; i < (int)got.size; i++) {
        if (gp[i] != rp[i]) {
            printf("FAIL %s: data[%d] got=%d ref=%d\n", label, i, gp[i], rp[i]);
            return 1;
        }
    }
    printf("PASS %s\n", label);
    return 0;
}

int main() {
    int fails = 0;
    fails += check("dvfill(1,5,7)",   1, 5, 7);
    fails += check("dvfill(0,0,42)",  0, 0, 42);
    fails += check("dvfill(3,7,99)",  3, 7, 99);
    fails += check("dvfill(-2,2,0)", -2, 2, 0);
    fails += check("dvfill(10,19,1)", 10, 19, 1);
    if (fails == 0) printf("All tests passed.\n");
    return fails;
}
