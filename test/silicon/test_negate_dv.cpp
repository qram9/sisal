#include <stdio.h>
#include <stdint.h>
#include "sisal_runtime.h"

extern "C" sisal_array_t NEGATE(sisal_array_t a);

/* Reference: negate all elements of a 1-based integer array_dv */
static sisal_array_t ref_negate(int32_t lo, int32_t n, int32_t *elems) {
    sisal_array_t r = sisal_array_alloc_empty(1, 2, (uint64_t)n);
    r.lower_bound = (int64_t)lo;
    int32_t *p = (int32_t *)r.data;
    for (int i = 0; i < n; i++) p[i] = -elems[i];
    return r;
}

static sisal_array_t make_array(int32_t lo, int32_t n, int32_t *elems) {
    sisal_array_t a = sisal_array_alloc_empty(1, 2, (uint64_t)n);
    a.lower_bound = (int64_t)lo;
    int32_t *p = (int32_t *)a.data;
    for (int i = 0; i < n; i++) p[i] = elems[i];
    return a;
}

static int check(const char *label, int32_t lo, int32_t n, int32_t *elems) {
    sisal_array_t input = make_array(lo, n, elems);
    sisal_array_t got   = NEGATE(input);
    sisal_array_t ref   = ref_negate(lo, n, elems);

    if (got.size != (uint64_t)n) {
        printf("FAIL %s: size got=%llu want=%d\n", label,
               (unsigned long long)got.size, n);
        return 1;
    }
    if (got.lower_bound != ref.lower_bound) {
        printf("FAIL %s: lower_bound got=%lld want=%lld\n", label,
               (long long)got.lower_bound, (long long)ref.lower_bound);
        return 1;
    }
    int32_t *gp = (int32_t *)got.data;
    int32_t *rp = (int32_t *)ref.data;
    for (int i = 0; i < n; i++) {
        if (gp[i] != rp[i]) {
            printf("FAIL %s: data[%d] got=%d want=%d\n", label, i, gp[i], rp[i]);
            return 1;
        }
    }
    printf("PASS %s\n", label);
    return 0;
}

int main() {
    int fails = 0;

    int32_t a1[] = {1, 2, 3, 4, 5};
    fails += check("negate [1..5] = {1,2,3,4,5}", 1, 5, a1);

    int32_t a2[] = {-3, 0, 7};
    fails += check("negate [1..3] = {-3,0,7}", 1, 3, a2);

    int32_t a3[] = {42};
    fails += check("negate single element", 1, 1, a3);

    int32_t a4[] = {0, 0, 0};
    fails += check("negate all-zeros", 1, 3, a4);

    int32_t a5[] = {100, -200, 300, -400};
    fails += check("negate mixed signs", 1, 4, a5);

    if (fails == 0) printf("All tests passed.\n");
    return fails;
}
