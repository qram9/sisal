#include <stdio.h>
#include <stdint.h>
#include "sisal_runtime.h"

extern "C" sisal_array_t PICK(int32_t mode, sisal_array_t a);

/* Reference implementations */
static sisal_array_t make_array(int32_t lo, int32_t n, int32_t *elems) {
    sisal_array_t a = sisal_array_alloc_empty(1, 2, (uint64_t)n);
    a.lower_bound = (int64_t)lo;
    int32_t *p = (int32_t *)a.data;
    for (int i = 0; i < n; i++) p[i] = elems[i];
    return a;
}

static int check(const char *label, int32_t mode,
                 int32_t lo, int32_t n, int32_t *elems,
                 int32_t *want) {
    sisal_array_t input = make_array(lo, n, elems);
    sisal_array_t got   = PICK(mode, input);

    if (got.size != (uint64_t)n) {
        printf("FAIL %s: size got=%llu want=%d\n", label,
               (unsigned long long)got.size, n);
        return 1;
    }
    int32_t *gp = (int32_t *)got.data;
    for (int i = 0; i < n; i++) {
        if (gp[i] != want[i]) {
            printf("FAIL %s: data[%d] got=%d want=%d\n", label, i, gp[i], want[i]);
            return 1;
        }
    }
    printf("PASS %s\n", label);
    return 0;
}

int main() {
    int fails = 0;

    int32_t a[] = {1, -2, 3, -4, 5};

    /* mode = 0: passthrough */
    int32_t want0[] = {1, -2, 3, -4, 5};
    fails += check("mode=0 passthrough", 0, 1, 5, a, want0);

    /* mode = 1: negate */
    int32_t want1[] = {-1, 2, -3, 4, -5};
    fails += check("mode=1 negate", 1, 1, 5, a, want1);

    /* mode = 2: double */
    int32_t want2[] = {2, -4, 6, -8, 10};
    fails += check("mode=2 double", 2, 1, 5, a, want2);

    /* mode = 99 (else): also double */
    int32_t want99[] = {2, -4, 6, -8, 10};
    fails += check("mode=99 also double", 99, 1, 5, a, want99);

    /* single-element */
    int32_t b[] = {7};
    int32_t wb0[] = {7};
    int32_t wb1[] = {-7};
    int32_t wb2[] = {14};
    fails += check("single mode=0", 0, 1, 1, b, wb0);
    fails += check("single mode=1", 1, 1, 1, b, wb1);
    fails += check("single mode=2", 2, 1, 1, b, wb2);

    /* all-zeros */
    int32_t z[] = {0, 0, 0};
    int32_t wz[] = {0, 0, 0};
    fails += check("zeros mode=0", 0, 1, 3, z, wz);
    fails += check("zeros mode=1", 1, 1, 3, z, wz);
    fails += check("zeros mode=2", 2, 1, 3, z, wz);

    if (fails == 0) printf("All tests passed.\n");
    return fails;
}
