#include <stdio.h>
#include <assert.h>
#include <stdint.h>
#include <stdbool.h>
#include "sisal_runtime.h"

// Generated from if_elseif.sis:
// FUNCTION MAIN(I, E, F : INTEGER RETURNS INTEGER)
//   if I < E then I elseif E < F then E else F end if
extern "C" int32_t MAIN(int32_t i, int32_t e, int32_t f);

static int32_t ref_main(int32_t i, int32_t e, int32_t f) {
    if (i < e) return i;
    else if (e < f) return e;
    else return f;
}

struct TestCase { int32_t i; int32_t e; int32_t f; };

int main() {
    printf("--- Testing if_elseif.sis: if I<E then I elseif E<F then E else F ---\n\n");

    TestCase cases[] = {
        {1, 5, 10},   // I < E         -> I = 1
        {5, 1, 10},   // I >= E, E < F -> E = 1
        {5, 10, 1},   // I >= E, E >= F -> F = 1
        {3, 3, 3},    // all equal      -> F = 3
        {-1, 0, 1},   // -1 < 0        -> I = -1
        {0, -1, 1},   // 0 >= -1, -1 < 1 -> E = -1
        {0, 1, -1},   // 0 < 1         -> I = 0
        {10, 5, 7},   // 10 >= 5, 5 < 7 -> E = 5
        {10, 5, 3},   // 10 >= 5, 5 >= 3 -> F = 3
    };

    int pass = 0, fail = 0;
    for (auto& tc : cases) {
        int32_t got  = MAIN(tc.i, tc.e, tc.f);
        int32_t want = ref_main(tc.i, tc.e, tc.f);
        bool ok = (got == want);
        printf("MAIN(%3d, %3d, %3d) = %3d  (want %3d)  %s\n",
               tc.i, tc.e, tc.f, got, want, ok ? "PASS" : "FAIL");
        ok ? pass++ : fail++;
    }

    printf("\n%d passed, %d failed\n", pass, fail);
    return fail == 0 ? 0 : 1;
}
