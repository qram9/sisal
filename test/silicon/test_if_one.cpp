#include <stdio.h>
#include <assert.h>
#include <stdint.h>
#include <stdbool.h>
#include "sisal_runtime.h"

// Generated from if_one.sis: FUNCTION MAIN(I, E: INTEGER RETURNS INTEGER)
//   if I < E then I else E end if
extern "C" int32_t MAIN(int32_t i, int32_t e);

// C reference: same logic
static int32_t ref_main(int32_t i, int32_t e) {
    return i < e ? i : e;
}

struct TestCase { int32_t i; int32_t e; };

int main() {
    printf("--- Testing if_one.sis: if I < E then I else E ---\n\n");

    TestCase cases[] = {
        {3, 7},    // I < E  → I = 3
        {7, 3},    // I > E  → E = 3
        {5, 5},    // I == E → E = 5
        {-4, 2},   // neg < pos → -4
        {0, -1},   // 0 > -1  → -1
    };

    int pass = 0, fail = 0;
    for (auto& tc : cases) {
        int32_t got = MAIN(tc.i, tc.e);
        int32_t want = ref_main(tc.i, tc.e);
        bool ok = (got == want);
        printf("MAIN(%3d, %3d) = %3d  (want %3d)  %s\n",
               tc.i, tc.e, got, want, ok ? "PASS" : "FAIL");
        ok ? pass++ : fail++;
    }

    printf("\n%d passed, %d failed\n", pass, fail);
    return fail == 0 ? 0 : 1;
}
