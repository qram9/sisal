// Auto-generated harness code using numpy_verify for TEST_RANK8_SLICES
#ifdef TEST_RANK8_SLICES
#include "numpy_verify.h"
#include <cmath>

struct FUNC_RANK8_results {
  sisal_array_t res_0;
  sisal_array_t res_1;
  double res_2;
  sisal_array_t res_3;
  sisal_array_t res_4;
  sisal_array_t res_5;
};

extern "C" struct FUNC_RANK8_results func_MAIN();
static void check(const char* name, bool cond);

void run_rank8_slices() {
    FUNC_RANK8_results r = func_MAIN();
    
    std::vector<int> shape(8, 2);
    std::vector<double> flat_data(256);
    for (int i = 0; i < 256; ++i) {
        int d1 = (i >> 7) & 1;
        int d2 = (i >> 6) & 1;
        int d3 = (i >> 5) & 1;
        int d4 = (i >> 4) & 1;
        int d5 = (i >> 3) & 1;
        int d6 = (i >> 2) & 1;
        int d7 = (i >> 1) & 1;
        int d8 = i & 1;
        flat_data[i] = d1*128.0 + d2*64.0 + d3*32.0 + d4*16.0 + d5*8.0 + d6*4.0 + d7*2.0 + (d8 + 1.0);
    }
    
    check("res_0 (A[1, .., 2, .., 1, .., 2, ..]) matches NumPy", verify_slice_numpy(shape, flat_data, "[0, :, 1, :, 0, :, 1, :]", r.res_0));
    check("res_1 (A[.., 2, 1, 2, 1, 2, 1, ..]) matches NumPy", verify_slice_numpy(shape, flat_data, "[:, 1, 0, 1, 0, 1, 0, :]", r.res_1));
    check("res_2 (A[1,1,1,1,1,1,1,1]) scalar matches", std::abs(r.res_2 - 1.0) < 1e-5);
    check("res_3 (A[.., .., .., .., .., .., .., ..]) matches NumPy", verify_slice_numpy(shape, flat_data, "[:, :, :, :, :, :, :, :]", r.res_3));
    check("res_4 (A[1, 2, 1, 2, .., .., .., ..]) matches NumPy", verify_slice_numpy(shape, flat_data, "[0, 1, 0, 1, :, :, :, :]", r.res_4));
    check("res_5 (A[.., .., .., .., 1, 2, 1, 2]) matches NumPy", verify_slice_numpy(shape, flat_data, "[:, :, :, :, 0, 1, 0, 1]", r.res_5));
}
#endif