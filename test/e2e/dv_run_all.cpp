// dv_run_all.cpp — Test harness for all 9 dv_*.sis generated C++ files.
//
// Compile with a -DTEST_XXX flag to select one group, e.g.:
//   clang++ -std=c++17 -I<runtime> -DTEST_ABS_DEMO dv_run_all.cpp dv_abs_demo.cpp -o test_abs_demo
//
// See run_dv_tests.sh for the full build + run script.

#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>
#include <cmath>
#include <sisal_runtime.h>

// ============================================================
// External declarations — one block per generated .cpp file.
// Only the block matching the active TEST_XXX guard is linked.
// ============================================================

#ifdef TEST_ABS_DEMO
extern "C" sisal_array_t func_DV_ABS_DEMO(sisal_array_t V);
#endif

#ifdef TEST_AGREEMENT
extern "C" sisal_array_t func_MAIN(sisal_array_t A, sisal_array_t B);  // dv_agreement
#endif

#ifdef TEST_LIFTED_ARITH
extern "C" sisal_array_t func_MAIN(sisal_array_t A, sisal_array_t B);  // dv_lifted_arith
#endif

#ifdef TEST_SHL
extern "C" sisal_array_t func_DV_SHL_SCALAR(sisal_array_t V, int32_t N);
#endif

#ifdef TEST_TEST_SUBSET
extern "C" sisal_array_t func_DV_ABS_REAL(sisal_array_t V);
extern "C" sisal_array_t func_DV_NEGATE_REAL(sisal_array_t V);
extern "C" sisal_array_t func_DV_SQRT_REAL(sisal_array_t V);
extern "C" sisal_array_t func_DV_SIN_REAL(sisal_array_t V);
extern "C" sisal_array_t func_DV_COS_REAL(sisal_array_t V);
extern "C" sisal_array_t func_DV_ADD_DV(sisal_array_t A, sisal_array_t B);
extern "C" sisal_array_t func_DV_MUL_SCALAR(sisal_array_t V, float S);
extern "C" sisal_array_t func_DV_ADD_SCALAR(sisal_array_t V, float S);
extern "C" sisal_array_t func_DV_GT_SCALAR(sisal_array_t V, float S);
extern "C" float         func_DV_SUM_REAL(sisal_array_t V);
#endif

#ifdef TEST_INTRINSICS
extern "C" sisal_array_t func_DV_ABS_REAL(sisal_array_t V);
extern "C" sisal_array_t func_DV_SQRT_REAL(sisal_array_t V);
extern "C" sisal_array_t func_DV_SIN_REAL(sisal_array_t V);
extern "C" sisal_array_t func_DV_COS_REAL(sisal_array_t V);
extern "C" sisal_array_t func_DV_LOG_REAL(sisal_array_t V);
extern "C" sisal_array_t func_DV_FLOOR_REAL(sisal_array_t V);
extern "C" sisal_array_t func_DV_TRUNC_REAL(sisal_array_t V);
extern "C" sisal_array_t func_DV_ABS_DOUBLE(sisal_array_t V);
extern "C" sisal_array_t func_DV_SQRT_DOUBLE(sisal_array_t V);
extern "C" sisal_array_t func_DV_ADD_DV(sisal_array_t A, sisal_array_t B);
extern "C" sisal_array_t func_DV_SUB_DV(sisal_array_t A, sisal_array_t B);
extern "C" sisal_array_t func_DV_MUL_DV(sisal_array_t A, sisal_array_t B);
extern "C" sisal_array_t func_DV_DIV_DV(sisal_array_t A, sisal_array_t B);
extern "C" sisal_array_t func_SCALAR_ADD_DV(float S, sisal_array_t V);
extern "C" sisal_array_t func_DV_GT_SCALAR(sisal_array_t V, float S);
extern "C" sisal_array_t func_DV_EQ_DV(sisal_array_t A, sisal_array_t B);
extern "C" sisal_array_t func_DV_NE_DV(sisal_array_t A, sisal_array_t B);
extern "C" sisal_array_t func_DV_AND_DV(sisal_array_t A, sisal_array_t B);
extern "C" sisal_array_t func_DV_OR_DV(sisal_array_t A, sisal_array_t B);
extern "C" sisal_array_t func_DV_SHL_SCALAR(sisal_array_t V, int32_t N);
extern "C" sisal_array_t func_DV_SHR_SCALAR(sisal_array_t V, int32_t N);
extern "C" float         func_DV_SUM_REAL(sisal_array_t V);
extern "C" float         func_DV_PRODUCT_REAL(sisal_array_t V);
extern "C" float         func_DV_LEAST_REAL(sisal_array_t V);
extern "C" float         func_DV_GREATEST_REAL(sisal_array_t V);
extern "C" int32_t       func_DV_SUM_INT(sisal_array_t V);
extern "C" int32_t       func_DV_PRODUCT_INT(sisal_array_t V);
extern "C" int32_t       func_DV_LEAST_INT(sisal_array_t V);
extern "C" int32_t       func_DV_GREATEST_INT(sisal_array_t V);
#endif

#ifdef TEST_BROADCAST_COMPLEX
extern "C" sisal_array_t func_BROADCAST_VEC_MAT(sisal_array_t V, sisal_array_t M);
extern "C" sisal_array_t func_BROADCAST_UNIT(sisal_array_t A, sisal_array_t B);
extern "C" sisal_array_t func_BROADCAST_SCALAR(double S, sisal_array_t M);
#endif

#ifdef TEST_COMPRESS
extern "C" sisal_array_t func_COMPRESS_MONOLITHIC(sisal_array_t MASK, sisal_array_t A);
extern "C" sisal_array_t func_COMPRESS_DV_INPUT(int32_t N);
extern "C" int32_t       func_COMPRESS_CHAIN(sisal_array_t MASK, sisal_array_t A);
#endif

#ifdef TEST_BROADCAST_NUMPY
extern "C" sisal_array_t func_MAIN(sisal_array_t A, sisal_array_t B);  // dv_broadcast_numpy
#endif

#ifdef TEST_FORALL_CPU
extern "C" sisal_array_t func_MAIN_CPU(int32_t N);
#endif

#ifdef TEST_NEGATE_DV
extern "C" sisal_array_t func_NEGATE(sisal_array_t A);
#endif

#ifdef TEST_FORALL_BASIC_DV
extern "C" sisal_array_t func_FORALL_BASIC(int32_t N);
#endif

#ifdef TEST_FORALL_REDUCE_DV
extern "C" int32_t func_SUM_TO_N(int32_t N);
extern "C" int32_t func_PRODUCT_TO_N(int32_t N);
extern "C" int32_t func_MIN_TO_N(int32_t N);
extern "C" int32_t func_MAX_TO_N(int32_t N);
#endif

#ifdef TEST_FOR_INITIAL
extern "C" int32_t func_FI_SUM(int32_t N);
extern "C" int32_t func_FI_PRODUCT(int32_t N);
extern "C" int32_t func_FI_FINAL_I(int32_t N);
extern "C" int32_t func_FI_PASSTHRU(int32_t N);
extern "C" int32_t func_FI_SWAP(int32_t N);
extern "C" int32_t func_FI_FIB(int32_t N);
extern "C" int32_t func_FI_FIB_A(int32_t N);
extern "C" sisal_array_t func_FI_PARAM_IDENTITY(int32_t N, sisal_array_t Ain);
extern "C" sisal_array_t func_FI_PARAM_BUMP(int32_t N, sisal_array_t Ain);
#endif

#ifdef TEST_INNERPRODUCT_DV
extern "C" sisal_array_t func_IP_F32(sisal_array_t A, sisal_array_t B);
extern "C" sisal_array_t func_IP_I32(sisal_array_t A, sisal_array_t B);
#endif

#ifdef TEST_BULK_BASIC
extern "C" sisal_array_t func_T_ARR_ADD(sisal_array_t A, sisal_array_t B);
extern "C" sisal_array_t func_T_ARR_SUB(sisal_array_t A, sisal_array_t B);
extern "C" sisal_array_t func_T_ARR_MUL(sisal_array_t A, sisal_array_t B);
extern "C" sisal_array_t func_T_ARR_NEG(sisal_array_t A);
extern "C" sisal_array_t func_T_ARR_EQ (sisal_array_t A, sisal_array_t B);
extern "C" sisal_array_t func_T_ARR_LT (sisal_array_t A, sisal_array_t B);
extern "C" sisal_array_t func_T_ARR_ADD_SCALAR(sisal_array_t A, int32_t N);
extern "C" sisal_array_t func_T_ARR_MUL_SCALAR(sisal_array_t A, int32_t N);
extern "C" int32_t       func_T_SUM    (sisal_array_t A);
extern "C" int32_t       func_T_PRODUCT(sisal_array_t A);
extern "C" int32_t       func_T_LEAST  (sisal_array_t A);
extern "C" int32_t       func_T_GREATEST(sisal_array_t A);
extern "C" sisal_array_t func_T_COMPRESS(sisal_array_t MASK, sisal_array_t A);
extern "C" sisal_array_t func_T_SORT   (sisal_array_t A);
extern "C" sisal_array_t func_T_REVERSE(sisal_array_t A);
#endif

// ============================================================
// Pass/fail accounting
// ============================================================

static int g_pass = 0;
static int g_fail = 0;

static void check(const char* name, bool cond) {
    if (cond) {
        printf("  PASS  %s\n", name);
        g_pass++;
    } else {
        printf("  FAIL  %s\n", name);
        g_fail++;
    }
}

// ============================================================
// Approximate equality
// ============================================================

static inline bool near_f(float a, float b) { return fabsf(a - b) < 1e-4f; }
static inline bool near_d(double a, double b) { return fabs(a - b) < 1e-9; }

// ============================================================
// Array constructors
//
// sisal_array_alloc_empty sets lower_bound = 1.
// The generated code iterates indices starting at lower_bound and
// accesses data[idx - lower_bound], so lb=1 is required for input
// arrays too.  We replicate that here.
// ============================================================

static sisal_array_t make_float_arr(const float* data, int n) {
    sisal_array_t a = sisal_array_alloc_empty(1, 8, (uint64_t)n);
    // lower_bound already set to 1 by alloc_empty
    memcpy(a.data, data, (size_t)n * sizeof(float));
    return a;
}

static sisal_array_t make_double_arr(const double* data, int n) {
    sisal_array_t a = sisal_array_alloc_empty(1, 4, (uint64_t)n);
    memcpy(a.data, data, (size_t)n * sizeof(double));
    return a;
}

static sisal_array_t make_int_arr(const int32_t* data, int n) {
    sisal_array_t a = sisal_array_alloc_empty(1, 6, (uint64_t)n);
    memcpy(a.data, data, (size_t)n * sizeof(int32_t));
    return a;
}

static sisal_array_t make_bool_arr(const bool* data, int n) {
    sisal_array_t a = sisal_array_alloc_empty(1, 1, (uint64_t)n);
    memcpy(a.data, data, (size_t)n * sizeof(bool));
    return a;
}

// 2D row-major arrays.  After alloc_empty (which sets dims[0]=size for rank==1),
// we overwrite dims[0]/dims[1] for rank==2.
static sisal_array_t make_float_2d(const float* data, int rows, int cols) {
    int n = rows * cols;
    sisal_array_t a = sisal_array_alloc_empty(2, 8, (uint64_t)n);
    a.dims[0] = rows;
    a.dims[1] = cols;
    memcpy(a.data, data, (size_t)n * sizeof(float));
    return a;
}

static sisal_array_t make_double_2d(const double* data, int rows, int cols) {
    int n = rows * cols;
    sisal_array_t a = sisal_array_alloc_empty(2, 4, (uint64_t)n);
    a.dims[0] = rows;
    a.dims[1] = cols;
    memcpy(a.data, data, (size_t)n * sizeof(double));
    return a;
}

static sisal_array_t make_int_2d(const int32_t* data, int rows, int cols) {
    int n = rows * cols;
    sisal_array_t a = sisal_array_alloc_empty(2, 6, (uint64_t)n);
    a.dims[0] = rows;
    a.dims[1] = cols;
    memcpy(a.data, data, (size_t)n * sizeof(int32_t));
    return a;
}

// ============================================================
// Accessors for result arrays
// ============================================================

static inline float  af(sisal_array_t a, int i) { return ((float*)a.data)[i]; }
static inline double ad(sisal_array_t a, int i) { return ((double*)a.data)[i]; }
static inline int32_t ai(sisal_array_t a, int i) { return ((int32_t*)a.data)[i]; }
static inline bool   ab(sisal_array_t a, int i) { return ((bool*)a.data)[i]; }

// ============================================================
// GROUP A — dv_abs_demo
// ============================================================

#ifdef TEST_ABS_DEMO
static void test_abs_demo(void) {
    printf("\n=== Group A: dv_abs_demo ===\n");
    float inp[] = {-1.5f, 2.5f, -3.5f};
    float exp[] = { 1.5f, 2.5f,  3.5f};
    sisal_array_t v = make_float_arr(inp, 3);
    sisal_array_t r = func_DV_ABS_DEMO(v);
    check("abs_demo[0]", near_f(af(r, 0), exp[0]));
    check("abs_demo[1]", near_f(af(r, 1), exp[1]));
    check("abs_demo[2]", near_f(af(r, 2), exp[2]));
    free(v.data); free(r.data);
}
#endif

// ============================================================
// GROUP B — dv_agreement  (func_MAIN: int32 + int32 → int32)
// ============================================================

#ifdef TEST_AGREEMENT
static void test_agreement(void) {
    printf("\n=== Group B: dv_agreement ===\n");
    int32_t a[] = {1, 2, 3};
    int32_t b[] = {10, 20, 30};
    int32_t ex[] = {11, 22, 33};
    sisal_array_t va = make_int_arr(a, 3);
    sisal_array_t vb = make_int_arr(b, 3);
    sisal_array_t r  = func_MAIN(va, vb);
    check("agreement[0]", ai(r, 0) == ex[0]);
    check("agreement[1]", ai(r, 1) == ex[1]);
    check("agreement[2]", ai(r, 2) == ex[2]);
    free(va.data); free(vb.data); free(r.data);
}
#endif

// ============================================================
// GROUP C — dv_lifted_arith  (func_MAIN: double A*B+A)
// ============================================================

#ifdef TEST_LIFTED_ARITH
static void test_lifted_arith(void) {
    printf("\n=== Group C: dv_lifted_arith ===\n");
    double a[] = {1.0, 2.0, 3.0};
    double b[] = {10.0, 20.0, 30.0};
    // A*B+A = [1*10+1, 2*20+2, 3*30+3] = [11, 42, 93]
    double ex[] = {11.0, 42.0, 93.0};
    sisal_array_t va = make_double_arr(a, 3);
    sisal_array_t vb = make_double_arr(b, 3);
    sisal_array_t r  = func_MAIN(va, vb);
    check("lifted_arith[0]", near_d(ad(r, 0), ex[0]));
    check("lifted_arith[1]", near_d(ad(r, 1), ex[1]));
    check("lifted_arith[2]", near_d(ad(r, 2), ex[2]));
    free(va.data); free(vb.data); free(r.data);
}
#endif

// ============================================================
// GROUP D — dv_shl  (int32 << N)
// ============================================================

#ifdef TEST_SHL
static void test_shl(void) {
    printf("\n=== Group D: dv_shl ===\n");
    int32_t v[] = {1, 2, 4};
    int32_t ex[] = {4, 8, 16};
    sisal_array_t vv = make_int_arr(v, 3);
    sisal_array_t r  = func_DV_SHL_SCALAR(vv, 2);
    check("shl[0]", ai(r, 0) == ex[0]);
    check("shl[1]", ai(r, 1) == ex[1]);
    check("shl[2]", ai(r, 2) == ex[2]);
    free(vv.data); free(r.data);
}
#endif

// ============================================================
// GROUP E — dv_test_subset
// ============================================================

#ifdef TEST_TEST_SUBSET
static void test_test_subset(void) {
    printf("\n=== Group E: dv_test_subset ===\n");

    // abs([-1,2,-3]) → [1,2,3]
    { float inp[] = {-1.f, 2.f, -3.f};
      sisal_array_t v = make_float_arr(inp, 3);
      sisal_array_t r = func_DV_ABS_REAL(v);
      check("ts_abs[0]", near_f(af(r,0), 1.f));
      check("ts_abs[1]", near_f(af(r,1), 2.f));
      check("ts_abs[2]", near_f(af(r,2), 3.f));
      free(v.data); free(r.data); }

    // negate([1,-2,3]) → [-1,2,-3]
    { float inp[] = {1.f, -2.f, 3.f};
      sisal_array_t v = make_float_arr(inp, 3);
      sisal_array_t r = func_DV_NEGATE_REAL(v);
      check("ts_negate[0]", near_f(af(r,0), -1.f));
      check("ts_negate[1]", near_f(af(r,1),  2.f));
      check("ts_negate[2]", near_f(af(r,2), -3.f));
      free(v.data); free(r.data); }

    // sqrt([1,4,9]) → [1,2,3]
    { float inp[] = {1.f, 4.f, 9.f};
      sisal_array_t v = make_float_arr(inp, 3);
      sisal_array_t r = func_DV_SQRT_REAL(v);
      check("ts_sqrt[0]", near_f(af(r,0), 1.f));
      check("ts_sqrt[1]", near_f(af(r,1), 2.f));
      check("ts_sqrt[2]", near_f(af(r,2), 3.f));
      free(v.data); free(r.data); }

    // sin([0]) → [0]
    { float inp[] = {0.f};
      sisal_array_t v = make_float_arr(inp, 1);
      sisal_array_t r = func_DV_SIN_REAL(v);
      check("ts_sin[0]", near_f(af(r,0), 0.f));
      free(v.data); free(r.data); }

    // cos([0]) → [1]
    { float inp[] = {0.f};
      sisal_array_t v = make_float_arr(inp, 1);
      sisal_array_t r = func_DV_COS_REAL(v);
      check("ts_cos[0]", near_f(af(r,0), 1.f));
      free(v.data); free(r.data); }

    // add_dv([1,2],[3,4]) → [4,6]
    { float a[] = {1.f, 2.f};
      float b[] = {3.f, 4.f};
      sisal_array_t va = make_float_arr(a, 2);
      sisal_array_t vb = make_float_arr(b, 2);
      sisal_array_t r  = func_DV_ADD_DV(va, vb);
      check("ts_add_dv[0]", near_f(af(r,0), 4.f));
      check("ts_add_dv[1]", near_f(af(r,1), 6.f));
      free(va.data); free(vb.data); free(r.data); }

    // mul_scalar([2,3,4], 10) → [20,30,40]
    { float inp[] = {2.f, 3.f, 4.f};
      sisal_array_t v = make_float_arr(inp, 3);
      sisal_array_t r = func_DV_MUL_SCALAR(v, 10.f);
      check("ts_mul_scalar[0]", near_f(af(r,0), 20.f));
      check("ts_mul_scalar[1]", near_f(af(r,1), 30.f));
      check("ts_mul_scalar[2]", near_f(af(r,2), 40.f));
      free(v.data); free(r.data); }

    // add_scalar([1,2,3], 10) → [11,12,13]
    { float inp[] = {1.f, 2.f, 3.f};
      sisal_array_t v = make_float_arr(inp, 3);
      sisal_array_t r = func_DV_ADD_SCALAR(v, 10.f);
      check("ts_add_scalar[0]", near_f(af(r,0), 11.f));
      check("ts_add_scalar[1]", near_f(af(r,1), 12.f));
      check("ts_add_scalar[2]", near_f(af(r,2), 13.f));
      free(v.data); free(r.data); }

    // gt_scalar([1,5,3], 2) → [false,true,true]
    { float inp[] = {1.f, 5.f, 3.f};
      sisal_array_t v = make_float_arr(inp, 3);
      sisal_array_t r = func_DV_GT_SCALAR(v, 2.f);
      check("ts_gt_scalar[0]", ab(r,0) == false);
      check("ts_gt_scalar[1]", ab(r,1) == true);
      check("ts_gt_scalar[2]", ab(r,2) == true);
      free(v.data); free(r.data); }

    // sum_real([1,2,3,4]) → 10
    { float inp[] = {1.f, 2.f, 3.f, 4.f};
      sisal_array_t v = make_float_arr(inp, 4);
      float s = func_DV_SUM_REAL(v);
      check("ts_sum_real", near_f(s, 10.f));
      free(v.data); }
}
#endif

// ============================================================
// GROUP F — dv_intrinsics (representative subset)
// ============================================================

#ifdef TEST_INTRINSICS
static void test_intrinsics(void) {
    printf("\n=== Group F: dv_intrinsics ===\n");

    // dv_abs_real([-1,2,-3]) → [1,2,3]
    { float inp[] = {-1.f, 2.f, -3.f};
      sisal_array_t v = make_float_arr(inp, 3);
      sisal_array_t r = func_DV_ABS_REAL(v);
      check("intr_abs_real[0]", near_f(af(r,0), 1.f));
      check("intr_abs_real[1]", near_f(af(r,1), 2.f));
      check("intr_abs_real[2]", near_f(af(r,2), 3.f));
      free(v.data); free(r.data); }

    // dv_sqrt_real([1,4,9]) → [1,2,3]
    { float inp[] = {1.f, 4.f, 9.f};
      sisal_array_t v = make_float_arr(inp, 3);
      sisal_array_t r = func_DV_SQRT_REAL(v);
      check("intr_sqrt_real[0]", near_f(af(r,0), 1.f));
      check("intr_sqrt_real[1]", near_f(af(r,1), 2.f));
      check("intr_sqrt_real[2]", near_f(af(r,2), 3.f));
      free(v.data); free(r.data); }

    // dv_sin_real([0]) → [0]
    { float inp[] = {0.f};
      sisal_array_t v = make_float_arr(inp, 1);
      sisal_array_t r = func_DV_SIN_REAL(v);
      check("intr_sin_real[0]", near_f(af(r,0), 0.f));
      free(v.data); free(r.data); }

    // dv_cos_real([0]) → [1]
    { float inp[] = {0.f};
      sisal_array_t v = make_float_arr(inp, 1);
      sisal_array_t r = func_DV_COS_REAL(v);
      check("intr_cos_real[0]", near_f(af(r,0), 1.f));
      free(v.data); free(r.data); }

    // dv_log_real([1]) → [0]  (ln 1 = 0)
    { float inp[] = {1.f};
      sisal_array_t v = make_float_arr(inp, 1);
      sisal_array_t r = func_DV_LOG_REAL(v);
      check("intr_log_real[0]", near_f(af(r,0), 0.f));
      free(v.data); free(r.data); }

    // dv_floor_real([1.7, 2.3, -0.5]) → int32[1, 2, -1]
    { float inp[] = {1.7f, 2.3f, -0.5f};
      sisal_array_t v = make_float_arr(inp, 3);
      sisal_array_t r = func_DV_FLOOR_REAL(v);
      check("intr_floor_real[0]", ai(r,0) == 1);
      check("intr_floor_real[1]", ai(r,1) == 2);
      check("intr_floor_real[2]", ai(r,2) == -1);
      free(v.data); free(r.data); }

    // dv_trunc_real([1.7, 2.3, -0.5]) → int32[1, 2, 0]
    { float inp[] = {1.7f, 2.3f, -0.5f};
      sisal_array_t v = make_float_arr(inp, 3);
      sisal_array_t r = func_DV_TRUNC_REAL(v);
      check("intr_trunc_real[0]", ai(r,0) == 1);
      check("intr_trunc_real[1]", ai(r,1) == 2);
      check("intr_trunc_real[2]", ai(r,2) == 0);
      free(v.data); free(r.data); }

    // dv_abs_double([-1.0, 2.0]) → [1.0, 2.0]
    { double inp[] = {-1.0, 2.0};
      sisal_array_t v = make_double_arr(inp, 2);
      sisal_array_t r = func_DV_ABS_DOUBLE(v);
      check("intr_abs_double[0]", near_d(ad(r,0), 1.0));
      check("intr_abs_double[1]", near_d(ad(r,1), 2.0));
      free(v.data); free(r.data); }

    // dv_sqrt_double([4.0, 9.0]) → [2.0, 3.0]
    { double inp[] = {4.0, 9.0};
      sisal_array_t v = make_double_arr(inp, 2);
      sisal_array_t r = func_DV_SQRT_DOUBLE(v);
      check("intr_sqrt_double[0]", near_d(ad(r,0), 2.0));
      check("intr_sqrt_double[1]", near_d(ad(r,1), 3.0));
      free(v.data); free(r.data); }

    // dv_add_dv([1,2,3],[4,5,6]) → [5,7,9]
    { float a[] = {1.f,2.f,3.f}, b[] = {4.f,5.f,6.f};
      sisal_array_t va = make_float_arr(a,3), vb = make_float_arr(b,3);
      sisal_array_t r = func_DV_ADD_DV(va, vb);
      check("intr_add_dv[0]", near_f(af(r,0),5.f));
      check("intr_add_dv[1]", near_f(af(r,1),7.f));
      check("intr_add_dv[2]", near_f(af(r,2),9.f));
      free(va.data); free(vb.data); free(r.data); }

    // dv_sub_dv([4,5,6],[1,2,3]) → [3,3,3]
    { float a[] = {4.f,5.f,6.f}, b[] = {1.f,2.f,3.f};
      sisal_array_t va = make_float_arr(a,3), vb = make_float_arr(b,3);
      sisal_array_t r = func_DV_SUB_DV(va, vb);
      check("intr_sub_dv[0]", near_f(af(r,0),3.f));
      check("intr_sub_dv[1]", near_f(af(r,1),3.f));
      check("intr_sub_dv[2]", near_f(af(r,2),3.f));
      free(va.data); free(vb.data); free(r.data); }

    // dv_mul_dv([2,3,4],[5,6,7]) → [10,18,28]
    { float a[] = {2.f,3.f,4.f}, b[] = {5.f,6.f,7.f};
      sisal_array_t va = make_float_arr(a,3), vb = make_float_arr(b,3);
      sisal_array_t r = func_DV_MUL_DV(va, vb);
      check("intr_mul_dv[0]", near_f(af(r,0),10.f));
      check("intr_mul_dv[1]", near_f(af(r,1),18.f));
      check("intr_mul_dv[2]", near_f(af(r,2),28.f));
      free(va.data); free(vb.data); free(r.data); }

    // dv_div_dv([10,20,30],[2,4,5]) → [5,5,6]
    { float a[] = {10.f,20.f,30.f}, b[] = {2.f,4.f,5.f};
      sisal_array_t va = make_float_arr(a,3), vb = make_float_arr(b,3);
      sisal_array_t r = func_DV_DIV_DV(va, vb);
      check("intr_div_dv[0]", near_f(af(r,0),5.f));
      check("intr_div_dv[1]", near_f(af(r,1),5.f));
      check("intr_div_dv[2]", near_f(af(r,2),6.f));
      free(va.data); free(vb.data); free(r.data); }

    // scalar_add_dv(10, [1,2,3]) → [11,12,13]
    { float inp[] = {1.f, 2.f, 3.f};
      sisal_array_t v = make_float_arr(inp, 3);
      sisal_array_t r = func_SCALAR_ADD_DV(10.f, v);
      check("intr_scalar_add_dv[0]", near_f(af(r,0),11.f));
      check("intr_scalar_add_dv[1]", near_f(af(r,1),12.f));
      check("intr_scalar_add_dv[2]", near_f(af(r,2),13.f));
      free(v.data); free(r.data); }

    // dv_gt_scalar([1,5,3], 2) → [F,T,T]
    { float inp[] = {1.f, 5.f, 3.f};
      sisal_array_t v = make_float_arr(inp, 3);
      sisal_array_t r = func_DV_GT_SCALAR(v, 2.f);
      check("intr_gt_scalar[0]", ab(r,0) == false);
      check("intr_gt_scalar[1]", ab(r,1) == true);
      check("intr_gt_scalar[2]", ab(r,2) == true);
      free(v.data); free(r.data); }

    // dv_eq_dv([1,2,3],[1,9,3]) → [T,F,T]
    { float a[] = {1.f,2.f,3.f}, b[] = {1.f,9.f,3.f};
      sisal_array_t va = make_float_arr(a,3), vb = make_float_arr(b,3);
      sisal_array_t r = func_DV_EQ_DV(va, vb);
      check("intr_eq_dv[0]", ab(r,0) == true);
      check("intr_eq_dv[1]", ab(r,1) == false);
      check("intr_eq_dv[2]", ab(r,2) == true);
      free(va.data); free(vb.data); free(r.data); }

    // dv_ne_dv([1,2,3],[1,9,3]) → [F,T,F]
    { float a[] = {1.f,2.f,3.f}, b[] = {1.f,9.f,3.f};
      sisal_array_t va = make_float_arr(a,3), vb = make_float_arr(b,3);
      sisal_array_t r = func_DV_NE_DV(va, vb);
      check("intr_ne_dv[0]", ab(r,0) == false);
      check("intr_ne_dv[1]", ab(r,1) == true);
      check("intr_ne_dv[2]", ab(r,2) == false);
      free(va.data); free(vb.data); free(r.data); }

    // dv_and_dv([T,T,F],[T,F,F]) → [T,F,F]
    { bool a[] = {true,true,false}, b[] = {true,false,false};
      sisal_array_t va = make_bool_arr(a,3), vb = make_bool_arr(b,3);
      sisal_array_t r = func_DV_AND_DV(va, vb);
      check("intr_and_dv[0]", ab(r,0) == true);
      check("intr_and_dv[1]", ab(r,1) == false);
      check("intr_and_dv[2]", ab(r,2) == false);
      free(va.data); free(vb.data); free(r.data); }

    // dv_or_dv([T,F,F],[F,F,T]) → [T,F,T]
    { bool a[] = {true,false,false}, b[] = {false,false,true};
      sisal_array_t va = make_bool_arr(a,3), vb = make_bool_arr(b,3);
      sisal_array_t r = func_DV_OR_DV(va, vb);
      check("intr_or_dv[0]", ab(r,0) == true);
      check("intr_or_dv[1]", ab(r,1) == false);
      check("intr_or_dv[2]", ab(r,2) == true);
      free(va.data); free(vb.data); free(r.data); }

    // dv_shl_scalar([1,2,4], 2) → [4,8,16]
    { int32_t inp[] = {1, 2, 4};
      sisal_array_t v = make_int_arr(inp, 3);
      sisal_array_t r = func_DV_SHL_SCALAR(v, 2);
      check("intr_shl_scalar[0]", ai(r,0) == 4);
      check("intr_shl_scalar[1]", ai(r,1) == 8);
      check("intr_shl_scalar[2]", ai(r,2) == 16);
      free(v.data); free(r.data); }

    // dv_shr_scalar([8,4,16], 2) → [2,1,4]
    { int32_t inp[] = {8, 4, 16};
      sisal_array_t v = make_int_arr(inp, 3);
      sisal_array_t r = func_DV_SHR_SCALAR(v, 2);
      check("intr_shr_scalar[0]", ai(r,0) == 2);
      check("intr_shr_scalar[1]", ai(r,1) == 1);
      check("intr_shr_scalar[2]", ai(r,2) == 4);
      free(v.data); free(r.data); }

    // dv_sum_real([1,2,3,4]) → 10
    { float inp[] = {1.f,2.f,3.f,4.f};
      sisal_array_t v = make_float_arr(inp, 4);
      float s = func_DV_SUM_REAL(v);
      check("intr_sum_real", near_f(s, 10.f));
      free(v.data); }

    // dv_product_real([1,2,3,4]) → 24
    // NOTE: sisal_array_reduce_float_product is a stub returning 1.0f — EXPECTED FAIL
    { float inp[] = {1.f,2.f,3.f,4.f};
      sisal_array_t v = make_float_arr(inp, 4);
      float s = func_DV_PRODUCT_REAL(v);
      printf("  INFO  intr_product_real = %g (expected 24; runtime stub returns 1 — known issue)\n", s);
      check("intr_product_real", near_f(s, 24.f));
      free(v.data); }

    // dv_least_real([3,1,4,1,5]) → 1
    // NOTE: sisal_array_reduce_least is a stub returning 0.0f — EXPECTED FAIL
    { float inp[] = {3.f,1.f,4.f,1.f,5.f};
      sisal_array_t v = make_float_arr(inp, 5);
      float s = func_DV_LEAST_REAL(v);
      printf("  INFO  intr_least_real = %g (expected 1; runtime stub returns 0 — known issue)\n", s);
      check("intr_least_real", near_f(s, 1.f));
      free(v.data); }

    // dv_greatest_real([3,1,4,1,5]) → 5
    // NOTE: sisal_array_reduce_greatest is a stub returning 0.0f — EXPECTED FAIL
    { float inp[] = {3.f,1.f,4.f,1.f,5.f};
      sisal_array_t v = make_float_arr(inp, 5);
      float s = func_DV_GREATEST_REAL(v);
      printf("  INFO  intr_greatest_real = %g (expected 5; runtime stub returns 0 — known issue)\n", s);
      check("intr_greatest_real", near_f(s, 5.f));
      free(v.data); }

    // dv_sum_int([1,2,3,4]) → 10
    // NOTE: reduce_int_sum calls reduce_sum (float*) on int32 data — result is implementation-defined
    { int32_t inp[] = {1, 2, 3, 4};
      sisal_array_t v = make_int_arr(inp, 4);
      int32_t s = func_DV_SUM_INT(v);
      printf("  INFO  intr_sum_int = %d (expected 10; runtime interprets int bits as float — may differ)\n", s);
      check("intr_sum_int", s == 10);
      free(v.data); }

    // dv_product_int([1,2,3,4]) → 24  (reduce_int_product is properly implemented)
    { int32_t inp[] = {1, 2, 3, 4};
      sisal_array_t v = make_int_arr(inp, 4);
      int32_t s = func_DV_PRODUCT_INT(v);
      check("intr_product_int", s == 24);
      free(v.data); }

    // dv_least_int([3,1,4]) → 1
    // NOTE: reduce_int_least is a stub returning 0 — EXPECTED FAIL
    { int32_t inp[] = {3, 1, 4};
      sisal_array_t v = make_int_arr(inp, 3);
      int32_t s = func_DV_LEAST_INT(v);
      printf("  INFO  intr_least_int = %d (expected 1; runtime stub returns 0 — known issue)\n", s);
      check("intr_least_int", s == 1);
      free(v.data); }

    // dv_greatest_int([3,1,4]) → 4
    // NOTE: reduce_int_greatest is a stub returning 0 — EXPECTED FAIL
    { int32_t inp[] = {3, 1, 4};
      sisal_array_t v = make_int_arr(inp, 3);
      int32_t s = func_DV_GREATEST_INT(v);
      printf("  INFO  intr_greatest_int = %d (expected 4; runtime stub returns 0 — known issue)\n", s);
      check("intr_greatest_int", s == 4);
      free(v.data); }
}
#endif

// ============================================================
// GROUP G — dv_broadcast_complex  (2D double broadcasting)
//
// Known compiler bug: the broadcast functions produce wrong shape metadata
// (rank/dims) and in the vec_mat case also wrong element count.  The tests
// below assert the *actual* observed behaviour so they function as a
// regression baseline.  Correct expected values are noted in comments.
// ============================================================

#ifdef TEST_BROADCAST_COMPLEX
static void test_broadcast_complex(void) {
    printf("\n=== Group G: dv_broadcast_complex ===\n");

    // broadcast_vec_mat: V=[1,2,3] (1D) + M=[[10,20,30],[40,50,60]] (shape [2,3])
    // numpy: result shape [2,3], values [11,22,33, 41,52,63].
    {
        double v_data[] = {1.0, 2.0, 3.0};
        double m_data[] = {10.0,20.0,30.0, 40.0,50.0,60.0};
        sisal_array_t V = make_double_arr(v_data, 3);
        sisal_array_t M = make_double_2d(m_data, 2, 3);
        sisal_array_t r = func_BROADCAST_VEC_MAT(V, M);
        check("bcast_vec_mat shape [2,3]", r.rank==2 && r.dims[0]==2 && r.dims[1]==3 && r.size==6);
        double ex[] = {11,22,33, 41,52,63};
        bool ok = (r.size==6); for (int i=0;i<6 && ok;i++) ok &= near_d(ad(r,i), ex[i]);
        check("bcast_vec_mat values 11 22 33 41 52 63", ok);
        free(V.data); free(M.data); free(r.data);
    }

    // broadcast_unit: A=[[1],[2]] (shape [2,1]) + B=[[10,20,30]] (shape [1,3])
    // numpy: result shape [2,3], values [11,21,31, 12,22,32].
    {
        double a_data[] = {1.0, 2.0};
        double b_data[] = {10.0, 20.0, 30.0};
        sisal_array_t A = make_double_2d(a_data, 2, 1);
        sisal_array_t B = make_double_2d(b_data, 1, 3);
        sisal_array_t r = func_BROADCAST_UNIT(A, B);
        check("bcast_unit shape [2,3]", r.rank==2 && r.dims[0]==2 && r.dims[1]==3 && r.size==6);
        double ex[] = {11,21,31, 12,22,32};
        bool ok = (r.size==6); for (int i=0;i<6 && ok;i++) ok &= near_d(ad(r,i), ex[i]);
        check("bcast_unit values 11 21 31 12 22 32", ok);
        free(A.data); free(B.data); free(r.data);
    }

    // broadcast_scalar: S=100.0 + M=[[1..9]] (shape [3,3]) -> values [101..109].
    // VALUES are correct; the result SHAPE is still rank-1 [9] -- a separate bug in
    // the scalar+array path (the conform fix only covers array+array rank mismatch).
    {
        double m_data[] = {1.0,2.0,3.0, 4.0,5.0,6.0, 7.0,8.0,9.0};
        sisal_array_t M = make_double_2d(m_data, 3, 3);
        sisal_array_t r = func_BROADCAST_SCALAR(100.0, M);
        // scalar broadcast keeps M's shape: the flat elementwise result is reshaped
        // back to M's runtime rank/dims (DV_NUM_RANK -> DV_DIMENSION -> RESHAPE).
        check("bcast_scalar shape [3,3]", r.rank==2 && r.dims[0]==3 && r.dims[1]==3 && r.size==9);
        bool ok = (r.size==9); for (int i=0;i<9 && ok;i++) ok &= near_d(ad(r,i), m_data[i] + 100.0);
        check("bcast_scalar values 101..109", ok);
        free(M.data); free(r.data);
    }
}
#endif

// ============================================================
// GROUP H — dv_compress_test
// ============================================================

#ifdef TEST_COMPRESS
static void test_compress(void) {
    printf("\n=== Group H: dv_compress_test ===\n");

    // compress_monolithic: mask=[T,F,T,F,T], a=[10,20,30,40,50] → [10,30,50]
    // NOTE: sisal_array_compress uses float* cast to copy elements regardless of type_id.
    // For int32 inputs, this means a 4-byte copy as if the bits were float.
    // The result array has type_id=6 (int32) but was written via float*, so values
    // should still be bit-identical to the original int32 values if sizeof(float)==sizeof(int32_t).
    {
        bool mask[] = {true,false,true,false,true};
        int32_t a[]  = {10, 20, 30, 40, 50};
        sisal_array_t vm = make_bool_arr(mask, 5);
        sisal_array_t va = make_int_arr(a, 5);
        sisal_array_t r  = func_COMPRESS_MONOLITHIC(vm, va);
        check("compress_mono_size", r.size == 3);
        // The runtime copies via float* (4 bytes each), same width as int32_t,
        // so the bit pattern is preserved.
        check("compress_mono[0]", ai(r,0) == 10);
        check("compress_mono[1]", ai(r,1) == 30);
        check("compress_mono[2]", ai(r,2) == 50);
        free(vm.data); free(va.data); free(r.data);
    }

    // compress_dv_input(6): even numbers from 1..6 = [2,4,6]
    {
        sisal_array_t r = func_COMPRESS_DV_INPUT(6);
        check("compress_dv_size", r.size == 3);
        // The values array was int32, copied via float* — bit-identical
        check("compress_dv[0]", ai(r,0) == 2);
        check("compress_dv[1]", ai(r,1) == 4);
        check("compress_dv[2]", ai(r,2) == 6);
        free(r.data);
    }

    // compress_chain: mask=[T,F,T], a=[10,20,30] → size=2
    {
        bool mask[] = {true, false, true};
        int32_t a[]  = {10, 20, 30};
        sisal_array_t vm = make_bool_arr(mask, 3);
        sisal_array_t va = make_int_arr(a, 3);
        int32_t s = func_COMPRESS_CHAIN(vm, va);
        check("compress_chain", s == 2);
        free(vm.data); free(va.data);
    }
}
#endif

// ============================================================
// GROUP I — dv_broadcast_numpy (APL rank-mismatch: expected error)
// ============================================================

#ifdef TEST_BROADCAST_NUMPY
static void test_broadcast_numpy(void) {
    printf("\n=== Group I: dv_broadcast_numpy ===\n");
    printf("  NOTE  APL semantics: 2D [2,3] + 1D [3] is a rank mismatch.\n");
    printf("  NOTE  The function may produce garbage, crash, or return an error result.\n");
    printf("  NOTE  This test just checks that it doesn't hard-crash the process.\n");

    double a_data[] = {1.0,2.0,3.0, 4.0,5.0,6.0};
    double b_data[] = {10.0, 20.0, 30.0};
    sisal_array_t A = make_double_2d(a_data, 2, 3);
    sisal_array_t B = make_double_arr(b_data, 3);   // 1D, rank=1

    // Call and record whatever comes out — success here means no crash.
    sisal_array_t r = func_MAIN(A, B);
    printf("  INFO  broadcast_numpy returned: rank=%d size=%llu dims[0]=%lld dims[1]=%lld\n",
           r.rank, (unsigned long long)r.size,
           (long long)r.dims[0], (long long)r.dims[1]);
    check("broadcast_numpy_no_crash", true);   // we got here without crashing

    free(A.data); free(B.data);
    if (r.data) free(r.data);
}
#endif

// ============================================================
// GROUP J — forall_cpu  (for i in 1..N → array_dv of -real(i))
// ============================================================

#ifdef TEST_FORALL_CPU
static void test_forall_cpu(void) {
    printf("\n=== Group J: forall_cpu ===\n");
    // func_MAIN_CPU(4): X = real(i) for i in 1..4, return -X
    // Expected: [-1.0, -2.0, -3.0, -4.0]
    sisal_array_t r = func_MAIN_CPU(4);
    float exp[] = {-1.0f, -2.0f, -3.0f, -4.0f};
    check("forall_cpu_size", (int32_t)r.size == 4);
    for (int i = 0; i < 4; i++) {
        char name[32]; snprintf(name, sizeof(name), "forall_cpu[%d]", i);
        check(name, near_f(af(r, i), exp[i]));
    }
    if (r.data) free(r.data);
}
#endif

// ============================================================
// GROUP K — negate_dv  (let N := size(A) in for I in 1..N: -A[I])
// ============================================================

#ifdef TEST_NEGATE_DV
static void test_negate_dv(void) {
    printf("\n=== Group K: negate_dv ===\n");
    // func_NEGATE([3, 1, 4, 1, 5]) → [-3, -1, -4, -1, -5]
    int32_t inp[] = {3, 1, 4, 1, 5};
    int32_t exp[] = {-3, -1, -4, -1, -5};
    sisal_array_t A = make_int_arr(inp, 5);  // lower_bound = 1
    sisal_array_t r = func_NEGATE(A);
    check("negate_dv_size", (int32_t)r.size == 5);
    for (int i = 0; i < 5; i++) {
        char name[32]; snprintf(name, sizeof(name), "negate_dv[%d]", i);
        check(name, ai(r, i) == exp[i]);
    }
    free(A.data);
    if (r.data) free(r.data);
}
#endif

// ============================================================
// GROUP L — dv_forall_basic  (for i in 1..N → array_dv of i)
// ============================================================

#ifdef TEST_FORALL_BASIC_DV
static void test_forall_basic_dv(void) {
    printf("\n=== Group L: dv_forall_basic ===\n");
    // func_FORALL_BASIC(5) → [1, 2, 3, 4, 5]
    sisal_array_t r = func_FORALL_BASIC(5);
    int32_t exp[] = {1, 2, 3, 4, 5};
    check("forall_basic_dv_size", (int32_t)r.size == 5);
    for (int i = 0; i < 5; i++) {
        char name[32]; snprintf(name, sizeof(name), "forall_basic_dv[%d]", i);
        check(name, ai(r, i) == exp[i]);
    }
    if (r.data) free(r.data);
}
#endif

#ifdef TEST_FORALL_REDUCE_DV
static void test_forall_reduce_dv(void) {
    printf("\n=== Group M: dv_forall_reduce ===\n");
    // sum_to_n(5)  = 1+2+3+4+5 = 15
    check("sum_to_n_5",     func_SUM_TO_N(5)     == 15);
    check("sum_to_n_0",     func_SUM_TO_N(0)     == 0);
    // product_to_n(5) = 120
    check("product_to_n_5", func_PRODUCT_TO_N(5) == 120);
    check("product_to_n_1", func_PRODUCT_TO_N(1) == 1);
    // min_to_n(5) = 1, max_to_n(5) = 5
    check("min_to_n_5",     func_MIN_TO_N(5)     == 1);
    check("max_to_n_5",     func_MAX_TO_N(5)     == 5);
    check("max_to_n_1",     func_MAX_TO_N(1)     == 1);
}
#endif

#ifdef TEST_FOR_INITIAL
static void test_for_initial(void) {
    printf("\n=== Group FI: for_initial (LoopB) ===\n");
    // single self-recurrences
    check("fi_sum_10",      func_FI_SUM(10)      == 55);   // 1+..+10
    check("fi_sum_1",       func_FI_SUM(1)       == 1);
    check("fi_product_5",   func_FI_PRODUCT(5)   == 120);  // 5!
    check("fi_product_1",   func_FI_PRODUCT(1)   == 1);
    check("fi_final_i_5",   func_FI_FINAL_I(5)   == 6);    // i runs 1..n, stops at n+1
    check("fi_final_i_1",   func_FI_FINAL_I(1)   == 2);
    // identity-recurrence carry (k := old k) — needs the MERGE-filter fix
    check("fi_passthru_5",  func_FI_PASSTHRU(5)  == 42);
    check("fi_passthru_1",  func_FI_PASSTHRU(1)  == 42);
    // mutual old-references — needs the get_symbol_id_old carry-in fix
    check("fi_swap_1",      func_FI_SWAP(1)      == 20);   // a,b exchange each iter
    check("fi_swap_2",      func_FI_SWAP(2)      == 10);
    check("fi_swap_3",      func_FI_SWAP(3)      == 20);
    check("fi_fib_1",       func_FI_FIB(1)       == 1);    // Fibonacci
    check("fi_fib_5",       func_FI_FIB(5)       == 5);
    check("fi_fib_7",       func_FI_FIB(7)       == 13);
    check("fi_fib_10",      func_FI_FIB(10)      == 55);
    // LoopA (post-test repeat..until) Fibonacci — same recurrence via the other loop block
    check("fi_fib_a_1",     func_FI_FIB_A(1)     == 1);
    check("fi_fib_a_5",     func_FI_FIB_A(5)     == 5);
    check("fi_fib_a_7",     func_FI_FIB_A(7)     == 13);
    check("fi_fib_a_10",    func_FI_FIB_A(10)    == 55);

    // Regression: array-PARAMETER-seeded carry (A := Ain) — needs the to_if1
    // INIT-seed MERGE fix (a pass-through alias must still become a loop carry).
    int32_t seed[] = {10, 20, 30};
    sisal_array_t s1 = make_int_arr(seed, 3);
    sisal_array_t id = func_FI_PARAM_IDENTITY(3, s1);   // identity carry -> unchanged
    check("fi_param_identity rank=1",  id.rank == 1);
    check("fi_param_identity size=3",  (int)id.size == 3);
    check("fi_param_identity[0]=10",   ai(id, 0) == 10);
    check("fi_param_identity[1]=20",   ai(id, 1) == 20);
    check("fi_param_identity[2]=30",   ai(id, 2) == 30);
    // identity carry returns the same buffer as the input (id.data == s1.data),
    // so free it only once.
    if (s1.data) free(s1.data);

    sisal_array_t s2 = make_int_arr(seed, 3);
    sisal_array_t bp = func_FI_PARAM_BUMP(3, s2);       // +1 per elem, 3 iters
    check("fi_param_bump size=3",      (int)bp.size == 3);
    check("fi_param_bump[0]=13",       ai(bp, 0) == 13);
    check("fi_param_bump[1]=23",       ai(bp, 1) == 23);
    check("fi_param_bump[2]=33",       ai(bp, 2) == 33);
    if (bp.data) free(bp.data);
    if (s2.data) free(s2.data);
}
#endif

#ifdef TEST_INNERPRODUCT_DV
static void test_innerproduct_dv(void) {
    printf("\n=== Group O: dv_innerproduct ===\n");
    printf("  (innerproduct always returns sisal_array_t; caller reads [0] for scalar)\n");

    // --- 1D float dot via Sisal wrapper: [1,2,3].[4,5,6] = 32 ---
    float fa[] = {1.0f, 2.0f, 3.0f};
    float fb[] = {4.0f, 5.0f, 6.0f};
    sisal_array_t va = make_float_arr(fa, 3);
    sisal_array_t vb = make_float_arr(fb, 3);
    sisal_array_t dr = func_IP_F32(va, vb);
    check("dot_f32 returns rank-1",      dr.rank == 1);
    check("dot_f32 returns size-1",      (int)dr.size == 1);
    check("dot_f32 [1,2,3].[4,5,6]=32", af(dr, 0) == 32.0f);
    if (dr.data) free(dr.data);
    if (va.data) free(va.data);
    if (vb.data) free(vb.data);

    // --- 1D int dot via Sisal wrapper: [1,2,3].[4,5,6] = 32 ---
    int32_t ia[] = {1, 2, 3};
    int32_t ib[] = {4, 5, 6};
    sisal_array_t vai = make_int_arr(ia, 3);
    sisal_array_t vbi = make_int_arr(ib, 3);
    sisal_array_t ir = func_IP_I32(vai, vbi);
    check("dot_i32 returns rank-1",      ir.rank == 1);
    check("dot_i32 returns size-1",      (int)ir.size == 1);
    check("dot_i32 [1,2,3].[4,5,6]=32", ai(ir, 0) == 32);
    if (ir.data) free(ir.data);
    if (vai.data) free(vai.data);
    if (vbi.data) free(vbi.data);

    // --- 1D empty dot ---
    sisal_array_t ve = make_float_arr(NULL, 0);
    sisal_array_t er = func_IP_F32(ve, ve);
    check("dot_f32 empty returns 0",     af(er, 0) == 0.0f);
    if (er.data) free(er.data);
    if (ve.data) free(ve.data);

    // --- 2D x 2D float matmul via Sisal wrapper ---
    // A=[[1,2],[3,4]]  B=[[5,6],[7,8]]  C=[[19,22],[43,50]]
    float ma[] = {1,2,3,4};
    float mb[] = {5,6,7,8};
    sisal_array_t A2 = make_float_2d(ma, 2, 2);
    sisal_array_t B2 = make_float_2d(mb, 2, 2);
    sisal_array_t C2 = func_IP_F32(A2, B2);
    check("matmul rank",    C2.rank == 2);
    check("matmul dims[0]", (int)C2.dims[0] == 2);
    check("matmul dims[1]", (int)C2.dims[1] == 2);
    check("matmul[0,0]=19", af(C2,0) == 19.0f);
    check("matmul[0,1]=22", af(C2,1) == 22.0f);
    check("matmul[1,0]=43", af(C2,2) == 43.0f);
    check("matmul[1,1]=50", af(C2,3) == 50.0f);
    if (A2.data) free(A2.data);
    if (B2.data) free(B2.data);
    if (C2.data) free(C2.data);

    // --- 2D x 1D matvec via Sisal wrapper ---
    // A=[[1,2,3],[4,5,6]]  x=[1,0,-1]  r=[-2,-2]
    float mav[] = {1,2,3,4,5,6};
    float vx[]  = {1.0f, 0.0f, -1.0f};
    sisal_array_t Amv = make_float_2d(mav, 2, 3);
    sisal_array_t xv  = make_float_arr(vx, 3);
    sisal_array_t rv  = func_IP_F32(Amv, xv);
    check("matvec rank",   rv.rank == 1);
    check("matvec size=2", (int)rv.size == 2);
    check("matvec[0]=-2",  af(rv,0) == -2.0f);
    check("matvec[1]=-2",  af(rv,1) == -2.0f);
    if (Amv.data) free(Amv.data);
    if (xv.data)  free(xv.data);
    if (rv.data)  free(rv.data);

    // --- 1D x 2D vecmat via Sisal wrapper ---
    // y=[1,2]  B=[[1,2,3],[4,5,6]]  r=[9,12,15]
    float vy[]  = {1.0f, 2.0f};
    float mbv[] = {1,2,3,4,5,6};
    sisal_array_t yv  = make_float_arr(vy, 2);
    sisal_array_t Bvm = make_float_2d(mbv, 2, 3);
    sisal_array_t rvm = func_IP_F32(yv, Bvm);
    check("vecmat rank",    rvm.rank == 1);
    check("vecmat size=3",  (int)rvm.size == 3);
    check("vecmat[0]=9",    af(rvm,0) == 9.0f);
    check("vecmat[1]=12",   af(rvm,1) == 12.0f);
    check("vecmat[2]=15",   af(rvm,2) == 15.0f);
    if (yv.data)  free(yv.data);
    if (Bvm.data) free(Bvm.data);
    if (rvm.data) free(rvm.data);

    // --- 1D double dot (direct runtime) ---
    // [1,2].[3,4] = 11
    double da[] = {1.0, 2.0};
    double db[] = {3.0, 4.0};
    sisal_array_t dva = make_double_arr(da, 2);
    sisal_array_t dvb = make_double_arr(db, 2);
    sisal_array_t dvr = sisal_array_innerproduct(dva, dvb);
    check("dot_f64 rank",             dvr.rank == 1);
    check("dot_f64 [1,2].[3,4]=11",   ((double*)dvr.data)[0] == 11.0);
    if (dva.data) free(dva.data);
    if (dvb.data) free(dvb.data);
    if (dvr.data) free(dvr.data);

    // --- rank-3 x rank-1: A(2,3,4) @ b(4) -> r(2,3) ---
    // A has 24 elements [0..23], b = [1,0,0,0] so result = A[:,:,0]
    float a3[24]; for(int i=0;i<24;i++) a3[i]=(float)i;
    float b1[] = {1.0f,0.0f,0.0f,0.0f};
    sisal_array_t A3 = sisal_array_alloc_empty(3, 8, 24);
    A3.dims[0]=2; A3.dims[1]=3; A3.dims[2]=4;
    memcpy(A3.data, a3, 24*sizeof(float));
    sisal_array_t B1 = make_float_arr(b1, 4);
    sisal_array_t R31 = sisal_array_innerproduct(A3, B1);
    // numpy: np.dot(A3,b1) shape=(2,3), values = A3[:,:,0] = [0,4,8,12,16,20]
    check("rank3x1 result rank=2",    R31.rank == 2);
    check("rank3x1 dims[0]=2",        (int)R31.dims[0] == 2);
    check("rank3x1 dims[1]=3",        (int)R31.dims[1] == 3);
    check("rank3x1 [0,0]=0",          af(R31,0) == 0.0f);
    check("rank3x1 [0,1]=4",          af(R31,1) == 4.0f);
    check("rank3x1 [0,2]=8",          af(R31,2) == 8.0f);
    check("rank3x1 [1,0]=12",         af(R31,3) == 12.0f);
    check("rank3x1 [1,1]=16",         af(R31,4) == 16.0f);
    check("rank3x1 [1,2]=20",         af(R31,5) == 20.0f);
    if (A3.data) free(A3.data);
    if (B1.data) free(B1.data);
    if (R31.data) free(R31.data);

    // --- rank-3 x rank-2: A(2,3,4) @ B(4,5) -> r(2,3,5) ---
    // Use identity-ish B: B[k,j] = (k==j ? 1 : 0) for k<4,j<5 — selects columns
    float a32[24]; for(int i=0;i<24;i++) a32[i]=(float)i;
    float b25[20]={0}; for(int k=0;k<4;k++) b25[k*5+k]=1.0f; // identity (4x5 padded)
    sisal_array_t A32 = sisal_array_alloc_empty(3, 8, 24);
    A32.dims[0]=2; A32.dims[1]=3; A32.dims[2]=4;
    memcpy(A32.data, a32, 24*sizeof(float));
    sisal_array_t B25 = make_float_2d(b25, 4, 5);
    sisal_array_t R32 = sisal_array_innerproduct(A32, B25);
    // A(2,3,4) @ I(4,5): result(2,3,5), result[:,:,0..3]=A, result[:,:,4]=0
    check("rank3x2 result rank=3",    R32.rank == 3);
    check("rank3x2 dims[0]=2",        (int)R32.dims[0] == 2);
    check("rank3x2 dims[1]=3",        (int)R32.dims[1] == 3);
    check("rank3x2 dims[2]=5",        (int)R32.dims[2] == 5);
    // result[0,0,:] = A[0,0,:] padded = [0,1,2,3,0]
    check("rank3x2 [0,0,0]=0",        af(R32,0) == 0.0f);
    check("rank3x2 [0,0,1]=1",        af(R32,1) == 1.0f);
    check("rank3x2 [0,0,3]=3",        af(R32,3) == 3.0f);
    check("rank3x2 [0,0,4]=0",        af(R32,4) == 0.0f);
    // result[1,2,:] = A[1,2,:] padded = [20,21,22,23,0]
    check("rank3x2 [1,2,0]=20",       af(R32,25) == 20.0f);
    check("rank3x2 [1,2,3]=23",       af(R32,28) == 23.0f);
    check("rank3x2 [1,2,4]=0",        af(R32,29) == 0.0f);
    if (A32.data) free(A32.data);
    if (B25.data) free(B25.data);
    if (R32.data) free(R32.data);

    // --- mismatch: rank-2(2,3) @ rank-2(4,5) -> empty (axis error) ---
    float mm_a[]={1,2,3,4,5,6}, mm_b[20]={0};
    sisal_array_t Amm = make_float_2d(mm_a, 2, 3);
    sisal_array_t Bmm = make_float_2d(mm_b, 4, 5);
    sisal_array_t Rmm = sisal_array_innerproduct(Amm, Bmm);
    check("mismatch returns empty",   (int)Rmm.size == 0);
    if (Amm.data) free(Amm.data);
    if (Bmm.data) free(Bmm.data);
    if (Rmm.data) free(Rmm.data);
}
#endif

#ifdef TEST_BULK_BASIC
static void test_bulk_basic(void) {
    printf("\n=== Group N: dv_bulk_basic ===\n");
    int32_t va_data[] = {1, 2, 3, 4};
    int32_t vb_data[] = {10, 20, 30, 40};
    sisal_array_t va = make_int_arr(va_data, 4);
    sisal_array_t vb = make_int_arr(vb_data, 4);

    // element-wise add: [11, 22, 33, 44]
    sisal_array_t r = func_T_ARR_ADD(va, vb);
    check("arr_add[0]", ai(r, 0) == 11);
    check("arr_add[1]", ai(r, 1) == 22);
    check("arr_add[2]", ai(r, 2) == 33);
    check("arr_add[3]", ai(r, 3) == 44);
    if (r.data) free(r.data);

    // element-wise sub: [-9, -18, -27, -36]
    r = func_T_ARR_SUB(va, vb);
    check("arr_sub[0]", ai(r, 0) == -9);
    check("arr_sub[1]", ai(r, 1) == -18);
    if (r.data) free(r.data);

    // element-wise mul: [10, 40, 90, 160]
    r = func_T_ARR_MUL(va, vb);
    check("arr_mul[0]", ai(r, 0) == 10);
    check("arr_mul[1]", ai(r, 1) == 40);
    check("arr_mul[2]", ai(r, 2) == 90);
    if (r.data) free(r.data);

    // negate: [-1, -2, -3, -4]
    r = func_T_ARR_NEG(va);
    check("arr_neg[0]", ai(r, 0) == -1);
    check("arr_neg[3]", ai(r, 3) == -4);
    if (r.data) free(r.data);

    // add scalar: [6, 7, 8, 9]
    r = func_T_ARR_ADD_SCALAR(va, 5);
    check("arr_add_scalar[0]", ai(r, 0) == 6);
    check("arr_add_scalar[3]", ai(r, 3) == 9);
    if (r.data) free(r.data);

    // mul scalar: [3, 6, 9, 12]
    r = func_T_ARR_MUL_SCALAR(va, 3);
    check("arr_mul_scalar[0]", ai(r, 0) == 3);
    check("arr_mul_scalar[3]", ai(r, 3) == 12);
    if (r.data) free(r.data);

    // whole-array reductions on [1,2,3,4]
    check("sum_1234",     func_T_SUM(va)     == 10);
    check("product_1234", func_T_PRODUCT(va) == 24);
    check("least_1234",   func_T_LEAST(va)   == 1);
    check("greatest_1234",func_T_GREATEST(va)== 4);

    // compress: mask=[T,F,T,F], data=[1,2,3,4] → [1,3]
    bool mask_data[] = {true, false, true, false};
    sisal_array_t vmask = make_bool_arr(mask_data, 4);
    r = func_T_COMPRESS(vmask, va);
    check("compress_size",  (int32_t)r.size == 2);
    check("compress[0]",    ai(r, 0) == 1);
    check("compress[1]",    ai(r, 1) == 3);
    if (r.data) free(r.data);
    if (vmask.data) free(vmask.data);

    // sort: [4,2,1,3] → [1,2,3,4]
    int32_t unsorted[] = {4, 2, 1, 3};
    sisal_array_t vu = make_int_arr(unsorted, 4);
    r = func_T_SORT(vu);
    check("sort[0]", ai(r, 0) == 1);
    check("sort[1]", ai(r, 1) == 2);
    check("sort[2]", ai(r, 2) == 3);
    check("sort[3]", ai(r, 3) == 4);
    if (r.data) free(r.data);
    if (vu.data) free(vu.data);

    // reverse: [1,2,3,4] → [4,3,2,1]
    r = func_T_REVERSE(va);
    check("reverse[0]", ai(r, 0) == 4);
    check("reverse[3]", ai(r, 3) == 1);
    if (r.data) free(r.data);

    if (va.data) free(va.data);
    if (vb.data) free(vb.data);
}
#endif

#ifdef TEST_GAUSSJ_PARTS
struct gp_arr2 { sisal_array_t res_0, res_1; };
struct gp_int2 { int32_t res_0, res_1; };
extern "C" int32_t      func_IDFAMAX(sisal_array_t A, int32_t N);
extern "C" int32_t      func_IDFMAX(sisal_array_t A, int32_t N);
extern "C" gp_arr2      func_GP_TWO(int32_t N, sisal_array_t A);
extern "C" sisal_array_t func_GP_AOR(int32_t N);
extern "C" gp_int2      func_GETPIVOT(int32_t N, sisal_array_t A, sisal_array_t PIVR);
extern "C" gp_arr2      func_COMPUTE(int32_t N, int32_t PVTROW, sisal_array_t AIN, sisal_array_t BIN);

static void test_gaussj_parts(void) {
    printf("\n=== Group GJ: gaussj component pieces ===\n");

    // argmax over a row [1,-5,3]: max|.| at idx 2, max at idx 3
    double row[] = {1.0, -5.0, 3.0};
    sisal_array_t r = make_double_arr(row, 3);
    check("idfamax([1,-5,3])=2", func_IDFAMAX(r, 3) == 2);
    check("idfmax([1,-5,3])=3",  func_IDFMAX(r, 3)  == 3);
    free(r.data);

    // multi-output 2-array gather: P=A+1, Q=A*2 over [10,20,30]
    double a3[] = {10.0, 20.0, 30.0};
    sisal_array_t va = make_double_arr(a3, 3);
    gp_arr2 t = func_GP_TWO(3, va);
    check("gp_two P[0]=11", ad(t.res_0, 0) == 11.0);
    check("gp_two P[2]=31", ad(t.res_0, 2) == 31.0);
    check("gp_two Q[0]=20", ad(t.res_1, 0) == 20.0);
    check("gp_two Q[2]=60", ad(t.res_1, 2) == 60.0);
    free(va.data); free(t.res_0.data); free(t.res_1.data);

    // box-then-flatten: array-of-rows -> flat rank-2 [11,12,21,22]
    sisal_array_t ar = func_GP_AOR(2);
    check("gp_aor rank=2", ar.rank == 2);
    check("gp_aor size=4", (int)ar.size == 4);
    check("gp_aor=11 12 21 22",
          ad(ar,0)==11.0 && ad(ar,1)==12.0 && ad(ar,2)==21.0 && ad(ar,3)==22.0);
    free(ar.data);

    // GetPivot on [[0,2],[3,0]], PIVR=[0,0] -> (Icol=1, Irow=2)
    double m[] = {0,2, 3,0}; sisal_array_t A2 = make_double_2d(m, 2, 2);
    int32_t pv[] = {0,0};    sisal_array_t Pv = make_int_arr(pv, 2);
    gp_int2 gp = func_GETPIVOT(2, A2, Pv);
    check("GetPivot Icol=1", gp.res_0 == 1);
    check("GetPivot Irow=2", gp.res_1 == 2);
    free(A2.data); free(Pv.data);

    // Compute(n=2, pvtrow=1, [[2,4],[1,3]], [2,3]) -> A'=[1,2,0,1], B'=[1,2]
    double cm[] = {2,4, 1,3}; sisal_array_t Ac = make_double_2d(cm, 2, 2);
    double cb[] = {2,3};      sisal_array_t Bc = make_double_arr(cb, 2);
    gp_arr2 c = func_COMPUTE(2, 1, Ac, Bc);
    check("Compute A'=1 2 0 1",
          ad(c.res_0,0)==1.0 && ad(c.res_0,1)==2.0 && ad(c.res_0,2)==0.0 && ad(c.res_0,3)==1.0);
    check("Compute B'=1 2", ad(c.res_1,0)==1.0 && ad(c.res_1,1)==2.0);
    free(Ac.data); free(Bc.data); free(c.res_0.data); free(c.res_1.data);
}
#endif

#ifdef TEST_GAUSSJ
extern "C" sisal_array_t func_MAIN(int32_t N, sisal_array_t A, sisal_array_t B);
static void test_gaussj(void) {
    printf("\n=== Group GJX: gaussj full solve (gaussj_dv_rr) ===\n");
    // 2x2 swap-forcing [[0,2],[3,0]] b=[4,9] -> x=[3,2]
    { double A[]={0,2, 3,0}, B[]={4,9};
      sisal_array_t Aa=make_double_2d(A,2,2), Bb=make_double_arr(B,2);
      sisal_array_t r=func_MAIN(2,Aa,Bb);
      check("gaussj 2x2 swap x=[3,2]", fabs(ad(r,0)-3.0)<1e-9 && fabs(ad(r,1)-2.0)<1e-9);
      free(Aa.data); free(Bb.data); free(r.data); }
    // 2x2 diagonal -> x=[2,3]
    { double A[]={2,0, 0,3}, B[]={4,9};
      sisal_array_t Aa=make_double_2d(A,2,2), Bb=make_double_arr(B,2);
      sisal_array_t r=func_MAIN(2,Aa,Bb);
      check("gaussj 2x2 diag x=[2,3]", fabs(ad(r,0)-2.0)<1e-9 && fabs(ad(r,1)-3.0)<1e-9);
      free(Aa.data); free(Bb.data); free(r.data); }
    // 3x3 dense [[2,1,1],[1,3,2],[1,0,0]] b=[4,5,1] -> x=[1,0,2]
    { double A[]={2,1,1, 1,3,2, 1,0,0}, B[]={4,5,1};
      sisal_array_t Aa=make_double_2d(A,3,3), Bb=make_double_arr(B,3);
      sisal_array_t r=func_MAIN(3,Aa,Bb);
      check("gaussj 3x3 dense x=[1,0,2]",
            fabs(ad(r,0)-1.0)<1e-9 && fabs(ad(r,1)-0.0)<1e-9 && fabs(ad(r,2)-2.0)<1e-9);
      free(Aa.data); free(Bb.data); free(r.data); }
    // larger B = A*x round-trip: diagonally dominant, x = 1..n, recover x
    { const int n=12; double A[n*n], B[n], x[n];
      for (int i=0;i<n;i++) x[i]=i+1;
      for (int i=0;i<n;i++) for (int j=0;j<n;j++) A[i*n+j]=(i==j)?(double)(n+1):1.0;
      for (int i=0;i<n;i++){ double s=0; for(int j=0;j<n;j++) s+=A[i*n+j]*x[j]; B[i]=s; }
      sisal_array_t Aa=make_double_2d(A,n,n), Bb=make_double_arr(B,n);
      sisal_array_t r=func_MAIN(n,Aa,Bb); double e=0;
      for (int i=0;i<n;i++){ double d=fabs(ad(r,i)-x[i]); if(d>e) e=d; }
      check("gaussj 12x12 B=A*x round-trip (err<1e-9)", e<1e-9);
      free(Aa.data); free(Bb.data); free(r.data); }
}
#endif

#ifdef TEST_SWAPLOOP
extern "C" sisal_array_t func_MAIN(int32_t N, sisal_array_t A);
static void test_swaploop(void) {
    printf("\n=== Group SWAP: in-loop row swap (DV_RANK_REPLACE, aliasing) ===\n");
    double A[]={11,12, 21,22};
    { sisal_array_t Aa=make_double_2d(A,2,2); sisal_array_t r=func_MAIN(1,Aa);  // one swap
      check("swaploop n=1 -> 21 22 11 12",
            ad(r,0)==21.0 && ad(r,1)==22.0 && ad(r,2)==11.0 && ad(r,3)==12.0);
      free(Aa.data); free(r.data); }
    { sisal_array_t Aa=make_double_2d(A,2,2); sisal_array_t r=func_MAIN(2,Aa);  // two swaps -> original
      check("swaploop n=2 -> original (round-trip)",
            ad(r,0)==11.0 && ad(r,1)==12.0 && ad(r,2)==21.0 && ad(r,3)==22.0);
      free(Aa.data); free(r.data); }
}
#endif

#ifdef TEST_GEN_EXTENT
extern "C" sisal_array_t func_GENEXT_SUB(int32_t n);
extern "C" sisal_array_t func_GENEXT_LB(int32_t n);
extern "C" sisal_array_t func_GENEXT_CROSS(int32_t n, int32_t m);
static void test_gen_extent(void) {
    printf("\n=== Group GE: generator expression-bound lowering ===\n");
    // single-level expr upper bound: i in 1..(n-1).  n=5 -> [1,4,9,16]
    { sisal_array_t r = func_GENEXT_SUB(5);
      check("genext_sub n=5 -> 1 4 9 16",
            (int)r.size==4 && ai(r,0)==1 && ai(r,1)==4 && ai(r,2)==9 && ai(r,3)==16);
      free(r.data); }
    // expr LOWER bound: i in (n-3)..n.  n=6 -> [3,4,5,6]
    { sisal_array_t r = func_GENEXT_LB(6);
      check("genext_lb n=6 -> 3 4 5 6",
            (int)r.size==4 && ai(r,0)==3 && ai(r,1)==4 && ai(r,2)==5 && ai(r,3)==6);
      free(r.data); }
    // cross nest, expr bound on inner axis: i in 1..n, j in 1..(m-1).
    // n=2,m=4 -> rank2 [2,3]: 11 12 13 21 22 23
    { sisal_array_t r = func_GENEXT_CROSS(2,4);
      check("genext_cross n=2,m=4 rank/dims", r.rank==2 && r.dims[0]==2 && r.dims[1]==3);
      check("genext_cross -> 11 12 13 21 22 23",
            (int)r.size==6 && ai(r,0)==11 && ai(r,1)==12 && ai(r,2)==13 &&
            ai(r,3)==21 && ai(r,4)==22 && ai(r,5)==23);
      free(r.data); }
}
#endif

#ifdef TEST_BROADCAST_PARTS
extern "C" int32_t       func_BP_RANK(sisal_array_t A);
extern "C" int32_t       func_BP_PRODUCT(sisal_array_t S);
extern "C" sisal_array_t func_BP_RESHAPE(sisal_array_t A, sisal_array_t S);
extern "C" int32_t       func_BP_OFFSET(sisal_array_t A, int32_t k, sisal_array_t S);
extern "C" int32_t       func_BP_LOAD(sisal_array_t A, int32_t off);
extern "C" sisal_array_t func_BP_BCAST_ADD(sisal_array_t A, sisal_array_t B,
                                           sisal_array_t S, int32_t total);
static void test_broadcast_parts(void) {
    printf("\n=== Group BP: A+B broadcast pieces (bottom-up) ===\n");
    int32_t d1[]={1,2,3}, d2[]={1,2,3,4,5,6};
    sisal_array_t v3  = make_int_arr(d1, 3);
    sisal_array_t v6  = make_int_arr(d2, 6);
    // Step 0 — rank
    { sisal_array_t m = make_int_2d(d2, 2, 3);
      check("bp_rank([3])=1",   func_BP_RANK(v3) == 1);
      check("bp_rank([2x3])=2", func_BP_RANK(m)  == 2);
      free(m.data); }
    // Step 1 — product over shape
    { int32_t s[]={2,3}, s2[]={2,3,4};
      sisal_array_t S=make_int_arr(s,2), S2=make_int_arr(s2,3);
      check("bp_product([2,3])=6",    func_BP_PRODUCT(S)  == 6);
      check("bp_product([2,3,4])=24", func_BP_PRODUCT(S2) == 24);
      free(S.data); free(S2.data); }
    // Step 2 — reshape flat[6] by [2,3]
    { int32_t s[]={2,3}; sisal_array_t S=make_int_arr(s,2);
      sisal_array_t r=func_BP_RESHAPE(v6, S);
      check("bp_reshape rank/dims", r.rank==2 && r.dims[0]==2 && r.dims[1]==3);
      check("bp_reshape data 1..6",
            ai(r,0)==1 && ai(r,1)==2 && ai(r,2)==3 && ai(r,3)==4 && ai(r,4)==5 && ai(r,5)==6);
      // NOTE: reshape aliases the input's data (res = a), so r.data == v6.data --
      // do NOT free r.data here; v6 is freed once at the end.
      free(S.data); }
    // Step 3a — offset (broadcast a [3] across result shape [2,3] -> 0 1 2 0 1 2)
    { int32_t a[]={10,20,30}, s[]={2,3};
      sisal_array_t A=make_int_arr(a,3), S=make_int_arr(s,2);
      bool ok=true; int exp[]={0,1,2,0,1,2};
      for (int k=0;k<6;k++) ok = ok && (func_BP_OFFSET(A,k,S)==exp[k]);
      check("bp_offset broadcast 0 1 2 0 1 2", ok);
      free(A.data); free(S.data); }
    // Step 3b — linear load
    { int32_t a[]={10,20,30,40}; sisal_array_t A=make_int_arr(a,4);
      check("bp_load(a,0)=10", func_BP_LOAD(A,0)==10);
      check("bp_load(a,2)=30", func_BP_LOAD(A,2)==30);
      free(A.data); }
    // Step 4 — offset element-wise forall (same-shape + real broadcast)
    { int32_t a[]={10,20,30}, b[]={1,2,3}, s[]={3};
      sisal_array_t A=make_int_arr(a,3), B=make_int_arr(b,3), S=make_int_arr(s,1);
      sisal_array_t r=func_BP_BCAST_ADD(A,B,S,3);
      check("bp_bcast_add same-shape -> 11 22 33",
            (int)r.size==3 && ai(r,0)==11 && ai(r,1)==22 && ai(r,2)==33);
      free(A.data); free(B.data); free(S.data); free(r.data); }
    { int32_t a[]={1,2,3,4,5,6}, b[]={10,20,30}, s[]={2,3};
      sisal_array_t A=make_int_2d(a,2,3), B=make_int_arr(b,3), S=make_int_arr(s,2);
      sisal_array_t r=func_BP_BCAST_ADD(A,B,S,6);
      check("bp_bcast_add broadcast -> 11 22 33 14 25 36",
            (int)r.size==6 && ai(r,0)==11 && ai(r,1)==22 && ai(r,2)==33 &&
            ai(r,3)==14 && ai(r,4)==25 && ai(r,5)==36);
      free(A.data); free(B.data); free(S.data); free(r.data); }
    free(v3.data); free(v6.data);
}
#endif

#ifdef TEST_IF_COND
extern "C" int32_t func_IFMIN(int32_t a, int32_t b);
extern "C" int32_t func_IF3(int32_t i, int32_t e);
extern "C" int32_t func_IF3V(int32_t i, int32_t e, int32_t f);
extern "C" int32_t func_IFDEEP(int32_t x);
static void test_if_cond(void) {
    printf("\n=== Group IF: if / elseif / else chains ===\n");
    // simple if/else = min
    check("ifmin(3,5)=3", func_IFMIN(3, 5) == 3);
    check("ifmin(5,3)=3", func_IFMIN(5, 3) == 3);
    // one elseif: i<e -> i*2 ; i=e -> e+3 ; else -> i-2
    check("if3(2,5)=4 (i<e)",   func_IF3(2, 5) == 4);
    check("if3(5,5)=8 (i=e)",   func_IF3(5, 5) == 8);
    check("if3(7,5)=5 (else)",  func_IF3(7, 5) == 5);
    // elseif over 3 vars: i<e -> i ; e<f -> e ; else -> f
    check("if3v(1,5,9)=1 (i<e)",  func_IF3V(1, 5, 9) == 1);
    check("if3v(5,3,9)=3 (e<f)",  func_IF3V(5, 3, 9) == 3);
    check("if3v(5,3,1)=1 (else f)",func_IF3V(5, 3, 1) == 1);
    // deep 6-branch chain
    check("ifdeep(0)=10", func_IFDEEP(0) == 10);
    check("ifdeep(2)=30", func_IFDEEP(2) == 30);
    check("ifdeep(4)=50", func_IFDEEP(4) == 50);
    check("ifdeep(5)=60", func_IFDEEP(5) == 60);
    check("ifdeep(9)=60", func_IFDEEP(9) == 60);
}
#endif

// ============================================================
// GROUP FDS — forall_dv_simple  (for i in 1..N → array_dv of i*i)
// ============================================================
#ifdef TEST_FORALL_DV_SIMPLE
extern "C" sisal_array_t func_MAIN(int32_t N);
static void test_forall_dv_simple(void) {
    printf("\n=== Group FDS: forall_dv_simple (i*i) ===\n");
    // func_MAIN(5) → [1, 4, 9, 16, 25]
    sisal_array_t r = func_MAIN(5);
    int32_t exp[] = {1, 4, 9, 16, 25};
    check("fds_size", (int32_t)r.size == 5);
    for (int i = 0; i < 5; i++) {
        char n[32]; snprintf(n, sizeof n, "fds[%d]", i);
        check(n, ai(r, i) == exp[i]);
    }
    if (r.data) free(r.data);
}
#endif

// ============================================================
// GROUP CDD — cross_dv_demo  (for i in 1..N cross j in 1..M → array_dv of i*j)
// ============================================================
#ifdef TEST_CROSS_DV_DEMO
extern "C" sisal_array_t func_MAIN(int32_t N, int32_t M);
static void test_cross_dv_demo(void) {
    printf("\n=== Group CDD: cross_dv_demo (i*j cross) ===\n");
    // func_MAIN(2,3): i in 1..2 cross j in 1..3 → [1,2,3, 2,4,6]
    sisal_array_t r = func_MAIN(2, 3);
    int32_t exp[] = {1, 2, 3, 2, 4, 6};
    check("cdd_size", (int32_t)r.size == 6);
    for (int i = 0; i < 6; i++) {
        char n[32]; snprintf(n, sizeof n, "cdd[%d]", i);
        check(n, ai(r, i) == exp[i]);
    }
    if (r.data) free(r.data);
}
#endif

// ============================================================
// GROUP FN — forall_negate  (for i in 1..N → array_dv of -real(i))
// ============================================================
#ifdef TEST_FORALL_NEGATE
extern "C" sisal_array_t func_MAIN_GPU(int32_t N);
static void test_forall_negate(void) {
    printf("\n=== Group FN: forall_negate (-real(i)) ===\n");
    // func_MAIN_GPU(4) → [-1.0, -2.0, -3.0, -4.0]
    sisal_array_t r = func_MAIN_GPU(4);
    float exp[] = {-1.0f, -2.0f, -3.0f, -4.0f};
    check("fn_size", (int32_t)r.size == 4);
    for (int i = 0; i < 4; i++) {
        char n[32]; snprintf(n, sizeof n, "fn[%d]", i);
        check(n, near_f(af(r, i), exp[i]));
    }
    if (r.data) free(r.data);
}
#endif

// ============================================================
// main — dispatches to the single active test group
// ============================================================

int main(void) {
    printf("=== dv_run_all test harness ===\n");

#ifdef TEST_ABS_DEMO
    test_abs_demo();
#endif
#ifdef TEST_AGREEMENT
    test_agreement();
#endif
#ifdef TEST_LIFTED_ARITH
    test_lifted_arith();
#endif
#ifdef TEST_SHL
    test_shl();
#endif
#ifdef TEST_TEST_SUBSET
    test_test_subset();
#endif
#ifdef TEST_INTRINSICS
    test_intrinsics();
#endif
#ifdef TEST_BROADCAST_COMPLEX
    test_broadcast_complex();
#endif
#ifdef TEST_COMPRESS
    test_compress();
#endif
#ifdef TEST_BROADCAST_NUMPY
    test_broadcast_numpy();
#endif
#ifdef TEST_FORALL_CPU
    test_forall_cpu();
#endif
#ifdef TEST_NEGATE_DV
    test_negate_dv();
#endif
#ifdef TEST_FORALL_BASIC_DV
    test_forall_basic_dv();
#endif
#ifdef TEST_FORALL_REDUCE_DV
    test_forall_reduce_dv();
#endif
#ifdef TEST_BULK_BASIC
    test_bulk_basic();
#endif
#ifdef TEST_INNERPRODUCT_DV
    test_innerproduct_dv();
#endif
#ifdef TEST_FOR_INITIAL
    test_for_initial();
#endif
#ifdef TEST_GAUSSJ_PARTS
    test_gaussj_parts();
#endif
#ifdef TEST_GAUSSJ
    test_gaussj();
#endif
#ifdef TEST_SWAPLOOP
    test_swaploop();
#endif
#ifdef TEST_GEN_EXTENT
    test_gen_extent();
#endif
#ifdef TEST_BROADCAST_PARTS
    test_broadcast_parts();
#endif
#ifdef TEST_IF_COND
    test_if_cond();
#endif
#ifdef TEST_FORALL_DV_SIMPLE
    test_forall_dv_simple();
#endif
#ifdef TEST_CROSS_DV_DEMO
    test_cross_dv_demo();
#endif
#ifdef TEST_FORALL_NEGATE
    test_forall_negate();
#endif

#if !defined(TEST_ABS_DEMO) && !defined(TEST_AGREEMENT) && !defined(TEST_LIFTED_ARITH) && \
    !defined(TEST_SHL) && !defined(TEST_TEST_SUBSET) && !defined(TEST_INTRINSICS) && \
    !defined(TEST_BROADCAST_COMPLEX) && !defined(TEST_COMPRESS) && !defined(TEST_BROADCAST_NUMPY) && \
    !defined(TEST_FORALL_CPU) && !defined(TEST_NEGATE_DV) && !defined(TEST_FORALL_BASIC_DV) && \
    !defined(TEST_FORALL_REDUCE_DV) && !defined(TEST_BULK_BASIC) && !defined(TEST_INNERPRODUCT_DV) && \
    !defined(TEST_FOR_INITIAL) && !defined(TEST_GAUSSJ_PARTS) && \
    !defined(TEST_GAUSSJ) && !defined(TEST_SWAPLOOP) && !defined(TEST_GEN_EXTENT) && \
    !defined(TEST_BROADCAST_PARTS) && !defined(TEST_IF_COND) && \
    !defined(TEST_FORALL_DV_SIMPLE) && !defined(TEST_CROSS_DV_DEMO) && \
    !defined(TEST_FORALL_NEGATE)
    printf("ERROR: No TEST_XXX macro defined.  Compile with e.g. -DTEST_ABS_DEMO\n");
    return 1;
#endif

    printf("\n--- Summary: %d passed, %d failed ---\n", g_pass, g_fail);
    return (g_fail > 0) ? 1 : 0;
}
