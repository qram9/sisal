// dv_run_all.cpp — Test harness for all 9 dv_*.sis generated C++ files.
//
// Compile with a -DTEST_XXX flag to select one group, e.g.:
//   clang++ -std=c++17 -I<runtime> -DTEST_ABS_DEMO dv_run_all.cpp
//   dv_abs_demo.cpp -o test_abs_demo
//
// See run_dv_tests.sh for the full build + run script.

#include <cmath>
#include <sisal_runtime.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "dv_rank8_slices_harness.h"


// ============================================================
// External declarations — one block per generated .cpp file.
// Only the block matching the active TEST_XXX guard is linked.
// ============================================================

#ifdef TEST_ABS_DEMO
extern "C" sisal_array_t func_DV_ABS_DEMO (sisal_array_t V);
#endif

#ifdef TEST_AGREEMENT
extern "C" sisal_array_t func_MAIN (sisal_array_t A,
                                    sisal_array_t B); // dv_agreement
#endif

#ifdef TEST_LIFTED_ARITH
extern "C" sisal_array_t func_MAIN (sisal_array_t A,
                                    sisal_array_t B); // dv_lifted_arith
#endif

#ifdef TEST_SHL
extern "C" sisal_array_t func_DV_SHL_SCALAR (sisal_array_t V, int32_t N);
#endif

#ifdef TEST_TEST_SUBSET
extern "C" sisal_array_t func_DV_ABS_REAL (sisal_array_t V);
extern "C" sisal_array_t func_DV_NEGATE_REAL (sisal_array_t V);
extern "C" sisal_array_t func_DV_SQRT_REAL (sisal_array_t V);
extern "C" sisal_array_t func_DV_SIN_REAL (sisal_array_t V);
extern "C" sisal_array_t func_DV_COS_REAL (sisal_array_t V);
extern "C" sisal_array_t func_DV_ADD_DV (sisal_array_t A, sisal_array_t B);
extern "C" sisal_array_t func_DV_MUL_SCALAR (sisal_array_t V, float S);
extern "C" sisal_array_t func_DV_ADD_SCALAR (sisal_array_t V, float S);
extern "C" sisal_array_t func_DV_GT_SCALAR (sisal_array_t V, float S);
extern "C" float func_DV_SUM_REAL (sisal_array_t V);
#endif

#ifdef TEST_INTRINSICS
extern "C" sisal_array_t func_DV_ABS_REAL (sisal_array_t V);
extern "C" sisal_array_t func_DV_SQRT_REAL (sisal_array_t V);
extern "C" sisal_array_t func_DV_SIN_REAL (sisal_array_t V);
extern "C" sisal_array_t func_DV_COS_REAL (sisal_array_t V);
extern "C" sisal_array_t func_DV_LOG_REAL (sisal_array_t V);
extern "C" sisal_array_t func_DV_FLOOR_REAL (sisal_array_t V);
extern "C" sisal_array_t func_DV_TRUNC_REAL (sisal_array_t V);
extern "C" sisal_array_t func_DV_ABS_DOUBLE (sisal_array_t V);
extern "C" sisal_array_t func_DV_SQRT_DOUBLE (sisal_array_t V);
extern "C" sisal_array_t func_DV_ADD_DV (sisal_array_t A, sisal_array_t B);
extern "C" sisal_array_t func_DV_SUB_DV (sisal_array_t A, sisal_array_t B);
extern "C" sisal_array_t func_DV_MUL_DV (sisal_array_t A, sisal_array_t B);
extern "C" sisal_array_t func_DV_DIV_DV (sisal_array_t A, sisal_array_t B);
extern "C" sisal_array_t func_SCALAR_ADD_DV (float S, sisal_array_t V);
extern "C" sisal_array_t func_DV_GT_SCALAR (sisal_array_t V, float S);
extern "C" sisal_array_t func_DV_EQ_DV (sisal_array_t A, sisal_array_t B);
extern "C" sisal_array_t func_DV_NE_DV (sisal_array_t A, sisal_array_t B);
extern "C" sisal_array_t func_DV_AND_DV (sisal_array_t A, sisal_array_t B);
extern "C" sisal_array_t func_DV_OR_DV (sisal_array_t A, sisal_array_t B);
extern "C" sisal_array_t func_DV_SHL_SCALAR (sisal_array_t V, int32_t N);
extern "C" sisal_array_t func_DV_SHR_SCALAR (sisal_array_t V, int32_t N);
extern "C" float func_DV_SUM_REAL (sisal_array_t V);
extern "C" float func_DV_PRODUCT_REAL (sisal_array_t V);
extern "C" float func_DV_LEAST_REAL (sisal_array_t V);
extern "C" float func_DV_GREATEST_REAL (sisal_array_t V);
extern "C" int32_t func_DV_SUM_INT (sisal_array_t V);
extern "C" int32_t func_DV_PRODUCT_INT (sisal_array_t V);
extern "C" int32_t func_DV_LEAST_INT (sisal_array_t V);
extern "C" int32_t func_DV_GREATEST_INT (sisal_array_t V);
#endif

#ifdef TEST_BROADCAST_COMPLEX
extern "C" sisal_array_t func_BROADCAST_VEC_MAT (sisal_array_t V,
                                                 sisal_array_t M);
extern "C" sisal_array_t func_BROADCAST_UNIT (sisal_array_t A,
                                              sisal_array_t B);
extern "C" sisal_array_t func_BROADCAST_SCALAR (double S, sisal_array_t M);
#endif

#ifdef TEST_COMPRESS
extern "C" sisal_array_t func_COMPRESS_MONOLITHIC (sisal_array_t MASK,
                                                   sisal_array_t A);
extern "C" sisal_array_t func_COMPRESS_DV_INPUT (int32_t N);
extern "C" int32_t func_COMPRESS_CHAIN (sisal_array_t MASK, sisal_array_t A);
#endif

#ifdef TEST_BROADCAST_NUMPY
extern "C" sisal_array_t func_MAIN (sisal_array_t A,
                                    sisal_array_t B); // dv_broadcast_numpy
#endif

#ifdef TEST_FORALL_CPU
extern "C" sisal_array_t func_MAIN_CPU (int32_t N);
#endif

#ifdef TEST_NEGATE_DV
extern "C" sisal_array_t func_NEGATE (sisal_array_t A);
#endif

#ifdef TEST_FORALL_BASIC_DV
extern "C" sisal_array_t func_FORALL_BASIC (int32_t N);
#endif

#ifdef TEST_FORALL_REDUCE_DV
extern "C" int32_t func_SUM_TO_N (int32_t N);
extern "C" int32_t func_PRODUCT_TO_N (int32_t N);
extern "C" int32_t func_MIN_TO_N (int32_t N);
extern "C" int32_t func_MAX_TO_N (int32_t N);
#endif

#ifdef TEST_NEWTON_RAPHSON
extern "C" float func_MAIN(float X, float Eps);
#endif

#ifdef TEST_FEO_FFT_PARTS1
struct FUNC_MAIN_results {
  int32_t res_0;
  double res_1;
  double res_2;
  sisal_array_t res_3;
  sisal_array_t res_4;
};
extern "C" struct FUNC_MAIN_results func_MAIN();
#endif

#ifdef TEST_FEO_FFT_PARTS2
struct FUNC_MAIN_results {
  sisal_array_t res_0;
  sisal_array_t res_1;
  sisal_array_t res_2;
  sisal_array_t res_3;
  sisal_array_t res_4;
  sisal_array_t res_5;
};
extern "C" struct FUNC_MAIN_results func_MAIN();
#endif

#ifdef TEST_SHAPED_GATHER_DV
struct FUNC_MAIN_results {
  sisal_array_t res_0;
  sisal_array_t res_1;
};
extern "C" struct FUNC_MAIN_results func_MAIN();
#endif

#ifdef TEST_FORINIT_MAT_GATHER_DV
extern "C" sisal_array_t func_MAIN();  // bare for-initial gather of rank-2 elems
#endif

#ifdef TEST_SCATTER_AT_DV
struct FUNC_MAIN_results {
  sisal_array_t res_0;
  sisal_array_t res_1;
};
extern "C" struct FUNC_MAIN_results func_MAIN();
#endif

#ifdef TEST_GROW_NEST_DV
extern "C" sisal_array_t func_MAIN();  // rank grows 1->2->3 inner nest to outer
#endif

#ifdef TEST_TRANSPOSE_AT_DV
extern "C" sisal_array_t func_MAIN(sisal_array_t A, int32_t n, int32_t m);
#endif

#ifdef TEST_FORALL_ROWSCATTER_DV
extern "C" sisal_array_t func_MAIN();
#endif

#ifdef TEST_SMOOTH_DV
extern "C" sisal_array_t func_MAIN(int32_t n);  // 3-D 3-point stencil, 3 passes
#endif

#ifdef TEST_DFT_DV
extern "C" sisal_array_t func_MAIN(int32_t N);  // DFT, complex_double records in array_dv
#endif

#ifdef TEST_RECORD_OPS_DV
struct FUNC_MAIN_results { int32_t r0, r1, r2, r3, r4, r5, r6; };
extern "C" struct FUNC_MAIN_results func_MAIN();
#endif

#ifdef TEST_FEO_FFT_PARTS3
struct FUNC_MAIN_results {
  sisal_array_t res_0;
  sisal_array_t res_1;
  sisal_array_t res_2;
  sisal_array_t res_3;
  sisal_array_t res_4;
  sisal_array_t res_5;
  sisal_array_t res_6;
  sisal_array_t res_7;
};
extern "C" struct FUNC_MAIN_results func_MAIN();
#endif

#ifdef TEST_FEO_FFT_PARTS4
struct FUNC_MAIN_results {
  int32_t res_0;
  int32_t res_1;
  int32_t res_2;
  sisal_array_t res_3;
  sisal_array_t res_4;
};
extern "C" struct FUNC_MAIN_results func_MAIN();
#endif

#ifdef TEST_FEO_FFT_DV
struct FUNC_MAIN_results {
  sisal_array_t res_0;
  sisal_array_t res_1;
};
extern "C" struct FUNC_MAIN_results func_MAIN(int32_t N);
#endif

#ifdef TEST_FEO_FFT
struct FUNC_MAIN_results {
  sisal_array_t res_0;
  sisal_array_t res_1;
};
extern "C" struct FUNC_MAIN_results func_MAIN(int32_t N);
#endif

#ifdef TEST_FOR_INITIAL
extern "C" int32_t func_FI_SUM (int32_t N);
extern "C" int32_t func_FI_PRODUCT (int32_t N);
extern "C" int32_t func_FI_FINAL_I (int32_t N);
extern "C" int32_t func_FI_PASSTHRU (int32_t N);
extern "C" int32_t func_FI_SWAP (int32_t N);
extern "C" int32_t func_FI_FIB (int32_t N);
extern "C" int32_t func_FI_FIB_A (int32_t N);
extern "C" sisal_array_t func_FI_PARAM_IDENTITY (int32_t N, sisal_array_t Ain);
extern "C" sisal_array_t func_FI_PARAM_BUMP (int32_t N, sisal_array_t Ain);
#endif

#ifdef TEST_INNERPRODUCT_DV
extern "C" sisal_array_t func_IP_F32 (sisal_array_t A, sisal_array_t B);
extern "C" sisal_array_t func_IP_I32 (sisal_array_t A, sisal_array_t B);
#endif

#ifdef TEST_MATMUL_DV
extern "C" sisal_array_t func_MAIN (sisal_array_t A, sisal_array_t B,
                                    int32_t N); // matmul_dv
#endif

#ifdef TEST_MATMUL_OP_DV
extern "C" sisal_array_t func_MM_F32 (sisal_array_t A, sisal_array_t B);
extern "C" sisal_array_t func_MM_I32 (sisal_array_t A, sisal_array_t B);
#endif


#ifdef TEST_FOR_INITIAL_DV
extern "C" sisal_array_t
func_MAIN (int32_t N); // for_initial_dv: array_dv loop-carry
#endif

// Simple scalar / control-flow / let cases (no arrays).
#ifdef TEST_THREE
extern "C" int32_t func_MAIN (); // constant 3
#endif
#ifdef TEST_FACT
extern "C" int32_t func_MAIN (int32_t N); // scalar recursion: n!
#endif
#ifdef TEST_IF_ONE
extern "C" int32_t func_MAIN (int32_t I, int32_t E); // if/else -> min
#endif
#ifdef TEST_IF_TWO
extern "C" int32_t func_MAIN (int32_t I, int32_t E); // if/elseif/else
#endif
#ifdef TEST_IF_ELSEIF
extern "C" int32_t func_MAIN (int32_t I, int32_t E,
                              int32_t F); // 3-var elseif chain
#endif
#ifdef TEST_RECORD_E2E
struct FUNC_MAIN_results { int32_t r0; float r1; };
extern "C" struct FUNC_MAIN_results func_MAIN ();
#endif
#ifdef TEST_TAGCASE_E2E
struct FUNC_MAIN_results { float r0; float r1; };
extern "C" struct FUNC_MAIN_results func_MAIN (int32_t SEL, float VAL);
#endif
#ifdef TEST_COMPLEX_FEATURES_E2E
extern "C" float func_MAIN (int32_t SEL, float VAL, int32_t SIZE);
#endif
#ifdef TEST_COMPLEX_OPS_E2E
struct FUNC_MAIN_results { float r0; float r1; float r2; float r3; float r4; float r5; };
extern "C" struct FUNC_MAIN_results func_MAIN (float re1, float im1, float re2, float im2);
#endif
#ifdef TEST_MR_TWO_SCALAR
extern "C" int32_t func_MAIN (int32_t A,
                              int32_t B); // let P,Q := Two2(a,b) -> P+Q
#endif
#ifdef TEST_LET_MULTI_BIND
extern "C" int32_t func_MAIN (); // parallel let -> 60
#endif
#ifdef TEST_LET_SEQ_BIND
extern "C" int32_t func_MAIN (); // sequential let -> 25
#endif
#ifdef TEST_XFA_B2_COND
extern "C" sisal_array_t func_MAIN (int32_t N,
                                    int32_t M); // if inside forall cross body
#endif
#ifdef TEST_AGGREGATE_ADD
extern "C" sisal_array_t
func_VECTORADD_CPU (sisal_array_t A, sisal_array_t B); // real vector add
#endif
#ifdef TEST_AREA
extern "C" float func_MAIN (float start, float finish,
                            int32_t gran); // Riemann sum of x^2+1
#endif
#ifdef TEST_MULTIDECL
struct MULTIDECL_results
{
  double res_0;
  int32_t res_1;
};
extern "C" struct MULTIDECL_results
func_MAIN (); // returns (double, integer) reordered
#endif
#ifdef TEST_LOOPCARRY_USED
extern "C" sisal_array_t
func_MAIN (int32_t N, sisal_array_t AIN); // double array_dv carry, x2/iter
#endif
#ifdef TEST_LOOPCARRY_IDENTITY
extern "C" sisal_array_t
func_MAIN (int32_t N, sisal_array_t AIN,
           sisal_array_t BIN); // parallel multi-carry, returns B
#endif
#ifdef TEST_SUB_2D
extern "C" int32_t func_MAIN (int32_t N); // build A[i,j]=i*10+j, read A[2,3]
#endif
#ifdef TEST_SUB_3D
extern "C" int32_t func_MAIN (int32_t N); // build A[i,j,k], read A[2,3,1]
#endif
#ifdef TEST_SLICE_DOTDOT
extern "C" sisal_array_t
func_MAIN (int32_t N); // A[2, ..] row slice (rank-reduce)
#endif
#ifdef TEST_TEST_MULTI_ARRAY_IF
struct MULTI_ARRAY_results
{
  sisal_array_t res_0;
  sisal_array_t res_1;
};
extern "C" struct MULTI_ARRAY_results
func_MAIN (int32_t N); // two array outputs, if-in-body
#endif
#ifdef TEST_SUB_2D_DIAG
extern "C" int32_t func_MAIN (int32_t N); // A[1,1]+A[2,2]+A[3,3]
#endif
#ifdef TEST_LET_NESTED_SEQ
extern "C" int32_t func_MAIN (); // nested lets -> 25
#endif
#ifdef TEST_FORTY2
extern "C" int32_t func_MAIN (int32_t X, int32_t Y,
                              int32_t Z); // if/elseif with arithmetic
#endif
#ifdef TEST_XFA_B1_DECLDEF
extern "C" sisal_array_t func_MAIN (int32_t N,
                                    int32_t M); // cross i*j via body decldef
#endif
#ifdef TEST_XFA_C3_3AXIS
extern "C" sisal_array_t func_MAIN (int32_t A, int32_t B,
                                    int32_t C); // rank-3 cross i*j*k
#endif
#ifdef TEST_SLICE_STORE
extern "C" sisal_array_t
func_MAIN (int32_t N); // A[2, .. : Z] write-side slice
#endif
#ifdef TEST_MR_TWO_ARRAY
extern "C" sisal_array_t
func_MAIN (int32_t N, sisal_array_t A); // multi-array destructure -> P
#endif
#ifdef TEST_AA
extern "C" sisal_array_t func_DVFILL (int32_t LO, int32_t HI,
                                      int32_t V); // array_dv fill
#endif
#ifdef TEST_SUB_MATMUL
extern "C" int32_t
func_MAIN (int32_t N); // matmul via 2-D subscripts, read C[1,1]
#endif
#ifdef TEST_PI
extern "C" float func_MAIN (int32_t Cycles); // Leibniz pi (for-initial) * 4
#endif
#ifdef TEST_TEST_MIX_ARRAY_DV
struct MIX_ARRAY_DV_results
{
  sisal_array_t res_0;
  sisal_array_t res_1;
};
extern "C" struct MIX_ARRAY_DV_results
func_MAIN (int32_t N); // (array of i, array_dv of i*10)
#endif
#ifdef TEST_TST_LOOP1_DV
extern "C" sisal_array_t func_MAIN (int32_t N, double Q, double R, double T,
                                    sisal_array_t Y,
                                    sisal_array_t Z); // for K in Y -> K+K
#endif
#ifdef TEST_LOOP2_INNER
extern "C" sisal_array_t
func_MAIN (int32_t IPNT, int32_t IPNTP, sisal_array_t V,
           sisal_array_t X); // loop2 inner for-initial
#endif

// ---- Livermore loop kernels (array_dv), each vs an independent C reference
// ----
#ifdef TEST_LOOP1_DV
extern "C" sisal_array_t func_MAIN (int32_t REP, int32_t N, double Q, double R,
                                    double T, sisal_array_t Y,
                                    sisal_array_t Z); // hydro fragment
#endif
#ifdef TEST_LOOP3_DV
extern "C" double func_MAIN (int32_t REP, int32_t N, sisal_array_t X,
                             sisal_array_t Z); // inner product
#endif
#ifdef TEST_LOOP7_DV
extern "C" sisal_array_t func_MAIN (int32_t REP, int32_t N, double R, double T,
                                    sisal_array_t U, sisal_array_t Y,
                                    sisal_array_t Z); // equation of state
#endif
#ifdef TEST_LOOP12_DV
extern "C" sisal_array_t func_MAIN (int32_t REP, int32_t N,
                                    sisal_array_t YIN); // first difference
#endif
#ifdef TEST_LOOP24_DV
extern "C" int32_t func_MAIN (int32_t REP, int32_t N,
                              sisal_array_t X); // location of first minimum
#endif
#ifdef TEST_LOOP9_DV
extern "C" sisal_array_t
func_MAIN (int32_t REP, int32_t N, double CO, double DM22, double DM23,
           double DM24, double DM25, double DM26, double DM27, double DM28,
           sisal_array_t PXIN); // integrate predictors
#endif
#ifdef TEST_LOOP10_DV
extern "C" sisal_array_t
func_MAIN (int32_t REP, int32_t N, sisal_array_t CX,
           sisal_array_t PXIN); // difference predictors
#endif
#ifdef TEST_LOOP19S_DV
struct FUNC_MAIN_results
{
  sisal_array_t res_0;
  double res_1;
};
extern "C" struct FUNC_MAIN_results func_MAIN (int32_t REP, int32_t N,
                                               double STB5IN, sisal_array_t SA,
                                               sisal_array_t SB);
#endif
#ifdef TEST_LOOP18P_DV
struct FUNC_MAIN_results
{
  sisal_array_t res_0;
  sisal_array_t res_1;
};
extern "C" struct FUNC_MAIN_results func_MAIN (int32_t REP, int32_t N, double S, double T,
                                               sisal_array_t ZAIN, sisal_array_t ZBIN, sisal_array_t ZM,
                                               sisal_array_t ZP, sisal_array_t ZQ, sisal_array_t ZRIN,
                                               sisal_array_t ZUIN, sisal_array_t ZVIN, sisal_array_t ZZIN);
#endif
#ifdef TEST_LOOP8P_DV
struct FUNC_MAIN_results
{
  sisal_array_t res_0;
  sisal_array_t res_1;
  sisal_array_t res_2;
};
extern "C" struct FUNC_MAIN_results func_MAIN (int32_t REP, int32_t N,
                                               double A11, double A12, double A13,
                                               double A21, double A22, double A23,
                                               double A31, double A32, double A33,
                                               double SIG,
                                               sisal_array_t U1IN, sisal_array_t U2IN, sisal_array_t U3IN);
#endif
#ifdef TEST_LOOP14_DV
struct FUNC_MAIN_results
{
  sisal_array_t res_0;
  sisal_array_t res_1;
  sisal_array_t res_2;
  sisal_array_t res_3;
  sisal_array_t res_4;
  sisal_array_t res_5;
  sisal_array_t res_6;
  sisal_array_t res_7;
  sisal_array_t res_8;
};
extern "C" struct FUNC_MAIN_results
func_MAIN (int32_t REP, int32_t N, double FLX, sisal_array_t DEX,
           sisal_array_t EX, sisal_array_t GRD, sisal_array_t RHIN);
#endif
#ifdef TEST_LOOP21_DV
extern "C" sisal_array_t func_MAIN (int32_t REP, int32_t N, sisal_array_t CX,
                                    sisal_array_t PXIN,
                                    sisal_array_t VY); // matrix*matrix product
#endif
#ifdef TEST_LOOP23S_DV
extern "C" sisal_array_t func_MAIN (int32_t REP, int32_t N, sisal_array_t ZAIN,
                                    sisal_array_t ZB, sisal_array_t ZR,
                                    sisal_array_t ZU, sisal_array_t ZV,
                                    sisal_array_t ZZ);
#endif
#ifdef TEST_LOOP2_DV
extern "C" sisal_array_t func_MAIN (int32_t REP, int32_t N, sisal_array_t V,
                                    sisal_array_t XIN); // ICCG excerpt
#endif
#ifdef TEST_LOOP2S_DV
extern "C" sisal_array_t
func_MAIN (int32_t REP, int32_t N, sisal_array_t V,
           sisal_array_t XIN); // ICCG excerpt (s-form)
#endif
#ifdef TEST_MR2_INIT
struct MR2_results
{
  sisal_array_t res_0;
  sisal_array_t res_1;
};
extern "C" struct MR2_results
func_MAIN (int32_t N); // for-initial returning TWO array_dv carries
#endif
#ifdef TEST_LOOP16_DV
struct LOOP16_results
{
  int32_t res_0;
  int32_t res_1;
};
extern "C" struct LOOP16_results
func_MAIN (int32_t REP, int32_t N, double R, double S, double T,
           sisal_array_t D, sisal_array_t PLAN,
           sisal_array_t ZONE); // Monte Carlo search (v1,v2)
#endif
#ifdef TEST_LOOP13_DV
struct LOOP13_results
{
  sisal_array_t res_0;
  sisal_array_t res_1;
};
extern "C" struct LOOP13_results
func_MAIN (int32_t REP, int32_t N, sisal_array_t E, sisal_array_t F,
           sisal_array_t B, sisal_array_t C, sisal_array_t HIN,
           sisal_array_t PIN, sisal_array_t Y,
           sisal_array_t Z); // 2-D PIC -> (H,P)
#endif
#ifdef TEST_LOOP5_DV
extern "C" sisal_array_t
func_MAIN (int32_t REP, int32_t N, sisal_array_t XIN, sisal_array_t Y,
           sisal_array_t Z); // tridiagonal: for-initial `array of X` gather
#endif
#ifdef TEST_LOOP11S_DV
extern "C" sisal_array_t
func_MAIN (int32_t REP, int32_t N,
           sisal_array_t YIN); // first-sum (prefix sum): for-initial gather
#endif
#ifdef TEST_LOOP17_DV
struct LOOP17_results
{
  sisal_array_t res_0;
  sisal_array_t res_1;
  sisal_array_t res_2;
};
extern "C" struct LOOP17_results
func_MAIN (int32_t REP, int32_t N, sisal_array_t VLIN, sisal_array_t VLR,
           sisal_array_t VSP, sisal_array_t VSTP,
           sisal_array_t VXNEIN); // descending for-initial, 3 gathers
#endif
#ifdef TEST_LOOP15_DV
struct LOOP15_results
{
  sisal_array_t res_0;
  sisal_array_t res_1;
};
extern "C" struct LOOP15_results
func_MAIN (int32_t REP, int32_t N, sisal_array_t VF, sisal_array_t VG,
           sisal_array_t VH); // nested forall + addh/fill -> (VS,VYc)
#endif
#ifdef TEST_LOOP22_DV
struct LOOP22_results
{
  sisal_array_t res_0;
  sisal_array_t res_1;
};
extern "C" struct LOOP22_results
func_MAIN (int32_t REP, int32_t N, sisal_array_t U, sisal_array_t V,
           sisal_array_t X); // Planckian -> (W,Y)
#endif
#ifdef TEST_BUILDFILL_DV
extern "C" sisal_array_t
func_MAIN (int32_t N); // empty array_dv build + array_fill keep-last
#endif
#ifdef TEST_LOOP20_DV
struct LOOP20_results
{
  sisal_array_t res_0;
  sisal_array_t res_1;
};
extern "C" struct LOOP20_results func_MAIN (
    int32_t REP, int32_t N, double DK, double S, double T, sisal_array_t XXIN,
    sisal_array_t G, sisal_array_t U, sisal_array_t V, sisal_array_t VX,
    sisal_array_t W, sisal_array_t Y,
    sisal_array_t Z); // for-initial recurrence + gather -> (Xgather, XX)
#endif
/* ---- language-feature regression tests (capture / multi-rank / multi-output) ---- */
#ifdef TEST_CAP_NESTED_DV
extern "C" int32_t func_MAIN();  // free-var capture, nested lets 3 deep
#endif
#ifdef TEST_CAP_ARRAY_DV
extern "C" sisal_array_t func_MAIN(sisal_array_t A);  // grab arrays + multi-bind nested -> forall
#endif
#ifdef TEST_CAP_FORINIT_DV
extern "C" int32_t func_MAIN(sisal_array_t A);  // grab array into for-initial RHS
#endif
#ifdef TEST_MR_FORALL_DV
struct MRFA_results { int32_t res_0; sisal_array_t res_1; };
extern "C" struct MRFA_results func_MAIN();  // forall (scalar, 1-D)
#endif
#ifdef TEST_MR_FORINIT_DV
struct MRFI_results { int32_t res_0; sisal_array_t res_1; };
extern "C" struct MRFI_results func_MAIN();  // for-initial (scalar, 1-D gather)
#endif
#ifdef TEST_MR_1D2D_DV
struct MR12_results { sisal_array_t res_0; sisal_array_t res_1; };
extern "C" struct MR12_results func_MAIN();  // forall (1-D, 2-D)
#endif
#ifdef TEST_FN_MULTIOUT_DV
struct FNMO_results { int32_t res_0; sisal_array_t res_1; };
extern "C" struct FNMO_results func_MAIN();  // function multi-output (scalar, array)
#endif
#ifdef TEST_IF_MULTIOUT_DV
struct IFMO_results { int32_t res_0; int32_t res_1; };
extern "C" struct IFMO_results func_MAIN(int32_t c);  // if-expression multi-output
#endif
#ifdef TEST_FNCALL_FORALL_DV
extern "C" sisal_array_t func_MAIN();  // multi-output fn called inside a forall
#endif
#ifdef TEST_NESTED_FORALL_DV
extern "C" sisal_array_t func_MAIN();  // nested forall -> 2-D
#endif
#ifdef TEST_CAP_2DEEP_DV
extern "C" sisal_array_t func_MAIN();  // capture across two nested foralls -> 2-D
#endif
#ifdef TEST_FN3RANK_DV
struct FN3_results { int32_t res_0; sisal_array_t res_1; sisal_array_t res_2; };
extern "C" struct FN3_results func_MAIN();  // function: 3 mixed-rank outputs
#endif
#ifdef TEST_IFTUPLE_FORALL_DV
extern "C" sisal_array_t func_MAIN();  // if-tuple inside a forall
#endif
#ifdef TEST_RED_RANKS_DV
struct RRK_results { sisal_array_t res_0; int32_t res_1; sisal_array_t res_2; };
extern "C" struct RRK_results func_MAIN();  // nested reduce/gather -> ranks 1, 0, 2
#endif
#ifdef TEST_RED_OPS_DV
struct ROP_results { sisal_array_t res_0; sisal_array_t res_1; sisal_array_t res_2; };
extern "C" struct ROP_results func_MAIN();  // product / greatest / least, gathered (rank 1)
#endif
#ifdef TEST_RED_ARR_DV
struct RAR_results { sisal_array_t s; sisal_array_t p; sisal_array_t g; sisal_array_t l; sisal_array_t m; };
extern "C" struct RAR_results func_MAIN();  // array-VALUED reductions (elementwise), 1-D + 2-D
#endif
#ifdef TEST_IP_DV
extern "C" sisal_array_t func_MAIN(sisal_array_t A, sisal_array_t B);  // rank-poly innerproduct
static sisal_array_t mk_dvi(int rank, int d0, int d1, int d2, const int32_t* v) {
    int n = (rank==3)? d0*d1*d2 : (rank==2)? d0*d1 : d0;
    sisal_array_t a = sisal_array_alloc_empty(rank, 6, (uint64_t)n);
    a.dims[0]=d0; if(rank>=2)a.dims[1]=d1; if(rank>=3)a.dims[2]=d2;
    for (int i=0;i<n;i++) ((int32_t*)a.data)[i]=v[i];
    return a;
}
static bool dvi_eq(sisal_array_t r, int rank, int d0, int d1, const int32_t* exp, int n) {
    if (r.rank!=rank || (int)r.dims[0]!=d0) return false;
    if (rank>=2 && (int)r.dims[1]!=d1) return false;
    if ((int)r.size!=n) return false;
    for (int k=0;k<n;k++) if (((int32_t*)r.data)[k] != exp[k]) return false;
    return true;
}
#endif
#ifdef TEST_CONV_DV
extern "C" sisal_array_t func_MAIN(int32_t M, int32_t Cycles);  // convolution Y[i]=Σ_j A[j]*X[i+j-1]
#endif
#ifdef TEST_LAPLACE_DV
extern "C" sisal_array_t func_MAIN(int32_t Num, int32_t Rows, int32_t Cols);  // Laplace relaxation -> flat 2-D grid
#endif
#if defined(TEST_BCAST3D_DV) || defined(TEST_BCAST31_DV)
extern "C" sisal_array_t func_MAIN(sisal_array_t A, sisal_array_t B);  // rank-poly A + B
// build a rank-1/2/3 double array_dv with explicit dims (numpy-style row-major)
static sisal_array_t mk_dv3(int rank, int d0, int d1, int d2, const double* v) {
    int n = (rank==3)? d0*d1*d2 : (rank==2)? d0*d1 : d0;
    sisal_array_t a = sisal_array_alloc_empty(rank, 4, (uint64_t)n);
    a.dims[0]=d0; if(rank>=2)a.dims[1]=d1; if(rank>=3)a.dims[2]=d2;
    for (int i=0;i<n;i++) ((double*)a.data)[i]=v[i];
    return a;
}
static bool dv_eq(sisal_array_t r, int rank, int d0, int d1, int d2, const double* exp, int n) {
    if (r.rank!=rank || (int)r.dims[0]!=d0) return false;
    if (rank>=2 && (int)r.dims[1]!=d1) return false;
    if (rank>=3 && (int)r.dims[2]!=d2) return false;
    if ((int)r.size!=n) return false;
    for (int k=0;k<n;k++) if (!(fabs(((double*)r.data)[k] - exp[k]) < 1e-9)) return false;
    return true;
}
#endif
#ifdef TEST_LOOP6_DV
extern "C" sisal_array_t
func_MAIN (int32_t REP, int32_t N, sisal_array_t B,
           sisal_array_t WIN); // general linear recurrence
#endif
#ifdef TEST_LOOP4_DV
extern "C" sisal_array_t
func_MAIN (int32_t REP, int32_t N, sisal_array_t XIN,
           sisal_array_t Y); // banded linear equations
#endif

// Scatter-axis generators over array params (element var renamed off the array
// name to avoid the case-insensitive self-shadow; see forall_rebuild_note.md).
#ifdef TEST_FORALL_DV_AT
extern "C" sisal_array_t func_MAIN (sisal_array_t A); // for x in A at i -> x+i
#endif
#ifdef TEST_FORALL_DV_CROSS
extern "C" sisal_array_t func_MAIN (sisal_array_t A,
                                    sisal_array_t B); // x cross y -> x*y
#endif
#ifdef TEST_FORALL_DV_DOT
extern "C" sisal_array_t func_MAIN (sisal_array_t A,
                                    sisal_array_t B); // x dot y -> x+y
#endif
#ifdef TEST_FORALL_DV_DOT3
extern "C" sisal_array_t func_MAIN (sisal_array_t A, sisal_array_t B,
                                    sisal_array_t C); // x dot y dot z -> x+y+z
#endif

// Scalar forall reductions (red_*.sis): each folds a forall body to one
// integer.
#ifdef TEST_RED_SUM
extern "C" int32_t func_MAIN (int32_t N); // value of sum i
#endif
#ifdef TEST_RED_PRODUCT
extern "C" int32_t func_MAIN (int32_t N); // value of product i
#endif
#ifdef TEST_RED_GREATEST
extern "C" int32_t func_MAIN (int32_t N); // value of greatest i*(N+1-i)
#endif
#ifdef TEST_RED_LEAST
extern "C" int32_t func_MAIN (int32_t N); // value of least (i-3)*(i-3)
#endif
#ifdef TEST_RED_ARGMAX
extern "C" int32_t func_MAIN (int32_t N); // value of argmax i*(N+1-i)
#endif
#ifdef TEST_RED_ARGMIN
extern "C" int32_t func_MAIN (int32_t N); // value of argmin i*i-6*i
#endif
#ifdef TEST_RED_SUM_CROSS
extern "C" int32_t func_MAIN (int32_t N,
                              int32_t M); // value of sum i*j over i cross j
#endif

#ifdef TEST_BULK_BASIC
extern "C" sisal_array_t func_T_ARR_ADD (sisal_array_t A, sisal_array_t B);
extern "C" sisal_array_t func_T_ARR_SUB (sisal_array_t A, sisal_array_t B);
extern "C" sisal_array_t func_T_ARR_MUL (sisal_array_t A, sisal_array_t B);
extern "C" sisal_array_t func_T_ARR_NEG (sisal_array_t A);
extern "C" sisal_array_t func_T_ARR_EQ (sisal_array_t A, sisal_array_t B);
extern "C" sisal_array_t func_T_ARR_LT (sisal_array_t A, sisal_array_t B);
extern "C" sisal_array_t func_T_ARR_ADD_SCALAR (sisal_array_t A, int32_t N);
extern "C" sisal_array_t func_T_ARR_MUL_SCALAR (sisal_array_t A, int32_t N);
extern "C" int32_t func_T_SUM (sisal_array_t A);
extern "C" int32_t func_T_PRODUCT (sisal_array_t A);
extern "C" int32_t func_T_LEAST (sisal_array_t A);
extern "C" int32_t func_T_GREATEST (sisal_array_t A);
extern "C" sisal_array_t func_T_COMPRESS (sisal_array_t MASK, sisal_array_t A);
extern "C" sisal_array_t func_T_SORT (sisal_array_t A);
extern "C" sisal_array_t func_T_REVERSE (sisal_array_t A);
#endif

// ============================================================
// Pass/fail accounting
// ============================================================

static int g_pass = 0;
static int g_fail = 0;

static void
check (const char *name, bool cond)
{
  if (cond)
    {
      printf ("  PASS  %s\n", name);
      g_pass++;
    }
  else
    {
      printf ("  FAIL  %s\n", name);
      g_fail++;
    }
}

// ============================================================
// Approximate equality
// ============================================================

static inline bool
near_f (float a, float b)
{
  return fabsf (a - b) < 1e-4f;
}
static inline bool
near_d (double a, double b)
{
  return fabs (a - b) < 1e-9;
}

// ============================================================
// Array constructors
//
// sisal_array_alloc_empty sets lower_bound = 1.
// The generated code iterates indices starting at lower_bound and
// accesses data[idx - lower_bound], so lb=1 is required for input
// arrays too.  We replicate that here.
// ============================================================

static sisal_array_t
make_float_arr (const float *data, int n)
{
  sisal_array_t a = sisal_array_alloc_empty (1, 8, (uint64_t)n);
  // lower_bound already set to 1 by alloc_empty
  memcpy (a.data, data, (size_t)n * sizeof (float));
  return a;
}

static sisal_array_t
make_double_arr (const double *data, int n)
{
  sisal_array_t a = sisal_array_alloc_empty (1, 4, (uint64_t)n);
  memcpy (a.data, data, (size_t)n * sizeof (double));
  return a;
}

static sisal_array_t
make_int_arr (const int32_t *data, int n)
{
  sisal_array_t a = sisal_array_alloc_empty (1, 6, (uint64_t)n);
  memcpy (a.data, data, (size_t)n * sizeof (int32_t));
  return a;
}

static sisal_array_t
make_bool_arr (const bool *data, int n)
{
  sisal_array_t a = sisal_array_alloc_empty (1, 1, (uint64_t)n);
  memcpy (a.data, data, (size_t)n * sizeof (bool));
  return a;
}

// 2D row-major arrays.  After alloc_empty (which sets dims[0]=size for
// rank==1), we overwrite dims[0]/dims[1] for rank==2.
static sisal_array_t
make_float_2d (const float *data, int rows, int cols)
{
  int n = rows * cols;
  sisal_array_t a = sisal_array_alloc_empty (2, 8, (uint64_t)n);
  a.dims[0] = rows;
  a.dims[1] = cols;
  memcpy (a.data, data, (size_t)n * sizeof (float));
  return a;
}

static sisal_array_t
make_double_2d (const double *data, int rows, int cols)
{
  int n = rows * cols;
  sisal_array_t a = sisal_array_alloc_empty (2, 4, (uint64_t)n);
  a.dims[0] = rows;
  a.dims[1] = cols;
  memcpy (a.data, data, (size_t)n * sizeof (double));
  return a;
}

static sisal_array_t
make_double_2d_lb (const double *data, int rows, int cols, int lb0, int lb1)
{
  int n = rows * cols;
  sisal_array_t a = sisal_array_alloc_empty (2, 4, (uint64_t)n);
  a.dims[0] = rows;
  a.dims[1] = cols;
  a.lower_bound[0] = lb0;
  a.lower_bound[1] = lb1;
  memcpy (a.data, data, (size_t)n * sizeof (double));
  return a;
}static sisal_array_t
make_double_3d_lb (const double *data, int d0, int d1, int d2, int lb0, int lb1, int lb2)
{
  int n = d0 * d1 * d2;
  sisal_array_t a = sisal_array_alloc_empty (3, 4, (uint64_t)n);
  a.dims[0] = d0;
  a.dims[1] = d1;
  a.dims[2] = d2;
  a.lower_bound[0] = lb0;
  a.lower_bound[1] = lb1;
  a.lower_bound[2] = lb2;
  memcpy (a.data, data, (size_t)n * sizeof (double));
  return a;
}

static sisal_array_t
make_int_2d (const int32_t *data, int rows, int cols)
{
  int n = rows * cols;
  sisal_array_t a = sisal_array_alloc_empty (2, 6, (uint64_t)n);
  a.dims[0] = rows;
  a.dims[1] = cols;
  memcpy (a.data, data, (size_t)n * sizeof (int32_t));
  return a;
}

// ============================================================
// Accessors for result arrays
// ============================================================

static inline float
af (sisal_array_t a, int i)
{
  return ((float *)a.data)[i];
}
static inline double
ad (sisal_array_t a, int i)
{
  return ((double *)a.data)[i];
}
static inline int32_t
ai (sisal_array_t a, int i)
{
  return ((int32_t *)a.data)[i];
}
static inline bool
ab (sisal_array_t a, int i)
{
  return ((bool *)a.data)[i];
}

// ============================================================
// GROUP A — dv_abs_demo
// ============================================================

#ifdef TEST_ABS_DEMO
static void
test_abs_demo (void)
{
  printf ("\n=== Group A: dv_abs_demo ===\n");
  float inp[] = { -1.5f, 2.5f, -3.5f };
  float exp[] = { 1.5f, 2.5f, 3.5f };
  sisal_array_t v = make_float_arr (inp, 3);
  sisal_array_t r = func_DV_ABS_DEMO (v);
  check ("abs_demo[0]", near_f (af (r, 0), exp[0]));
  check ("abs_demo[1]", near_f (af (r, 1), exp[1]));
  check ("abs_demo[2]", near_f (af (r, 2), exp[2]));
  free (v.data);
  free (r.data);
}
#endif

// ============================================================
// GROUP B — dv_agreement  (func_MAIN: int32 + int32 → int32)
// ============================================================

#ifdef TEST_AGREEMENT
static void
test_agreement (void)
{
  printf ("\n=== Group B: dv_agreement ===\n");
  int32_t a[] = { 1, 2, 3 };
  int32_t b[] = { 10, 20, 30 };
  int32_t ex[] = { 11, 22, 33 };
  sisal_array_t va = make_int_arr (a, 3);
  sisal_array_t vb = make_int_arr (b, 3);
  sisal_array_t r = func_MAIN (va, vb);
  check ("agreement[0]", ai (r, 0) == ex[0]);
  check ("agreement[1]", ai (r, 1) == ex[1]);
  check ("agreement[2]", ai (r, 2) == ex[2]);
  free (va.data);
  free (vb.data);
  free (r.data);
}
#endif

// ============================================================
// GROUP C — dv_lifted_arith  (func_MAIN: double A*B+A)
// ============================================================

#ifdef TEST_LIFTED_ARITH
static void
test_lifted_arith (void)
{
  printf ("\n=== Group C: dv_lifted_arith ===\n");
  double a[] = { 1.0, 2.0, 3.0 };
  double b[] = { 10.0, 20.0, 30.0 };
  // A*B+A = [1*10+1, 2*20+2, 3*30+3] = [11, 42, 93]
  double ex[] = { 11.0, 42.0, 93.0 };
  sisal_array_t va = make_double_arr (a, 3);
  sisal_array_t vb = make_double_arr (b, 3);
  sisal_array_t r = func_MAIN (va, vb);
  check ("lifted_arith[0]", near_d (ad (r, 0), ex[0]));
  check ("lifted_arith[1]", near_d (ad (r, 1), ex[1]));
  check ("lifted_arith[2]", near_d (ad (r, 2), ex[2]));
  free (va.data);
  free (vb.data);
  free (r.data);
}
#endif

// ============================================================
// GROUP D — dv_shl  (int32 << N)
// ============================================================

#ifdef TEST_SHL
static void
test_shl (void)
{
  printf ("\n=== Group D: dv_shl ===\n");
  int32_t v[] = { 1, 2, 4 };
  int32_t ex[] = { 4, 8, 16 };
  sisal_array_t vv = make_int_arr (v, 3);
  sisal_array_t r = func_DV_SHL_SCALAR (vv, 2);
  check ("shl[0]", ai (r, 0) == ex[0]);
  check ("shl[1]", ai (r, 1) == ex[1]);
  check ("shl[2]", ai (r, 2) == ex[2]);
  free (vv.data);
  free (r.data);
}
#endif

// ============================================================
// GROUP E — dv_test_subset
// ============================================================

#ifdef TEST_TEST_SUBSET
static void
test_test_subset (void)
{
  printf ("\n=== Group E: dv_test_subset ===\n");

  // abs([-1,2,-3]) → [1,2,3]
  {
    float inp[] = { -1.f, 2.f, -3.f };
    sisal_array_t v = make_float_arr (inp, 3);
    sisal_array_t r = func_DV_ABS_REAL (v);
    check ("ts_abs[0]", near_f (af (r, 0), 1.f));
    check ("ts_abs[1]", near_f (af (r, 1), 2.f));
    check ("ts_abs[2]", near_f (af (r, 2), 3.f));
    free (v.data);
    free (r.data);
  }

  // negate([1,-2,3]) → [-1,2,-3]
  {
    float inp[] = { 1.f, -2.f, 3.f };
    sisal_array_t v = make_float_arr (inp, 3);
    sisal_array_t r = func_DV_NEGATE_REAL (v);
    check ("ts_negate[0]", near_f (af (r, 0), -1.f));
    check ("ts_negate[1]", near_f (af (r, 1), 2.f));
    check ("ts_negate[2]", near_f (af (r, 2), -3.f));
    free (v.data);
    free (r.data);
  }

  // sqrt([1,4,9]) → [1,2,3]
  {
    float inp[] = { 1.f, 4.f, 9.f };
    sisal_array_t v = make_float_arr (inp, 3);
    sisal_array_t r = func_DV_SQRT_REAL (v);
    check ("ts_sqrt[0]", near_f (af (r, 0), 1.f));
    check ("ts_sqrt[1]", near_f (af (r, 1), 2.f));
    check ("ts_sqrt[2]", near_f (af (r, 2), 3.f));
    free (v.data);
    free (r.data);
  }

  // sin([0]) → [0]
  {
    float inp[] = { 0.f };
    sisal_array_t v = make_float_arr (inp, 1);
    sisal_array_t r = func_DV_SIN_REAL (v);
    check ("ts_sin[0]", near_f (af (r, 0), 0.f));
    free (v.data);
    free (r.data);
  }

  // cos([0]) → [1]
  {
    float inp[] = { 0.f };
    sisal_array_t v = make_float_arr (inp, 1);
    sisal_array_t r = func_DV_COS_REAL (v);
    check ("ts_cos[0]", near_f (af (r, 0), 1.f));
    free (v.data);
    free (r.data);
  }

  // add_dv([1,2],[3,4]) → [4,6]
  {
    float a[] = { 1.f, 2.f };
    float b[] = { 3.f, 4.f };
    sisal_array_t va = make_float_arr (a, 2);
    sisal_array_t vb = make_float_arr (b, 2);
    sisal_array_t r = func_DV_ADD_DV (va, vb);
    check ("ts_add_dv[0]", near_f (af (r, 0), 4.f));
    check ("ts_add_dv[1]", near_f (af (r, 1), 6.f));
    free (va.data);
    free (vb.data);
    free (r.data);
  }

  // mul_scalar([2,3,4], 10) → [20,30,40]
  {
    float inp[] = { 2.f, 3.f, 4.f };
    sisal_array_t v = make_float_arr (inp, 3);
    sisal_array_t r = func_DV_MUL_SCALAR (v, 10.f);
    check ("ts_mul_scalar[0]", near_f (af (r, 0), 20.f));
    check ("ts_mul_scalar[1]", near_f (af (r, 1), 30.f));
    check ("ts_mul_scalar[2]", near_f (af (r, 2), 40.f));
    free (v.data);
    free (r.data);
  }

  // add_scalar([1,2,3], 10) → [11,12,13]
  {
    float inp[] = { 1.f, 2.f, 3.f };
    sisal_array_t v = make_float_arr (inp, 3);
    sisal_array_t r = func_DV_ADD_SCALAR (v, 10.f);
    check ("ts_add_scalar[0]", near_f (af (r, 0), 11.f));
    check ("ts_add_scalar[1]", near_f (af (r, 1), 12.f));
    check ("ts_add_scalar[2]", near_f (af (r, 2), 13.f));
    free (v.data);
    free (r.data);
  }

  // gt_scalar([1,5,3], 2) → [false,true,true]
  {
    float inp[] = { 1.f, 5.f, 3.f };
    sisal_array_t v = make_float_arr (inp, 3);
    sisal_array_t r = func_DV_GT_SCALAR (v, 2.f);
    check ("ts_gt_scalar[0]", ab (r, 0) == false);
    check ("ts_gt_scalar[1]", ab (r, 1) == true);
    check ("ts_gt_scalar[2]", ab (r, 2) == true);
    free (v.data);
    free (r.data);
  }

  // sum_real([1,2,3,4]) → 10
  {
    float inp[] = { 1.f, 2.f, 3.f, 4.f };
    sisal_array_t v = make_float_arr (inp, 4);
    float s = func_DV_SUM_REAL (v);
    check ("ts_sum_real", near_f (s, 10.f));
    free (v.data);
  }
}
#endif

// ============================================================
// GROUP F — dv_intrinsics (representative subset)
// ============================================================

#ifdef TEST_INTRINSICS
static void
test_intrinsics (void)
{
  printf ("\n=== Group F: dv_intrinsics ===\n");

  // dv_abs_real([-1,2,-3]) → [1,2,3]
  {
    float inp[] = { -1.f, 2.f, -3.f };
    sisal_array_t v = make_float_arr (inp, 3);
    sisal_array_t r = func_DV_ABS_REAL (v);
    check ("intr_abs_real[0]", near_f (af (r, 0), 1.f));
    check ("intr_abs_real[1]", near_f (af (r, 1), 2.f));
    check ("intr_abs_real[2]", near_f (af (r, 2), 3.f));
    free (v.data);
    free (r.data);
  }

  // dv_sqrt_real([1,4,9]) → [1,2,3]
  {
    float inp[] = { 1.f, 4.f, 9.f };
    sisal_array_t v = make_float_arr (inp, 3);
    sisal_array_t r = func_DV_SQRT_REAL (v);
    check ("intr_sqrt_real[0]", near_f (af (r, 0), 1.f));
    check ("intr_sqrt_real[1]", near_f (af (r, 1), 2.f));
    check ("intr_sqrt_real[2]", near_f (af (r, 2), 3.f));
    free (v.data);
    free (r.data);
  }

  // dv_sin_real([0]) → [0]
  {
    float inp[] = { 0.f };
    sisal_array_t v = make_float_arr (inp, 1);
    sisal_array_t r = func_DV_SIN_REAL (v);
    check ("intr_sin_real[0]", near_f (af (r, 0), 0.f));
    free (v.data);
    free (r.data);
  }

  // dv_cos_real([0]) → [1]
  {
    float inp[] = { 0.f };
    sisal_array_t v = make_float_arr (inp, 1);
    sisal_array_t r = func_DV_COS_REAL (v);
    check ("intr_cos_real[0]", near_f (af (r, 0), 1.f));
    free (v.data);
    free (r.data);
  }

  // dv_log_real([1]) → [0]  (ln 1 = 0)
  {
    float inp[] = { 1.f };
    sisal_array_t v = make_float_arr (inp, 1);
    sisal_array_t r = func_DV_LOG_REAL (v);
    check ("intr_log_real[0]", near_f (af (r, 0), 0.f));
    free (v.data);
    free (r.data);
  }

  // dv_floor_real([1.7, 2.3, -0.5]) → int32[1, 2, -1]
  {
    float inp[] = { 1.7f, 2.3f, -0.5f };
    sisal_array_t v = make_float_arr (inp, 3);
    sisal_array_t r = func_DV_FLOOR_REAL (v);
    check ("intr_floor_real[0]", ai (r, 0) == 1);
    check ("intr_floor_real[1]", ai (r, 1) == 2);
    check ("intr_floor_real[2]", ai (r, 2) == -1);
    free (v.data);
    free (r.data);
  }

  // dv_trunc_real([1.7, 2.3, -0.5]) → int32[1, 2, 0]
  {
    float inp[] = { 1.7f, 2.3f, -0.5f };
    sisal_array_t v = make_float_arr (inp, 3);
    sisal_array_t r = func_DV_TRUNC_REAL (v);
    check ("intr_trunc_real[0]", ai (r, 0) == 1);
    check ("intr_trunc_real[1]", ai (r, 1) == 2);
    check ("intr_trunc_real[2]", ai (r, 2) == 0);
    free (v.data);
    free (r.data);
  }

  // dv_abs_double([-1.0, 2.0]) → [1.0, 2.0]
  {
    double inp[] = { -1.0, 2.0 };
    sisal_array_t v = make_double_arr (inp, 2);
    sisal_array_t r = func_DV_ABS_DOUBLE (v);
    check ("intr_abs_double[0]", near_d (ad (r, 0), 1.0));
    check ("intr_abs_double[1]", near_d (ad (r, 1), 2.0));
    free (v.data);
    free (r.data);
  }

  // dv_sqrt_double([4.0, 9.0]) → [2.0, 3.0]
  {
    double inp[] = { 4.0, 9.0 };
    sisal_array_t v = make_double_arr (inp, 2);
    sisal_array_t r = func_DV_SQRT_DOUBLE (v);
    check ("intr_sqrt_double[0]", near_d (ad (r, 0), 2.0));
    check ("intr_sqrt_double[1]", near_d (ad (r, 1), 3.0));
    free (v.data);
    free (r.data);
  }

  // dv_add_dv([1,2,3],[4,5,6]) → [5,7,9]
  {
    float a[] = { 1.f, 2.f, 3.f }, b[] = { 4.f, 5.f, 6.f };
    sisal_array_t va = make_float_arr (a, 3), vb = make_float_arr (b, 3);
    sisal_array_t r = func_DV_ADD_DV (va, vb);
    check ("intr_add_dv[0]", near_f (af (r, 0), 5.f));
    check ("intr_add_dv[1]", near_f (af (r, 1), 7.f));
    check ("intr_add_dv[2]", near_f (af (r, 2), 9.f));
    free (va.data);
    free (vb.data);
    free (r.data);
  }

  // dv_sub_dv([4,5,6],[1,2,3]) → [3,3,3]
  {
    float a[] = { 4.f, 5.f, 6.f }, b[] = { 1.f, 2.f, 3.f };
    sisal_array_t va = make_float_arr (a, 3), vb = make_float_arr (b, 3);
    sisal_array_t r = func_DV_SUB_DV (va, vb);
    check ("intr_sub_dv[0]", near_f (af (r, 0), 3.f));
    check ("intr_sub_dv[1]", near_f (af (r, 1), 3.f));
    check ("intr_sub_dv[2]", near_f (af (r, 2), 3.f));
    free (va.data);
    free (vb.data);
    free (r.data);
  }

  // dv_mul_dv([2,3,4],[5,6,7]) → [10,18,28]
  {
    float a[] = { 2.f, 3.f, 4.f }, b[] = { 5.f, 6.f, 7.f };
    sisal_array_t va = make_float_arr (a, 3), vb = make_float_arr (b, 3);
    sisal_array_t r = func_DV_MUL_DV (va, vb);
    check ("intr_mul_dv[0]", near_f (af (r, 0), 10.f));
    check ("intr_mul_dv[1]", near_f (af (r, 1), 18.f));
    check ("intr_mul_dv[2]", near_f (af (r, 2), 28.f));
    free (va.data);
    free (vb.data);
    free (r.data);
  }

  // dv_div_dv([10,20,30],[2,4,5]) → [5,5,6]
  {
    float a[] = { 10.f, 20.f, 30.f }, b[] = { 2.f, 4.f, 5.f };
    sisal_array_t va = make_float_arr (a, 3), vb = make_float_arr (b, 3);
    sisal_array_t r = func_DV_DIV_DV (va, vb);
    check ("intr_div_dv[0]", near_f (af (r, 0), 5.f));
    check ("intr_div_dv[1]", near_f (af (r, 1), 5.f));
    check ("intr_div_dv[2]", near_f (af (r, 2), 6.f));
    free (va.data);
    free (vb.data);
    free (r.data);
  }

  // scalar_add_dv(10, [1,2,3]) → [11,12,13]
  {
    float inp[] = { 1.f, 2.f, 3.f };
    sisal_array_t v = make_float_arr (inp, 3);
    sisal_array_t r = func_SCALAR_ADD_DV (10.f, v);
    check ("intr_scalar_add_dv[0]", near_f (af (r, 0), 11.f));
    check ("intr_scalar_add_dv[1]", near_f (af (r, 1), 12.f));
    check ("intr_scalar_add_dv[2]", near_f (af (r, 2), 13.f));
    free (v.data);
    free (r.data);
  }

  // dv_gt_scalar([1,5,3], 2) → [F,T,T]
  {
    float inp[] = { 1.f, 5.f, 3.f };
    sisal_array_t v = make_float_arr (inp, 3);
    sisal_array_t r = func_DV_GT_SCALAR (v, 2.f);
    check ("intr_gt_scalar[0]", ab (r, 0) == false);
    check ("intr_gt_scalar[1]", ab (r, 1) == true);
    check ("intr_gt_scalar[2]", ab (r, 2) == true);
    free (v.data);
    free (r.data);
  }

  // dv_eq_dv([1,2,3],[1,9,3]) → [T,F,T]
  {
    float a[] = { 1.f, 2.f, 3.f }, b[] = { 1.f, 9.f, 3.f };
    sisal_array_t va = make_float_arr (a, 3), vb = make_float_arr (b, 3);
    sisal_array_t r = func_DV_EQ_DV (va, vb);
    check ("intr_eq_dv[0]", ab (r, 0) == true);
    check ("intr_eq_dv[1]", ab (r, 1) == false);
    check ("intr_eq_dv[2]", ab (r, 2) == true);
    free (va.data);
    free (vb.data);
    free (r.data);
  }

  // dv_ne_dv([1,2,3],[1,9,3]) → [F,T,F]
  {
    float a[] = { 1.f, 2.f, 3.f }, b[] = { 1.f, 9.f, 3.f };
    sisal_array_t va = make_float_arr (a, 3), vb = make_float_arr (b, 3);
    sisal_array_t r = func_DV_NE_DV (va, vb);
    check ("intr_ne_dv[0]", ab (r, 0) == false);
    check ("intr_ne_dv[1]", ab (r, 1) == true);
    check ("intr_ne_dv[2]", ab (r, 2) == false);
    free (va.data);
    free (vb.data);
    free (r.data);
  }

  // dv_and_dv([T,T,F],[T,F,F]) → [T,F,F]
  {
    bool a[] = { true, true, false }, b[] = { true, false, false };
    sisal_array_t va = make_bool_arr (a, 3), vb = make_bool_arr (b, 3);
    sisal_array_t r = func_DV_AND_DV (va, vb);
    check ("intr_and_dv[0]", ab (r, 0) == true);
    check ("intr_and_dv[1]", ab (r, 1) == false);
    check ("intr_and_dv[2]", ab (r, 2) == false);
    free (va.data);
    free (vb.data);
    free (r.data);
  }

  // dv_or_dv([T,F,F],[F,F,T]) → [T,F,T]
  {
    bool a[] = { true, false, false }, b[] = { false, false, true };
    sisal_array_t va = make_bool_arr (a, 3), vb = make_bool_arr (b, 3);
    sisal_array_t r = func_DV_OR_DV (va, vb);
    check ("intr_or_dv[0]", ab (r, 0) == true);
    check ("intr_or_dv[1]", ab (r, 1) == false);
    check ("intr_or_dv[2]", ab (r, 2) == true);
    free (va.data);
    free (vb.data);
    free (r.data);
  }

  // dv_shl_scalar([1,2,4], 2) → [4,8,16]
  {
    int32_t inp[] = { 1, 2, 4 };
    sisal_array_t v = make_int_arr (inp, 3);
    sisal_array_t r = func_DV_SHL_SCALAR (v, 2);
    check ("intr_shl_scalar[0]", ai (r, 0) == 4);
    check ("intr_shl_scalar[1]", ai (r, 1) == 8);
    check ("intr_shl_scalar[2]", ai (r, 2) == 16);
    free (v.data);
    free (r.data);
  }

  // dv_shr_scalar([8,4,16], 2) → [2,1,4]
  {
    int32_t inp[] = { 8, 4, 16 };
    sisal_array_t v = make_int_arr (inp, 3);
    sisal_array_t r = func_DV_SHR_SCALAR (v, 2);
    check ("intr_shr_scalar[0]", ai (r, 0) == 2);
    check ("intr_shr_scalar[1]", ai (r, 1) == 1);
    check ("intr_shr_scalar[2]", ai (r, 2) == 4);
    free (v.data);
    free (r.data);
  }

  // dv_sum_real([1,2,3,4]) → 10
  {
    float inp[] = { 1.f, 2.f, 3.f, 4.f };
    sisal_array_t v = make_float_arr (inp, 4);
    float s = func_DV_SUM_REAL (v);
    check ("intr_sum_real", near_f (s, 10.f));
    free (v.data);
  }

  // dv_product_real([1,2,3,4]) → 24
  // NOTE: sisal_array_reduce_float_product is a stub returning 1.0f — EXPECTED
  // FAIL
  {
    float inp[] = { 1.f, 2.f, 3.f, 4.f };
    sisal_array_t v = make_float_arr (inp, 4);
    float s = func_DV_PRODUCT_REAL (v);
    printf ("  INFO  intr_product_real = %g (expected 24; runtime stub "
            "returns 1 — known issue)\n",
            s);
    check ("intr_product_real", near_f (s, 24.f));
    free (v.data);
  }

  // dv_least_real([3,1,4,1,5]) → 1
  // NOTE: sisal_array_reduce_least is a stub returning 0.0f — EXPECTED FAIL
  {
    float inp[] = { 3.f, 1.f, 4.f, 1.f, 5.f };
    sisal_array_t v = make_float_arr (inp, 5);
    float s = func_DV_LEAST_REAL (v);
    printf ("  INFO  intr_least_real = %g (expected 1; runtime stub returns 0 "
            "— known issue)\n",
            s);
    check ("intr_least_real", near_f (s, 1.f));
    free (v.data);
  }

  // dv_greatest_real([3,1,4,1,5]) → 5
  // NOTE: sisal_array_reduce_greatest is a stub returning 0.0f — EXPECTED FAIL
  {
    float inp[] = { 3.f, 1.f, 4.f, 1.f, 5.f };
    sisal_array_t v = make_float_arr (inp, 5);
    float s = func_DV_GREATEST_REAL (v);
    printf ("  INFO  intr_greatest_real = %g (expected 5; runtime stub "
            "returns 0 — known issue)\n",
            s);
    check ("intr_greatest_real", near_f (s, 5.f));
    free (v.data);
  }

  // dv_sum_int([1,2,3,4]) → 10
  // NOTE: reduce_int_sum calls reduce_sum (float*) on int32 data — result is
  // implementation-defined
  {
    int32_t inp[] = { 1, 2, 3, 4 };
    sisal_array_t v = make_int_arr (inp, 4);
    int32_t s = func_DV_SUM_INT (v);
    printf ("  INFO  intr_sum_int = %d (expected 10; runtime interprets int "
            "bits as float — may differ)\n",
            s);
    check ("intr_sum_int", s == 10);
    free (v.data);
  }

  // dv_product_int([1,2,3,4]) → 24  (reduce_int_product is properly
  // implemented)
  {
    int32_t inp[] = { 1, 2, 3, 4 };
    sisal_array_t v = make_int_arr (inp, 4);
    int32_t s = func_DV_PRODUCT_INT (v);
    check ("intr_product_int", s == 24);
    free (v.data);
  }

  // dv_least_int([3,1,4]) → 1
  // NOTE: reduce_int_least is a stub returning 0 — EXPECTED FAIL
  {
    int32_t inp[] = { 3, 1, 4 };
    sisal_array_t v = make_int_arr (inp, 3);
    int32_t s = func_DV_LEAST_INT (v);
    printf ("  INFO  intr_least_int = %d (expected 1; runtime stub returns 0 "
            "— known issue)\n",
            s);
    check ("intr_least_int", s == 1);
    free (v.data);
  }

  // dv_greatest_int([3,1,4]) → 4
  // NOTE: reduce_int_greatest is a stub returning 0 — EXPECTED FAIL
  {
    int32_t inp[] = { 3, 1, 4 };
    sisal_array_t v = make_int_arr (inp, 3);
    int32_t s = func_DV_GREATEST_INT (v);
    printf ("  INFO  intr_greatest_int = %d (expected 4; runtime stub returns "
            "0 — known issue)\n",
            s);
    check ("intr_greatest_int", s == 4);
    free (v.data);
  }
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
static void
test_broadcast_complex (void)
{
  printf ("\n=== Group G: dv_broadcast_complex ===\n");

  // broadcast_vec_mat: V=[1,2,3] (1D) + M=[[10,20,30],[40,50,60]] (shape
  // [2,3]) numpy: result shape [2,3], values [11,22,33, 41,52,63].
  {
    double v_data[] = { 1.0, 2.0, 3.0 };
    double m_data[] = { 10.0, 20.0, 30.0, 40.0, 50.0, 60.0 };
    sisal_array_t V = make_double_arr (v_data, 3);
    sisal_array_t M = make_double_2d (m_data, 2, 3);
    sisal_array_t r = func_BROADCAST_VEC_MAT (V, M);
    check ("bcast_vec_mat shape [2,3]",
           r.rank == 2 && r.dims[0] == 2 && r.dims[1] == 3 && r.size == 6);
    double ex[] = { 11, 22, 33, 41, 52, 63 };
    bool ok = (r.size == 6);
    for (int i = 0; i < 6 && ok; i++)
      ok &= near_d (ad (r, i), ex[i]);
    check ("bcast_vec_mat values 11 22 33 41 52 63", ok);
    free (V.data);
    free (M.data);
    free (r.data);
  }

  // broadcast_unit: A=[[1],[2]] (shape [2,1]) + B=[[10,20,30]] (shape [1,3])
  // numpy: result shape [2,3], values [11,21,31, 12,22,32].
  {
    double a_data[] = { 1.0, 2.0 };
    double b_data[] = { 10.0, 20.0, 30.0 };
    sisal_array_t A = make_double_2d (a_data, 2, 1);
    sisal_array_t B = make_double_2d (b_data, 1, 3);
    sisal_array_t r = func_BROADCAST_UNIT (A, B);
    check ("bcast_unit shape [2,3]",
           r.rank == 2 && r.dims[0] == 2 && r.dims[1] == 3 && r.size == 6);
    double ex[] = { 11, 21, 31, 12, 22, 32 };
    bool ok = (r.size == 6);
    for (int i = 0; i < 6 && ok; i++)
      ok &= near_d (ad (r, i), ex[i]);
    check ("bcast_unit values 11 21 31 12 22 32", ok);
    free (A.data);
    free (B.data);
    free (r.data);
  }

  // broadcast_scalar: S=100.0 + M=[[1..9]] (shape [3,3]) -> values [101..109].
  // VALUES are correct; the result SHAPE is still rank-1 [9] -- a separate bug
  // in the scalar+array path (the conform fix only covers array+array rank
  // mismatch).
  {
    double m_data[] = { 1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0 };
    sisal_array_t M = make_double_2d (m_data, 3, 3);
    sisal_array_t r = func_BROADCAST_SCALAR (100.0, M);
    // scalar broadcast keeps M's shape: the flat elementwise result is
    // reshaped back to M's runtime rank/dims (DV_NUM_RANK -> DV_DIMENSION ->
    // RESHAPE).
    check ("bcast_scalar shape [3,3]",
           r.rank == 2 && r.dims[0] == 3 && r.dims[1] == 3 && r.size == 9);
    bool ok = (r.size == 9);
    for (int i = 0; i < 9 && ok; i++)
      ok &= near_d (ad (r, i), m_data[i] + 100.0);
    check ("bcast_scalar values 101..109", ok);
    free (M.data);
    free (r.data);
  }
}
#endif

// ============================================================
// GROUP H — dv_compress_test
// ============================================================

#ifdef TEST_COMPRESS
static void
test_compress (void)
{
  printf ("\n=== Group H: dv_compress_test ===\n");

  // compress_monolithic: mask=[T,F,T,F,T], a=[10,20,30,40,50] → [10,30,50]
  // NOTE: sisal_array_compress uses float* cast to copy elements regardless of
  // type_id. For int32 inputs, this means a 4-byte copy as if the bits were
  // float. The result array has type_id=6 (int32) but was written via float*,
  // so values should still be bit-identical to the original int32 values if
  // sizeof(float)==sizeof(int32_t).
  {
    bool mask[] = { true, false, true, false, true };
    int32_t a[] = { 10, 20, 30, 40, 50 };
    sisal_array_t vm = make_bool_arr (mask, 5);
    sisal_array_t va = make_int_arr (a, 5);
    sisal_array_t r = func_COMPRESS_MONOLITHIC (vm, va);
    check ("compress_mono_size", r.size == 3);
    // The runtime copies via float* (4 bytes each), same width as int32_t,
    // so the bit pattern is preserved.
    check ("compress_mono[0]", ai (r, 0) == 10);
    check ("compress_mono[1]", ai (r, 1) == 30);
    check ("compress_mono[2]", ai (r, 2) == 50);
    free (vm.data);
    free (va.data);
    free (r.data);
  }

  // compress_dv_input(6): even numbers from 1..6 = [2,4,6]
  {
    sisal_array_t r = func_COMPRESS_DV_INPUT (6);
    check ("compress_dv_size", r.size == 3);
    // The values array was int32, copied via float* — bit-identical
    check ("compress_dv[0]", ai (r, 0) == 2);
    check ("compress_dv[1]", ai (r, 1) == 4);
    check ("compress_dv[2]", ai (r, 2) == 6);
    free (r.data);
  }

  // compress_chain: mask=[T,F,T], a=[10,20,30] → size=2
  {
    bool mask[] = { true, false, true };
    int32_t a[] = { 10, 20, 30 };
    sisal_array_t vm = make_bool_arr (mask, 3);
    sisal_array_t va = make_int_arr (a, 3);
    int32_t s = func_COMPRESS_CHAIN (vm, va);
    check ("compress_chain", s == 2);
    free (vm.data);
    free (va.data);
  }
}
#endif

// ============================================================
// GROUP I — dv_broadcast_numpy (APL rank-mismatch: expected error)
// ============================================================

#ifdef TEST_BROADCAST_NUMPY
static void
test_broadcast_numpy (void)
{
  printf ("\n=== Group I: dv_broadcast_numpy (trailing-axis broadcast, vs C "
          "reference) ===\n");
  // Implemented semantics for 2D [2,3] + 1D [3]: broadcast B across rows,
  //   out[i,j] = A[i,j] + B[j].  (numpy-style, despite the source's stale
  //   note.)
  const int R = 2, C = 3;
  double a_data[] = { 1.0, 2.0, 3.0, 4.0, 5.0, 6.0 };
  double b_data[] = { 10.0, 20.0, 30.0 };
  double exp[6];
  for (int i = 0; i < R; i++)
    for (int j = 0; j < C; j++)
      exp[i * C + j] = a_data[i * C + j] + b_data[j];
  sisal_array_t A = make_double_2d (a_data, R, C);
  sisal_array_t B = make_double_arr (b_data, C); // 1D, rank=1
  sisal_array_t r = func_MAIN (A, B);
  bool ok = (r.rank == 2) && ((int)r.dims[0] == R) && ((int)r.dims[1] == C);
  for (int t = 0; ok && t < R * C; t++)
    ok = ok && (fabs (ad (r, t) - exp[t]) < 1e-9);
  check ("broadcast_numpy [2,3]+[3] == A[i,j]+B[j] (vs C reference)", ok);
  free (A.data);
  free (B.data);
  if (r.data)
    free (r.data);
}
#endif

// ============================================================
// GROUP J — forall_cpu  (for i in 1..N → array_dv of -real(i))
// ============================================================

#ifdef TEST_FORALL_CPU
static void
test_forall_cpu (void)
{
  printf ("\n=== Group J: forall_cpu ===\n");
  // func_MAIN_CPU(4): X = real(i) for i in 1..4, return -X
  // Expected: [-1.0, -2.0, -3.0, -4.0]
  sisal_array_t r = func_MAIN_CPU (4);
  float exp[] = { -1.0f, -2.0f, -3.0f, -4.0f };
  check ("forall_cpu_size", (int32_t)r.size == 4);
  for (int i = 0; i < 4; i++)
    {
      char name[32];
      snprintf (name, sizeof (name), "forall_cpu[%d]", i);
      check (name, near_f (af (r, i), exp[i]));
    }
  if (r.data)
    free (r.data);
}
#endif

// ============================================================
// GROUP K — negate_dv  (let N := size(A) in for I in 1..N: -A[I])
// ============================================================

#ifdef TEST_NEGATE_DV
static void
test_negate_dv (void)
{
  printf ("\n=== Group K: negate_dv ===\n");
  // func_NEGATE([3, 1, 4, 1, 5]) → [-3, -1, -4, -1, -5]
  int32_t inp[] = { 3, 1, 4, 1, 5 };
  int32_t exp[] = { -3, -1, -4, -1, -5 };
  sisal_array_t A = make_int_arr (inp, 5); // lower_bound = 1
  sisal_array_t r = func_NEGATE (A);
  check ("negate_dv_size", (int32_t)r.size == 5);
  for (int i = 0; i < 5; i++)
    {
      char name[32];
      snprintf (name, sizeof (name), "negate_dv[%d]", i);
      check (name, ai (r, i) == exp[i]);
    }
  free (A.data);
  if (r.data)
    free (r.data);
}
#endif

// ============================================================
// GROUP L — dv_forall_basic  (for i in 1..N → array_dv of i)
// ============================================================

#ifdef TEST_FORALL_BASIC_DV
static void
test_forall_basic_dv (void)
{
  printf ("\n=== Group L: dv_forall_basic ===\n");
  // func_FORALL_BASIC(5) → [1, 2, 3, 4, 5]
  sisal_array_t r = func_FORALL_BASIC (5);
  int32_t exp[] = { 1, 2, 3, 4, 5 };
  check ("forall_basic_dv_size", (int32_t)r.size == 5);
  for (int i = 0; i < 5; i++)
    {
      char name[32];
      snprintf (name, sizeof (name), "forall_basic_dv[%d]", i);
      check (name, ai (r, i) == exp[i]);
    }
  if (r.data)
    free (r.data);
}
#endif

#ifdef TEST_FORALL_REDUCE_DV
static void
test_forall_reduce_dv (void)
{
  printf ("\n=== Group M: dv_forall_reduce ===\n");
  // sum_to_n(5)  = 1+2+3+4+5 = 15
  check ("sum_to_n_5", func_SUM_TO_N (5) == 15);
  check ("sum_to_n_0", func_SUM_TO_N (0) == 0);
  // product_to_n(5) = 120
  check ("product_to_n_5", func_PRODUCT_TO_N (5) == 120);
  check ("product_to_n_1", func_PRODUCT_TO_N (1) == 1);
  // min_to_n(5) = 1, max_to_n(5) = 5
  check ("min_to_n_5", func_MIN_TO_N (5) == 1);
  check ("max_to_n_5", func_MAX_TO_N (5) == 5);
  check ("max_to_n_1", func_MAX_TO_N (1) == 1);
}
#endif

#ifdef TEST_FOR_INITIAL
static void
test_for_initial (void)
{
  printf ("\n=== Group FI: for_initial (LoopB) ===\n");
  // single self-recurrences
  check ("fi_sum_10", func_FI_SUM (10) == 55); // 1+..+10
  check ("fi_sum_1", func_FI_SUM (1) == 1);
  check ("fi_product_5", func_FI_PRODUCT (5) == 120); // 5!
  check ("fi_product_1", func_FI_PRODUCT (1) == 1);
  check ("fi_final_i_5",
         func_FI_FINAL_I (5) == 6); // i runs 1..n, stops at n+1
  check ("fi_final_i_1", func_FI_FINAL_I (1) == 2);
  // identity-recurrence carry (k := old k) — needs the MERGE-filter fix
  check ("fi_passthru_5", func_FI_PASSTHRU (5) == 42);
  check ("fi_passthru_1", func_FI_PASSTHRU (1) == 42);
  // mutual old-references — needs the get_symbol_id_old carry-in fix
  check ("fi_swap_1", func_FI_SWAP (1) == 20); // a,b exchange each iter
  check ("fi_swap_2", func_FI_SWAP (2) == 10);
  check ("fi_swap_3", func_FI_SWAP (3) == 20);
  check ("fi_fib_1", func_FI_FIB (1) == 1); // Fibonacci
  check ("fi_fib_5", func_FI_FIB (5) == 5);
  check ("fi_fib_7", func_FI_FIB (7) == 13);
  check ("fi_fib_10", func_FI_FIB (10) == 55);
  // LoopA (post-test repeat..until) Fibonacci — same recurrence via the other
  // loop block
  check ("fi_fib_a_1", func_FI_FIB_A (1) == 1);
  check ("fi_fib_a_5", func_FI_FIB_A (5) == 5);
  check ("fi_fib_a_7", func_FI_FIB_A (7) == 13);
  check ("fi_fib_a_10", func_FI_FIB_A (10) == 55);

  // Regression: array-PARAMETER-seeded carry (A := Ain) — needs the to_if1
  // INIT-seed MERGE fix (a pass-through alias must still become a loop carry).
  int32_t seed[] = { 10, 20, 30 };
  sisal_array_t s1 = make_int_arr (seed, 3);
  sisal_array_t id
      = func_FI_PARAM_IDENTITY (3, s1); // identity carry -> unchanged
  check ("fi_param_identity rank=1", id.rank == 1);
  check ("fi_param_identity size=3", (int)id.size == 3);
  check ("fi_param_identity[0]=10", ai (id, 0) == 10);
  check ("fi_param_identity[1]=20", ai (id, 1) == 20);
  check ("fi_param_identity[2]=30", ai (id, 2) == 30);
  // identity carry returns the same buffer as the input (id.data == s1.data),
  // so free it only once.
  if (s1.data)
    free (s1.data);

  sisal_array_t s2 = make_int_arr (seed, 3);
  sisal_array_t bp = func_FI_PARAM_BUMP (3, s2); // +1 per elem, 3 iters
  check ("fi_param_bump size=3", (int)bp.size == 3);
  check ("fi_param_bump[0]=13", ai (bp, 0) == 13);
  check ("fi_param_bump[1]=23", ai (bp, 1) == 23);
  check ("fi_param_bump[2]=33", ai (bp, 2) == 33);
  if (bp.data)
    free (bp.data);
  if (s2.data)
    free (s2.data);
}
#endif

#ifdef TEST_INNERPRODUCT_DV
static void
test_innerproduct_dv (void)
{
  printf ("\n=== Group O: dv_innerproduct ===\n");
  printf ("  (innerproduct always returns sisal_array_t; caller reads [0] for "
          "scalar)\n");

  // --- 1D float dot via Sisal wrapper: [1,2,3].[4,5,6] = 32 ---
  float fa[] = { 1.0f, 2.0f, 3.0f };
  float fb[] = { 4.0f, 5.0f, 6.0f };
  sisal_array_t va = make_float_arr (fa, 3);
  sisal_array_t vb = make_float_arr (fb, 3);
  sisal_array_t dr = func_IP_F32 (va, vb);
  check ("dot_f32 returns rank-1", dr.rank == 1);
  check ("dot_f32 returns size-1", (int)dr.size == 1);
  check ("dot_f32 [1,2,3].[4,5,6]=32", af (dr, 0) == 32.0f);
  if (dr.data)
    free (dr.data);
  if (va.data)
    free (va.data);
  if (vb.data)
    free (vb.data);

  // --- 1D int dot via Sisal wrapper: [1,2,3].[4,5,6] = 32 ---
  int32_t ia[] = { 1, 2, 3 };
  int32_t ib[] = { 4, 5, 6 };
  sisal_array_t vai = make_int_arr (ia, 3);
  sisal_array_t vbi = make_int_arr (ib, 3);
  sisal_array_t ir = func_IP_I32 (vai, vbi);
  check ("dot_i32 returns rank-1", ir.rank == 1);
  check ("dot_i32 returns size-1", (int)ir.size == 1);
  check ("dot_i32 [1,2,3].[4,5,6]=32", ai (ir, 0) == 32);
  if (ir.data)
    free (ir.data);
  if (vai.data)
    free (vai.data);
  if (vbi.data)
    free (vbi.data);

  // --- 1D empty dot ---
  sisal_array_t ve = make_float_arr (NULL, 0);
  sisal_array_t er = func_IP_F32 (ve, ve);
  check ("dot_f32 empty returns 0", af (er, 0) == 0.0f);
  if (er.data)
    free (er.data);
  if (ve.data)
    free (ve.data);

  // --- 2D x 2D float matmul via Sisal wrapper ---
  // A=[[1,2],[3,4]]  B=[[5,6],[7,8]]  C=[[19,22],[43,50]]
  float ma[] = { 1, 2, 3, 4 };
  float mb[] = { 5, 6, 7, 8 };
  sisal_array_t A2 = make_float_2d (ma, 2, 2);
  sisal_array_t B2 = make_float_2d (mb, 2, 2);
  sisal_array_t C2 = func_IP_F32 (A2, B2);
  check ("matmul rank", C2.rank == 2);
  check ("matmul dims[0]", (int)C2.dims[0] == 2);
  check ("matmul dims[1]", (int)C2.dims[1] == 2);
  check ("matmul[0,0]=19", af (C2, 0) == 19.0f);
  check ("matmul[0,1]=22", af (C2, 1) == 22.0f);
  check ("matmul[1,0]=43", af (C2, 2) == 43.0f);
  check ("matmul[1,1]=50", af (C2, 3) == 50.0f);
  if (A2.data)
    free (A2.data);
  if (B2.data)
    free (B2.data);
  if (C2.data)
    free (C2.data);

  // --- 2D x 1D matvec via Sisal wrapper ---
  // A=[[1,2,3],[4,5,6]]  x=[1,0,-1]  r=[-2,-2]
  float mav[] = { 1, 2, 3, 4, 5, 6 };
  float vx[] = { 1.0f, 0.0f, -1.0f };
  sisal_array_t Amv = make_float_2d (mav, 2, 3);
  sisal_array_t xv = make_float_arr (vx, 3);
  sisal_array_t rv = func_IP_F32 (Amv, xv);
  check ("matvec rank", rv.rank == 1);
  check ("matvec size=2", (int)rv.size == 2);
  check ("matvec[0]=-2", af (rv, 0) == -2.0f);
  check ("matvec[1]=-2", af (rv, 1) == -2.0f);
  if (Amv.data)
    free (Amv.data);
  if (xv.data)
    free (xv.data);
  if (rv.data)
    free (rv.data);

  // --- 1D x 2D vecmat via Sisal wrapper ---
  // y=[1,2]  B=[[1,2,3],[4,5,6]]  r=[9,12,15]
  float vy[] = { 1.0f, 2.0f };
  float mbv[] = { 1, 2, 3, 4, 5, 6 };
  sisal_array_t yv = make_float_arr (vy, 2);
  sisal_array_t Bvm = make_float_2d (mbv, 2, 3);
  sisal_array_t rvm = func_IP_F32 (yv, Bvm);
  check ("vecmat rank", rvm.rank == 1);
  check ("vecmat size=3", (int)rvm.size == 3);
  check ("vecmat[0]=9", af (rvm, 0) == 9.0f);
  check ("vecmat[1]=12", af (rvm, 1) == 12.0f);
  check ("vecmat[2]=15", af (rvm, 2) == 15.0f);
  if (yv.data)
    free (yv.data);
  if (Bvm.data)
    free (Bvm.data);
  if (rvm.data)
    free (rvm.data);

  // --- 1D double dot (direct runtime) ---
  // [1,2].[3,4] = 11
  double da[] = { 1.0, 2.0 };
  double db[] = { 3.0, 4.0 };
  sisal_array_t dva = make_double_arr (da, 2);
  sisal_array_t dvb = make_double_arr (db, 2);
  sisal_array_t dvr = sisal_array_innerproduct (dva, dvb);
  check ("dot_f64 rank", dvr.rank == 1);
  check ("dot_f64 [1,2].[3,4]=11", ((double *)dvr.data)[0] == 11.0);
  if (dva.data)
    free (dva.data);
  if (dvb.data)
    free (dvb.data);
  if (dvr.data)
    free (dvr.data);

  // --- rank-3 x rank-1: A(2,3,4) @ b(4) -> r(2,3) ---
  // A has 24 elements [0..23], b = [1,0,0,0] so result = A[:,:,0]
  float a3[24];
  for (int i = 0; i < 24; i++)
    a3[i] = (float)i;
  float b1[] = { 1.0f, 0.0f, 0.0f, 0.0f };
  sisal_array_t A3 = sisal_array_alloc_empty (3, 8, 24);
  A3.dims[0] = 2;
  A3.dims[1] = 3;
  A3.dims[2] = 4;
  memcpy (A3.data, a3, 24 * sizeof (float));
  sisal_array_t B1 = make_float_arr (b1, 4);
  sisal_array_t R31 = sisal_array_innerproduct (A3, B1);
  // numpy: np.dot(A3,b1) shape=(2,3), values = A3[:,:,0] = [0,4,8,12,16,20]
  check ("rank3x1 result rank=2", R31.rank == 2);
  check ("rank3x1 dims[0]=2", (int)R31.dims[0] == 2);
  check ("rank3x1 dims[1]=3", (int)R31.dims[1] == 3);
  check ("rank3x1 [0,0]=0", af (R31, 0) == 0.0f);
  check ("rank3x1 [0,1]=4", af (R31, 1) == 4.0f);
  check ("rank3x1 [0,2]=8", af (R31, 2) == 8.0f);
  check ("rank3x1 [1,0]=12", af (R31, 3) == 12.0f);
  check ("rank3x1 [1,1]=16", af (R31, 4) == 16.0f);
  check ("rank3x1 [1,2]=20", af (R31, 5) == 20.0f);
  if (A3.data)
    free (A3.data);
  if (B1.data)
    free (B1.data);
  if (R31.data)
    free (R31.data);

  // --- rank-3 x rank-2: A(2,3,4) @ B(4,5) -> r(2,3,5) ---
  // Use identity-ish B: B[k,j] = (k==j ? 1 : 0) for k<4,j<5 — selects columns
  float a32[24];
  for (int i = 0; i < 24; i++)
    a32[i] = (float)i;
  float b25[20] = { 0 };
  for (int k = 0; k < 4; k++)
    b25[k * 5 + k] = 1.0f; // identity (4x5 padded)
  sisal_array_t A32 = sisal_array_alloc_empty (3, 8, 24);
  A32.dims[0] = 2;
  A32.dims[1] = 3;
  A32.dims[2] = 4;
  memcpy (A32.data, a32, 24 * sizeof (float));
  sisal_array_t B25 = make_float_2d (b25, 4, 5);
  sisal_array_t R32 = sisal_array_innerproduct (A32, B25);
  // A(2,3,4) @ I(4,5): result(2,3,5), result[:,:,0..3]=A, result[:,:,4]=0
  check ("rank3x2 result rank=3", R32.rank == 3);
  check ("rank3x2 dims[0]=2", (int)R32.dims[0] == 2);
  check ("rank3x2 dims[1]=3", (int)R32.dims[1] == 3);
  check ("rank3x2 dims[2]=5", (int)R32.dims[2] == 5);
  // result[0,0,:] = A[0,0,:] padded = [0,1,2,3,0]
  check ("rank3x2 [0,0,0]=0", af (R32, 0) == 0.0f);
  check ("rank3x2 [0,0,1]=1", af (R32, 1) == 1.0f);
  check ("rank3x2 [0,0,3]=3", af (R32, 3) == 3.0f);
  check ("rank3x2 [0,0,4]=0", af (R32, 4) == 0.0f);
  // result[1,2,:] = A[1,2,:] padded = [20,21,22,23,0]
  check ("rank3x2 [1,2,0]=20", af (R32, 25) == 20.0f);
  check ("rank3x2 [1,2,3]=23", af (R32, 28) == 23.0f);
  check ("rank3x2 [1,2,4]=0", af (R32, 29) == 0.0f);
  if (A32.data)
    free (A32.data);
  if (B25.data)
    free (B25.data);
  if (R32.data)
    free (R32.data);

  // --- mismatch: rank-2(2,3) @ rank-2(4,5) -> empty (axis error) ---
  float mm_a[] = { 1, 2, 3, 4, 5, 6 }, mm_b[20] = { 0 };
  sisal_array_t Amm = make_float_2d (mm_a, 2, 3);
  sisal_array_t Bmm = make_float_2d (mm_b, 4, 5);
  sisal_array_t Rmm = sisal_array_innerproduct (Amm, Bmm);
  check ("mismatch returns empty", (int)Rmm.size == 0);
  if (Amm.data)
    free (Amm.data);
  if (Bmm.data)
    free (Bmm.data);
  if (Rmm.data)
    free (Rmm.data);

  // --- 4D x 4D float dot via Sisal compiled innerproduct ---
  float a4[48], b4[48];
  for (int i = 0; i < 48; i++) {
    a4[i] = (float)i * 0.1f;
    b4[i] = (float)(48 - i) * 0.05f;
  }
  sisal_array_t A4 = sisal_array_alloc_empty (4, 8, 48);
  int64_t dims_a4[] = { 2, 3, 2, 4 };
  memcpy (A4.dims, dims_a4, sizeof (dims_a4));
  memcpy (A4.data, a4, sizeof (a4));

  sisal_array_t B4 = sisal_array_alloc_empty (4, 8, 48);
  int64_t dims_b4[] = { 2, 2, 4, 3 };
  memcpy (B4.dims, dims_b4, sizeof (dims_b4));
  memcpy (B4.data, b4, sizeof (b4));

  sisal_array_t R4 = func_IP_F32 (A4, B4);
  check ("dot_f32 4D rank", R4.rank == 6);
  check ("dot_f32 4D size", (int)R4.size == 144);
  check ("dot_f32 4D dims[0]", (int)R4.dims[0] == 2);
  check ("dot_f32 4D dims[5]", (int)R4.dims[5] == 3);
  check ("dot_f32 4D [0]=1.23", fabsf(af(R4, 0) - 1.23f) < 1e-4f);
  check ("dot_f32 4D [143]=4.93", fabsf(af(R4, 143) - 4.93f) < 1e-4f);

  if (A4.data) free (A4.data);
  if (B4.data) free (B4.data);
  if (R4.data) free (R4.data);
}
#endif

#ifdef TEST_MATMUL_OP_DV
static void
test_matmul_op_dv (void)
{
  printf ("\n=== Group: matmul_op_dv (matmul keyword) ===\n");

  // A=[[1,2],[3,4]]  B=[[5,6],[7,8]]  C=[[19,22],[43,50]]
  float ma[] = { 1, 2, 3, 4 };
  float mb[] = { 5, 6, 7, 8 };
  sisal_array_t A2 = make_float_2d (ma, 2, 2);
  sisal_array_t B2 = make_float_2d (mb, 2, 2);
  sisal_array_t C2 = func_MM_F32 (A2, B2);
  check ("matmul_op rank", C2.rank == 2);
  check ("matmul_op dims[0]", (int)C2.dims[0] == 2);
  check ("matmul_op dims[1]", (int)C2.dims[1] == 2);
  check ("matmul_op[0,0]=19", af (C2, 0) == 19.0f);
  check ("matmul_op[0,1]=22", af (C2, 1) == 22.0f);
  check ("matmul_op[1,0]=43", af (C2, 2) == 43.0f);
  check ("matmul_op[1,1]=50", af (C2, 3) == 50.0f);
  if (A2.data)
    free (A2.data);
  if (B2.data)
    free (B2.data);
  if (C2.data)
    free (C2.data);

  // --- 4D x 4D float dot via Sisal compiled matmul ---
  float a4[48], b4[48];
  for (int i = 0; i < 48; i++) {
    a4[i] = (float)i * 0.1f;
    b4[i] = (float)(48 - i) * 0.05f;
  }
  sisal_array_t A4 = sisal_array_alloc_empty (4, 8, 48);
  int64_t dims_a4[] = { 2, 3, 2, 4 };
  memcpy (A4.dims, dims_a4, sizeof (dims_a4));
  memcpy (A4.data, a4, sizeof (a4));

  sisal_array_t B4 = sisal_array_alloc_empty (4, 8, 48);
  int64_t dims_b4[] = { 2, 2, 4, 3 };
  memcpy (B4.dims, dims_b4, sizeof (dims_b4));
  memcpy (B4.data, b4, sizeof (b4));

  sisal_array_t R4 = func_MM_F32 (A4, B4);
  check ("matmul_op 4D rank", R4.rank == 6);
  check ("matmul_op 4D size", (int)R4.size == 144);
  check ("matmul_op 4D dims[0]", (int)R4.dims[0] == 2);
  check ("matmul_op 4D dims[5]", (int)R4.dims[5] == 3);
  check ("matmul_op 4D [0]=1.23", fabsf(af(R4, 0) - 1.23f) < 1e-4f);
  check ("matmul_op 4D [143]=4.93", fabsf(af(R4, 143) - 4.93f) < 1e-4f);

  if (A4.data) free (A4.data);
  if (B4.data) free (B4.data);
  if (R4.data) free (R4.data);
}
#endif


#ifdef TEST_MATMUL_DV
// Explicit triple-nested forall matmul over array_dv[integer] (matmul_dv.sis):
//   for i,row=for j,val=for k returns sum A[i,k]*B[k,j]
// Distinct from the innerproduct-wrapper matmul above — this exercises the
// nested-forall -> array_dv lowering directly.
static void
test_matmul_dv (void)
{
  printf ("\n=== Group: matmul_dv (nested forall) ===\n");
  // A=[[1,2],[3,4]]  B=[[5,6],[7,8]]  C=[[19,22],[43,50]]
  int32_t da[] = { 1, 2, 3, 4 };
  int32_t db[] = { 5, 6, 7, 8 };
  sisal_array_t A = make_int_2d (da, 2, 2);
  sisal_array_t B = make_int_2d (db, 2, 2);
  sisal_array_t C = func_MAIN (A, B, 2);
  check ("matmul_dv rank", C.rank == 2);
  check ("matmul_dv dims[0]", (int)C.dims[0] == 2);
  check ("matmul_dv dims[1]", (int)C.dims[1] == 2);
  check ("matmul_dv[0,0]=19", ai (C, 0) == 19);
  check ("matmul_dv[0,1]=22", ai (C, 1) == 22);
  check ("matmul_dv[1,0]=43", ai (C, 2) == 43);
  check ("matmul_dv[1,1]=50", ai (C, 3) == 50);
  if (A.data)
    free (A.data);
  if (B.data)
    free (B.data);
  if (C.data)
    free (C.data);

  // 3x3 to exercise non-trivial K accumulation across rows.
  // A=[[1,2,3],[4,5,6],[7,8,9]]  B=I3  => C==A
  int32_t da3[] = { 1, 2, 3, 4, 5, 6, 7, 8, 9 };
  int32_t i3[] = { 1, 0, 0, 0, 1, 0, 0, 0, 1 };
  sisal_array_t A3 = make_int_2d (da3, 3, 3);
  sisal_array_t I3 = make_int_2d (i3, 3, 3);
  sisal_array_t C3 = func_MAIN (A3, I3, 3);
  bool id_ok
      = (C3.rank == 2) && ((int)C3.dims[0] == 3) && ((int)C3.dims[1] == 3);
  for (int k = 0; k < 9; k++)
    id_ok = id_ok && (ai (C3, k) == da3[k]);
  check ("matmul_dv 3x3 * I3 == A", id_ok);
  if (A3.data)
    free (A3.data);
  if (I3.data)
    free (I3.data);
  if (C3.data)
    free (C3.data);
}
#endif

// ============================================================
// GROUPS RED_* — scalar forall reductions (red_*.sis)
// ============================================================

#ifdef TEST_THREE
static void
test_three (void)
{
  printf ("\n=== Group: three (constant) ===\n");
  check ("three()=3", func_MAIN () == 3);
}
#endif

#ifdef TEST_FACT
static void
test_fact (void)
{
  printf ("\n=== Group: fact (scalar recursion) ===\n");
  check ("fact(0)=1", func_MAIN (0) == 1);
  check ("fact(1)=1", func_MAIN (1) == 1);
  check ("fact(5)=120", func_MAIN (5) == 120);
  check ("fact(7)=5040", func_MAIN (7) == 5040);
}
#endif
#ifdef TEST_RECORD_E2E
static void
test_record_e2e (void)
{
  printf ("\n=== Group: record_e2e (flat record construct and replace) ===\n");
  struct FUNC_MAIN_results r = func_MAIN ();
  check ("val_x == 84", r.r0 == 84);
  check ("val_y == 3.0", r.r1 == 3.0f);
}
#endif
#ifdef TEST_TAGCASE_E2E
static void
test_tagcase_e2e (void)
{
  printf ("\n=== Group: tagcase_e2e (union match and tagcase selection) ===\n");
  struct FUNC_MAIN_results r1 = func_MAIN (1, 3.14f);
  check ("sel=1, res_0 == 2.0", r1.r0 == 2.0f);
  check ("sel=1, res_1 == 4.0", r1.r1 == 4.0f);

  struct FUNC_MAIN_results r2 = func_MAIN (2, 3.14f);
  check ("sel=2, res_0 == 3.14", fabs(r2.r0 - 3.14f) < 1e-5);
  check ("sel=2, res_1 == 3.14", fabs(r2.r1 - 3.14f) < 1e-5);

  struct FUNC_MAIN_results r3 = func_MAIN (3, 3.14f);
  check ("sel=3, res_0 == 5.0", r3.r0 == 5.0f);
  check ("sel=3, res_1 == 3.0", r3.r1 == 3.0f);
}
#endif
#ifdef TEST_COMPLEX_FEATURES_E2E
static void
test_complex_features_e2e (void)
{
  printf ("\n=== Group: complex_features_e2e (combined conditional, tagcase, for-initial, and for-all) ===\n");
  float r1 = func_MAIN (1, 3.14f, 4);
  check ("sel=1 (for initial sum of 1..4) == 10.0", fabs (r1 - 10.0f) < 1e-5);

  float r2 = func_MAIN (2, 3.14f, 4);
  check ("sel=2 (scalar payload * 2) == 6.28", fabs (r2 - 6.28f) < 1e-5);

  float r3 = func_MAIN (3, 3.14f, 4);
  check ("sel=3 (for all array sum) == 12.56", fabs (r3 - 12.56f) < 1e-5);
}
#endif
#ifdef TEST_COMPLEX_OPS_E2E
static void
test_complex_ops_e2e (void)
{
  printf ("\n=== Group: complex_ops_e2e ===\n");
  struct FUNC_MAIN_results r = func_MAIN (1.5f, 2.5f, 3.0f, -4.0f);
  check ("Add real == 4.5", fabs (r.r0 - 4.5f) < 1e-5);
  check ("Add imag == -1.5", fabs (r.r1 - -1.5f) < 1e-5);
  check ("Mul real == 14.5", fabs (r.r2 - 14.5f) < 1e-5);
  check ("Mul imag == 1.5", fabs (r.r3 - 1.5f) < 1e-5);
  check ("Sum real == 6.0", fabs (r.r4 - 6.0f) < 1e-5);
  check ("Sum imag == 10.0", fabs (r.r5 - 10.0f) < 1e-5);
}
#endif

#ifdef TEST_IF_ONE
static void
test_if_one (void)
{
  printf ("\n=== Group: if_one (if/else -> min) ===\n");
  check ("if_one(3,7)=3", func_MAIN (3, 7) == 3);
  check ("if_one(7,3)=3", func_MAIN (7, 3) == 3);
  check ("if_one(5,5)=5", func_MAIN (5, 5) == 5);
}
#endif

#ifdef TEST_IF_TWO
static void
test_if_two (void)
{
  printf ("\n=== Group: if_two (if/elseif/else) ===\n");
  check ("if_two(3,7)=6", func_MAIN (3, 7) == 6); // I<E -> I*2
  check ("if_two(5,5)=8", func_MAIN (5, 5) == 8); // I=E -> E+3
  check ("if_two(7,3)=5", func_MAIN (7, 3) == 5); // else -> I-2
}
#endif

#ifdef TEST_IF_ELSEIF
static void
test_if_elseif (void)
{
  printf ("\n=== Group: if_elseif (3-var elseif chain) ===\n");
  check ("if_elseif(1,2,3)=1", func_MAIN (1, 2, 3) == 1); // I<E
  check ("if_elseif(3,2,5)=2", func_MAIN (3, 2, 5) == 2); // E<F
  check ("if_elseif(5,4,3)=3", func_MAIN (5, 4, 3) == 3); // else -> F
}
#endif

#ifdef TEST_MR_TWO_SCALAR
static void
test_mr_two_scalar (void)
{
  printf ("\n=== Group: mr_two_scalar (multi-result destructure) ===\n");
  // Two2(a,b) = (a+b, a-b); Main returns P+Q = 2a
  check ("mr(10,3)=20", func_MAIN (10, 3) == 20);
  check ("mr(4,9)=8", func_MAIN (4, 9) == 8);
  check ("mr(0,0)=0", func_MAIN (0, 0) == 0);
}
#endif

#ifdef TEST_LET_MULTI_BIND
static void
test_let_multi_bind (void)
{
  printf ("\n=== Group: let_multi_bind (parallel let) ===\n");
  check ("10+20+30=60", func_MAIN () == 60);
}
#endif

#ifdef TEST_LET_SEQ_BIND
static void
test_let_seq_bind (void)
{
  printf ("\n=== Group: let_seq_bind (sequential let) ===\n");
  // Base=5; Doubled=10; Tripled=15; -> 25
  check ("Doubled+Tripled=25", func_MAIN () == 25);
}
#endif

#ifdef TEST_XFA_B2_COND
// for i in 1,n cross j in 1,m returns array_dv of (if i<j then i else j)
static void
test_xfa_b2_cond (void)
{
  printf ("\n=== Group: xfa_b2_cond (if inside forall cross body) ===\n");
  sisal_array_t r = func_MAIN (2, 3);
  // i=1: min(1,1..3)=[1,1,1]; i=2: min(2,1..3)=[1,2,2]
  int32_t exp[] = { 1, 1, 1, 1, 2, 2 };
  bool ok = (r.rank == 2) && ((int)r.dims[0] == 2) && ((int)r.dims[1] == 3);
  for (int k = 0; ok && k < 6; k++)
    ok = ok && (ai (r, k) == exp[k]);
  check ("xfa_b2_cond(2,3) == [1,1,1,1,2,2] 2x3", ok);
  if (r.data)
    free (r.data);
}
#endif

#ifdef TEST_AGGREGATE_ADD
static void
test_aggregate_add (void)
{
  printf ("\n=== Group: aggregate_add (real vector add) ===\n");
  float a[] = { 1.0f, 2.0f, 3.0f };
  float b[] = { 10.0f, 20.0f, 30.0f };
  sisal_array_t A = make_float_arr (a, 3);
  sisal_array_t B = make_float_arr (b, 3);
  sisal_array_t r = func_VECTORADD_CPU (A, B);
  check ("vadd rank-1", r.rank == 1 && (int)r.size == 3);
  check ("vadd[0]=11", near_f (af (r, 0), 11.0f));
  check ("vadd[1]=22", near_f (af (r, 1), 22.0f));
  check ("vadd[2]=33", near_f (af (r, 2), 33.0f));
  if (A.data)
    free (A.data);
  if (B.data)
    free (B.data);
  if (r.data)
    free (r.data);
}
#endif

#ifdef TEST_AREA
// Left-Riemann sum of x^2+1 over [start,finish] in `gran` steps; -> integral
// as gran grows.
static void
test_area (void)
{
  printf ("\n=== Group: area (real Riemann sum) ===\n");
  // integral_1^2 (x^2+1) dx = 10/3; integral_0^1 = 4/3
  check ("area(1,2,100000) ~ 3.3333",
         fabs (func_MAIN (1.0f, 2.0f, 100000) - 3.33333f) < 1e-3f);
  check ("area(0,1,10000)  ~ 1.3333",
         fabs (func_MAIN (0.0f, 1.0f, 10000) - 1.33333f) < 1e-2f);
}
#endif

#ifdef TEST_MULTIDECL
// GetValues() = (10, double(3.14159f)); Main returns (y,x) = (3.14159, 10)
// reordered.
static void
test_multidecl (void)
{
  printf ("\n=== Group: multidecl (mixed multi-result, reordered) ===\n");
  struct MULTIDECL_results r = func_MAIN ();
  check ("multidecl res_0 ~ 3.14159", fabs (r.res_0 - 3.14159) < 1e-4);
  check ("multidecl res_1 = 10", r.res_1 == 10);
}
#endif

#ifdef TEST_LOOPCARRY_USED
// array_dv[double] carried through `for initial`: each iter doubles every
// element; n iters -> x2^n.
static void
test_loopcarry_used (void)
{
  printf ("\n=== Group: loopcarry_used (double array carry, x2/iter) ===\n");
  double a[] = { 1.0, 2.0, 3.0 };
  sisal_array_t A = make_double_arr (a, 3);
  sisal_array_t r = func_MAIN (3, A); // x2 three times = x8
  check ("lcu rank-1", r.rank == 1 && (int)r.size == 3);
  check ("lcu[0]=8", ad (r, 0) == 8.0);
  check ("lcu[1]=16", ad (r, 1) == 16.0);
  check ("lcu[2]=24", ad (r, 2) == 24.0);
  if (A.data)
    free (A.data);
  if (r.data)
    free (r.data);
}
#endif

#ifdef TEST_LOOPCARRY_IDENTITY
// Parallel multi-carry A,B := old A, old B; returns B unchanged.
static void
test_loopcarry_identity (void)
{
  printf ("\n=== Group: loopcarry_identity (parallel multi-carry -> B) ===\n");
  double a[] = { 1.0, 2.0, 3.0 }, b[] = { 10.0, 20.0, 30.0 };
  sisal_array_t A = make_double_arr (a, 3), B = make_double_arr (b, 3);
  sisal_array_t r = func_MAIN (3, A, B);
  check ("lci rank-1", r.rank == 1 && (int)r.size == 3);
  check ("lci[0]=10", ad (r, 0) == 10.0);
  check ("lci[1]=20", ad (r, 1) == 20.0);
  check ("lci[2]=30", ad (r, 2) == 30.0);
  // Identity carry returns B unchanged, so r.data aliases B.data (no copy):
  // free A and B only — freeing r too would double-free.
  if (A.data)
    free (A.data);
  if (B.data)
    free (B.data);
}
#endif

#ifdef TEST_SUB_MATMUL
static void
test_sub_matmul (void)
{
  printf ("\n=== Group: sub_matmul (matmul via 2-D subscripts) ===\n");
  // A[i,k]=i+k, B[k,j]=k*j; C[1,1] = 2*1 + 3*2 = 8
  check ("sub_matmul(2)=8", func_MAIN (2) == 8);
}
#endif

#ifdef TEST_PI
static void
test_pi (void)
{
  printf ("\n=== Group: pi (Leibniz for-initial) ===\n");
  check ("pi(100000) ~ 3.14159", fabs (func_MAIN (100000) - 3.14159f) < 1e-3f);
}
#endif

#ifdef TEST_TEST_MIX_ARRAY_DV
// for i in 1,N returns (array of i) AND (array_dv of i*10) — mixed plain+dv
// outputs.
static void
test_test_mix_array_dv (void)
{
  printf (
      "\n=== Group: test_mix_array_dv (mixed plain + array_dv outputs) ===\n");
  struct MIX_ARRAY_DV_results r = func_MAIN (3);
  bool ok0 = ((int)r.res_0.size == 3);
  for (int k = 0; ok0 && k < 3; k++)
    ok0 = ok0 && (((int32_t *)r.res_0.data)[k] == k + 1);
  bool ok1 = ((int)r.res_1.size == 3);
  for (int k = 0; ok1 && k < 3; k++)
    ok1 = ok1 && (((int32_t *)r.res_1.data)[k] == (k + 1) * 10);
  check ("mix res_0 = [1,2,3]", ok0);
  check ("mix res_1 = [10,20,30]", ok1);
}
#endif

#ifdef TEST_TST_LOOP1_DV
// Hydro fragment: for K in Y returns array_dv of K+K (scatter over a double
// array).
static void
test_tst_loop1_dv (void)
{
  printf ("\n=== Group: tst_loop1_dv (scatter for K in Y -> K+K) ===\n");
  double y[] = { 1.0, 2.0, 3.0 };
  sisal_array_t Y = make_double_arr (y, 3);
  sisal_array_t Z = make_double_arr (y, 3);
  sisal_array_t r = func_MAIN (3, 0.0, 0.0, 0.0, Y, Z);
  check ("hydro rank-1", r.rank == 1 && (int)r.size == 3);
  check ("hydro[0]=2", ad (r, 0) == 2.0);
  check ("hydro[1]=4", ad (r, 1) == 4.0);
  check ("hydro[2]=6", ad (r, 2) == 6.0);
  if (Y.data)
    free (Y.data);
  if (Z.data)
    free (Z.data);
  if (r.data)
    free (r.data);
}
#endif

#ifdef TEST_LOOP2_INNER
// Standalone innermost `for initial` of loop2 (ICCG kernel): array carry Xt +
// int carries k,i. Verified against an INDEPENDENT C reference, element-wise.
// (The same loop nested inside loop2's outer for-initial mis-wires its MERGE
// seeds — see nested_init_merge_dv.sis — but standalone it is correct.)
static void
ref_loop2_inner (int IPNT, int IPNTP, const double *V, const double *X, int n,
                 double *out)
{
  for (int j = 0; j < n; j++)
    out[j] = X[j]; // Xt := X
  int k = IPNT + 2, i = IPNTP;
  while (k <= IPNTP)
    {
      int ok = k;
      k = ok + 2;
      i = i + 1; // k := old k + 2 ; i := old i + 1
      // Xt[i] := Xt[ok] - V[ok]*Xt[ok-1] + V[ok+1]*Xt[ok+1]  (1-based Sisal
      // indices)
      double nv = out[ok - 1] - V[ok - 1] * out[ok - 2] + V[ok] * out[ok];
      out[i - 1] = nv; // Xt := old Xt[i: nv]
    }
}
static void
test_loop2_inner (void)
{
  printf ("\n=== Group: loop2_inner (for-initial array carry, vs C reference) "
          "===\n");
  const int n = 20;
  double Vd[20], Xd[20];
  for (int j = 0; j < n; j++)
    {
      Vd[j] = 0.5 * (j + 1);
      Xd[j] = (double)(j + 1);
    }
  int IPNT = 2, IPNTP = 8; // -> loop runs (k=4,6,8 <= 8), updates Xt[9..11]
  double expd[20];
  ref_loop2_inner (IPNT, IPNTP, Vd, Xd, n, expd);
  sisal_array_t V = make_double_arr (Vd, n), X = make_double_arr (Xd, n);
  sisal_array_t r = func_MAIN (IPNT, IPNTP, V, X);
  bool ok = (r.rank == 1) && ((int)r.size == n);
  for (int j = 0; ok && j < n; j++)
    ok = ok && (fabs (((double *)r.data)[j] - expd[j]) < 1e-9);
  check ("loop2_inner matches C reference (n=20, IPNT=2, IPNTP=8)", ok);
  // also assert the loop actually changed something (Xt[9..11] != X)
  check ("loop2_inner did update Xt[9..11]",
         ((double *)r.data)[8] != Xd[8] && ((double *)r.data)[9] != Xd[9]
             && ((double *)r.data)[10] != Xd[10]);
  if (V.data)
    free (V.data);
  if (X.data)
    free (X.data);
  if (r.data)
    free (r.data);
}
#endif



#ifdef TEST_SUB_2D_DIAG
static void
test_sub_2d_diag (void)
{
  printf ("\n=== Group: sub_2d_diag (A[1,1]+A[2,2]+A[3,3]) ===\n");
  check ("sub_2d_diag(3)=66", func_MAIN (3) == 66); // 11+22+33
}
#endif

#ifdef TEST_LET_NESTED_SEQ
static void
test_let_nested_seq (void)
{
  printf ("\n=== Group: let_nested_seq (nested let scoping) ===\n");
  // X=10; Y=X+5=15; Z=X+Y=25
  check ("let_nested_seq()=25", func_MAIN () == 25);
}
#endif

#ifdef TEST_FORTY2
static void
test_forty2 (void)
{
  printf ("\n=== Group: forty2 (if/elseif with arithmetic) ===\n");
  check ("forty2(1,5,_)=213", func_MAIN (1, 5, 0) == 213); // X<Y -> 3+42*5
  check ("forty2(5,1,_)=40", func_MAIN (5, 1, 0) == 40);   // X>Y -> 3+42-5
  check ("forty2(3,3,3)=11", func_MAIN (3, 3, 3) == 11);   // Z=Y -> 3+42/5
  check ("forty2(3,3,5)=47", func_MAIN (3, 3, 5) == 47);   // else -> 5+42
}
#endif

#ifdef TEST_XFA_B1_DECLDEF
static void
test_xfa_b1_decldef (void)
{
  printf ("\n=== Group: xfa_b1_decldef (cross i*j via body decldef) ===\n");
  sisal_array_t r = func_MAIN (2, 3);
  int32_t exp[] = { 1, 2, 3, 2, 4, 6 };
  bool ok = (r.rank == 2) && ((int)r.dims[0] == 2) && ((int)r.dims[1] == 3);
  for (int k = 0; ok && k < 6; k++)
    ok = ok && (ai (r, k) == exp[k]);
  check ("xfa_b1_decldef(2,3) == [1,2,3,2,4,6] 2x3", ok);
  if (r.data)
    free (r.data);
}
#endif

#ifdef TEST_XFA_C3_3AXIS
static void
test_xfa_c3_3axis (void)
{
  printf ("\n=== Group: xfa_c3_3axis (rank-3 cross i*j*k) ===\n");
  sisal_array_t r = func_MAIN (2, 2, 2);
  int32_t exp[] = { 1, 2, 2, 4, 2, 4, 4, 8 };
  bool ok = (r.rank == 3) && ((int)r.dims[0] == 2) && ((int)r.dims[1] == 2)
            && ((int)r.dims[2] == 2);
  for (int k = 0; ok && k < 8; k++)
    ok = ok && (ai (r, k) == exp[k]);
  check ("xfa_c3_3axis(2,2,2) == [1,2,2,4,2,4,4,8] 2x2x2", ok);
  if (r.data)
    free (r.data);
}
#endif

#ifdef TEST_SLICE_STORE
static void
test_slice_store (void)
{
  printf ("\n=== Group: slice_store (A[2, .. : Z] write-side slice) ===\n");
  sisal_array_t r = func_MAIN (3); // row 2 replaced by zeros
  int32_t exp[] = { 11, 12, 13, 0, 0, 0, 31, 32, 33 };
  bool ok = (r.rank == 2) && ((int)r.dims[0] == 3) && ((int)r.dims[1] == 3);
  for (int k = 0; ok && k < 9; k++)
    ok = ok && (ai (r, k) == exp[k]);
  check ("slice_store(3) == [11,12,13,0,0,0,31,32,33]", ok);
  if (r.data)
    free (r.data);
}
#endif

#ifdef TEST_MR_TWO_ARRAY
static void
test_mr_two_array (void)
{
  printf ("\n=== Group: mr_two_array (multi-array destructure -> P) ===\n");
  double a[] = { 1.0, 2.0, 3.0 };
  sisal_array_t A = make_double_arr (a, 3);
  sisal_array_t r = func_MAIN (3, A); // P = A[i]+1 = [2,3,4]
  check ("mr_two_array rank-1", r.rank == 1 && (int)r.size == 3);
  check ("mr_two_array[0]=2", ad (r, 0) == 2.0);
  check ("mr_two_array[1]=3", ad (r, 1) == 3.0);
  check ("mr_two_array[2]=4", ad (r, 2) == 4.0);
  if (A.data)
    free (A.data);
  if (r.data)
    free (r.data);
}
#endif

#ifdef TEST_AA
static void
test_aa (void)
{
  printf ("\n=== Group: aa (array_dv fill) ===\n");
  sisal_array_t r = func_DVFILL (1, 5, 7); // [7,7,7,7,7]
  check ("dvfill rank-1", r.rank == 1 && (int)r.size == 5);
  bool ok = true;
  for (int k = 0; k < 5; k++)
    ok = ok && (ai (r, k) == 7);
  check ("dvfill(1,5,7) == [7]*5", ok);
  if (r.data)
    free (r.data);
}
#endif

#ifdef TEST_SUB_2D
static void
test_sub_2d (void)
{
  printf ("\n=== Group: sub_2d (2-D subscript A[2,3]) ===\n");
  check ("sub_2d(3)=23", func_MAIN (3) == 23); // 2*10+3
  check ("sub_2d(5)=23", func_MAIN (5) == 23);
}
#endif

#ifdef TEST_SUB_3D
static void
test_sub_3d (void)
{
  printf ("\n=== Group: sub_3d (3-D subscript A[2,3,1]) ===\n");
  check ("sub_3d(3)=231", func_MAIN (3) == 231); // 2*100+3*10+1
  check ("sub_3d(4)=231", func_MAIN (4) == 231);
}
#endif

#ifdef TEST_SLICE_DOTDOT
static void
test_slice_dotdot (void)
{
  printf ("\n=== Group: slice_dotdot (A[2, ..] row slice) ===\n");
  sisal_array_t r = func_MAIN (3); // row 2 of A[i,j]=i*10+j -> [21,22,23]
  check ("slice rank-1", r.rank == 1 && (int)r.size == 3);
  check ("slice[0]=21", ai (r, 0) == 21);
  check ("slice[1]=22", ai (r, 1) == 22);
  check ("slice[2]=23", ai (r, 2) == 23);
}
#endif

#ifdef TEST_TEST_MULTI_ARRAY_IF
// for i in 1,N returns array of (even? i*1.5 : i*0.5)  AND  array of i*i
static void
test_test_multi_array_if (void)
{
  printf ("\n=== Group: test_multi_array_if (dual array output, if-in-body) "
          "===\n");
  struct MULTI_ARRAY_results r = func_MAIN (4);
  double e0[] = { 0.5, 3.0, 1.5, 6.0 };
  int32_t e1[] = { 1, 4, 9, 16 };
  bool ok0 = (r.res_0.rank == 1) && ((int)r.res_0.size == 4);
  for (int k = 0; ok0 && k < 4; k++)
    ok0 = ok0 && (((double *)r.res_0.data)[k] == e0[k]);
  bool ok1 = (r.res_1.rank == 1) && ((int)r.res_1.size == 4);
  for (int k = 0; ok1 && k < 4; k++)
    ok1 = ok1 && (((int32_t *)r.res_1.data)[k] == e1[k]);
  check ("multi_array_if res_0 = [0.5,3,1.5,6]", ok0);
  check ("multi_array_if res_1 = [1,4,9,16]", ok1);
}
#endif

#ifdef TEST_FORALL_DV_AT
// for x in A at i returns array_dv of x + i  (i = 1-based index,
// lower_bound+k)
static void
test_forall_dv_at (void)
{
  printf ("\n=== Group: forall_dv_at (for x in A at i -> x+i) ===\n");
  int32_t d[] = { 10, 20, 30 };
  sisal_array_t A = make_int_arr (d, 3);
  sisal_array_t r = func_MAIN (A);
  check ("at rank-1", r.rank == 1 && (int)r.size == 3);
  check ("at[0]=11", ai (r, 0) == 11);
  check ("at[1]=22", ai (r, 1) == 22);
  check ("at[2]=33", ai (r, 2) == 33);
  if (A.data)
    free (A.data);
  if (r.data)
    free (r.data);
}
#endif

#ifdef TEST_FORALL_DV_CROSS
// for x in A cross y in B returns array_dv of x*y  (rank-2 cartesian product)
static void
test_forall_dv_cross (void)
{
  printf ("\n=== Group: forall_dv_cross (x cross y -> x*y) ===\n");
  int32_t da[] = { 1, 2 }, db[] = { 3, 4 };
  sisal_array_t A = make_int_arr (da, 2), B = make_int_arr (db, 2);
  sisal_array_t r = func_MAIN (A, B);
  check ("cross rank-2", r.rank == 2);
  check ("cross dims 2x2", (int)r.dims[0] == 2 && (int)r.dims[1] == 2);
  check ("cross[0]=3", ai (r, 0) == 3); // 1*3
  check ("cross[1]=4", ai (r, 1) == 4); // 1*4
  check ("cross[2]=6", ai (r, 2) == 6); // 2*3
  check ("cross[3]=8", ai (r, 3) == 8); // 2*4
  if (A.data)
    free (A.data);
  if (B.data)
    free (B.data);
  if (r.data)
    free (r.data);
}
#endif

#ifdef TEST_FORALL_DV_DOT
// for x in A dot y in B returns array_dv of x+y  (zip)
static void
test_forall_dv_dot (void)
{
  printf ("\n=== Group: forall_dv_dot (x dot y -> x+y) ===\n");
  int32_t da[] = { 10, 20, 30 }, db[] = { 1, 2, 3 };
  sisal_array_t A = make_int_arr (da, 3), B = make_int_arr (db, 3);
  sisal_array_t r = func_MAIN (A, B);
  check ("dot rank-1", r.rank == 1 && (int)r.size == 3);
  check ("dot[0]=11", ai (r, 0) == 11);
  check ("dot[1]=22", ai (r, 1) == 22);
  check ("dot[2]=33", ai (r, 2) == 33);
  if (A.data)
    free (A.data);
  if (B.data)
    free (B.data);
  if (r.data)
    free (r.data);
}
#endif

#ifdef TEST_FORALL_DV_DOT3
// for x in A dot y in B dot z in C returns array_dv of x+y+z  (3-way zip)
static void
test_forall_dv_dot3 (void)
{
  printf ("\n=== Group: forall_dv_dot3 (x dot y dot z -> x+y+z) ===\n");
  int32_t da[] = { 1, 2 }, db[] = { 10, 20 }, dc[] = { 100, 200 };
  sisal_array_t A = make_int_arr (da, 2), B = make_int_arr (db, 2),
                C = make_int_arr (dc, 2);
  sisal_array_t r = func_MAIN (A, B, C);
  check ("dot3 rank-1", r.rank == 1 && (int)r.size == 2);
  check ("dot3[0]=111", ai (r, 0) == 111);
  check ("dot3[1]=222", ai (r, 1) == 222);
  if (A.data)
    free (A.data);
  if (B.data)
    free (B.data);
  if (C.data)
    free (C.data);
  if (r.data)
    free (r.data);
}
#endif

#ifdef TEST_FOR_INITIAL_DV
// array_dv carried through a `for initial` loop: v starts as n zeros, each
// iteration i=1..n bumps element i via v := old v[i: DV_LOAD_LINEAR(old
// v,i)+1]. After n iters every element has been bumped once -> all ones.
static void
test_for_initial_dv (void)
{
  printf ("\n=== Group: for_initial_dv (array_dv loop-carry) ===\n");
  for (int n = 1; n <= 5; n++)
    {
      sisal_array_t r = func_MAIN (n);
      bool ok = (r.rank == 1) && ((int)r.size == n);
      for (int k = 0; ok && k < n; k++)
        ok = ok && (ai (r, k) == 1);
      char msg[48];
      snprintf (msg, sizeof msg, "for_initial_dv(%d) == [1]*%d", n, n);
      check (msg, ok);
      if (r.data)
        free (r.data);
    }
}
#endif

#ifdef TEST_RED_SUM
static void
test_red_sum (void)
{
  printf ("\n=== Group: red_sum (value of sum i) ===\n");
  check ("red_sum(5)=15", func_MAIN (5) == 15);
  check ("red_sum(1)=1", func_MAIN (1) == 1);
  check ("red_sum(0)=0", func_MAIN (0) == 0); // empty range -> identity 0
  check ("red_sum(10)=55", func_MAIN (10) == 55);
}
#endif

#ifdef TEST_RED_PRODUCT
static void
test_red_product (void)
{
  printf ("\n=== Group: red_product (value of product i) ===\n");
  check ("red_product(5)=120", func_MAIN (5) == 120);
  check ("red_product(1)=1", func_MAIN (1) == 1);
  check ("red_product(0)=1", func_MAIN (0) == 1); // empty range -> identity 1
  check ("red_product(4)=24", func_MAIN (4) == 24);
}
#endif

#ifdef TEST_RED_GREATEST
static void
test_red_greatest (void)
{
  printf ("\n=== Group: red_greatest (value of greatest i*(N+1-i)) ===\n");
  // N=5: {5,8,9,8,5} -> 9
  check ("red_greatest(5)=9", func_MAIN (5) == 9);
  // N=1: {1*1}=1
  check ("red_greatest(1)=1", func_MAIN (1) == 1);
  // N=4: {4,6,6,4} -> 6
  check ("red_greatest(4)=6", func_MAIN (4) == 6);
}
#endif

#ifdef TEST_RED_LEAST
static void
test_red_least (void)
{
  printf ("\n=== Group: red_least (value of least (i-3)*(i-3)) ===\n");
  // N=5: {4,1,0,1,4} -> 0
  check ("red_least(5)=0", func_MAIN (5) == 0);
  // N=2: {4,1} -> 1
  check ("red_least(2)=1", func_MAIN (2) == 1);
}
#endif

#ifdef TEST_RED_ARGMAX
static void
test_red_argmax (void)
{
  printf ("\n=== Group: red_argmax (value of argmax i*(N+1-i)) ===\n");
  // N=5: {5,8,9,8,5}, peak at i=3
  check ("red_argmax(5)=3", func_MAIN (5) == 3);
  // N=1: only i=1
  check ("red_argmax(1)=1", func_MAIN (1) == 1);
}
#endif

#ifdef TEST_RED_ARGMIN
static void
test_red_argmin (void)
{
  printf ("\n=== Group: red_argmin (value of argmin i*i-6*i) ===\n");
  // N=5: {-5,-8,-9,-8,-5}, min at i=3
  check ("red_argmin(5)=3", func_MAIN (5) == 3);
  // N=2: {-5,-8}, min at i=2
  check ("red_argmin(2)=2", func_MAIN (2) == 2);
}
#endif

#ifdef TEST_RED_SUM_CROSS
static void
test_red_sum_cross (void)
{
  printf (
      "\n=== Group: red_sum_cross (value of sum i*j over i cross j) ===\n");
  // (sum_{1..N} i)*(sum_{1..M} j)
  check ("red_sum_cross(3,4)=60", func_MAIN (3, 4) == 60); // 6*10
  check ("red_sum_cross(2,2)=9", func_MAIN (2, 2) == 9);   // 3*3
  check ("red_sum_cross(1,1)=1", func_MAIN (1, 1) == 1);
}
#endif

#ifdef TEST_BULK_BASIC
static void
test_bulk_basic (void)
{
  printf ("\n=== Group N: dv_bulk_basic ===\n");
  int32_t va_data[] = { 1, 2, 3, 4 };
  int32_t vb_data[] = { 10, 20, 30, 40 };
  sisal_array_t va = make_int_arr (va_data, 4);
  sisal_array_t vb = make_int_arr (vb_data, 4);

  // element-wise add: [11, 22, 33, 44]
  sisal_array_t r = func_T_ARR_ADD (va, vb);
  check ("arr_add[0]", ai (r, 0) == 11);
  check ("arr_add[1]", ai (r, 1) == 22);
  check ("arr_add[2]", ai (r, 2) == 33);
  check ("arr_add[3]", ai (r, 3) == 44);
  if (r.data)
    free (r.data);

  // element-wise sub: [-9, -18, -27, -36]
  r = func_T_ARR_SUB (va, vb);
  check ("arr_sub[0]", ai (r, 0) == -9);
  check ("arr_sub[1]", ai (r, 1) == -18);
  if (r.data)
    free (r.data);

  // element-wise mul: [10, 40, 90, 160]
  r = func_T_ARR_MUL (va, vb);
  check ("arr_mul[0]", ai (r, 0) == 10);
  check ("arr_mul[1]", ai (r, 1) == 40);
  check ("arr_mul[2]", ai (r, 2) == 90);
  if (r.data)
    free (r.data);

  // negate: [-1, -2, -3, -4]
  r = func_T_ARR_NEG (va);
  check ("arr_neg[0]", ai (r, 0) == -1);
  check ("arr_neg[3]", ai (r, 3) == -4);
  if (r.data)
    free (r.data);

  // add scalar: [6, 7, 8, 9]
  r = func_T_ARR_ADD_SCALAR (va, 5);
  check ("arr_add_scalar[0]", ai (r, 0) == 6);
  check ("arr_add_scalar[3]", ai (r, 3) == 9);
  if (r.data)
    free (r.data);

  // mul scalar: [3, 6, 9, 12]
  r = func_T_ARR_MUL_SCALAR (va, 3);
  check ("arr_mul_scalar[0]", ai (r, 0) == 3);
  check ("arr_mul_scalar[3]", ai (r, 3) == 12);
  if (r.data)
    free (r.data);

  // whole-array reductions on [1,2,3,4]
  check ("sum_1234", func_T_SUM (va) == 10);
  check ("product_1234", func_T_PRODUCT (va) == 24);
  check ("least_1234", func_T_LEAST (va) == 1);
  check ("greatest_1234", func_T_GREATEST (va) == 4);

  // compress: mask=[T,F,T,F], data=[1,2,3,4] → [1,3]
  bool mask_data[] = { true, false, true, false };
  sisal_array_t vmask = make_bool_arr (mask_data, 4);
  r = func_T_COMPRESS (vmask, va);
  check ("compress_size", (int32_t)r.size == 2);
  check ("compress[0]", ai (r, 0) == 1);
  check ("compress[1]", ai (r, 1) == 3);
  if (r.data)
    free (r.data);
  if (vmask.data)
    free (vmask.data);

  // sort: [4,2,1,3] → [1,2,3,4]
  int32_t unsorted[] = { 4, 2, 1, 3 };
  sisal_array_t vu = make_int_arr (unsorted, 4);
  r = func_T_SORT (vu);
  check ("sort[0]", ai (r, 0) == 1);
  check ("sort[1]", ai (r, 1) == 2);
  check ("sort[2]", ai (r, 2) == 3);
  check ("sort[3]", ai (r, 3) == 4);
  if (r.data)
    free (r.data);
  if (vu.data)
    free (vu.data);

  // reverse: [1,2,3,4] → [4,3,2,1]
  r = func_T_REVERSE (va);
  check ("reverse[0]", ai (r, 0) == 4);
  check ("reverse[3]", ai (r, 3) == 1);
  if (r.data)
    free (r.data);

  if (va.data)
    free (va.data);
  if (vb.data)
    free (vb.data);
}
#endif

#ifdef TEST_GAUSSJ_PARTS
struct gp_arr2
{
  sisal_array_t res_0, res_1;
};
struct gp_int2
{
  int32_t res_0, res_1;
};
extern "C" int32_t func_IDFAMAX (sisal_array_t A, int32_t N);
extern "C" int32_t func_IDFMAX (sisal_array_t A, int32_t N);
extern "C" gp_arr2 func_GP_TWO (int32_t N, sisal_array_t A);
extern "C" sisal_array_t func_GP_AOR (int32_t N);
extern "C" gp_int2 func_GETPIVOT (int32_t N, sisal_array_t A,
                                  sisal_array_t PIVR);
extern "C" gp_arr2 func_COMPUTE (int32_t N, int32_t PVTROW, sisal_array_t AIN,
                                 sisal_array_t BIN);

static void
test_gaussj_parts (void)
{
  printf ("\n=== Group GJ: gaussj component pieces ===\n");

  // argmax over a row [1,-5,3]: max|.| at idx 2, max at idx 3
  double row[] = { 1.0, -5.0, 3.0 };
  sisal_array_t r = make_double_arr (row, 3);
  check ("idfamax([1,-5,3])=2", func_IDFAMAX (r, 3) == 2);
  check ("idfmax([1,-5,3])=3", func_IDFMAX (r, 3) == 3);
  free (r.data);

  // multi-output 2-array gather: P=A+1, Q=A*2 over [10,20,30]
  double a3[] = { 10.0, 20.0, 30.0 };
  sisal_array_t va = make_double_arr (a3, 3);
  gp_arr2 t = func_GP_TWO (3, va);
  check ("gp_two P[0]=11", ad (t.res_0, 0) == 11.0);
  check ("gp_two P[2]=31", ad (t.res_0, 2) == 31.0);
  check ("gp_two Q[0]=20", ad (t.res_1, 0) == 20.0);
  check ("gp_two Q[2]=60", ad (t.res_1, 2) == 60.0);
  free (va.data);
  free (t.res_0.data);
  free (t.res_1.data);

  // box-then-flatten: array-of-rows -> flat rank-2 [11,12,21,22]
  sisal_array_t ar = func_GP_AOR (2);
  check ("gp_aor rank=2", ar.rank == 2);
  check ("gp_aor size=4", (int)ar.size == 4);
  check ("gp_aor=11 12 21 22", ad (ar, 0) == 11.0 && ad (ar, 1) == 12.0
                                   && ad (ar, 2) == 21.0
                                   && ad (ar, 3) == 22.0);
  free (ar.data);

  // GetPivot on [[0,2],[3,0]], PIVR=[0,0] -> (Icol=1, Irow=2)
  double m[] = { 0, 2, 3, 0 };
  sisal_array_t A2 = make_double_2d (m, 2, 2);
  int32_t pv[] = { 0, 0 };
  sisal_array_t Pv = make_int_arr (pv, 2);
  gp_int2 gp = func_GETPIVOT (2, A2, Pv);
  check ("GetPivot Icol=1", gp.res_0 == 1);
  check ("GetPivot Irow=2", gp.res_1 == 2);
  free (A2.data);
  free (Pv.data);

  // Compute(n=2, pvtrow=1, [[2,4],[1,3]], [2,3]) -> A'=[1,2,0,1], B'=[1,2]
  double cm[] = { 2, 4, 1, 3 };
  sisal_array_t Ac = make_double_2d (cm, 2, 2);
  double cb[] = { 2, 3 };
  sisal_array_t Bc = make_double_arr (cb, 2);
  gp_arr2 c = func_COMPUTE (2, 1, Ac, Bc);
  check ("Compute A'=1 2 0 1", ad (c.res_0, 0) == 1.0 && ad (c.res_0, 1) == 2.0
                                   && ad (c.res_0, 2) == 0.0
                                   && ad (c.res_0, 3) == 1.0);
  check ("Compute B'=1 2", ad (c.res_1, 0) == 1.0 && ad (c.res_1, 1) == 2.0);
  free (Ac.data);
  free (Bc.data);
  free (c.res_0.data);
  free (c.res_1.data);
}
#endif

#ifdef TEST_GAUSSJ
extern "C" sisal_array_t func_MAIN (int32_t N, sisal_array_t A,
                                    sisal_array_t B);
static void
test_gaussj (void)
{
  printf ("\n=== Group GJX: gaussj full solve (gaussj_dv_rr) ===\n");
  // 2x2 swap-forcing [[0,2],[3,0]] b=[4,9] -> x=[3,2]
  {
    double A[] = { 0, 2, 3, 0 }, B[] = { 4, 9 };
    sisal_array_t Aa = make_double_2d (A, 2, 2), Bb = make_double_arr (B, 2);
    sisal_array_t r = func_MAIN (2, Aa, Bb);
    check ("gaussj 2x2 swap x=[3,2]",
           fabs (ad (r, 0) - 3.0) < 1e-9 && fabs (ad (r, 1) - 2.0) < 1e-9);
    free (Aa.data);
    free (Bb.data);
    free (r.data);
  }
  // 2x2 diagonal -> x=[2,3]
  {
    double A[] = { 2, 0, 0, 3 }, B[] = { 4, 9 };
    sisal_array_t Aa = make_double_2d (A, 2, 2), Bb = make_double_arr (B, 2);
    sisal_array_t r = func_MAIN (2, Aa, Bb);
    check ("gaussj 2x2 diag x=[2,3]",
           fabs (ad (r, 0) - 2.0) < 1e-9 && fabs (ad (r, 1) - 3.0) < 1e-9);
    free (Aa.data);
    free (Bb.data);
    free (r.data);
  }
  // 3x3 dense [[2,1,1],[1,3,2],[1,0,0]] b=[4,5,1] -> x=[1,0,2]
  {
    double A[] = { 2, 1, 1, 1, 3, 2, 1, 0, 0 }, B[] = { 4, 5, 1 };
    sisal_array_t Aa = make_double_2d (A, 3, 3), Bb = make_double_arr (B, 3);
    sisal_array_t r = func_MAIN (3, Aa, Bb);
    check ("gaussj 3x3 dense x=[1,0,2]", fabs (ad (r, 0) - 1.0) < 1e-9
                                             && fabs (ad (r, 1) - 0.0) < 1e-9
                                             && fabs (ad (r, 2) - 2.0) < 1e-9);
    free (Aa.data);
    free (Bb.data);
    free (r.data);
  }
  // larger B = A*x round-trip: diagonally dominant, x = 1..n, recover x
  {
    const int n = 12;
    double A[n * n], B[n], x[n];
    for (int i = 0; i < n; i++)
      x[i] = i + 1;
    for (int i = 0; i < n; i++)
      for (int j = 0; j < n; j++)
        A[i * n + j] = (i == j) ? (double)(n + 1) : 1.0;
    for (int i = 0; i < n; i++)
      {
        double s = 0;
        for (int j = 0; j < n; j++)
          s += A[i * n + j] * x[j];
        B[i] = s;
      }
    sisal_array_t Aa = make_double_2d (A, n, n), Bb = make_double_arr (B, n);
    sisal_array_t r = func_MAIN (n, Aa, Bb);
    double e = 0;
    for (int i = 0; i < n; i++)
      {
        double d = fabs (ad (r, i) - x[i]);
        if (d > e)
          e = d;
      }
    check ("gaussj 12x12 B=A*x round-trip (err<1e-9)", e < 1e-9);
    free (Aa.data);
    free (Bb.data);
    free (r.data);
  }
}
#endif

#ifdef TEST_SWAPLOOP
extern "C" sisal_array_t func_MAIN (int32_t N, sisal_array_t A);
static void
test_swaploop (void)
{
  printf (
      "\n=== Group SWAP: in-loop row swap (DV_RANK_REPLACE, aliasing) ===\n");
  double A[] = { 11, 12, 21, 22 };
  {
    sisal_array_t Aa = make_double_2d (A, 2, 2);
    sisal_array_t r = func_MAIN (1, Aa); // one swap
    check ("swaploop n=1 -> 21 22 11 12",
           ad (r, 0) == 21.0 && ad (r, 1) == 22.0 && ad (r, 2) == 11.0
               && ad (r, 3) == 12.0);
    free (Aa.data);
    free (r.data);
  }
  {
    sisal_array_t Aa = make_double_2d (A, 2, 2);
    sisal_array_t r = func_MAIN (2, Aa); // two swaps -> original
    check ("swaploop n=2 -> original (round-trip)",
           ad (r, 0) == 11.0 && ad (r, 1) == 12.0 && ad (r, 2) == 21.0
               && ad (r, 3) == 22.0);
    free (Aa.data);
    free (r.data);
  }
}
#endif

#ifdef TEST_GEN_EXTENT
extern "C" sisal_array_t func_GENEXT_SUB (int32_t n);
extern "C" sisal_array_t func_GENEXT_LB (int32_t n);
extern "C" sisal_array_t func_GENEXT_CROSS (int32_t n, int32_t m);
static void
test_gen_extent (void)
{
  printf ("\n=== Group GE: generator expression-bound lowering ===\n");
  // single-level expr upper bound: i in 1..(n-1).  n=5 -> [1,4,9,16]
  {
    sisal_array_t r = func_GENEXT_SUB (5);
    check ("genext_sub n=5 -> 1 4 9 16",
           (int)r.size == 4 && ai (r, 0) == 1 && ai (r, 1) == 4
               && ai (r, 2) == 9 && ai (r, 3) == 16);
    free (r.data);
  }
  // expr LOWER bound: i in (n-3)..n.  n=6 -> [3,4,5,6]
  {
    sisal_array_t r = func_GENEXT_LB (6);
    check ("genext_lb n=6 -> 3 4 5 6", (int)r.size == 4 && ai (r, 0) == 3
                                           && ai (r, 1) == 4 && ai (r, 2) == 5
                                           && ai (r, 3) == 6);
    free (r.data);
  }
  // cross nest, expr bound on inner axis: i in 1..n, j in 1..(m-1).
  // n=2,m=4 -> rank2 [2,3]: 11 12 13 21 22 23
  {
    sisal_array_t r = func_GENEXT_CROSS (2, 4);
    check ("genext_cross n=2,m=4 rank/dims",
           r.rank == 2 && r.dims[0] == 2 && r.dims[1] == 3);
    check ("genext_cross -> 11 12 13 21 22 23",
           (int)r.size == 6 && ai (r, 0) == 11 && ai (r, 1) == 12
               && ai (r, 2) == 13 && ai (r, 3) == 21 && ai (r, 4) == 22
               && ai (r, 5) == 23);
    free (r.data);
  }
}
#endif

#ifdef TEST_BROADCAST_PARTS
extern "C" int32_t func_BP_RANK (sisal_array_t A);
extern "C" int32_t func_BP_PRODUCT (sisal_array_t S);
extern "C" sisal_array_t func_BP_RESHAPE (sisal_array_t A, sisal_array_t S);
extern "C" int32_t func_BP_OFFSET (sisal_array_t A, int32_t k,
                                   sisal_array_t S);
extern "C" int32_t func_BP_LOAD (sisal_array_t A, int32_t off);
extern "C" sisal_array_t func_BP_BCAST_ADD (sisal_array_t A, sisal_array_t B,
                                            sisal_array_t S, int32_t total);
static void
test_broadcast_parts (void)
{
  printf ("\n=== Group BP: A+B broadcast pieces (bottom-up) ===\n");
  int32_t d1[] = { 1, 2, 3 }, d2[] = { 1, 2, 3, 4, 5, 6 };
  sisal_array_t v3 = make_int_arr (d1, 3);
  sisal_array_t v6 = make_int_arr (d2, 6);
  // Step 0 — rank
  {
    sisal_array_t m = make_int_2d (d2, 2, 3);
    check ("bp_rank([3])=1", func_BP_RANK (v3) == 1);
    check ("bp_rank([2x3])=2", func_BP_RANK (m) == 2);
    free (m.data);
  }
  // Step 1 — product over shape
  {
    int32_t s[] = { 2, 3 }, s2[] = { 2, 3, 4 };
    sisal_array_t S = make_int_arr (s, 2), S2 = make_int_arr (s2, 3);
    check ("bp_product([2,3])=6", func_BP_PRODUCT (S) == 6);
    check ("bp_product([2,3,4])=24", func_BP_PRODUCT (S2) == 24);
    free (S.data);
    free (S2.data);
  }
  // Step 2 — reshape flat[6] by [2,3]
  {
    int32_t s[] = { 2, 3 };
    sisal_array_t S = make_int_arr (s, 2);
    sisal_array_t r = func_BP_RESHAPE (v6, S);
    check ("bp_reshape rank/dims",
           r.rank == 2 && r.dims[0] == 2 && r.dims[1] == 3);
    check ("bp_reshape data 1..6", ai (r, 0) == 1 && ai (r, 1) == 2
                                       && ai (r, 2) == 3 && ai (r, 3) == 4
                                       && ai (r, 4) == 5 && ai (r, 5) == 6);
    // NOTE: reshape aliases the input's data (res = a), so r.data == v6.data
    // -- do NOT free r.data here; v6 is freed once at the end.
    free (S.data);
  }
  // Step 3a — offset (broadcast a [3] across result shape [2,3] -> 0 1 2 0 1
  // 2)
  {
    int32_t a[] = { 10, 20, 30 }, s[] = { 2, 3 };
    sisal_array_t A = make_int_arr (a, 3), S = make_int_arr (s, 2);
    bool ok = true;
    int exp[] = { 0, 1, 2, 0, 1, 2 };
    for (int k = 0; k < 6; k++)
      ok = ok && (func_BP_OFFSET (A, k, S) == exp[k]);
    check ("bp_offset broadcast 0 1 2 0 1 2", ok);
    free (A.data);
    free (S.data);
  }
  // Step 3b — linear load
  {
    int32_t a[] = { 10, 20, 30, 40 };
    sisal_array_t A = make_int_arr (a, 4);
    check ("bp_load(a,0)=10", func_BP_LOAD (A, 0) == 10);
    check ("bp_load(a,2)=30", func_BP_LOAD (A, 2) == 30);
    free (A.data);
  }
  // Step 4 — offset element-wise forall (same-shape + real broadcast)
  {
    int32_t a[] = { 10, 20, 30 }, b[] = { 1, 2, 3 }, s[] = { 3 };
    sisal_array_t A = make_int_arr (a, 3), B = make_int_arr (b, 3),
                  S = make_int_arr (s, 1);
    sisal_array_t r = func_BP_BCAST_ADD (A, B, S, 3);
    check ("bp_bcast_add same-shape -> 11 22 33",
           (int)r.size == 3 && ai (r, 0) == 11 && ai (r, 1) == 22
               && ai (r, 2) == 33);
    free (A.data);
    free (B.data);
    free (S.data);
    free (r.data);
  }
  {
    int32_t a[] = { 1, 2, 3, 4, 5, 6 }, b[] = { 10, 20, 30 }, s[] = { 2, 3 };
    sisal_array_t A = make_int_2d (a, 2, 3), B = make_int_arr (b, 3),
                  S = make_int_arr (s, 2);
    sisal_array_t r = func_BP_BCAST_ADD (A, B, S, 6);
    check ("bp_bcast_add broadcast -> 11 22 33 14 25 36",
           (int)r.size == 6 && ai (r, 0) == 11 && ai (r, 1) == 22
               && ai (r, 2) == 33 && ai (r, 3) == 14 && ai (r, 4) == 25
               && ai (r, 5) == 36);
    free (A.data);
    free (B.data);
    free (S.data);
    free (r.data);
  }
  free (v3.data);
  free (v6.data);
}
#endif

#ifdef TEST_IF_COND
extern "C" int32_t func_IFMIN (int32_t a, int32_t b);
extern "C" int32_t func_IF3 (int32_t i, int32_t e);
extern "C" int32_t func_IF3V (int32_t i, int32_t e, int32_t f);
extern "C" int32_t func_IFDEEP (int32_t x);
static void
test_if_cond (void)
{
  printf ("\n=== Group IF: if / elseif / else chains ===\n");
  // simple if/else = min
  check ("ifmin(3,5)=3", func_IFMIN (3, 5) == 3);
  check ("ifmin(5,3)=3", func_IFMIN (5, 3) == 3);
  // one elseif: i<e -> i*2 ; i=e -> e+3 ; else -> i-2
  check ("if3(2,5)=4 (i<e)", func_IF3 (2, 5) == 4);
  check ("if3(5,5)=8 (i=e)", func_IF3 (5, 5) == 8);
  check ("if3(7,5)=5 (else)", func_IF3 (7, 5) == 5);
  // elseif over 3 vars: i<e -> i ; e<f -> e ; else -> f
  check ("if3v(1,5,9)=1 (i<e)", func_IF3V (1, 5, 9) == 1);
  check ("if3v(5,3,9)=3 (e<f)", func_IF3V (5, 3, 9) == 3);
  check ("if3v(5,3,1)=1 (else f)", func_IF3V (5, 3, 1) == 1);
  // deep 6-branch chain
  check ("ifdeep(0)=10", func_IFDEEP (0) == 10);
  check ("ifdeep(2)=30", func_IFDEEP (2) == 30);
  check ("ifdeep(4)=50", func_IFDEEP (4) == 50);
  check ("ifdeep(5)=60", func_IFDEEP (5) == 60);
  check ("ifdeep(9)=60", func_IFDEEP (9) == 60);
}
#endif

// ============================================================
// GROUP FDS — forall_dv_simple  (for i in 1..N → array_dv of i*i)
// ============================================================
#ifdef TEST_FORALL_DV_SIMPLE
extern "C" sisal_array_t func_MAIN (int32_t N);
static void
test_forall_dv_simple (void)
{
  printf ("\n=== Group FDS: forall_dv_simple (i*i) ===\n");
  // func_MAIN(5) → [1, 4, 9, 16, 25]
  sisal_array_t r = func_MAIN (5);
  int32_t exp[] = { 1, 4, 9, 16, 25 };
  check ("fds_size", (int32_t)r.size == 5);
  for (int i = 0; i < 5; i++)
    {
      char n[32];
      snprintf (n, sizeof n, "fds[%d]", i);
      check (n, ai (r, i) == exp[i]);
    }
  if (r.data)
    free (r.data);
}
#endif

// ============================================================
// GROUP CDD — cross_dv_demo  (for i in 1..N cross j in 1..M → array_dv of i*j)
// ============================================================
#ifdef TEST_CROSS_DV_DEMO
extern "C" sisal_array_t func_MAIN (int32_t N, int32_t M);
static void
test_cross_dv_demo (void)
{
  printf ("\n=== Group CDD: cross_dv_demo (i*j cross) ===\n");
  // func_MAIN(2,3): i in 1..2 cross j in 1..3 → [1,2,3, 2,4,6]
  sisal_array_t r = func_MAIN (2, 3);
  int32_t exp[] = { 1, 2, 3, 2, 4, 6 };
  check ("cdd_size", (int32_t)r.size == 6);
  for (int i = 0; i < 6; i++)
    {
      char n[32];
      snprintf (n, sizeof n, "cdd[%d]", i);
      check (n, ai (r, i) == exp[i]);
    }
  if (r.data)
    free (r.data);
}
#endif

// ============================================================
// GROUP FN — forall_negate  (for i in 1..N → array_dv of -real(i))
// ============================================================
#ifdef TEST_FORALL_NEGATE
extern "C" sisal_array_t func_MAIN_GPU (int32_t N);
static void
test_forall_negate (void)
{
  printf ("\n=== Group FN: forall_negate (-real(i)) ===\n");
  // func_MAIN_GPU(4) → [-1.0, -2.0, -3.0, -4.0]
  sisal_array_t r = func_MAIN_GPU (4);
  float exp[] = { -1.0f, -2.0f, -3.0f, -4.0f };
  check ("fn_size", (int32_t)r.size == 4);
  for (int i = 0; i < 4; i++)
    {
      char n[32];
      snprintf (n, sizeof n, "fn[%d]", i);
      check (n, near_f (af (r, i), exp[i]));
    }
  if (r.data)
    free (r.data);
}
#endif

#ifdef TEST_NEWTON_RAPHSON
static void
test_newton_raphson (void)
{
  printf ("\n=== Group: newton_raphson (iterative sqrt, LoopA) ===\n");
  check ("newton_raphson sqrt(25.0) == 5.0", fabs(func_MAIN(25.0f, 1e-4f) - 5.0f) < 1e-4f);
  check ("newton_raphson sqrt(2.0) == 1.4142", fabs(func_MAIN(2.0f, 1e-4f) - 1.4142135f) < 1e-4f);
}
#endif

#ifdef TEST_FEO_FFT_PARTS1
static void
test_feo_fft_parts1 (void)
{
  printf ("\n=== Group: feo_fft_parts1 ===\n");
  FUNC_MAIN_results r = func_MAIN();
  check ("log2(16) == 4", r.res_0 == 4);
  check ("cmult real == -5.0", fabs(r.res_1 - (-5.0)) < 1e-9);
  check ("cmult imag == 10.0", fabs(r.res_2 - 10.0) < 1e-9);
  check ("data real size == 4", r.res_3.size == 4);
  check ("data imag size == 4", r.res_4.size == 4);
}
#endif

#ifdef TEST_FEO_FFT_PARTS2
static void
test_feo_fft_parts2 (void)
{
  printf ("\n=== Group: feo_fft_parts2 ===\n");
  FUNC_MAIN_results r = func_MAIN();
  check ("W[0] size == 3", r.res_0.size == 3);
  check ("W[1] size == 3", r.res_1.size == 3);
}
#endif

#ifdef TEST_FEO_FFT_PARTS3
static void
test_feo_fft_parts3 (void)
{
  printf ("\n=== Group: feo_fft_parts3 (radix-4 butterfly, values vs python DFT) ===\n");
  FUNC_MAIN_results r = func_MAIN();
  // Pack_j on x=[1,2,3,4], im=0, twiddles=(1,0): DFT([1,2,3,4]) in decimated order.
  // are/bre/cre/dre = 10,-2,-2,-2 ; aim/bim/cim/dim = 0,0,2,-2  (python-verified)
  sisal_array_t o[8] = { r.res_0, r.res_1, r.res_2, r.res_3, r.res_4, r.res_5, r.res_6, r.res_7 };
  double ex[8] = { 10, 0, -2, 0, -2, 2, -2, -2 };
  const char *nm[8] = { "are", "aim", "bre", "bim", "cre", "cim", "dre", "dim" };
  for (int i = 0; i < 8; i++) {
    bool ok = (o[i].size == 1) && (fabs (((double *) o[i].data)[0] - ex[i]) < 1e-9);
    char msg[64];
    snprintf (msg, sizeof msg, "Pack_j %s == %g", nm[i], ex[i]);
    check (msg, ok);
  }
}
#endif

#ifdef TEST_FEO_FFT_PARTS4
static void
test_feo_fft_parts4 (void)
{
  printf ("\n=== Group: feo_fft_parts4 ===\n");
  FUNC_MAIN_results r = func_MAIN();
  check ("level_1: i == 1", r.res_0 == 1);
  check ("level_1: cards == 1", r.res_1 == 1);
  check ("level_1: packs == 4", r.res_2 == 4);
  check ("level_1: xre size == 4", r.res_3.size == 4);
  check ("level_1: xim size == 4", r.res_4.size == 4);
}
#endif

#ifdef TEST_FEO_FFT_DV
static void
test_feo_fft_dv (void)
{
  printf ("\n=== Group: feo_fft_dv (Full Radix-4 FFT) ===\n");
  FUNC_MAIN_results r = func_MAIN(4);
  printf("DEBUG size: %llu %llu\n", (unsigned long long)r.res_0.size, (unsigned long long)r.res_1.size);
  check ("res_0 size == 4", r.res_0.size == 4);
  check ("res_1 size == 4", r.res_1.size == 4);
}
#endif

#ifdef TEST_FEO_FFT
static void
test_feo_fft (void)
{
  printf ("\n=== Group: feo_fft (Full Radix-4 standard) ===\n");
  FUNC_MAIN_results r = func_MAIN(4);
  check ("res_0 size == 4", r.res_0.size == 4);
  check ("res_1 size == 4", r.res_1.size == 4);
}
#endif

// ---- Livermore loop kernels: independent C references + checks ----
#ifdef TEST_LOOP1_DV
// Hydro: X[k] = Q + Y[k]*(R*Z[k+10] + T*Z[k+11])  (Sisal 1-based; Z needs
// n+11)
static void
test_loop1_dv (void)
{
  printf ("\n=== Group: loop1_dv (hydro fragment, vs C reference) ===\n");
  const int n = 8;
  double Q = 1.0, R = 2.0, T = 3.0;
  double Y[8];
  for (int i = 0; i < n; i++)
    Y[i] = (double)(i + 1);
  double Z[19];
  for (int j = 0; j < n + 11; j++)
    Z[j] = 0.1 * (j + 1);
  double exp[8];
  for (int k = 0; k < n; k++)
    exp[k] = Q + Y[k] * (R * Z[k + 10] + T * Z[k + 11]);
  sisal_array_t Ya = make_double_arr (Y, n), Za = make_double_arr (Z, n + 11);
  sisal_array_t r = func_MAIN (1, n, Q, R, T, Ya, Za);
  bool ok = (r.rank == 1) && ((int)r.size == n);
  for (int k = 0; ok && k < n; k++)
    ok = ok && (fabs (ad (r, k) - exp[k]) < 1e-9);
  check ("loop1_dv hydro matches C reference (n=8)", ok);
  if (Ya.data)
    free (Ya.data);
  if (Za.data)
    free (Za.data);
  if (r.data)
    free (r.data);
}
#endif
#ifdef TEST_LOOP3_DV
// Inner product: sum_{i=1..n} X[i]*Z[i]
static void
test_loop3_dv (void)
{
  printf ("\n=== Group: loop3_dv (inner product, vs C reference) ===\n");
  const int n = 5;
  double X[5], Z[5];
  double exp = 0.0;
  for (int i = 0; i < n; i++)
    {
      X[i] = i + 1;
      Z[i] = i + 1;
      exp += X[i] * Z[i];
    }
  sisal_array_t Xa = make_double_arr (X, n), Za = make_double_arr (Z, n);
  double r = func_MAIN (1, n, Xa, Za);
  check ("loop3_dv inner product == 55", fabs (r - exp) < 1e-9);
  if (Xa.data)
    free (Xa.data);
  if (Za.data)
    free (Za.data);
}
#endif
#ifdef TEST_LOOP7_DV
// Equation of state: out[k] = U[k] + R*(Z[k]+R*Y[k])
//   + T*(U[k+3]+R*(U[k+2]+R*U[k+1]) + T*(U[k+6]+R*(U[k+5]+R*U[k+4])))  (U
//   needs n+6)
static void
test_loop7_dv (void)
{
  printf ("\n=== Group: loop7_dv (equation of state, vs C reference) ===\n");
  const int n = 6;
  double R = 0.5, T = 0.25;
  double U[12];
  for (int i = 0; i < n + 6; i++)
    U[i] = 0.1 * (i + 1);
  double Y[6], Z[6];
  for (int i = 0; i < n; i++)
    {
      Y[i] = i + 1;
      Z[i] = 2 * (i + 1);
    }
  double exp[6];
  for (int k = 0; k < n; k++)
    exp[k] = U[k] + R * (Z[k] + R * Y[k])
             + T
                   * (U[k + 3] + R * (U[k + 2] + R * U[k + 1])
                      + T * (U[k + 6] + R * (U[k + 5] + R * U[k + 4])));
  sisal_array_t Ua = make_double_arr (U, n + 6), Ya = make_double_arr (Y, n),
                Za = make_double_arr (Z, n);
  sisal_array_t r = func_MAIN (1, n, R, T, Ua, Ya, Za);
  bool ok = (r.rank == 1) && ((int)r.size == n);
  for (int k = 0; ok && k < n; k++)
    ok = ok && (fabs (ad (r, k) - exp[k]) < 1e-9);
  check ("loop7_dv eos matches C reference (n=6)", ok);
  if (Ua.data)
    free (Ua.data);
  if (Ya.data)
    free (Ya.data);
  if (Za.data)
    free (Za.data);
  if (r.data)
    free (r.data);
}
#endif
#ifdef TEST_LOOP12_DV
// First difference: out[i] = Y[i+1] - Y[i]  (Y needs n+1)
static void
test_loop12_dv (void)
{
  printf ("\n=== Group: loop12_dv (first difference, vs C reference) ===\n");
  const int n = 6;
  double Y[7];
  for (int i = 0; i < n + 1; i++)
    Y[i] = (double)(i * i);
  double exp[6];
  for (int i = 0; i < n; i++)
    exp[i] = Y[i + 1] - Y[i];
  sisal_array_t Ya = make_double_arr (Y, n + 1);
  sisal_array_t r = func_MAIN (1, n, Ya);
  bool ok = (r.rank == 1) && ((int)r.size == n);
  for (int i = 0; ok && i < n; i++)
    ok = ok && (fabs (ad (r, i) - exp[i]) < 1e-9);
  check ("loop12_dv first-difference matches C reference (2i+1)", ok);
  if (Ya.data)
    free (Ya.data);
  if (r.data)
    free (r.data);
}
#endif
#ifdef TEST_LOOP24_DV
// Location (1-based) of first minimum: loc=1; for k=2..n if X[k]<X[loc] loc=k
static void
test_loop24_dv (void)
{
  printf (
      "\n=== Group: loop24_dv (first-minimum location, vs C reference) ===\n");
  const int n = 7;
  double X[7]
      = { 5.0, 3.0, 8.0, 1.0, 1.0, 9.0, 2.0 }; // first min (1.0) at 1-based 4
  int loc = 1;
  for (int k = 2; k <= n; k++)
    if (X[k - 1] < X[loc - 1])
      loc = k;
  sisal_array_t Xa = make_double_arr (X, n);
  int32_t r = func_MAIN (1, n, Xa);
  check ("loop24_dv first-min location == 4", r == loc && r == 4);
  if (Xa.data)
    free (Xa.data);
}
#endif

#ifdef TEST_LOOP9_DV
// Integrate predictors: out[i] = PX[3,i] + CO*(PX[5,i]+PX[6,i]) + DM22*PX[7,i]
//   + DM23*PX[8,i] + ... + DM28*PX[13,i].  PX is 13 rows x n cols (row-major).
static void
test_loop9_dv (void)
{
  printf (
      "\n=== Group: loop9_dv (integrate predictors, vs C reference) ===\n");
  const int n = 4, R = 13;
  double CO = 0.5, DM[7] = { 0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7 }; // DM22..DM28
  double PX[13 * 4];
  for (int r = 1; r <= R; r++)
    for (int c = 1; c <= n; c++)
      PX[(r - 1) * n + (c - 1)] = (double)(r * 100 + c);
#define PXV(r, i) PX[((r) - 1) * n + ((i) - 1)]
  double exp[4];
  for (int i = 1; i <= n; i++)
    exp[i - 1] = PXV (3, i) + CO * (PXV (5, i) + PXV (6, i))
                 + DM[0] * PXV (7, i) + DM[1] * PXV (8, i) + DM[2] * PXV (9, i)
                 + DM[3] * PXV (10, i) + DM[4] * PXV (11, i)
                 + DM[5] * PXV (12, i) + DM[6] * PXV (13, i);
#undef PXV
  sisal_array_t PXa = make_double_2d (PX, R, n);
  sisal_array_t r = func_MAIN (1, n, CO, DM[0], DM[1], DM[2], DM[3], DM[4],
                               DM[5], DM[6], PXa);
  bool ok = (r.rank == 1) && ((int)r.size == n);
  for (int i = 0; ok && i < n; i++)
    ok = ok && (fabs (ad (r, i) - exp[i]) < 1e-6);
  check ("loop9_dv integrate-predictors matches C reference (n=4)", ok);
  if (PXa.data)
    free (PXa.data);
  if (r.data)
    free (r.data);
}
#endif

#ifdef TEST_LOOP10_DV
static void
test_loop10_dv (void)
{
  printf (
      "\n=== Group: loop10_dv (difference predictors, vs C reference) ===\n");
  const int R = 14, n = 2;
  double CX[28], PX[28];
  for (int r = 1; r <= R; r++)
    {
      for (int c = 1; c <= n; c++)
        {
          CX[(r - 1) * n + c - 1] = 100 + r;
          PX[(r - 1) * n + c - 1] = r;
        }
    }
  double ref[10 * n];
  for (int c = 0; c < n; c++)
    {
      double px = CX[(5 - 1) * n + c];
      ref[0 * n + c] = px;
      for (int k = 6; k <= 14; k++)
        {
          px = px - PX[((k - 1) - 1) * n + c];
          ref[(k - 5) * n + c] = px;
        }
    }
  sisal_array_t CXa = make_double_2d (CX, R, n);
  sisal_array_t PXa = make_double_2d (PX, R, n);
  sisal_array_t r = func_MAIN (1, n, CXa, PXa);
  bool ok = ((int)r.dims[0] == 10) && ((int)r.dims[1] == n);
  for (int k = 0; ok && k < 10 * n; k++)
    {
      ok = ok && (fabs (ad (r, k) - ref[k]) < 1e-9);
    }
  check ("loop10_dv difference-predictors matches C reference", ok);
  if (CXa.data)
    free (CXa.data);
  if (PXa.data)
    free (PXa.data);
  if (r.data)
    free (r.data);
}
#endif
#ifdef TEST_LOOP21_DV
// Matrix*matrix: out[i,j] = PX[i,j] + sum_{k=1..25} VY[i,k]*CX[j,k], i=1..25,
// j=1..n.
//   CX is n x 25, VY is 25 x 25, PX is 25 x n; output is 25 x n (row-major).
static void
test_loop21_dv (void)
{
  printf (
      "\n=== Group: loop21_dv (matrix*matrix product, vs C reference) ===\n");
  const int n = 3, M = 25;
  double CX[3 * 25], VY[25 * 25], PX[25 * 3];
  for (int j = 1; j <= n; j++)
    for (int k = 1; k <= M; k++)
      CX[(j - 1) * M + (k - 1)] = 0.01 * (j + k);
  for (int i = 1; i <= M; i++)
    for (int k = 1; k <= M; k++)
      VY[(i - 1) * M + (k - 1)] = 0.01 * ((i * k) % 7);
  for (int i = 1; i <= M; i++)
    for (int j = 1; j <= n; j++)
      PX[(i - 1) * n + (j - 1)] = 0.1 * (i + j);
  double exp[25 * 3];
  for (int i = 1; i <= M; i++)
    for (int j = 1; j <= n; j++)
      {
        double s = 0.0;
        for (int k = 1; k <= M; k++)
          s += VY[(i - 1) * M + (k - 1)] * CX[(j - 1) * M + (k - 1)];
        exp[(i - 1) * n + (j - 1)] = PX[(i - 1) * n + (j - 1)] + s;
      }
  sisal_array_t CXa = make_double_2d (CX, n, M),
                PXa = make_double_2d (PX, M, n),
                VYa = make_double_2d (VY, M, M);
  sisal_array_t r = func_MAIN (1, n, CXa, PXa, VYa);
  bool ok = (r.rank == 2) && ((int)r.dims[0] == M) && ((int)r.dims[1] == n);
  for (int t = 0; ok && t < M * n; t++)
    ok = ok && (fabs (ad (r, t) - exp[t]) < 1e-6);
  check ("loop21_dv matrix*matrix matches C reference (25x3)", ok);
  if (CXa.data)
    free (CXa.data);
  if (PXa.data)
    free (PXa.data);
  if (VYa.data)
    free (VYa.data);
  if (r.data)
    free (r.data);
}
#endif

#if defined(TEST_LOOP2_DV) || defined(TEST_LOOP2S_DV)
// ICCG excerpt (loop2 / loop2s -- identical kernels, only formatting differs):
// outer halving sweep (IL = n, n/2, ...) driving an inner tridiagonal-style
// update Xt[i] = Xt[k] - V[k]*Xt[k-1] + V[k+1]*Xt[k+1] (Sisal 1-based).
// In-place on X matches the Sisal `old Xt` semantics: each inner step writes
// one element and later steps read it back, which is exactly the running
// carry.  (This is the full kernel whose inner-only form is loop2_inner.)
static void
ref_loop2 (int n, const double *V, const double *Xin, int sz, double *X)
{
  for (int j = 0; j < sz; j++)
    X[j] = Xin[j];
  int IL = n, IPNTP = 0;
  while (IL > 1)
    {
      int IPNT = IPNTP;
      IPNTP = IPNTP + IL;
      IL = IL / 2;
      int k = IPNT + 2, i = IPNTP;
      while (k <= IPNTP)
        {
          int ok = k;
          k = ok + 2;
          i = i + 1;
          X[i - 1] = X[ok - 1] - V[ok - 1] * X[ok - 2] + V[ok] * X[ok];
        }
    }
}
#endif
#ifdef TEST_LOOP2_DV
static void
test_loop2_dv (void)
{
  printf ("\n=== Group: loop2_dv (ICCG excerpt, vs C reference) ===\n");
  const int n = 8, sz = 24;
  double V[24], Xin[24];
  for (int j = 0; j < sz; j++)
    {
      V[j] = 0.1 * (j + 1);
      Xin[j] = (double)(j + 1);
    }
  double exp[24];
  ref_loop2 (n, V, Xin, sz, exp);
  sisal_array_t Va = make_double_arr (V, sz), Xa = make_double_arr (Xin, sz);
  sisal_array_t r = func_MAIN (1, n, Va, Xa);
  bool ok = (r.rank == 1) && ((int)r.size == sz);
  for (int j = 0; ok && j < sz; j++)
    ok = ok && (fabs (ad (r, j) - exp[j]) < 1e-9);
  check ("loop2_dv ICCG matches C reference (n=8)", ok);
  check ("loop2_dv did update X (X[11] != Xin[11])",
         fabs (ad (r, 11) - Xin[11]) > 1e-12);
  if (Va.data)
    free (Va.data);
  if (Xa.data)
    free (Xa.data);
  if (r.data)
    free (r.data);
}
#endif
#ifdef TEST_LOOP2S_DV
// loop2s = loop2 with different source formatting only; same ref_loop2.
static void
test_loop2s_dv (void)
{
  printf ("\n=== Group: loop2s_dv (ICCG excerpt, vs C reference) ===\n");
  const int n = 8, sz = 24;
  double V[24], Xin[24];
  for (int j = 0; j < sz; j++)
    {
      V[j] = 0.1 * (j + 1);
      Xin[j] = (double)(j + 1);
    }
  double exp[24];
  ref_loop2 (n, V, Xin, sz, exp);
  sisal_array_t Va = make_double_arr (V, sz), Xa = make_double_arr (Xin, sz);
  sisal_array_t r = func_MAIN (1, n, Va, Xa);
  bool ok = (r.rank == 1) && ((int)r.size == sz);
  for (int j = 0; ok && j < sz; j++)
    ok = ok && (fabs (ad (r, j) - exp[j]) < 1e-9);
  check ("loop2s_dv ICCG matches C reference (n=8)", ok);
  if (Va.data)
    free (Va.data);
  if (Xa.data)
    free (Xa.data);
  if (r.data)
    free (r.data);
}
#endif

#ifdef TEST_LOOP6_DV
// General linear recurrence: for ii=2..n,  W[ii] += sum_{k=1..ii-1}
// B[ii,k]*W[ii-k]
//   (Sisal 1-based; running W -- reads previously-updated lower indices).  B
//   is nxn.
static void
test_loop6_dv (void)
{
  printf ("\n=== Group: loop6_dv (general linear recurrence, vs C reference) "
          "===\n");
  const int n = 5;
  double B[5 * 5];
  for (int r = 1; r <= n; r++)
    for (int c = 1; c <= n; c++)
      B[(r - 1) * n + (c - 1)] = 0.1 * (r + c);
  double Win[5];
  for (int j = 0; j < n; j++)
    Win[j] = (double)(j + 1);
  double W[5];
  for (int j = 0; j < n; j++)
    W[j] = Win[j];
  for (int ii = 2; ii <= n; ii++)
    {
      double V = 0.0;
      for (int k = 1; k <= ii - 1; k++)
        V += B[(ii - 1) * n + (k - 1)] * W[(ii - k) - 1];
      W[ii - 1] += V;
    }
  sisal_array_t Ba = make_double_2d (B, n, n), Wa = make_double_arr (Win, n);
  sisal_array_t r = func_MAIN (1, n, Ba, Wa);
  bool ok = (r.rank == 1) && ((int)r.size == n);
  for (int j = 0; ok && j < n; j++)
    ok = ok && (fabs (ad (r, j) - W[j]) < 1e-9);
  check ("loop6_dv linear-recurrence matches C reference (n=5)", ok);
  if (Ba.data)
    free (Ba.data);
  if (Wa.data)
    free (Wa.data);
  if (r.data)
    free (r.data);
}
#endif
#ifdef TEST_LOOP4_DV
// Banded linear (steps<6 branch): for p in {6,503,1000} (1-based):
//   T = X[p] - sum_{i=1..steps} X[p-6+i]*Y[5i];  X[p] := T*Y[5].  (Ts use
//   original X.)
static void
test_loop4_dv (void)
{
  printf (
      "\n=== Group: loop4_dv (banded linear equations, vs C reference) ===\n");
  const int n = 20, sz = 1000; // steps = n/5 = 4  (< 6 branch)
  const int steps = n / 5;
  double *X = (double *)malloc (sz * sizeof (double));
  for (int j = 0; j < sz; j++)
    X[j] = 0.001 * (j + 1);
  double Y[30];
  for (int j = 0; j < 30; j++)
    Y[j] = 0.01 * (j + 1);
  int Pp[3] = { 6, 503, 1000 };
  double *exp = (double *)malloc (sz * sizeof (double));
  for (int j = 0; j < sz; j++)
    exp[j] = X[j];
  for (int t = 0; t < 3; t++)
    {
      int p = Pp[t];
      double T = X[p - 1];
      for (int i = 1; i <= steps; i++)
        T -= X[(p - 6 + i) - 1] * Y[(5 * i) - 1];
      exp[p - 1] = T * Y[5 - 1];
    }
  sisal_array_t Xa = make_double_arr (X, sz), Ya = make_double_arr (Y, 30);
  sisal_array_t r = func_MAIN (1, n, Xa, Ya);
  bool ok = (r.rank == 1) && ((int)r.size == sz);
  for (int j = 0; ok && j < sz; j++)
    ok = ok && (fabs (ad (r, j) - exp[j]) < 1e-9);
  check ("loop4_dv banded-linear matches C reference (n=20)", ok);
  check ("loop4_dv updated X[6],X[503],X[1000]",
         fabs (ad (r, 5) - X[5]) > 1e-15 && fabs (ad (r, 502) - X[502]) > 1e-15
             && fabs (ad (r, 999) - X[999]) > 1e-15);
  free (X);
  free (exp);
  if (Xa.data)
    free (Xa.data);
  if (Ya.data)
    free (Ya.data);
  if (r.data)
    free (r.data);
}
#endif

#ifdef TEST_MR2_INIT
// Minimal two-array for-initial return: H = all 10, P = all 20 (n x n). Guards
// the multi-return tuple wiring -- the per-clause (node,port) resolution fix.
// Without it both slots collapse to one carry.
static void
test_mr2_init (void)
{
  printf ("\n=== Group: mr2_init (for-initial returns two array_dv carries) "
          "===\n");
  const int n = 3, sz = n * n;
  struct MR2_results r = func_MAIN (n);
  bool ok = (r.res_0.rank == 2) && ((int)r.res_0.dims[0] == n)
            && ((int)r.res_0.dims[1] == n) && (r.res_1.rank == 2)
            && ((int)r.res_1.dims[0] == n) && ((int)r.res_1.dims[1] == n);
  for (int t = 0; ok && t < sz; t++)
    ok = ok && (ai (r.res_0, t) == 10) && (ai (r.res_1, t) == 20);
  check ("mr2_init res_0 all 10 (H) AND res_1 all 20 (P) -- distinct returns",
         ok);
  if (r.res_0.data)
    free (r.res_0.data);
  if (r.res_1.data)
    free (r.res_1.data);
}
#endif
#ifdef TEST_LOOP16_DV
// Monte Carlo search (loop16): Y = least j4 of cells whose classifier C1==0;
// then (v1,v2) = Y==BIG ? (1,0) : ((Y-3)/(2n)+1, Y).  Sisal `exp(a,b)` is
// power -> pow.
static void
ref_loop16 (int n, double R, double S, double T, const double *D,
            const double *PLAN, const int *ZONE, int *v1, int *v2)
{
  int Z1 = ZONE[0];
  long BIG = 2L * n * Z1 + 2, Y = BIG;
  for (int j = 1; j <= n; j++)
    for (int i = 1; i <= Z1; i++)
      {
        int m = n * (i - 1) + j - 1;
        int j4 = 2 * m + 3;
        int j5 = ZONE[j4 - 1];
        int C1;
        if (j5 < n / 3)
          C1 = (PLAN[j5 - 1] < T)    ? ZONE[j4 - 2]
               : (PLAN[j5 - 1] == T) ? 0
                                     : -ZONE[j4 - 2];
        else if (j5 < 2 * n / 3)
          C1 = (PLAN[j5 - 1] < S)    ? ZONE[j4 - 2]
               : (PLAN[j5 - 1] == S) ? 0
                                     : -ZONE[j4 - 2];
        else if (j5 < n)
          C1 = (PLAN[j5 - 1] < R)    ? ZONE[j4 - 2]
               : (PLAN[j5 - 1] == R) ? 0
                                     : -ZONE[j4 - 2];
        else if (j5 == n)
          C1 = 0;
        else
          {
            double test
                = D[j5 - 1]
                  - (D[j5 - 2] * pow (T - D[j5 - 3], 2)
                     + pow (S - D[j5 - 4], 2) + pow (R - D[j5 - 5], 2));
            C1 = (test < 0.0) ? ZONE[j4 - 2] : -ZONE[j4 - 2];
          }
        long cand = (C1 == 0) ? j4 : BIG;
        if (cand < Y)
          Y = cand;
      }
  if (Y == BIG)
    {
      *v1 = 1;
      *v2 = 0;
    }
  else
    {
      *v1 = (int)((Y - 3) / (2 * n) + 1);
      *v2 = (int)Y;
    }
}
static void
test_loop16_dv (void)
{
  printf ("\n=== Group: loop16_dv (Monte Carlo search, vs C reference) ===\n");
  const int n = 3;
  double R = 0.3, S = 0.5, T = 0.7;
  double D[8] = { 0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8 };
  double PLAN[3] = { 0.0, 0.0, 0.0 };
  int32_t ZONE[13] = { 2, 7, 5, 9, 3, 11, 3, 13, 3, 15, 3, 17, 3 };
  int ev1, ev2;
  ref_loop16 (n, R, S, T, D, PLAN, ZONE, &ev1, &ev2);
  sisal_array_t Da = make_double_arr (D, 8), Pa = make_double_arr (PLAN, 3),
                Za = make_int_arr (ZONE, 13);
  struct LOOP16_results r = func_MAIN (1, n, R, S, T, Da, Pa, Za);
  check ("loop16_dv v1 matches C reference", r.res_0 == ev1);
  check ("loop16_dv v2 matches C reference", r.res_1 == ev2);
  if (Da.data)
    free (Da.data);
  if (Pa.data)
    free (Pa.data);
  if (Za.data)
    free (Za.data);
}
#endif
#ifdef TEST_LOOP13_DV
// 2-D PIC (loop13): per particle i, compute grid cell from P, push P, bump H
// histogram. MOD2N(i,j): i<0 ? i-(i/j)*j+j/2+|j/2| : i-(i/j)*j+j/2-|j/2|.  All
// indices Sisal 1-based. P is 4 x n; H/B/C are G x G; E/F/Y/Z 1-based length
// >= 96.  In-place on P and H matches the Sisal `old P`/`old H` carries (each
// particle writes its own P column; H accumulates). (This kernel is the
// regression guard for the 2-D element-update X[r,c: v] fix.)
static int
l13_mod2n (int i, int j)
{
  int r = i - (i / j) * j + j / 2;
  return (i < 0) ? r + abs (j / 2) : r - abs (j / 2);
}
static void
ref_loop13 (int n, const int32_t *E, const int32_t *F, const double *B,
            const double *C, int G, double *H, double *P, const double *Y,
            const double *Z)
{
  for (int i = 1; i <= n; i++)
    {
#define PV(r, c) P[((r) - 1) * n + ((c) - 1)]
      int i1 = 1 + l13_mod2n ((int)trunc (PV (1, i)), 64);
      int j1 = 1 + l13_mod2n ((int)trunc (PV (2, i)), 64);
      double Bij = B[(i1 - 1) * G + (j1 - 1)],
             Cij = C[(i1 - 1) * G + (j1 - 1)];
      double o1 = PV (1, i), o2 = PV (2, i), o3 = PV (3, i), o4 = PV (4, i);
      PV (4, i) = o4 + Cij;
      PV (3, i) = o3 + Bij;
      PV (2, i) = o2 + o4 + Cij;
      PV (1, i) = o1 + o3 + Bij;
      int i2 = l13_mod2n ((int)trunc (PV (1, i)), 64);
      int j2 = l13_mod2n ((int)trunc (PV (2, i)), 64);
      int i3 = i2 + E[(i2 + 32) - 1];
      int j3 = j2 + F[(j2 + 32) - 1];
      PV (1, i) = PV (1, i) + Y[(i2 + 32) - 1];
      PV (2, i) = PV (2, i) + Z[(j2 + 32) - 1];
      H[(i3 - 1) * G + (j3 - 1)] += 1.0;
#undef PV
    }
}
static void
test_loop13_dv (void)
{
  printf ("\n=== Group: loop13_dv (2-D PIC, vs C reference) ===\n");
  const int n = 2, G = 64;
  static int32_t E[96], F[96];
  static double B[64 * 64], C[64 * 64], Hin[64 * 64], Y[96], Z[96];
  for (int k = 0; k < 96; k++)
    {
      E[k] = 1;
      F[k] = 1;
      Y[k] = 0.5;
      Z[k] = 0.25;
    }
  for (int k = 0; k < G * G; k++)
    {
      B[k] = 0.0;
      C[k] = 0.0;
      Hin[k] = 0.0;
    }
  double Pin[4 * 2] = { 5, 3, 7, 9, 0, 0, 0, 0 };
  static double Hexp[64 * 64];
  for (int k = 0; k < G * G; k++)
    Hexp[k] = Hin[k];
  double Pexp[4 * 2];
  for (int k = 0; k < 8; k++)
    Pexp[k] = Pin[k];
  ref_loop13 (n, E, F, B, C, G, Hexp, Pexp, Y, Z);
  sisal_array_t Ea = make_int_arr (E, 96), Fa = make_int_arr (F, 96);
  sisal_array_t Ba = make_double_2d (B, G, G), Ca = make_double_2d (C, G, G);
  sisal_array_t Ha = make_double_2d (Hin, G, G),
                Pa = make_double_2d (Pin, 4, n);
  sisal_array_t Ya = make_double_arr (Y, 96), Za = make_double_arr (Z, 96);
  struct LOOP13_results r = func_MAIN (1, n, Ea, Fa, Ba, Ca, Ha, Pa, Ya, Za);
  bool hok = (r.res_0.rank == 2) && ((int)r.res_0.dims[0] == G)
             && ((int)r.res_0.dims[1] == G);
  for (int k = 0; hok && k < G * G; k++)
    hok = hok && (fabs (ad (r.res_0, k) - Hexp[k]) < 1e-9);
  bool pok = (r.res_1.rank == 2) && ((int)r.res_1.dims[0] == 4)
             && ((int)r.res_1.dims[1] == n);
  for (int k = 0; pok && k < 4 * n; k++)
    pok = pok && (fabs (ad (r.res_1, k) - Pexp[k]) < 1e-9);
  check ("loop13_dv H histogram matches C reference", hok);
  check ("loop13_dv P particles match C reference", pok);
  check ("loop13_dv H got the two particle hits (6,8)&(4,10)",
         ad (r.res_0, (6 - 1) * G + (8 - 1)) == 1.0
             && ad (r.res_0, (4 - 1) * G + (10 - 1)) == 1.0);
  if (Ea.data)
    free (Ea.data);
  if (Fa.data)
    free (Fa.data);
  if (Ba.data)
    free (Ba.data);
  if (Ca.data)
    free (Ca.data);
  if (Ha.data)
    free (Ha.data);
  if (Pa.data)
    free (Pa.data);
  if (Ya.data)
    free (Ya.data);
  if (Za.data)
    free (Za.data);
  if (r.res_0.data)
    free (r.res_0.data);
  if (r.res_1.data)
    free (r.res_1.data);
}
#endif
#ifdef TEST_LOOP5_DV
// Livermore loop 5: tridiagonal elimination (sequential recurrence) lowered as
// a `for initial ... returns array of X`.  X[1]=Xin[1];
// X[i]=Z[i]*(Y[i]-X[i-1]) for i=2..n.  The for-initial gather collects the
// per-iteration body values X[2..n] (n-1 elements) -- the regression guard for
// the for-initial DV_GATHER realization.
static void
test_loop5_dv (void)
{
  printf ("\n=== Group: loop5_dv (tridiagonal for-initial gather, vs C "
          "reference) ===\n");
  const int n = 6;
  double Xin[6] = { 2, 0, 0, 0, 0, 0 };         // only Xin[1] used
  double Y[6] = { 0, 5, 10, 15, 20, 25 };       // 1-based Y[2..6]
  double Z[6] = { 0, 0.5, 0.5, 0.5, 0.5, 0.5 }; // 1-based Z[2..6]
  double X[7];
  X[1] = Xin[0];
  for (int i = 2; i <= n; i++)
    X[i] = Z[i - 1] * (Y[i - 1] - X[i - 1]); // ref recurrence
  sisal_array_t Xa = make_double_arr (Xin, 6), Ya = make_double_arr (Y, 6),
                Za = make_double_arr (Z, 6);
  sisal_array_t r = func_MAIN (1, n, Xa, Ya, Za);
  bool ok
      = (r.rank == 1) && ((int)r.size == n - 1) && ((int)r.dims[0] == n - 1);
  for (int k = 0; ok && k < n - 1; k++)
    ok = ok && near_d (ad (r, k), X[k + 2]);
  check ("loop5_dv gather [X2..Xn] matches C reference", ok);
  if (Xa.data)
    free (Xa.data);
  if (Ya.data)
    free (Ya.data);
  if (Za.data)
    free (Za.data);
  if (r.data)
    free (r.data);
}
#endif
#ifdef TEST_LOOP11S_DV
// Livermore loop 11: first sum (prefix sum), a `for initial ... returns array
// of X` gather.  X[1]=Yin[1]; X[i]=X[i-1]+Yin[i]; gather body values X[2..n]
// (n-1 elems).
static void
test_loop11s_dv (void)
{
  printf ("\n=== Group: loop11s_dv (first-sum for-initial gather, vs C "
          "reference) ===\n");
  const int n = 6;
  double Yin[6] = { 1, 2, 3, 4, 5, 6 };
  double X[7];
  X[1] = Yin[0];
  for (int i = 2; i <= n; i++)
    X[i] = X[i - 1] + Yin[i - 1]; // ref prefix sum
  sisal_array_t Ya = make_double_arr (Yin, 6);
  sisal_array_t r = func_MAIN (1, n, Ya);
  bool ok
      = (r.rank == 1) && ((int)r.size == n - 1) && ((int)r.dims[0] == n - 1);
  for (int k = 0; ok && k < n - 1; k++)
    ok = ok && near_d (ad (r, k), X[k + 2]);
  check ("loop11s_dv prefix-sum gather [X2..Xn] matches C reference", ok);
  if (Ya.data)
    free (Ya.data);
  if (r.data)
    free (r.data);
}
#endif
#ifdef TEST_LOOP17_DV
// Livermore loop 17: implicit conditional computation, a DESCENDING
// for-initial (i:=n; while i>2; i:=old i-1) with THREE gathers (array of
// VXNE/VE3/VXND). Exercises multi-gather + the `>` comparison.  Body i =
// n-1..2 -> n-2 elements.
#define LV(arr, i) arr[(i) - 1]
static void
test_loop17_dv (void)
{
  printf ("\n=== Group: loop17_dv (descending for-initial, 3 gathers, vs C "
          "reference) ===\n");
  const int n = 4;
  double VLIN[4] = { 0.1, 0.2, 0.3, 0.4 }, VLR[4] = { 1.0, 1.1, 1.2, 1.3 },
         VSP[4] = { 2.0, 2.1, 2.2, 2.3 }, VSTP[4] = { 0.5, 0.6, 0.7, 0.8 },
         VXNEin[4] = { 3.0, 3.1, 3.2, 3.3 };
  double XNMt = 1.0 / 3.0, E6t = 1.03 / 3.07;
  (void)E6t;
  double E3 = XNMt * LV (VLR, n) + LV (VLIN, n), XNC = 5.0 / 3.0 * E3,
         XNEI = LV (VXNEin, n), E6, XNM;
  if (XNMt > XNC || XNEI > XNC)
    {
      E6 = XNMt * LV (VSP, n) + LV (VSTP, n);
      XNM = E6;
    }
  else
    {
      E6 = E3 + E3 - XNMt;
      XNM = E3 + E3 - XNMt;
    }
  double oldXNM = XNM, oldE6 = E6;
  int cnt = n - 2;
  double gV[8], gE[8], gD[8];
  int idx = 0;
  for (int i = n - 1; i >= 2; i--)
    {
      double e3 = oldXNM * LV (VLR, i) + LV (VLIN, i), xnc = 5.0 / 3.0 * e3,
             xnei = LV (VXNEin, i), vxnd = oldE6;
      double ve3, e6, vxne, xnm;
      if (oldXNM > xnc || xnei > xnc)
        {
          e6 = oldXNM * LV (VSP, i) + LV (VSTP, i);
          ve3 = e6;
          vxne = e6;
          xnm = e6;
        }
      else
        {
          ve3 = e3;
          e6 = e3 + e3 - oldXNM;
          vxne = e3 + e3 - xnei;
          xnm = e3 + e3 - oldXNM;
        }
      gV[idx] = vxne;
      gE[idx] = ve3;
      gD[idx] = vxnd;
      idx++;
      oldXNM = xnm;
      oldE6 = e6;
    }
  sisal_array_t a = make_double_arr (VLIN, 4), b = make_double_arr (VLR, 4),
                c = make_double_arr (VSP, 4), d = make_double_arr (VSTP, 4),
                e = make_double_arr (VXNEin, 4);
  struct LOOP17_results r = func_MAIN (1, n, a, b, c, d, e);
  bool ok = ((int)r.res_0.size == cnt) && ((int)r.res_1.size == cnt)
            && ((int)r.res_2.size == cnt);
  for (int k = 0; ok && k < cnt; k++)
    ok = ok && near_d (ad (r.res_0, k), gV[k])
         && near_d (ad (r.res_1, k), gE[k]) && near_d (ad (r.res_2, k), gD[k]);
  check ("loop17_dv 3 gathers (VXNE,VE3,VXND) match C reference", ok);
  if (a.data)
    free (a.data);
  if (b.data)
    free (b.data);
  if (c.data)
    free (c.data);
  if (d.data)
    free (d.data);
  if (e.data)
    free (e.data);
  if (r.res_0.data)
    free (r.res_0.data);
  if (r.res_1.data)
    free (r.res_1.data);
  if (r.res_2.data)
    free (r.res_2.data);
}
#undef LV
#endif
#ifdef TEST_LOOP15_DV
// Livermore loop 15: nested foralls (j=2..6 outer, i=2..n-1 inner) with
// conditional branches, per-row array_addh(VSrc,0)/array_addh(VYrc,LastY), and
// a final array_addh(VYc, array_fill(2,n,0)) appending a zero ROW to a 2-D
// matrix (the rank-poly DV_ARRAY_ADDH splice).  Returns VS [5 x n-1], VYc [6 x
// n-1].
static void
test_loop15_dv (void)
{
  printf ("\n=== Group: loop15_dv (nested forall + addh/fill, vs C reference) "
          "===\n");
  const int n = 4, NC = 4;
  double VF[28], VG[28], VH[28];
  for (int r = 1; r <= 7; r++)
    for (int c = 1; c <= 4; c++)
      {
        VF[(r - 1) * 4 + c - 1] = r + 0.1 * c;
        VG[(r - 1) * 4 + c - 1] = 0.5 * r + c;
        VH[(r - 1) * 4 + c - 1] = 0.3 * r + 0.2 * c;
      }
#define LV(a, r, c) a[((r) - 1) * NC + ((c) - 1)]
  const int W = n - 1;
  double VS[15], VYc[15];
  for (int j = 2; j <= 6; j++)
    {
      int jd = j - 2;
      for (int i = 2; i <= n - 1; i++)
        {
          int id = i - 2;
          double Si;
          if (LV (VF, j, i) >= LV (VF, j - 1, i))
            {
              double R = std::max (LV (VG, j, i), LV (VG, j, i + 1)),
                     s = LV (VF, j, i), t = 0.053;
              Si = sqrt (LV (VH, j, i) * LV (VH, j, i) + R * R) * t / s;
            }
          else
            {
              double R = std::max (LV (VG, j - 1, i), LV (VG, j - 1, i + 1)),
                     s = LV (VF, j - 1, i), t = 0.073;
              Si = sqrt (LV (VH, j, i) * LV (VH, j, i) + R * R) * t / s;
            }
          double Ti = (LV (VH, j + 1, i) > LV (VH, j, i)) ? 0.053 : 0.073, Yi;
          if (LV (VF, j, i) >= LV (VF, j, i - 1))
            {
              double R = std::max (LV (VH, j, i), LV (VH, j + 1, i)),
                     s = LV (VF, j, i);
              Yi = sqrt (LV (VG, j, i) * LV (VG, j, i) + R * R) * Ti / s;
            }
          else
            {
              double R = std::max (LV (VH, j, i - 1), LV (VH, j + 1, i - 1)),
                     s = LV (VF, j, i - 1);
              Yi = sqrt (LV (VG, j, i) * LV (VG, j, i) + R * R) * Ti / s;
            }
          VS[jd * W + id] = Si;
          VYc[jd * W + id] = Yi;
        }
      double Tj = (LV (VH, j + 1, n) > LV (VH, j, n)) ? 0.053 : 0.073, LastY;
      if (LV (VF, j, n) >= LV (VF, j, n - 1))
        {
          double R = std::max (LV (VH, j, n), LV (VH, j + 1, n)),
                 s = LV (VF, j, n);
          LastY = sqrt (LV (VG, j, n) * LV (VG, j, n) + R * R) * Tj / s;
        }
      else
        {
          double R = std::max (LV (VH, j, n - 1), LV (VH, j + 1, n - 1)),
                 s = LV (VF, j, n - 1);
          LastY = sqrt (LV (VG, j, n) * LV (VG, j, n) + R * R) * Tj / s;
        }
      VS[jd * W + (W - 1)] = 0.0;
      VYc[jd * W + (W - 1)] = LastY;
    }
  double VYcf[18];
  for (int k = 0; k < 5 * W; k++)
    VYcf[k] = VYc[k];
  for (int k = 0; k < W; k++)
    VYcf[5 * W + k] = 0.0;
#undef LV
  sisal_array_t a = make_double_2d (VF, 7, 4), b = make_double_2d (VG, 7, 4),
                c = make_double_2d (VH, 7, 4);
  struct LOOP15_results r = func_MAIN (1, n, a, b, c);
  bool sok = (r.res_0.rank == 2) && ((int)r.res_0.dims[0] == 5)
             && ((int)r.res_0.dims[1] == W);
  for (int k = 0; sok && k < 5 * W; k++)
    sok = sok && (fabs (ad (r.res_0, k) - VS[k]) < 1e-4);
  bool yok = (r.res_1.rank == 2) && ((int)r.res_1.dims[0] == 6)
             && ((int)r.res_1.dims[1] == W);
  for (int k = 0; yok && k < 6 * W; k++)
    yok = yok && (fabs (ad (r.res_1, k) - VYcf[k]) < 1e-4);
  check ("loop15_dv VS [5 x n-1] matches C reference", sok);
  check ("loop15_dv VYc [6 x n-1] (row-append via DV_ARRAY_ADDH) matches C "
         "reference",
         yok);
  if (a.data)
    free (a.data);
  if (b.data)
    free (b.data);
  if (c.data)
    free (c.data);
  if (r.res_0.data)
    free (r.res_0.data);
  if (r.res_1.data)
    free (r.res_1.data);
}
#endif
#ifdef TEST_LOOP22_DV
// Livermore loop 22: Planckian distribution.  forall k:
// Y=U[k]<20V[k]?U[k]/V[k]:20; W=X[k]/(exp(Y)-1).  Returns (W,Y), each length
// n.
static void
test_loop22_dv (void)
{
  printf ("\n=== Group: loop22_dv (Planckian, vs C reference) ===\n");
  const int n = 5;
  double U[5] = { 1, 2, 3, 100, 5 }, V[5] = { 1, 1, 1, 1, 1 },
         X[5] = { 10, 20, 30, 40, 50 };
  double W[5], Y[5];
  for (int k = 0; k < n; k++)
    {
      Y[k] = (U[k] < 20.0 * V[k]) ? U[k] / V[k] : 20.0;
      W[k] = X[k] / (exp (Y[k]) - 1.0);
    }
  sisal_array_t Ua = make_double_arr (U, 5), Va = make_double_arr (V, 5),
                Xa = make_double_arr (X, 5);
  struct LOOP22_results r = func_MAIN (1, n, Ua, Va, Xa);
  bool wok = ((int)r.res_0.size == n), yok = ((int)r.res_1.size == n);
  for (int k = 0; wok && k < n; k++)
    wok = wok && near_d (ad (r.res_0, k), W[k]);
  for (int k = 0; yok && k < n; k++)
    yok = yok && near_d (ad (r.res_1, k), Y[k]);
  check ("loop22_dv W (Planckian) matches C reference", wok);
  check ("loop22_dv Y (clamped ratio) matches C reference", yok);
  if (Ua.data)
    free (Ua.data);
  if (Va.data)
    free (Va.data);
  if (Xa.data)
    free (Xa.data);
  if (r.res_0.data)
    free (r.res_0.data);
  if (r.res_1.data)
    free (r.res_1.data);
}
#endif
#ifdef TEST_BUILDFILL_DV
// Empty array_dv build seed (array OneD []) + array_fill in a for-initial,
// keep-last on an array carry.  X := array_fill(1,i,2.0) each iteration; value
// of X = last fill.
static void
test_buildfill_dv (void)
{
  printf ("\n=== Group: buildfill_dv (empty DV_ARRAY_BUILD + DV_ARRAY_FILL "
          "keep-last) ===\n");
  const int n = 4;
  sisal_array_t r = func_MAIN (n);
  bool ok = (r.rank == 1) && ((int)r.size == n) && ((int)r.dims[0] == n);
  for (int k = 0; ok && k < n; k++)
    ok = ok && (ad (r, k) == 2.0);
  check ("buildfill_dv = fill(1,n,2.0) (n twos)", ok);
  if (r.data)
    free (r.data);
}
#endif
#ifdef TEST_LOOP20_DV
// Livermore loop 20: for-initial recurrence.  DI=Y[i]-G[i]/(XX[i]+DK);
// DN=DI==0?0.2:max(S,min(Z[i]/DI,T));
// X=(XX[i]*(W[i]+DN*V[i])+U[i])/(VX[i]+DN*V[i]); XX[i+1]=XX[i]+DN*(X-XX[i]).
// returns gather X (i=2..n, n-1 elems) + keep-last XX.
static void
test_loop20_dv (void)
{
  printf ("\n=== Group: loop20_dv (for-initial recurrence + gather, vs C "
          "reference) ===\n");
  const int n = 4;
  double XXin[5] = { 3, 3, 3, 3, 3 }, G[5] = { 0, 0, 0, 0, 0 },
         Y[5] = { 1, 1, 1, 1, 1 }, Z[5] = { 2, 2, 2, 2, 2 },
         U[5] = { 1, 1, 1, 1, 1 }, V[5] = { 1, 1, 1, 1, 1 },
         W[5] = { 1, 1, 1, 1, 1 }, VX[5] = { 2, 2, 2, 2, 2 };
  double DK = 1, S = 0, T = 100;
#define A(arr, i) arr[(i) - 1]
  double XX[6];
  for (int k = 1; k <= 5; k++)
    XX[k] = A (XXin, k);
  double Xg[8];
  int gc = 0;
  {
    double DI = A (Y, 1) - A (G, 1) / (A (XXin, 1) + DK);
    double DN = (DI == 0.0) ? 0.20 : std::max (S, std::min (A (Z, 1) / DI, T));
    double X = (A (XXin, 1) * (A (W, 1) + DN * A (V, 1)) + A (U, 1))
               / (A (VX, 1) + DN * A (V, 1));
    XX[2] = A (XXin, 1) + DN * (X - A (XXin, 1));
  }
  for (int i = 2; i <= n; i++)
    {
      double DI = A (Y, i) - A (G, i) / (XX[i] + DK);
      double DN
          = (DI == 0.0) ? 0.20 : std::max (S, std::min (A (Z, i) / DI, T));
      double X = (XX[i] * (A (W, i) + DN * A (V, i)) + A (U, i))
                 / (A (VX, i) + DN * A (V, i));
      Xg[gc++] = X;
      XX[i + 1] = XX[i] + DN * (X - XX[i]);
    }
#undef A
  sisal_array_t xx = make_double_arr (XXin, 5), g = make_double_arr (G, 5),
                u = make_double_arr (U, 5), v = make_double_arr (V, 5),
                vx = make_double_arr (VX, 5), w = make_double_arr (W, 5),
                y = make_double_arr (Y, 5), z = make_double_arr (Z, 5);
  struct LOOP20_results r
      = func_MAIN (1, n, DK, S, T, xx, g, u, v, vx, w, y, z);
  bool xok = ((int)r.res_0.size == gc);
  for (int k = 0; xok && k < gc; k++)
    xok = xok && near_d (ad (r.res_0, k), Xg[k]);
  bool xxok = ((int)r.res_1.size == 5);
  for (int k = 0; xxok && k < 5; k++)
    xxok = xxok && near_d (ad (r.res_1, k), XX[k + 1]);
  check ("loop20_dv X gather (i=2..n) matches C reference", xok);
  check ("loop20_dv XX (keep-last recurrence) matches C reference", xxok);
  if (xx.data)
    free (xx.data);
  if (g.data)
    free (g.data);
  if (u.data)
    free (u.data);
  if (v.data)
    free (v.data);
  if (vx.data)
    free (vx.data);
  if (w.data)
    free (w.data);
  if (y.data)
    free (y.data);
  if (z.data)
    free (z.data);
  if (r.res_0.data)
    free (r.res_0.data);
  if (r.res_1.data)
    free (r.res_1.data);
}
#endif

#ifdef TEST_LOOP19S_DV
static void
test_loop19s_dv (void)
{
  printf ("\n=== Group: loop19s_dv (general linear recurrence, vs C "
          "reference) ===\n");
  const int n = 5;
  double STB5in = 1.5;
  double SA[5] = { 0.5, 1.2, -0.8, 2.0, 1.1 };
  double SB[5] = { 1.1, 0.9, 1.3, 0.8, 1.2 };

  // C Reference Implementation
  double B5[5] = { 0 };
  double STB5 = STB5in;
  double STB5_tmp = STB5;
  double B5_tmp[5];
  B5_tmp[0] = SA[0] + STB5_tmp * SB[0];
  STB5_tmp = B5_tmp[0] - STB5_tmp;
  for (int k = 2; k <= n; k++)
    {
      B5_tmp[k - 1] = SA[k - 1] + STB5_tmp * SB[k - 1];
      STB5_tmp = B5_tmp[k - 1] - STB5_tmp;
    }
  for (int i = 0; i < n; i++)
    B5[i] = B5_tmp[i];
  STB5 = STB5_tmp;
  for (int i = 1; i <= n; i++)
    {
      int k = n + 1 - i;
      double B5V = SA[k - 1] + STB5 * SB[k - 1];
      B5[k - 1] = B5V;
      STB5 = B5V - STB5;
    }

  sisal_array_t sa = make_double_arr (SA, 5);
  sisal_array_t sb = make_double_arr (SB, 5);
  struct FUNC_MAIN_results r = func_MAIN (1, n, STB5in, sa, sb);

  bool ok = ((int)r.res_0.size == n);
  for (int k = 0; ok && k < n; k++)
    {
      ok = ok && near_d (ad (r.res_0, k), B5[k]);
    }
  ok = ok && near_d (r.res_1, STB5);
  check ("loop19s_dv general linear recurrence matches C reference", ok);

  if (sa.data)
    free (sa.data);
  if (sb.data)
    free (sb.data);
  if (r.res_0.data)
    free (r.res_0.data);
}
#endif

#ifdef TEST_LOOP14_DV
static void
test_loop14_dv (void)
{
  printf ("\n=== Group: loop14_dv (1-D PIC, vs C reference) ===\n");
  const int n = 5;
  double FLX = 0.25;
  double DEX[1001], EX[1001], GRD[1001], RH[1001];
  for (int i = 0; i < 1001; i++)
    {
      DEX[i] = 0.1 * (i % 5);
      EX[i] = 1.0 + 0.05 * i;
      GRD[i] = 1.0 + 0.9 * i;
      RH[i] = 10.0 + 0.1 * i;
    }

// C Reference Implementation (with 1-based indexing helper)
#define A_14(arr, idx) arr[(idx) - 1]
  double DEX1[5], EX1[5], RX1[5], VX1[5], XI1[5], XX1[5];
  int32_t IR1[5], IX1[5];
  for (int i = 1; i <= n; i++)
    {
      int j = (int)A_14 (GRD, i);
      EX1[i - 1] = A_14 (EX, j);
      DEX1[i - 1] = A_14 (DEX, j);
      XI1[i - 1] = (double)j;
      double vx = A_14 (EX, j) - A_14 (DEX, j) * (double)j;
      VX1[i - 1] = vx;
      int k = (int)(vx + FLX);
      int ir;
      if (k < 0)
        {
          ir = k - (k / 512 * 512) + 256 + abs (256);
        }
      else
        {
          ir = k - (k / 512 * 512) + 256 - abs (256);
        }
      ir = ir + 1;
      IR1[i - 1] = ir;
      IX1[i - 1] = j;
      RX1[i - 1] = vx + FLX - (double)k;
      XX1[i - 1] = vx + FLX - (double)k + (double)ir;
    }
  double RH_ref[1001];
  for (int i = 0; i < 1001; i++)
    RH_ref[i] = RH[i];
  for (int i = 1; i <= n; i++)
    {
      int ir1 = IR1[i - 1];
      double rx1 = RX1[i - 1];
      double val1 = A_14 (RH_ref, ir1) - rx1 + 1.0;
      double val2 = A_14 (RH_ref, ir1 + 1) + rx1;
      A_14 (RH_ref, ir1) = val1;
      A_14 (RH_ref, ir1 + 1) = val2;
    }
#undef A_14

  sisal_array_t dex = make_double_arr (DEX, 1001);
  sisal_array_t ex = make_double_arr (EX, 1001);
  sisal_array_t grd = make_double_arr (GRD, 1001);
  sisal_array_t rh = make_double_arr (RH, 1001);
  struct FUNC_MAIN_results r = func_MAIN (1, n, FLX, dex, ex, grd, rh);

  bool ok = ((int)r.res_0.size == n) && ((int)r.res_1.size == n)
            && ((int)r.res_2.size == n) && ((int)r.res_3.size == n)
            && ((int)r.res_4.size == n) && ((int)r.res_5.size == n)
            && ((int)r.res_6.size == n) && ((int)r.res_7.size == n)
            && ((int)r.res_8.size == 1001);

  for (int k = 0; ok && k < n; k++)
    {
      ok = ok && near_d (ad (r.res_0, k), DEX1[k]);
      ok = ok && near_d (ad (r.res_1, k), EX1[k]);
      ok = ok && (((int32_t *)r.res_2.data)[k] == IR1[k]);
      ok = ok && (((int32_t *)r.res_3.data)[k] == IX1[k]);
      ok = ok && near_d (ad (r.res_4, k), RX1[k]);
      ok = ok && near_d (ad (r.res_5, k), VX1[k]);
      ok = ok && near_d (ad (r.res_6, k), XI1[k]);
      ok = ok && near_d (ad (r.res_7, k), XX1[k]);
    }
  for (int k = 0; ok && k < 1001; k++)
    {
      ok = ok && near_d (ad (r.res_8, k), RH_ref[k]);
    }

  check ("loop14_dv 1-D PIC results match C reference", ok);

  if (dex.data)
    free (dex.data);
  if (ex.data)
    free (ex.data);
  if (grd.data)
    free (grd.data);
  if (rh.data)
    free (rh.data);
  if (r.res_0.data)
    free (r.res_0.data);
  if (r.res_1.data)
    free (r.res_1.data);
  if (r.res_2.data)
    free (r.res_2.data);
  if (r.res_3.data)
    free (r.res_3.data);
  if (r.res_4.data)
    free (r.res_4.data);
  if (r.res_5.data)
    free (r.res_5.data);
  if (r.res_6.data)
    free (r.res_6.data);
  if (r.res_7.data)
    free (r.res_7.data);
  if (r.res_8.data)
    free (r.res_8.data);
}
#endif

#ifdef TEST_LOOP23S_DV
static void
test_loop23s_dv (void)
{
  printf ("\n=== Group: loop23s_dv (2-D Implicit Hydrodynamics, vs C "
          "reference) ===\n");
  const int n = 5;
  // Dimensions: 8 rows (0..7), 6 columns (1..6)
  double ZAin[48], ZB[48], ZR[48], ZU[48], ZV[48], ZZ[48];
  for (int r = 0; r < 8; r++)
    {
      for (int c = 1; c <= 6; c++)
        {
          int idx = r * 6 + c - 1;
          ZAin[idx] = 1.0 + 0.1 * r + 0.02 * c;
          ZB[idx] = 0.5 + 0.05 * r;
          ZR[idx] = 0.2 + 0.01 * (r * c);
          ZU[idx] = 0.1 + 0.03 * r;
          ZV[idx] = 0.05 * c;
          ZZ[idx] = 0.01 * (r + c);
        }
    }

// C Reference Implementation
#define M23(arr, r, c) arr[(r) * 6 + (c) - 1]
  double ZAt[48];
  memcpy (ZAt, ZAin, 48 * sizeof (double));

  for (int j = 2; j <= 6; j++)
    {
      double ZArc[4]; // elements for k = 2, 3, 4, 5
      double ZA = M23 (ZAt, j, 1);
      for (int k = 2; k <= 5; k++)
        {
          double QA = M23 (ZAt, j + 1, k) * M23 (ZR, j, k)
                      + M23 (ZAt, j - 1, k) * M23 (ZB, j, k)
                      + M23 (ZAt, j, k + 1) * M23 (ZU, j, k)
                      + ZA * M23 (ZV, j, k) + M23 (ZZ, j, k);
          ZA = M23 (ZAt, j, k) + (double)0.175f * (QA - M23 (ZAt, j, k));
          ZArc[k - 2] = ZA;
        }

      // ZAt[j: array_addh(ZArc, ZAt[j, 6])]
      // ZArc_appended has elements at indices 1..5: ZArc[0..3] and ZAt[j, 6]
      double old_col6 = M23 (ZAt, j, 6);
      M23 (ZAt, j, 1) = ZArc[0];
      M23 (ZAt, j, 2) = ZArc[1];
      M23 (ZAt, j, 3) = ZArc[2];
      M23 (ZAt, j, 4) = ZArc[3];
      M23 (ZAt, j, 5) = old_col6;
      // column 6 of ZAt[j] remains unchanged.
    }
#undef M23

  sisal_array_t zain = make_double_2d_lb (ZAin, 8, 6, 0, 1);
  sisal_array_t zb = make_double_2d_lb (ZB, 8, 6, 0, 1);
  sisal_array_t zr = make_double_2d_lb (ZR, 8, 6, 0, 1);
  sisal_array_t zu = make_double_2d_lb (ZU, 8, 6, 0, 1);
  sisal_array_t zv = make_double_2d_lb (ZV, 8, 6, 0, 1);
  sisal_array_t zz = make_double_2d_lb (ZZ, 8, 6, 0, 1);

  sisal_array_t r = func_MAIN (1, n, zain, zb, zr, zu, zv, zz);

  bool ok = (r.rank == 2) && ((int)r.dims[0] == 8) && ((int)r.dims[1] == 6)
            && ((int)r.lower_bound[0] == 0) && ((int)r.lower_bound[1] == 1);

  for (int t = 0; ok && t < 48; t++)
    ok = ok && near_d (ad (r, t), ZAt[t]);

  check ("loop23s_dv 2-D implicit hydrodynamics matches C reference", ok);

  if (zain.data)
    free (zain.data);
  if (zb.data)
    free (zb.data);
  if (zr.data)
    free (zr.data);
  if (zu.data)
    free (zu.data);
  if (zv.data)
    free (zv.data);
  if (zz.data)
    free (zz.data);
  if (r.data)
    free (r.data);
}
#endif

#ifdef TEST_LOOP18P_DV
static void
test_loop18p_dv (void)
{
  printf ("\n=== Group: loop18p_dv (2-D Explicit Hydrodynamics, vs C reference) ===\n");
  const int n = 5;
  double S = 0.01;
  double T = 0.05;

  int rows = 8, cols = 6;
  int lb0 = 1, lb1 = 1;

  double ZA[48], ZB[48], ZM[48], ZP[48], ZQ[48], ZR[48], ZU[48], ZV[48], ZZ[48];
  for (int r = 1; r <= 8; r++)
    {
      for (int c = 1; c <= 6; c++)
        {
          int idx = (r - 1) * 6 + (c - 1);
          ZA[idx] = 1.0 + 0.1 * r + 0.02 * c;
          ZB[idx] = 0.5 + 0.05 * r + 0.01 * c;
          ZM[idx] = 2.0 + 0.1 * r;
          ZP[idx] = 0.1 * r * c;
          ZQ[idx] = 0.05 * r + 0.02 * c;
          ZR[idx] = 1.5 + 0.01 * r;
          ZU[idx] = 0.1 + 0.02 * c;
          ZV[idx] = 0.2 + 0.03 * r;
          ZZ[idx] = 3.0 + 0.05 * r * c;
        }
    }

  // C Reference Implementation
  #define M18(arr, r, c) arr[((r) - lb0) * cols + ((c) - lb1)]
  double ZANew[8 * 6], ZBNew[8 * 6];
  for (int j = 1; j <= 8; j++)
    {
      for (int i = 1; i <= 6; i++)
        {
          M18 (ZANew, j, i) = M18 (ZA, j, i);
          M18 (ZBNew, j, i) = M18 (ZB, j, i);
        }
    }

  for (int j = 2; j <= 6; j++)
    {
      double ZArc[6], ZBrc[6];
      for (int i = 2; i <= n; i++)
        {
          double term1_a = M18 (ZP, j + 1, i - 1) + M18 (ZQ, j + 1, i - 1) - M18 (ZP, j, i - 1) - M18 (ZQ, j, i - 1);
          double term2_a = M18 (ZR, j, i) + M18 (ZR, j, i - 1);
          double term3_a = M18 (ZM, j, i - 1) + M18 (ZM, j + 1, i - 1);
          ZArc[i] = term1_a * term2_a / term3_a;

          double term1_b = M18 (ZP, j, i - 1) + M18 (ZQ, j, i - 1) - M18 (ZP, j, i) - M18 (ZQ, j, i);
          double term2_b = M18 (ZR, j, i) + M18 (ZR, j - 1, i);
          double term3_b = M18 (ZM, j, i) + M18 (ZM, j, i - 1);
          ZBrc[i] = term1_b * term2_b / term3_b;
        }
      M18 (ZANew, j, 1) = M18 (ZA, j, 1);
      for (int i = 2; i <= n; i++)
        M18 (ZANew, j, i) = ZArc[i];
      M18 (ZANew, j, n + 1) = M18 (ZA, j, n + 1);

      M18 (ZBNew, j, 1) = M18 (ZB, j, 1);
      for (int i = 2; i <= n; i++)
        M18 (ZBNew, j, i) = ZBrc[i];
      M18 (ZBNew, j, n + 1) = M18 (ZB, j, n + 1);
    }

  double ZRNew[8 * 6], ZZNew[8 * 6];
  memcpy (ZRNew, ZR, 48 * sizeof (double));
  memcpy (ZZNew, ZZ, 48 * sizeof (double));

  for (int j = 2; j <= 6; j++)
    {
      for (int i = 2; i <= n; i++)
        {
          double ZUNew = M18 (ZU, j, i) + S *
                         (M18 (ZANew, j, i)  * (M18 (ZZ, j, i) - M18 (ZZ, j, i + 1)) -
                          M18 (ZANew, j, i - 1) * (M18 (ZZ, j, i) - M18 (ZZ, j, i - 1)) -
                          M18 (ZBNew, j, i)   * (M18 (ZZ, j, i) - M18 (ZZ, j - 1, i)) +
                          M18 (ZBNew, j + 1, i) * (M18 (ZZ, j, i) - M18 (ZZ, j + 1, i)));
          double ZVNew = M18 (ZV, j, i) + S *
                         (M18 (ZANew, j, i)  * (M18 (ZR, j, i) - M18 (ZR, j, i + 1)) -
                          M18 (ZANew, j, i - 1) * (M18 (ZR, j, i) - M18 (ZR, j, i - 1)) -
                          M18 (ZBNew, j, i)   * (M18 (ZR, j, i) - M18 (ZR, j - 1, i)) +
                          M18 (ZBNew, j + 1, i) * (M18 (ZR, j, i) - M18 (ZR, j + 1, i)));
          M18 (ZRNew, j, i) = M18 (ZR, j, i) + T * ZUNew;
          M18 (ZZNew, j, i) = M18 (ZZ, j, i) + T * ZVNew;
        }
    }
  #undef M18

  sisal_array_t zain = make_double_2d_lb (ZA, 8, 6, 1, 1);
  sisal_array_t zbin = make_double_2d_lb (ZB, 8, 6, 1, 1);
  sisal_array_t zm = make_double_2d_lb (ZM, 8, 6, 1, 1);
  sisal_array_t zp = make_double_2d_lb (ZP, 8, 6, 1, 1);
  sisal_array_t zq = make_double_2d_lb (ZQ, 8, 6, 1, 1);
  sisal_array_t zrin = make_double_2d_lb (ZR, 8, 6, 1, 1);
  sisal_array_t zuin = make_double_2d_lb (ZU, 8, 6, 1, 1);
  sisal_array_t zvin = make_double_2d_lb (ZV, 8, 6, 1, 1);
  sisal_array_t zzin = make_double_2d_lb (ZZ, 8, 6, 1, 1);

  struct FUNC_MAIN_results r = func_MAIN (1, n, S, T, zain, zbin, zm, zp, zq, zrin, zuin, zvin, zzin);

  bool ok = (r.res_0.rank == 2) && (r.res_1.rank == 2);
  for (int j = 2; ok && j <= 6; j++)
    {
      for (int i = 2; ok && i <= n; i++)
        {
          int row_offset = j - 2;
          int col_offset = i - 2;
          int flat_idx = row_offset * 4 + col_offset;
          double sisal_zr = ((double*)r.res_0.data)[flat_idx];
          double sisal_zz = ((double*)r.res_1.data)[flat_idx];
          
          double ref_zr = ZRNew[(j-1)*6 + (i-1)];
          double ref_zz = ZZNew[(j-1)*6 + (i-1)];
          ok = ok && near_d (sisal_zr, ref_zr) && near_d (sisal_zz, ref_zz);
        }
    }

  check ("loop18p_dv 2-D explicit hydrodynamics matches C reference", ok);

  if (zain.data) free (zain.data);
  if (zbin.data) free (zbin.data);
  if (zm.data) free (zm.data);
  if (zp.data) free (zp.data);
  if (zq.data) free (zq.data);
  if (zrin.data) free (zrin.data);
  if (zuin.data) free (zuin.data);
  if (zvin.data) free (zvin.data);
  if (zzin.data) free (zzin.data);
  if (r.res_0.data) free (r.res_0.data);
  if (r.res_1.data) free (r.res_1.data);
}
#endif

#ifdef TEST_LOOP8P_DV
static void
test_loop8p_dv (void)
{
  printf ("\n=== Group: loop8p_dv (ADI Integration, vs C reference) ===\n");
  const int n = 5;
  double A11 = 0.1, A12 = 0.2, A13 = 0.3;
  double A21 = 0.15, A22 = 0.25, A23 = 0.35;
  double A31 = 0.05, A32 = 0.15, A33 = 0.25;
  double SIG = 0.01;

  double U1[4 * 1 * 6], U2[4 * 1 * 6], U3[4 * 1 * 6];
  for (int i = 0; i < 24; i++)
    {
      U1[i] = 1.0 + 0.05 * i;
      U2[i] = 2.0 + 0.02 * i;
      U3[i] = 3.0 + 0.01 * i;
    }

  // C Reference Implementation
  double V1_ref[4][6], V2_ref[4][6], V3_ref[4][6];
  for (int kx = 2; kx <= 3; kx++)
    {
      for (int ky = 2; ky <= n; ky++)
        {
          double DU1 = U1[(kx - 1) * 6 + ky] - U1[(kx - 1) * 6 + ky - 2];
          double DU2 = U2[(kx - 1) * 6 + ky] - U2[(kx - 1) * 6 + ky - 2];
          double DU3 = U3[(kx - 1) * 6 + ky] - U3[(kx - 1) * 6 + ky - 2];

          double v1 = U1[(kx - 1) * 6 + ky - 1] + A11 * DU1 + A12 * DU2 + A13 * DU3 +
                      SIG * (U1[kx * 6 + ky - 1] - 2.0 * U1[(kx - 1) * 6 + ky - 1] + U1[(kx - 2) * 6 + ky - 1]);
          double v2 = U2[(kx - 1) * 6 + ky - 1] + A21 * DU1 + A22 * DU2 + A23 * DU3 +
                      SIG * (U2[kx * 6 + ky - 1] - 2.0 * U2[(kx - 1) * 6 + ky - 1] + U2[(kx - 2) * 6 + ky - 1]);
          double v3 = U3[(kx - 1) * 6 + ky - 1] + A31 * DU1 + A32 * DU2 + A33 * DU3 +
                      SIG * (U3[kx * 6 + ky - 1] - 2.0 * U3[(kx - 1) * 6 + ky - 1] + U3[(kx - 2) * 6 + ky - 1]);

          V1_ref[kx][ky] = v1;
          V2_ref[kx][ky] = v2;
          V3_ref[kx][ky] = v3;
        }
    }

  sisal_array_t u1in = make_double_3d_lb (U1, 4, 1, 6, 1, 1, 1);
  sisal_array_t u2in = make_double_3d_lb (U2, 4, 1, 6, 1, 1, 1);
  sisal_array_t u3in = make_double_3d_lb (U3, 4, 1, 6, 1, 1, 1);

  struct FUNC_MAIN_results r = func_MAIN (1, n, A11, A12, A13, A21, A22, A23, A31, A32, A33, SIG, u1in, u2in, u3in);

  bool ok = (r.res_0.rank == 3) && (r.res_1.rank == 3) && (r.res_2.rank == 3);
  for (int kx = 2; ok && kx <= 3; kx++)
    {
      for (int p = 1; ok && p <= 2; p++)
        {
          for (int ky = 1; ok && ky <= 6; ky++)
            {
              int row_offset = kx - 2;
              int flat_idx;
              if (p == 1)
                flat_idx = row_offset * 10 + (ky - 1);
              else
                flat_idx = row_offset * 10 + 6 + (ky - 2);

              double sisal_val1 = ((double*)r.res_0.data)[flat_idx];
              double sisal_val2 = ((double*)r.res_1.data)[flat_idx];
              double sisal_val3 = ((double*)r.res_2.data)[flat_idx];

              double ref_val1, ref_val2, ref_val3;
              if (p == 1)
                {
                  ref_val1 = U1[(kx - 1) * 6 + ky - 1];
                  ref_val2 = U2[(kx - 1) * 6 + ky - 1];
                  ref_val3 = U3[(kx - 1) * 6 + ky - 1];
                }
              else
                {
                  if (ky >= 2 && ky <= n)
                    {
                      ref_val1 = V1_ref[kx][ky];
                      ref_val2 = V2_ref[kx][ky];
                      ref_val3 = V3_ref[kx][ky];
                    }
                  else
                    {
                      continue;
                    }
                }
              ok = ok && near_d (sisal_val1, ref_val1) && near_d (sisal_val2, ref_val2) && near_d (sisal_val3, ref_val3);
            }
        }
    }

  check ("loop8p_dv ADI integration matches C reference", ok);

  if (u1in.data) free (u1in.data);
  if (u2in.data) free (u2in.data);
  if (u3in.data) free (u3in.data);
  if (r.res_0.data) free (r.res_0.data);
  if (r.res_1.data) free (r.res_1.data);
  if (r.res_2.data) free (r.res_2.data);
}
#endif

/* ---- language-feature regression tests ---- */
#ifdef TEST_CAP_NESTED_DV
static void test_cap_nested_dv(void) {
    printf("\n=== Group: cap_nested_dv (free-var capture, nested lets 3 deep) ===\n");
    check("cap_nested_dv a+b+c (a 3 levels deep) == 22", func_MAIN() == 22);
}
#endif
#ifdef TEST_CAP_ARRAY_DV
static void test_cap_array_dv(void) {
    printf("\n=== Group: cap_array_dv (grab arrays + multiple let binds) ===\n");
    int32_t A[3] = { 100, 200, 300 };
    sisal_array_t Aa = make_int_arr(A, 3);
    sisal_array_t r = func_MAIN(Aa);
    bool ok = ((int)r.size == 3);
    for (int k = 0; ok && k < 3; k++) ok = ok && (ai(r, k) == 2 * A[k] + 10);
    check("cap_array_dv B[i]+C[i]+s == 2*A[i]+10", ok);
    if (Aa.data) free(Aa.data); if (r.data) free(r.data);
}
#endif
#ifdef TEST_CAP_FORINIT_DV
static void test_cap_forinit_dv(void) {
    printf("\n=== Group: cap_forinit_dv (grab array into for-initial RHS) ===\n");
    int32_t A[3] = { 100, 200, 300 };
    sisal_array_t Aa = make_int_arr(A, 3);
    check("cap_forinit_dv sum(B[i]) == 600", func_MAIN(Aa) == 600);
    if (Aa.data) free(Aa.data);
}
#endif
#ifdef TEST_MR_FORALL_DV
static void test_mr_forall_dv(void) {
    printf("\n=== Group: mr_forall_dv (forall scalar + 1-D) ===\n");
    struct MRFA_results r = func_MAIN();
    bool ok = (r.res_0 == 30) && ((int)r.res_1.size == 3) && ai(r.res_1,0)==10 && ai(r.res_1,1)==20 && ai(r.res_1,2)==30;
    check("mr_forall_dv (value of x=30, array of x=[10,20,30])", ok);
    if (r.res_1.data) free(r.res_1.data);
}
#endif
#ifdef TEST_MR_FORINIT_DV
static void test_mr_forinit_dv(void) {
    printf("\n=== Group: mr_forinit_dv (for-initial scalar + 1-D gather) ===\n");
    struct MRFI_results r = func_MAIN();
    bool ok = (r.res_0 == 6) && ((int)r.res_1.size == 3) && ai(r.res_1,0)==1 && ai(r.res_1,1)==3 && ai(r.res_1,2)==6;
    check("mr_forinit_dv (value of acc=6, gather=[1,3,6])", ok);
    if (r.res_1.data) free(r.res_1.data);
}
#endif
#ifdef TEST_MR_1D2D_DV
static void test_mr_1d2d_dv(void) {
    printf("\n=== Group: mr_1d2d_dv (forall 1-D + 2-D) ===\n");
    struct MR12_results r = func_MAIN();
    bool ok = (r.res_0.rank==1) && ((int)r.res_0.size==3) && ai(r.res_0,0)==10 && ai(r.res_0,2)==30;
    int exp2[6] = {1,1,2,2,3,3};
    ok = ok && (r.res_1.rank==2) && ((int)r.res_1.dims[0]==3) && ((int)r.res_1.dims[1]==2);
    for (int k=0; ok && k<6; k++) ok = ok && (ai(r.res_1,k) == exp2[k]);
    check("mr_1d2d_dv (1-D [10,20,30], 2-D [3,2]=1 1 2 2 3 3)", ok);
    if (r.res_0.data) free(r.res_0.data); if (r.res_1.data) free(r.res_1.data);
}
#endif
#ifdef TEST_FN_MULTIOUT_DV
static void test_fn_multiout_dv(void) {
    printf("\n=== Group: fn_multiout_dv (function multi-output, scalar + array) ===\n");
    struct FNMO_results r = func_MAIN();
    bool ok = (r.res_0 == 6) && ((int)r.res_1.size == 3) && ai(r.res_1,0)==3 && ai(r.res_1,1)==3 && ai(r.res_1,2)==3;
    check("fn_multiout_dv pair(3) == (6, [3,3,3])", ok);
    if (r.res_1.data) free(r.res_1.data);
}
#endif
#ifdef TEST_IF_MULTIOUT_DV
static void test_if_multiout_dv(void) {
    printf("\n=== Group: if_multiout_dv (if-expression multi-output) ===\n");
    struct IFMO_results r1 = func_MAIN(5), r2 = func_MAIN(-1);
    check("if_multiout_dv if(5)==(1,2) && if(-1)==(3,4)",
          r1.res_0==1 && r1.res_1==2 && r2.res_0==3 && r2.res_1==4);
}
#endif
#ifdef TEST_FNCALL_FORALL_DV
static void test_fncall_forall_dv(void) {
    printf("\n=== Group: fncall_forall_dv (multi-output fn called in forall) ===\n");
    sisal_array_t r = func_MAIN();
    bool ok = ((int)r.size==3) && ai(r,0)==5 && ai(r,1)==10 && ai(r,2)==15;
    check("fncall_forall_dv a+b per i == [5,10,15]", ok);
    if (r.data) free(r.data);
}
#endif
#ifdef TEST_NESTED_FORALL_DV
static void test_nested_forall_dv(void) {
    printf("\n=== Group: nested_forall_dv (nested forall -> 2-D) ===\n");
    sisal_array_t r = func_MAIN();
    int exp[6] = {11,12,13,21,22,23};
    bool ok = (r.rank==2) && ((int)r.dims[0]==2) && ((int)r.dims[1]==3);
    for (int k=0; ok && k<6; k++) ok = ok && (ai(r,k)==exp[k]);
    check("nested_forall_dv 2-D == [[11,12,13],[21,22,23]]", ok);
    if (r.data) free(r.data);
}
#endif
#ifdef TEST_CAP_2DEEP_DV
static void test_cap_2deep_dv(void) {
    printf("\n=== Group: cap_2deep_dv (capture across two nested foralls) ===\n");
    sisal_array_t r = func_MAIN();
    int exp[6] = {1011,1012,1013,1021,1022,1023};
    bool ok = (r.rank==2) && ((int)r.dims[0]==2) && ((int)r.dims[1]==3);
    for (int k=0; ok && k<6; k++) ok = ok && (ai(r,k)==exp[k]);
    check("cap_2deep_dv base captured 2 loops deep", ok);
    if (r.data) free(r.data);
}
#endif
#ifdef TEST_FN3RANK_DV
static void test_fn3rank_dv(void) {
    printf("\n=== Group: fn3rank_dv (function 3 mixed-rank outputs) ===\n");
    struct FN3_results r = func_MAIN();
    int exp2[4] = {1,1,2,2};
    bool ok = (r.res_0==2) && ((int)r.res_1.size==2) && ai(r.res_1,0)==2 && ai(r.res_1,1)==2;
    ok = ok && (r.res_2.rank==2) && ((int)r.res_2.dims[0]==2) && ((int)r.res_2.dims[1]==2);
    for (int k=0; ok && k<4; k++) ok = ok && (ai(r.res_2,k)==exp2[k]);
    check("fn3rank_dv triple(2) == (2, [2,2], [[1,1],[2,2]])", ok);
    if (r.res_1.data) free(r.res_1.data); if (r.res_2.data) free(r.res_2.data);
}
#endif
#ifdef TEST_IFTUPLE_FORALL_DV
static void test_iftuple_forall_dv(void) {
    printf("\n=== Group: iftuple_forall_dv (if-tuple inside forall) ===\n");
    sisal_array_t r = func_MAIN();
    int exp[4] = {101,202,33,44};
    bool ok = ((int)r.size==4);
    for (int k=0; ok && k<4; k++) ok = ok && (ai(r,k)==exp[k]);
    check("iftuple_forall_dv == [101,202,33,44]", ok);
    if (r.data) free(r.data);
}
#endif
#ifdef TEST_RED_RANKS_DV
static void test_red_ranks_dv(void) {
    printf("\n=== Group: red_ranks_dv (nested reduce/gather -> ranks 1,0,2) ===\n");
    struct RRK_results r = func_MAIN();
    bool gok = (r.res_0.rank==1) && ((int)r.res_0.size==3) && ai(r.res_0,0)==10 && ai(r.res_0,1)==20 && ai(r.res_0,2)==30;
    bool rok = (r.res_1 == 60);
    int m[12] = {1,2,3,4,2,4,6,8,3,6,9,12};
    bool mok = (r.res_2.rank==2) && ((int)r.res_2.dims[0]==3) && ((int)r.res_2.dims[1]==4);
    for (int k=0; mok && k<12; k++) mok = mok && (ai(r.res_2,k)==m[k]);
    check("red_ranks_dv reduce/gather alternation gives ranks 1,0,2", gok && rok && mok);
    if (r.res_0.data) free(r.res_0.data); if (r.res_2.data) free(r.res_2.data);
}
#endif
#ifdef TEST_RED_OPS_DV
static void test_red_ops_dv(void) {
    printf("\n=== Group: red_ops_dv (product/greatest/least reductions) ===\n");
    struct ROP_results r = func_MAIN();
    int p[3]={24,384,1944}, g[3]={4,8,12}, l[3]={1,2,3};
    bool ok = (r.res_0.rank==1) && (r.res_1.rank==1) && (r.res_2.rank==1);
    for (int k=0; ok && k<3; k++) ok = ok && ai(r.res_0,k)==p[k] && ai(r.res_1,k)==g[k] && ai(r.res_2,k)==l[k];
    check("red_ops_dv product/greatest/least gathered (rank 1)", ok);
    if (r.res_0.data) free(r.res_0.data); if (r.res_1.data) free(r.res_1.data); if (r.res_2.data) free(r.res_2.data);
}
#endif
#ifdef TEST_RED_ARR_DV
static void test_red_arr_dv(void) {
    printf("\n=== Group: red_arr_dv (array-VALUED reductions, elementwise) ===\n");
    struct RAR_results r = func_MAIN();
    int s[4]={6,12,18,24}, p[4]={6,48,162,384}, g[4]={3,6,9,12}, l[4]={1,2,3,4};
    int m[6]={322,324,326,342,344,346};
    bool ok = (r.s.rank==1) && (r.p.rank==1) && (r.g.rank==1) && (r.l.rank==1);
    for (int k=0; ok && k<4; k++)
        ok = ok && ai(r.s,k)==s[k] && ai(r.p,k)==p[k] && ai(r.g,k)==g[k] && ai(r.l,k)==l[k];
    ok = ok && (r.m.rank==2) && ((int)r.m.dims[0]==2) && ((int)r.m.dims[1]==3);
    for (int k=0; ok && k<6; k++) ok = ok && (ai(r.m,k)==m[k]);
    check("red_arr_dv sum/product/greatest/least of arrays (1-D + 2-D)", ok);
    if (r.s.data) free(r.s.data); if (r.p.data) free(r.p.data); if (r.g.data) free(r.g.data);
    if (r.l.data) free(r.l.data); if (r.m.data) free(r.m.data);
}
#endif
#ifdef TEST_BCAST3D_DV
static void test_bcast3d_dv(void) {
    printf("\n=== Group: bcast3d_dv (rank-poly A+B, 3-D + 2-D vs numpy) ===\n");
    double A[12]={1,2,3,4,5,6,7,8,9,10,11,12};
    // (2,2,3) + (2,3): B broadcasts over the leading axis  [numpy oracle]
    double B2[6]={10,20,30,40,50,60};
    double e1[12]={11,22,33,44,55,66,17,28,39,50,61,72};
    sisal_array_t a1=mk_dv3(3,2,2,3,A), b1=mk_dv3(2,2,3,0,B2);
    sisal_array_t r1=func_MAIN(a1,b1);
    check("bcast3d_dv (2,2,3)+(2,3) == numpy", dv_eq(r1,3,2,2,3,e1,12));
    // (2,1,3) + (4,3): MUTUAL broadcast -> (2,4,3)  [numpy oracle]
    double Am[6]={1,2,3,4,5,6};
    double Bm[12]={10,20,30,40,50,60,70,80,90,100,110,120};
    double e2[24]={11,22,33,41,52,63,71,82,93,101,112,123,14,25,36,44,55,66,74,85,96,104,115,126};
    sisal_array_t a2=mk_dv3(3,2,1,3,Am), b2=mk_dv3(2,4,3,0,Bm);
    sisal_array_t r2=func_MAIN(a2,b2);
    check("bcast3d_dv mutual (2,1,3)+(4,3) -> (2,4,3) == numpy", dv_eq(r2,3,2,4,3,e2,24));
    if(a1.data)free(a1.data); if(b1.data)free(b1.data); if(r1.data)free(r1.data);
    if(a2.data)free(a2.data); if(b2.data)free(b2.data); if(r2.data)free(r2.data);
}
#endif
#ifdef TEST_BCAST31_DV
static void test_bcast31_dv(void) {
    printf("\n=== Group: bcast31_dv (rank-poly A+B, 3-D + 1-D vs numpy) ===\n");
    double A[12]={1,2,3,4,5,6,7,8,9,10,11,12};
    double B1[3]={100,200,300};
    double e[12]={101,202,303,104,205,306,107,208,309,110,211,312};
    sisal_array_t a=mk_dv3(3,2,2,3,A), b=mk_dv3(1,3,0,0,B1);
    sisal_array_t r=func_MAIN(a,b);
    check("bcast31_dv (2,2,3)+(3) == numpy", dv_eq(r,3,2,2,3,e,12));
    if(a.data)free(a.data); if(b.data)free(b.data); if(r.data)free(r.data);
}
#endif
#ifdef TEST_IP_DV
static void test_ip_dv(void) {
    printf("\n=== Group: ip_dv (rank-poly innerproduct vs numpy np.dot) ===\n");
    int32_t v1[3]={1,2,3}, v2[3]={4,5,6};
    int32_t e1[1]={32};                                  // 1D.1D dot
    sisal_array_t a,b,r;
    a=mk_dvi(1,3,0,0,v1); b=mk_dvi(1,3,0,0,v2); r=func_MAIN(a,b);
    check("ip_dv 1D.1D == np.dot (32)", dvi_eq(r,1,1,0,e1,1));
    free(a.data);free(b.data);free(r.data);
    int32_t m[6]={1,2,3,4,5,6}, ones[3]={1,1,1}; int32_t e2[2]={6,15};   // 2D(2,3).1D(3)
    a=mk_dvi(2,2,3,0,m); b=mk_dvi(1,3,0,0,ones); r=func_MAIN(a,b);
    check("ip_dv 2D(2,3).1D(3) == np.dot [6,15]", dvi_eq(r,1,2,0,e2,2));
    free(a.data);free(b.data);free(r.data);
    int32_t vv[3]={1,2,3}, M[6]={1,0,0,1,1,1}; int32_t e3[2]={4,5};       // 1D(3).2D(3,2)
    a=mk_dvi(1,3,0,0,vv); b=mk_dvi(2,3,2,0,M); r=func_MAIN(a,b);
    check("ip_dv 1D(3).2D(3,2) == np.dot [4,5]", dvi_eq(r,1,2,0,e3,2));
    free(a.data);free(b.data);free(r.data);
    int32_t X[4]={1,2,3,4}, Y[4]={5,6,7,8}; int32_t e4[4]={19,22,43,50};  // 2D.2D matmul
    a=mk_dvi(2,2,2,0,X); b=mk_dvi(2,2,2,0,Y); r=func_MAIN(a,b);
    check("ip_dv 2D(2,2).2D(2,2) == np.matmul [19,22,43,50]", dvi_eq(r,2,2,2,e4,4));
    free(a.data);free(b.data);free(r.data);
    int32_t A3[8]={1,2,3,4,5,6,7,8}, w[2]={1,1}; int32_t e5[4]={3,7,11,15}; // 3D(2,2,2).1D(2)
    a=mk_dvi(3,2,2,2,A3); b=mk_dvi(1,2,0,0,w); r=func_MAIN(a,b);
    check("ip_dv 3D(2,2,2).1D(2) == np.dot [[3,7],[11,15]]", dvi_eq(r,2,2,2,e5,4));
    free(a.data);free(b.data);free(r.data);
}
#endif
#ifdef TEST_CONV_DV
static void test_conv_dv(void) {
    printf("\n=== Group: conv_dv (convolution Y[i]=sum_j A[j]*X[i+j-1]) ===\n");
    // Main builds A=[1..M], X=[1..M*Cycles]; M=3,Cycles=2 -> A=[1,2,3], X=[1..6].
    // Y[i] = sum_{j=1..3} A[j]*X[i+j-1], i=1..4  ->  [14,20,26,32] (hand/numpy verified)
    sisal_array_t r = func_MAIN(3, 2);
    double ex[4] = { 14, 20, 26, 32 };
    bool ok = ((int)r.size == 4);
    for (int k = 0; ok && k < 4; k++) ok = ok && (fabs(((double*)r.data)[k] - ex[k]) < 1e-9);
    check("conv_dv(3,2) == [14,20,26,32]", ok);
    if (r.data) free(r.data);
}
#endif
#ifdef TEST_LAPLACE_DV
static void test_laplace_dv(void) {
    printf("\n=== Group: laplace_dv (Laplace relaxation, flat 2-D array_dv) ===\n");
    // Main(1,2,2): 4x4 grid, one Jacobi sweep. Phi(a,b)=a*b boundaries; interior avg.
    // Python-verified: [1,2,3,4, 2,1,2.75,8, 3,2.75,6,12, 4,8,12,16]
    sisal_array_t r = func_MAIN(1, 2, 2);
    double ex[16] = { 1,2,3,4, 2,1,2.75,8, 3,2.75,6,12, 4,8,12,16 };
    bool ok = (r.rank == 2) && ((int)r.dims[0] == 4) && ((int)r.dims[1] == 4) && ((int)r.size == 16);
    for (int k = 0; ok && k < 16; k++) ok = ok && (fabs(((double*)r.data)[k] - ex[k]) < 1e-9);
    check("laplace_dv(1,2,2) == relaxed 4x4 grid (vs python)", ok);
    if (r.data) free(r.data);
}
#endif
#ifdef TEST_SHAPED_GATHER_DV
static void test_shaped_gather_dv(void) {
    printf("\n=== Group: shaped_gather_dv (explicit-extent gather, non-additive loop) ===\n");
    // m := old m * 4 while m < 64 -> iterates m = 4, 16, 64.  bound-seed sizing
    // would allocate 64-1 = 63 slots; the declared extent (3) sizes it exactly.
    struct FUNC_MAIN_results r = func_MAIN();
    int32_t ex0[3] = { 4, 16, 64 };
    bool ok0 = (r.res_0.rank == 1) && ((int)r.res_0.dims[0] == 3) && ((int)r.res_0.size == 3);
    for (int k = 0; ok0 && k < 3; k++) ok0 = ok0 && (((int32_t*)r.res_0.data)[k] == ex0[k]);
    check("scalar array_dv(3) of m == [4,16,64]", ok0);
    // Row gather: element rank and byte size come off the element's dope at
    // RUNTIME (DV_NUM_RANK / sisal_array_shaped_store); leading dim = extent.
    int32_t ex1[12] = { 4,8,12,16, 16,32,48,64, 64,128,192,256 };
    bool ok1 = (r.res_1.rank == 2) && ((int)r.res_1.dims[0] == 3)
            && ((int)r.res_1.dims[1] == 4) && ((int)r.res_1.size == 12);
    for (int k = 0; ok1 && k < 12; k++) ok1 = ok1 && (((int32_t*)r.res_1.data)[k] == ex1[k]);
    check("row array_dv(3) of row(m) == 3x4 rows", ok1);
    if (r.res_0.data) free(r.res_0.data);
    if (r.res_1.data) free(r.res_1.data);
}
#endif
#ifdef TEST_FORINIT_MAT_GATHER_DV
static void test_forinit_mat_gather_dv(void) {
    printf("\n=== Group: forinit_mat_gather_dv (bare gather of rank-2 elems, concat_grow rank) ===\n");
    // m iterates 2, 4 -> gathers two 2x3 matrices.  concat_grow used to hardcode
    // rank=2 / dims[1]=val.size, flattening the element dims to (2,6); the
    // element's rank must be read off its dope at runtime -> rank 3, (2,2,3).
    sisal_array_t r = func_MAIN();
    int32_t ex[12] = { 22,24,26, 42,44,46,  44,48,52, 84,88,92 };
    bool ok = (r.rank == 3) && ((int)r.dims[0] == 2) && ((int)r.dims[1] == 2)
           && ((int)r.dims[2] == 3) && ((int)r.size == 12);
    for (int k = 0; ok && k < 12; k++) ok = ok && (((int32_t*)r.data)[k] == ex[k]);
    check("bare array_dv of mat(m) == rank-3 (2,2,3)", ok);
    if (r.data) free(r.data);
}
#endif
#ifdef TEST_SCATTER_AT_DV
static void test_scatter_at_dv(void) {
    printf("\n=== Group: scatter_at_dv (array_dv(n) of v at [..] -- shuffled placement) ===\n");
    // i = 1..3; value i*i lands at slot 4-i (reverse shuffle) -> [9,4,1];
    // row(i) lands at slot 4-i -> rows reversed, whole-row memcpy per iteration.
    struct FUNC_MAIN_results r = func_MAIN();
    int32_t ex0[3] = { 9, 4, 1 };
    bool ok0 = (r.res_0.rank == 1) && ((int)r.res_0.dims[0] == 3) && ((int)r.res_0.size == 3);
    for (int k = 0; ok0 && k < 3; k++) ok0 = ok0 && (((int32_t*)r.res_0.data)[k] == ex0[k]);
    check("scalar i*i at [4-i] == [9,4,1]", ok0);
    int32_t ex1[12] = { 3,6,9,12, 2,4,6,8, 1,2,3,4 };
    bool ok1 = (r.res_1.rank == 2) && ((int)r.res_1.dims[0] == 3)
            && ((int)r.res_1.dims[1] == 4) && ((int)r.res_1.size == 12);
    for (int k = 0; ok1 && k < 12; k++) ok1 = ok1 && (((int32_t*)r.res_1.data)[k] == ex1[k]);
    check("row(i) at [4-i] == reversed rows (3,4)", ok1);
    if (r.res_0.data) free(r.res_0.data);
    if (r.res_1.data) free(r.res_1.data);
}
#endif
#ifdef TEST_GROW_NEST_DV
static void test_grow_nest_dv(void) {
    printf("\n=== Group: grow_nest_dv (rank grows 1->2->3, inner nest to outer) ===\n");
    // vec (forall, rank 1) -> plane wraps 2 vecs (for-initial gather, rank 2)
    // -> main scatters 2 planes REVERSED (rank 3).  Each level declares only
    // its contributed dim; full shape (2,2,3) is assembled in the dope.
    sisal_array_t r = func_MAIN();
    int32_t ex[12] = { 2,4,6, 4,8,12,  1,2,3, 2,4,6 };
    bool ok = (r.rank == 3) && ((int)r.dims[0] == 2) && ((int)r.dims[1] == 2)
           && ((int)r.dims[2] == 3) && ((int)r.size == 12);
    for (int k = 0; ok && k < 12; k++) ok = ok && (((int32_t*)r.data)[k] == ex[k]);
    check("plane(q) at [3-q] == rank-3 (2,2,3), planes reversed", ok);
    if (r.data) free(r.data);
}
#endif
#ifdef TEST_TRANSPOSE_AT_DV
static void test_transpose_at_dv(void) {
    printf("\n=== Group: transpose_at_dv (cross forall scatter, no loop interchange) ===\n");
    // A 2x3 row-major [[1,2,3],[4,5,6]]; scatter at [j,i] -> 3x2 [[1,4],[2,5],[3,6]].
    sisal_array_t a = sisal_array_alloc_empty(2, 6, 6);
    a.dims[0] = 2; a.dims[1] = 3;
    for (int i = 0; i < 6; i++) ((int32_t*)a.data)[i] = i + 1;
    sisal_array_t t = func_MAIN(a, 2, 3);
    int32_t ex[6] = { 1,4, 2,5, 3,6 };
    bool ok = (t.rank == 2) && ((int)t.dims[0] == 3) && ((int)t.dims[1] == 2)
           && ((int)t.size == 6);
    for (int k = 0; ok && k < 6; k++) ok = ok && (((int32_t*)t.data)[k] == ex[k]);
    check("transpose(2x3) at [j,i] == 3x2", ok);
    if (a.data) free(a.data);
    if (t.data) free(t.data);
}
#endif
#ifdef TEST_FORALL_ROWSCATTER_DV
static void test_forall_rowscatter_dv(void) {
    printf("\n=== Group: forall_rowscatter_dv (whole arrays as tails at an index) ===\n");
    // row(i) lands at slot 4-i -> rows reversed; element dims = the slot's tail.
    sisal_array_t r = func_MAIN();
    int32_t ex[12] = { 3,6,9,12, 2,4,6,8, 1,2,3,4 };
    bool ok = (r.rank == 2) && ((int)r.dims[0] == 3) && ((int)r.dims[1] == 4)
           && ((int)r.size == 12);
    for (int k = 0; ok && k < 12; k++) ok = ok && (((int32_t*)r.data)[k] == ex[k]);
    check("forall row(i) at [4-i] == reversed rows (3,4)", ok);
    if (r.data) free(r.data);
}
#endif
#ifdef TEST_SMOOTH_DV
static void test_smooth_dv(void) {
    printf("\n=== Group: smooth_dv (rank-3 triple-cross stencil, 3 passes) ===\n");
    // Q quadratic per axis -> each pass adds 0.3*(D*2)/D = 0.6 at interior
    // points; boundary keeps S.  After 3 passes: interior = S + 1.8.
    int n = 4;
    sisal_array_t r = func_MAIN(n);
    float S = 924.143567f;
    bool ok = (r.rank == 3) && ((int)r.dims[0] == n) && ((int)r.dims[1] == n)
           && ((int)r.dims[2] == n) && ((int)r.size == n*n*n);
    for (int j = 1; ok && j <= n; j++)
      for (int k = 1; ok && k <= n; k++)
        for (int l = 1; ok && l <= n; l++) {
          bool interior = (j>1 && j<n && k>1 && k<n && l>1 && l<n);
          float exp = interior ? S + 1.8f : S;
          float got = ((float*)r.data)[((j-1)*n + (k-1))*n + (l-1)];
          ok = ok && (fabsf(got - exp) < 1e-2f);
        }
    check("smooth(4): interior == S+1.8, boundary == S, dims (4,4,4)", ok);
    if (r.data) free(r.data);
}
#endif
#ifdef TEST_DFT_DV
static void test_dft_dv(void) {
    printf("\n=== Group: dft_dv (DFT; RECORDS (complex_double) in array_dv) ===\n");
    // X[j] = sin(N*pi/8) is a CONSTANT signal (N=4 -> c=1): Y[1] = (N*c, 0),
    // all other bins 0.  First e2e exercising RBUILD/RELEMENTS lowering and
    // records as array_dv elements.  Tolerance 1e-6: some intermediates ride
    // float-typed slots (pre-existing inference default), not a records issue.
    struct cdbl { double re, im; };
    int N = 4;
    sisal_array_t y = func_MAIN(N);
    struct cdbl* d = (struct cdbl*)y.data;
    bool ok = ((int)y.size == N);
    ok = ok && (fabs(d[0].re - 4.0) < 1e-6) && (fabs(d[0].im) < 1e-6);
    for (int k = 1; ok && k < N; k++)
      ok = ok && (fabs(d[k].re) < 1e-6) && (fabs(d[k].im) < 1e-6);
    check("dft(const signal, N=4) == [(4,0), 0, 0, 0]", ok);
    if (y.data) free(y.data);
}
#endif
#ifdef TEST_RECORD_OPS_DV
static void test_record_ops_dv(void) {
    printf("\n=== Group: record_ops_dv (nested records, chained reads, replace) ===\n");
    // p = Pair{a:7, n:Inner{x:1,y:2}}; q = p replace [a:40];
    // s = p replace [n.x:9; a:50] (nested-field chain + plain clause).
    // Checks RBUILD (nested), RELEMENTS chains (p.n.x), RREPLACE, the
    // read-modify-write desugar for n.x, and TOPOLOGICAL struct emission.
    struct FUNC_MAIN_results r = func_MAIN();
    check("q: p.a+q.a, p.n.x+p.n.y, q.n.y == 47, 3, 2",
          r.r0 == 47 && r.r1 == 3 && r.r2 == 2);
    check("s = p replace [n.x:9; a:50]: s.n.x+s.n.y, s.a == 11, 50",
          r.r3 == 11 && r.r4 == 50);
    // record ARRAY through catenate (byte-math helper; elem_bytes authoritative)
    check("B = A || A: B[1].x+B[3].x, B[4].y == 2, 20",
          r.r5 == 2 && r.r6 == 20);
}
#endif

// ============================================================
// main — dispatches to the single active test group
// ============================================================

int
main (void)
{
  printf ("=== dv_run_all test harness ===\n");

#ifdef TEST_ABS_DEMO
  test_abs_demo ();
#endif
#ifdef TEST_AGREEMENT
  test_agreement ();
#endif
#ifdef TEST_LIFTED_ARITH
  test_lifted_arith ();
#endif
#ifdef TEST_SHL
  test_shl ();
#endif
#ifdef TEST_TEST_SUBSET
  test_test_subset ();
#endif
#ifdef TEST_INTRINSICS
  test_intrinsics ();
#endif
#ifdef TEST_BROADCAST_COMPLEX
  test_broadcast_complex ();
#endif
#ifdef TEST_COMPRESS
  test_compress ();
#endif
#ifdef TEST_BROADCAST_NUMPY
  test_broadcast_numpy ();
#endif
#ifdef TEST_FORALL_CPU
  test_forall_cpu ();
#endif
#ifdef TEST_NEGATE_DV
  test_negate_dv ();
#endif
#ifdef TEST_FORALL_BASIC_DV
  test_forall_basic_dv ();
#endif
#ifdef TEST_FORALL_REDUCE_DV
  test_forall_reduce_dv ();
#endif
#ifdef TEST_BULK_BASIC
  test_bulk_basic ();
#endif
#ifdef TEST_INNERPRODUCT_DV
  test_innerproduct_dv ();
#endif
#ifdef TEST_MATMUL_DV
  test_matmul_dv ();
#endif
#ifdef TEST_MATMUL_OP_DV
  test_matmul_op_dv ();
#endif

#ifdef TEST_FOR_INITIAL_DV
  test_for_initial_dv ();
#endif
#ifdef TEST_THREE
  test_three ();
#endif
#ifdef TEST_FACT
  test_fact ();
#endif
#ifdef TEST_IF_ONE
  test_if_one ();
#endif
#ifdef TEST_IF_TWO
  test_if_two ();
#endif
#ifdef TEST_IF_ELSEIF
  test_if_elseif ();
#endif
#ifdef TEST_MR_TWO_SCALAR
  test_mr_two_scalar ();
#endif
#ifdef TEST_LET_MULTI_BIND
  test_let_multi_bind ();
#endif
#ifdef TEST_LET_SEQ_BIND
  test_let_seq_bind ();
#endif
#ifdef TEST_XFA_B2_COND
  test_xfa_b2_cond ();
#endif
#ifdef TEST_AGGREGATE_ADD
  test_aggregate_add ();
#endif
#ifdef TEST_AREA
  test_area ();
#endif
#ifdef TEST_MULTIDECL
  test_multidecl ();
#endif
#ifdef TEST_LOOPCARRY_USED
  test_loopcarry_used ();
#endif
#ifdef TEST_LOOPCARRY_IDENTITY
  test_loopcarry_identity ();
#endif
#ifdef TEST_SUB_MATMUL
  test_sub_matmul ();
#endif
#ifdef TEST_PI
  test_pi ();
#endif
#ifdef TEST_TEST_MIX_ARRAY_DV
  test_test_mix_array_dv ();
#endif
#ifdef TEST_TST_LOOP1_DV
  test_tst_loop1_dv ();
#endif
#ifdef TEST_LOOP2_INNER
  test_loop2_inner ();
#endif
#ifdef TEST_LOOP1_DV
  test_loop1_dv ();
#endif
#ifdef TEST_LOOP3_DV
  test_loop3_dv ();
#endif
#ifdef TEST_LOOP7_DV
  test_loop7_dv ();
#endif
#ifdef TEST_LOOP12_DV
  test_loop12_dv ();
#endif
#ifdef TEST_LOOP24_DV
  test_loop24_dv ();
#endif
#ifdef TEST_LOOP9_DV
  test_loop9_dv ();
#endif
#ifdef TEST_LOOP10_DV
  test_loop10_dv ();
#endif
#ifdef TEST_LOOP21_DV
  test_loop21_dv ();
#endif
#ifdef TEST_LOOP2_DV
  test_loop2_dv ();
#endif
#ifdef TEST_LOOP2S_DV
  test_loop2s_dv ();
#endif
#ifdef TEST_MR2_INIT
  test_mr2_init ();
#endif
#ifdef TEST_LOOP16_DV
  test_loop16_dv ();
#endif
#ifdef TEST_LOOP13_DV
  test_loop13_dv ();
#endif
#ifdef TEST_LOOP5_DV
  test_loop5_dv ();
#endif
#ifdef TEST_LOOP11S_DV
  test_loop11s_dv ();
#endif
#ifdef TEST_LOOP17_DV
  test_loop17_dv ();
#endif
#ifdef TEST_LOOP15_DV
  test_loop15_dv ();
#endif
#ifdef TEST_LOOP22_DV
  test_loop22_dv ();
#endif
#ifdef TEST_BUILDFILL_DV
  test_buildfill_dv ();
#endif
#ifdef TEST_LOOP20_DV
  test_loop20_dv ();
#endif
#ifdef TEST_LOOP19S_DV
  test_loop19s_dv ();
#endif
#ifdef TEST_LOOP14_DV
  test_loop14_dv ();
#endif
#ifdef TEST_LOOP23S_DV
  test_loop23s_dv ();
#endif
#ifdef TEST_LOOP18P_DV
  test_loop18p_dv ();
#endif
#ifdef TEST_LOOP8P_DV
  test_loop8p_dv ();
#endif
#ifdef TEST_CAP_NESTED_DV
  test_cap_nested_dv ();
#endif
#ifdef TEST_CAP_ARRAY_DV
  test_cap_array_dv ();
#endif
#ifdef TEST_CAP_FORINIT_DV
  test_cap_forinit_dv ();
#endif
#ifdef TEST_MR_FORALL_DV
  test_mr_forall_dv ();
#endif
#ifdef TEST_MR_FORINIT_DV
  test_mr_forinit_dv ();
#endif
#ifdef TEST_MR_1D2D_DV
  test_mr_1d2d_dv ();
#endif
#ifdef TEST_FN_MULTIOUT_DV
  test_fn_multiout_dv ();
#endif
#ifdef TEST_IF_MULTIOUT_DV
  test_if_multiout_dv ();
#endif
#ifdef TEST_FNCALL_FORALL_DV
  test_fncall_forall_dv ();
#endif
#ifdef TEST_NESTED_FORALL_DV
  test_nested_forall_dv ();
#endif
#ifdef TEST_CAP_2DEEP_DV
  test_cap_2deep_dv ();
#endif
#ifdef TEST_FN3RANK_DV
  test_fn3rank_dv ();
#endif
#ifdef TEST_IFTUPLE_FORALL_DV
  test_iftuple_forall_dv ();
#endif
#ifdef TEST_RED_RANKS_DV
  test_red_ranks_dv ();
#endif
#ifdef TEST_RED_OPS_DV
  test_red_ops_dv ();
#endif
#ifdef TEST_RED_ARR_DV
  test_red_arr_dv ();
#endif
#ifdef TEST_BCAST3D_DV
  test_bcast3d_dv ();
#endif
#ifdef TEST_BCAST31_DV
  test_bcast31_dv ();
#endif
#ifdef TEST_IP_DV
  test_ip_dv ();
#endif
#ifdef TEST_CONV_DV
  test_conv_dv ();
#endif
#ifdef TEST_LAPLACE_DV
  test_laplace_dv ();
#endif
#ifdef TEST_SHAPED_GATHER_DV
  test_shaped_gather_dv ();
#endif
#ifdef TEST_FORINIT_MAT_GATHER_DV
  test_forinit_mat_gather_dv ();
#endif
#ifdef TEST_SCATTER_AT_DV
  test_scatter_at_dv ();
#endif
#ifdef TEST_GROW_NEST_DV
  test_grow_nest_dv ();
#endif
#ifdef TEST_TRANSPOSE_AT_DV
  test_transpose_at_dv ();
#endif
#ifdef TEST_FORALL_ROWSCATTER_DV
  test_forall_rowscatter_dv ();
#endif
#ifdef TEST_SMOOTH_DV
  test_smooth_dv ();
#endif
#ifdef TEST_DFT_DV
  test_dft_dv ();
#endif
#ifdef TEST_RECORD_OPS_DV
  test_record_ops_dv ();
#endif
#ifdef TEST_RECORD_E2E
  test_record_e2e ();
#endif
#ifdef TEST_TAGCASE_E2E
  test_tagcase_e2e ();
#endif
#ifdef TEST_COMPLEX_FEATURES_E2E
  test_complex_features_e2e ();
#endif
#ifdef TEST_COMPLEX_OPS_E2E
  test_complex_ops_e2e ();
#endif
#ifdef TEST_LOOP6_DV
  test_loop6_dv ();
#endif
#ifdef TEST_LOOP4_DV
  test_loop4_dv ();
#endif
#ifdef TEST_SUB_2D_DIAG
  test_sub_2d_diag ();
#endif
#ifdef TEST_LET_NESTED_SEQ
  test_let_nested_seq ();
#endif
#ifdef TEST_FORTY2
  test_forty2 ();
#endif
#ifdef TEST_XFA_B1_DECLDEF
  test_xfa_b1_decldef ();
#endif
#ifdef TEST_XFA_C3_3AXIS
  test_xfa_c3_3axis ();
#endif
#ifdef TEST_SLICE_STORE
  test_slice_store ();
#endif
#ifdef TEST_MR_TWO_ARRAY
  test_mr_two_array ();
#endif
#ifdef TEST_AA
  test_aa ();
#endif
#ifdef TEST_SUB_2D
  test_sub_2d ();
#endif
#ifdef TEST_SUB_3D
  test_sub_3d ();
#endif
#ifdef TEST_SLICE_DOTDOT
  test_slice_dotdot ();
#endif
#ifdef TEST_TEST_MULTI_ARRAY_IF
  test_test_multi_array_if ();
#endif
#ifdef TEST_FORALL_DV_AT
  test_forall_dv_at ();
#endif
#ifdef TEST_FORALL_DV_CROSS
  test_forall_dv_cross ();
#endif
#ifdef TEST_FORALL_DV_DOT
  test_forall_dv_dot ();
#endif
#ifdef TEST_FORALL_DV_DOT3
  test_forall_dv_dot3 ();
#endif
#ifdef TEST_RED_SUM
  test_red_sum ();
#endif
#ifdef TEST_RED_PRODUCT
  test_red_product ();
#endif
#ifdef TEST_RED_GREATEST
  test_red_greatest ();
#endif
#ifdef TEST_RED_LEAST
  test_red_least ();
#endif
#ifdef TEST_RED_ARGMAX
  test_red_argmax ();
#endif
#ifdef TEST_RED_ARGMIN
  test_red_argmin ();
#endif
#ifdef TEST_RED_SUM_CROSS
  test_red_sum_cross ();
#endif
#ifdef TEST_FOR_INITIAL
  test_for_initial ();
#endif
#ifdef TEST_GAUSSJ_PARTS
  test_gaussj_parts ();
#endif
#ifdef TEST_GAUSSJ
  test_gaussj ();
#endif
#ifdef TEST_SWAPLOOP
  test_swaploop ();
#endif
#ifdef TEST_GEN_EXTENT
  test_gen_extent ();
#endif
#ifdef TEST_BROADCAST_PARTS
  test_broadcast_parts ();
#endif
#ifdef TEST_IF_COND
  test_if_cond ();
#endif
#ifdef TEST_FORALL_DV_SIMPLE
  test_forall_dv_simple ();
#endif
#ifdef TEST_CROSS_DV_DEMO
  test_cross_dv_demo ();
#endif
#ifdef TEST_FORALL_NEGATE
  test_forall_negate ();
#endif
#ifdef TEST_RANK8_SLICES
  run_rank8_slices ();
#endif
#ifdef TEST_NEWTON_RAPHSON
  test_newton_raphson ();
#endif
#ifdef TEST_FEO_FFT_PARTS1
  test_feo_fft_parts1 ();
#endif
#ifdef TEST_FEO_FFT_PARTS2
  test_feo_fft_parts2 ();
#endif
#ifdef TEST_FEO_FFT_PARTS3
  test_feo_fft_parts3 ();
#endif
#ifdef TEST_FEO_FFT_PARTS4
  test_feo_fft_parts4 ();
#endif
#ifdef TEST_FEO_FFT_DV
  test_feo_fft_dv ();
#endif
#ifdef TEST_FEO_FFT
  test_feo_fft ();
#endif


#if !defined(TEST_ABS_DEMO) && !defined(TEST_AGREEMENT)                       \
    && !defined(TEST_LIFTED_ARITH) && !defined(TEST_SHL)                      \
    && !defined(TEST_TEST_SUBSET) && !defined(TEST_INTRINSICS)                \
    && !defined(TEST_BROADCAST_COMPLEX) && !defined(TEST_COMPRESS)            \
    && !defined(TEST_BROADCAST_NUMPY) && !defined(TEST_FORALL_CPU)            \
    && !defined(TEST_NEGATE_DV) && !defined(TEST_FORALL_BASIC_DV)             \
    && !defined(TEST_FORALL_REDUCE_DV) && !defined(TEST_BULK_BASIC)           \
    && !defined(TEST_INNERPRODUCT_DV) && !defined(TEST_MATMUL_DV)             \
    && !defined(TEST_FOR_INITIAL_DV) && !defined(TEST_FORALL_DV_AT)           \
    && !defined(TEST_FORALL_DV_CROSS) && !defined(TEST_FORALL_DV_DOT)         \
    && !defined(TEST_FORALL_DV_DOT3) && !defined(TEST_THREE)                  \
    && !defined(TEST_FACT) && !defined(TEST_IF_ONE) && !defined(TEST_IF_TWO)  \
    && !defined(TEST_IF_ELSEIF) && !defined(TEST_MR_TWO_SCALAR)               \
    && !defined(TEST_LET_MULTI_BIND) && !defined(TEST_LET_SEQ_BIND)           \
    && !defined(TEST_XFA_B2_COND) && !defined(TEST_AGGREGATE_ADD)             \
    && !defined(TEST_AREA) && !defined(TEST_MULTIDECL)                        \
    && !defined(TEST_LOOPCARRY_USED) && !defined(TEST_LOOPCARRY_IDENTITY)     \
    && !defined(TEST_SUB_2D) && !defined(TEST_SUB_3D)                         \
    && !defined(TEST_SLICE_DOTDOT) && !defined(TEST_TEST_MULTI_ARRAY_IF)      \
    && !defined(TEST_SUB_2D_DIAG) && !defined(TEST_LET_NESTED_SEQ)            \
    && !defined(TEST_FORTY2) && !defined(TEST_XFA_B1_DECLDEF)                 \
    && !defined(TEST_XFA_C3_3AXIS) && !defined(TEST_SLICE_STORE)              \
    && !defined(TEST_MR_TWO_ARRAY) && !defined(TEST_AA)                       \
    && !defined(TEST_SUB_MATMUL) && !defined(TEST_PI)                         \
    && !defined(TEST_TEST_MIX_ARRAY_DV) && !defined(TEST_TST_LOOP1_DV)        \
    && !defined(TEST_LOOP2_INNER) && !defined(TEST_RED_SUM)                   \
    && !defined(TEST_RED_PRODUCT) && !defined(TEST_RED_GREATEST)              \
    && !defined(TEST_RED_LEAST) && !defined(TEST_RED_ARGMAX)                  \
    && !defined(TEST_RED_ARGMIN) && !defined(TEST_RED_SUM_CROSS)              \
    && !defined(TEST_FOR_INITIAL) && !defined(TEST_GAUSSJ_PARTS)              \
    && !defined(TEST_GAUSSJ) && !defined(TEST_SWAPLOOP)                       \
    && !defined(TEST_GEN_EXTENT) && !defined(TEST_BROADCAST_PARTS)            \
    && !defined(TEST_IF_COND) && !defined(TEST_FORALL_DV_SIMPLE)              \
    && !defined(TEST_CROSS_DV_DEMO) && !defined(TEST_FORALL_NEGATE)           \
    && !defined(TEST_LOOP1_DV) && !defined(TEST_LOOP3_DV)                     \
    && !defined(TEST_LOOP7_DV) && !defined(TEST_LOOP12_DV)                    \
    && !defined(TEST_LOOP24_DV) && !defined(TEST_LOOP9_DV)                    \
    && !defined(TEST_LOOP21_DV) && !defined(TEST_LOOP2_DV)                    \
    && !defined(TEST_LOOP2S_DV) && !defined(TEST_LOOP6_DV)                    \
    && !defined(TEST_LOOP4_DV) && !defined(TEST_MR2_INIT)                     \
    && !defined(TEST_LOOP16_DV) && !defined(TEST_LOOP13_DV)                   \
    && !defined(TEST_LOOP5_DV) && !defined(TEST_LOOP11S_DV)                   \
    && !defined(TEST_LOOP17_DV) && !defined(TEST_LOOP15_DV)                   \
    && !defined(TEST_LOOP22_DV) && !defined(TEST_BUILDFILL_DV)                \
    && !defined(TEST_LOOP20_DV) && !defined(TEST_LOOP10_DV)                   \
    && !defined(TEST_LOOP19S_DV) && !defined(TEST_LOOP14_DV)                  \
    && !defined(TEST_LOOP23S_DV) && !defined(TEST_LOOP18P_DV) && !defined(TEST_LOOP8P_DV) \
    && !defined(TEST_CAP_NESTED_DV) && !defined(TEST_CAP_ARRAY_DV)            \
    && !defined(TEST_CAP_FORINIT_DV) && !defined(TEST_MR_FORALL_DV)           \
    && !defined(TEST_MR_FORINIT_DV) && !defined(TEST_MR_1D2D_DV)              \
    && !defined(TEST_FN_MULTIOUT_DV) && !defined(TEST_IF_MULTIOUT_DV)        \
    && !defined(TEST_FNCALL_FORALL_DV) && !defined(TEST_NESTED_FORALL_DV)     \
    && !defined(TEST_CAP_2DEEP_DV) && !defined(TEST_FN3RANK_DV)               \
    && !defined(TEST_IFTUPLE_FORALL_DV) && !defined(TEST_RED_RANKS_DV)         \
    && !defined(TEST_RED_OPS_DV) && !defined(TEST_RED_ARR_DV)                  \
    && !defined(TEST_BCAST3D_DV) && !defined(TEST_BCAST31_DV)                  \
    && !defined(TEST_IP_DV) && !defined(TEST_MATMUL_OP_DV) && !defined(TEST_CONV_DV) && !defined(TEST_LAPLACE_DV)                    \
    && !defined(TEST_SHAPED_GATHER_DV) && !defined(TEST_FORINIT_MAT_GATHER_DV) \
    && !defined(TEST_SCATTER_AT_DV) && !defined(TEST_GROW_NEST_DV)            \
    && !defined(TEST_TRANSPOSE_AT_DV) && !defined(TEST_FORALL_ROWSCATTER_DV)  \
    && !defined(TEST_SMOOTH_DV) && !defined(TEST_DFT_DV)                      \
    && !defined(TEST_RECORD_OPS_DV)                                           \
    && !defined(TEST_RECORD_E2E)                                              \
    && !defined(TEST_TAGCASE_E2E)                                              \
    && !defined(TEST_COMPLEX_FEATURES_E2E)                                    \
    && !defined(TEST_COMPLEX_OPS_E2E)                                         \
    && !defined(TEST_RANK8_SLICES)                                            \
    && !defined(TEST_NEWTON_RAPHSON)                                          \
    && !defined(TEST_FEO_FFT_PARTS1) && !defined(TEST_FEO_FFT_PARTS2)         \
    && !defined(TEST_FEO_FFT_PARTS3) && !defined(TEST_FEO_FFT_PARTS4)         \
    && !defined(TEST_FEO_FFT_DV) && !defined(TEST_FEO_FFT)
  printf ("ERROR: No TEST_XXX macro defined.  Compile with e.g. "
          "-DTEST_ABS_DEMO\n");
  return 1;
#endif

  printf ("\n--- Summary: %d passed, %d failed ---\n", g_pass, g_fail);
  return (g_fail > 0) ? 1 : 0;
}
