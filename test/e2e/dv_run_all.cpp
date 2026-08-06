// dv_run_all.cpp — Test harness for all 9 dv_*.sis generated C++ files.
//
// Compile with a -DTEST_XXX flag to select one group, e.g.:
//   clang++ -std=c++17 -I<runtime> -DTEST_ABS_DEMO dv_run_all.cpp
//   dv_abs_demo.cpp -o test_abs_demo
//
// See run_dv_tests.sh for the full build + run script.

#include <algorithm>
#include <cmath>
#include <sisal_runtime.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <vector>

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

#ifdef TEST_ARRAY_ADD_DV
extern "C" sisal_array_t func_MAIN(sisal_array_t A, sisal_array_t B);
#endif

#ifdef TEST_PICK_DV
extern "C" sisal_array_t func_PICK(int32_t mode, sisal_array_t A);
#endif

#ifdef TEST_ZERO_ARRAYS
struct FUNC_MAIN_results { sisal_array_t r0, r1, r2; };
extern "C" struct FUNC_MAIN_results func_MAIN(int32_t N);
#endif

#ifdef TEST_XFA_B4_REDUCE
extern "C" int32_t func_MAIN(int32_t n, int32_t m);
#endif

#if defined(TEST_XFA_C4_DEP2) || defined(TEST_XFA_C5_DEP3)
extern "C" sisal_array_t func_MAIN(int32_t n);
#endif

#ifdef TEST_FORALL_GPU_DV
extern "C" sisal_array_t func_MAIN_GPU(int32_t n);
#endif

#ifdef TEST_MIX_ARRAY_DV_IF
struct FUNC_MAIN_results { sisal_array_t r0, r1; };
extern "C" struct FUNC_MAIN_results func_MAIN(bool flag);
#endif

#ifdef TEST_QUEENS_DV
extern "C" sisal_array_t func_MAIN(int32_t level);
#endif

#ifdef TEST_GAUSSJ_PERM_DV
extern "C" sisal_array_t func_GAUSSJ_PERM(int32_t n, sisal_array_t A, sisal_array_t B);
#endif

#ifdef TEST_FORINIT_HISTORY_DV
extern "C" sisal_array_t func_MAIN(int32_t n);
extern "C" int32_t func_LAST_VAL(int32_t n);
#endif

#ifdef TEST_MATMULT_DV
extern "C" sisal_array_t func_MULTIPLY(int32_t x, int32_t y, int32_t z,
                                        sisal_array_t A, sisal_array_t B);
#endif

#ifdef TEST_MM_DV
extern "C" float func_MAIN(int32_t rowsize);
#endif

#ifdef TEST_TRANSPOSE_DV
extern "C" sisal_array_t func_TRANSPOSE(int32_t n, int32_t m, sisal_array_t A);
#endif

#ifdef TEST_SP_DV
struct FUNC_MAIN_results { int32_t res_0; sisal_array_t res_1; };
extern "C" struct FUNC_MAIN_results func_MAIN(int32_t n, sisal_array_t A,
                                              sisal_array_t AJ,
                                              sisal_array_t x0,
                                              sisal_array_t g);
#endif

#ifdef TEST_INVERSE_DV
extern "C" sisal_array_t func_FIND_INVERSE(sisal_array_t A, int32_t n);
#endif

#ifdef TEST_BADFFT_DV
extern "C" bool func_MAIN(int32_t m);
#endif

#ifdef TEST_FLOAT_SCATTER_DV
extern "C" sisal_array_t func_F(sisal_array_t v, sisal_array_t w);
#endif

#if defined(TEST_SUB_R3_PERM) || defined(TEST_SUB_R4_PERM) || defined(TEST_SUB_R5_PERM)
extern "C" int32_t func_MAIN(int32_t n);
#endif

#ifdef TEST_IF_ARRAY_DV
extern "C" sisal_array_t func_MAIN(bool flag);
#endif

#ifdef TEST_MIX_SCALAR_ARRAY_DV
// res_2 is FLOAT: the Sisal literal 3.14 is REAL even though the function
// declares double_real (frontend typing quirk).
struct FUNC_MAIN_results { int32_t res_0; sisal_array_t res_1; float res_2; };
extern "C" struct FUNC_MAIN_results func_MAIN(bool flag);
#endif

#ifdef TEST_IF_MULTI_ARRAY_DV
struct FUNC_MAIN_results { sisal_array_t res_0, res_1; };
extern "C" struct FUNC_MAIN_results func_MAIN(bool flag);
#endif

#if defined(TEST_MULTI_ARRAY_IF_DV) || defined(TEST_UNION_ARRAY_IF_DV)
struct FUNC_MAIN_results { sisal_array_t res_0, res_1; };
extern "C" struct FUNC_MAIN_results func_MAIN(int32_t n);
#endif

#ifdef TEST_ARRAY_SWAP_E2E
struct FUNC_MAIN_results { sisal_array_t res_0, res_1; };
extern "C" struct FUNC_MAIN_results func_MAIN(sisal_array_t A, sisal_array_t B);
#endif
#ifdef TEST_QUICKSORT_DV
extern "C" sisal_array_t func_MAIN(sisal_array_t Data);
#endif
#ifdef TEST_HEAPSORT_DV
extern "C" sisal_array_t func_MAIN(sisal_array_t list);
#endif
#ifdef TEST_NESTED_CAPTURE_DV
extern "C" int32_t func_MAIN(int32_t n);
#endif
#ifdef TEST_STREAM_GURD_DV
extern "C" sisal_generator<int32_t> func_MAIN(int32_t N);
#endif
#ifdef TEST_TEST_IF_NESTED_CAPTURE_DV
extern "C" int32_t func_MAIN(int32_t selector, bool flag, int32_t captured_val);
#endif
#ifdef TEST_TEST_IF_LET_CASCADE_DV
extern "C" int32_t func_MAIN(int32_t selector, bool flag, int32_t v1, int32_t v2, int32_t v3);
#endif
#ifdef TEST_TAGCASE_BARE_DV
struct FUNC_MAIN_results { int32_t res_0, res_1, res_2; bool res_3; };
extern "C" struct FUNC_MAIN_results func_MAIN(int32_t s);
#endif
#ifdef TEST_TAGCASE_BARE_MIXED_DV
struct FUNC_MAIN_results { int32_t res_0, res_1; };
extern "C" struct FUNC_MAIN_results func_MAIN(int32_t s);
#endif
#ifdef TEST_TAGCASE_BARE_NESTED_DV
extern "C" int32_t func_MAIN(int32_t s);
#endif
#ifdef TEST_CRYPTO_DV
extern "C" bool func_MAIN(sisal_array_t password, sisal_array_t trial);
#endif
#ifdef TEST_SQRT_DV
struct FUNC_MAIN_results { double res_0, res_1; };
extern "C" struct FUNC_MAIN_results func_MAIN(double X, double Epsilon);
#endif
#ifdef TEST_REC_FIELD_DV
extern "C" double func_MAIN();
#endif
#ifdef TEST_REC_AOS_DV
extern "C" int32_t func_MAIN();
#endif
#ifdef TEST_REC_SOA_DV
extern "C" int32_t func_MAIN();
#endif
#ifdef TEST_RESHAPE_DV
extern "C" int32_t func_MAIN();
#endif
#ifdef TEST_SOA_INIT_DV
extern "C" double func_MAIN();
#endif
#ifdef TEST_NUCLEIC_SOA_DV
extern "C" double func_MAIN();
#endif
#ifdef TEST_NUCLEIC_MAKET_DV
extern "C" double func_MAIN();
#endif
#ifdef TEST_NUCLEIC_DGFBASE_DV
extern "C" double func_MAIN();
#endif
#ifdef TEST_NUCLEIC_GETVAR_DV
extern "C" int32_t func_MAIN();
#endif
#ifdef TEST_MEMBER_DV
struct MEMBER_DV_results { int32_t res_0, res_1; bool res_2, res_3; };
extern "C" struct MEMBER_DV_results func_MAIN();
#endif
#ifdef TEST_ML_LIST_DV
struct ML_LIST_results { int32_t res_0, res_1, res_2, res_3; };
extern "C" struct ML_LIST_results func_MAIN();
#endif
#ifdef TEST_NUCLEIC_SEARCH_DV
struct NUC_SEARCH_results { int32_t res_0, res_1; };
extern "C" struct NUC_SEARCH_results func_MAIN();
#endif
#ifdef TEST_ML_LIST_REPLACE_DV
struct ML_REPL_results { int32_t res_0, res_1, res_2, res_3, res_4, res_5; };
extern "C" struct ML_REPL_results func_MAIN();
#endif
#ifdef TEST_NUCLEIC_KERNELS_DV
struct NUC_KERN_results { double res_0, res_1, res_2; };
extern "C" struct NUC_KERN_results func_MAIN();
#endif
#ifdef TEST_NUCLEIC_BUILDERS_DV
struct NUC_BLD_results { int32_t res_0, res_1, res_2, res_3, res_4; };
extern "C" struct NUC_BLD_results func_MAIN();
#endif
#ifdef TEST_NUCLEIC_BASES_DV
struct NUC_BASE_results { double res_0, res_1, res_2, res_3, res_4, res_5; };
extern "C" struct NUC_BASE_results func_MAIN();
#endif
#ifdef TEST_NUCLEIC_DV
struct NUCLEIC_results { double dist, count; };
extern "C" struct NUCLEIC_results func_MAIN();
#endif
#ifdef TEST_BINTREE_DV
struct BINTREE_results { int32_t res_0, res_1, res_2, res_3, res_4; };
extern "C" struct BINTREE_results func_MAIN();
#endif
#ifdef TEST_PARA_DEARRAY_DV
struct PARA_results { int32_t n0,n1,n2,n3,n4,n5,n6,n7; };
extern "C" struct PARA_results func_MAIN();
#endif
#ifdef TEST_LIST_ITER_DV
struct LIST_ITER_results { int32_t s1, l1, s2, l2; };
extern "C" struct LIST_ITER_results func_MAIN();
#endif
#ifdef TEST_FORINIT_REDUCE_DV
struct FORINIT_RED_results { int32_t s, p, g, l; sisal_array_t gath; int32_t par; };
extern "C" struct FORINIT_RED_results func_MAIN();
#endif
#ifdef TEST_WORDCOUNT_DV
extern "C" int32_t func_MAIN(sisal_array_t text);
#endif
#ifdef TEST_BACKTRACK_DV
struct BT_results { sisal_array_t jobs, segs, leafvals; };
extern "C" struct BT_results func_MAIN();
#endif
#ifdef TEST_SUCCESSOR_DV
extern "C" sisal_array_t func_MAIN(sisal_array_t ab, sisal_array_t del, int32_t q, int32_t n);
#endif
#ifdef TEST_GENLINKS_DV
struct GL_results { sisal_array_t links, ptrs, vs, depth; };
extern "C" struct GL_results func_MAIN(sisal_array_t ab, sisal_array_t zeros,
                                       int32_t n, int32_t q, sisal_array_t del);
#endif
#ifdef TEST_GENARCS_DV
struct GA_results { sisal_array_t grid, arcs; };
extern "C" struct GA_results func_MAIN(sisal_array_t links, sisal_array_t grid,
                                       sisal_array_t vs, sisal_array_t depth,
                                       int32_t n, int32_t q);
#endif
#ifdef TEST_FORINIT_MASK_DV
struct FM_results { sisal_array_t fa, fi; int32_t ra, ri;
                    sisal_array_t zt, zf, un; };
extern "C" struct FM_results func_MAIN();
#endif
#ifdef TEST_ZEROTRIP_EXPR_DV
struct ZT_results { int32_t fvb, fve, fvn; sisal_array_t gab, gae;
                    int32_t rdb, rde, live; };
extern "C" struct ZT_results func_MAIN();
#endif
#ifdef TEST_MOLDYN_NBRLIST_DV
struct nl_pos { sisal_array_t X, Y, Z; };
struct nl_vel { sisal_array_t VX, VY, VZ; };
struct nl_ens { float tout, step, err; int32_t size; nl_pos pos; nl_vel vel;
                sisal_array_t types; };
struct nl_pd  { int32_t nt; sisal_array_t A1, B1, Re, Rc, ALFA, C0, MASS;
                float dt, endt, tol; };
struct NL_results { sisal_array_t row, lens; int32_t nrows; };
extern "C" struct NL_results func_MAIN(nl_ens e, nl_pd pd, int32_t want);
#endif
#ifdef TEST_MOLDYN_NEIGHBORS_DV
struct mn_pos { sisal_array_t X, Y, Z; };
struct mn_vel { sisal_array_t VX, VY, VZ; };
struct mn_ens { float tout, step, err; int32_t size; mn_pos pos; mn_vel vel;
                sisal_array_t types; };
struct mn_pd  { int32_t nt; sisal_array_t A1, B1, Re, Rc, ALFA, C0, MASS;
                float dt, endt, tol; };
struct MN_results { sisal_array_t neighbors, ncount, scan; };
extern "C" struct MN_results func_MAIN(mn_ens e, mn_pd pd);
#endif
#ifdef TEST_GATHER_CONFORM_DV
struct GC_results { sisal_array_t rows, lens, last; };
extern "C" struct GC_results func_MAIN(int32_t m);
#endif
#ifdef TEST_FORINIT_CATENATE_DV
struct FCAT_results { sisal_array_t seq, zt, mask, fa; int32_t n; };
extern "C" struct FCAT_results func_MAIN(void);
#endif
#ifdef TEST_PSA_DV
struct PSA_results { sisal_array_t sz0, firsts; int32_t cost0, nsw, nsu;
                     sisal_array_t sz1, Es, szf; int32_t tot; };
extern "C" struct PSA_results func_MAIN(int32_t NT, int32_t MP, int32_t sd,
                                        int32_t msw, int32_t msu, float t0);
#endif
#ifdef TEST_PSA_UPDATE_DV
struct PSA_UPD_results { sisal_array_t sz1; int32_t E1; sisal_array_t subj1;
                         int32_t gc, E2; sisal_array_t sz2; };
extern "C" struct PSA_UPD_results func_MAIN(int32_t cap);
#endif
#ifdef TEST_PSA_SWAP_DV
struct PSA_SWAP_results { sisal_array_t sw, s1; int32_t ok;
                          sisal_array_t swp; bool b; };
extern "C" struct PSA_SWAP_results func_MAIN(int32_t sd, float tmp);
#endif
#ifdef TEST_XFA_DEP_EXPR
struct XDE_results { sisal_array_t bare, plus1, lower, upper; int32_t pairs; };
extern "C" struct XDE_results func_MAIN(int32_t n);
#endif
#ifdef TEST_PSA_COST_DV
struct PSA_COST_results { sisal_array_t PC; int32_t GC; bool m1, m2;
                          int32_t i1, i2; sisal_array_t RPC; int32_t RGC;
                          sisal_array_t RSZ; };
extern "C" struct PSA_COST_results func_MAIN(int32_t NP, int32_t NT);
#endif
#ifdef TEST_PSA_RNG_DV
struct PSA_RNG_results { sisal_array_t K, KB, AK, SS; double r; sisal_array_t s2; };
extern "C" struct PSA_RNG_results func_MAIN(int32_t n, int32_t s1);
#endif
#ifdef TEST_FORINIT_GATHER_GROWTH_DV
struct FGG_results { sisal_array_t ok, eq, cj, mk, rl, bl; };
extern "C" struct FGG_results func_MAIN(void);
#endif
#ifdef TEST_ADDH_ROW_DV
struct AR_results { sisal_array_t one, blk, grown, flat, ident,
                                  ah_one, ah_empty, ah_accum; };
extern "C" struct AR_results func_MAIN(int32_t n);
#endif
#ifdef TEST_MOLDYN_DV
struct mdy_posr { sisal_array_t X, Y, Z; };
struct mdy_velr { sisal_array_t VX, VY, VZ; };
struct mdy_ens { float tout, step, err; int32_t size; mdy_posr pos; mdy_velr vel;
                 sisal_array_t types; };
struct mdy_pd { int32_t nt; sisal_array_t A1, B1, Re, Rc, ALFA, C0, MASS;
                float dt, endt, tol; };
struct MDY_results { sisal_array_t traj; mdy_ens e; };
extern "C" struct MDY_results func_MAIN(mdy_ens e, sisal_array_t neighbors,
                                        sisal_array_t ncount, mdy_pd pd);
#endif
#ifdef TEST_MOLDYN_SOLVE_DV
struct sv_posr { sisal_array_t X, Y, Z; };
struct sv_velr { sisal_array_t VX, VY, VZ; };
struct sv_ens { float tout, step, err; int32_t size; sv_posr pos; sv_velr vel;
                sisal_array_t types; };
struct sv_pd { int32_t nt; sisal_array_t A1, B1, Re, Rc, ALFA, C0, MASS;
               float dt, endt, tol; };
extern "C" sv_ens func_MAIN(sv_ens e, sisal_array_t neighbors,
                            sisal_array_t ncount, sv_pd pd);
#endif
#ifdef TEST_MOLDYN_RKF45_DV
struct f45_pd { int32_t nt; sisal_array_t A1, B1, Re, Rc, ALFA, C0, MASS;
                float dt, endt, tol; };
struct F45_results { sisal_array_t s; float h, err; };
extern "C" struct F45_results func_MAIN(sisal_array_t S, float H, float TOUT,
                                        float TOL, sisal_array_t types,
                                        sisal_array_t neighbors,
                                        sisal_array_t ncount, f45_pd pd);
#endif
#ifdef TEST_MOLDYN_RK_DV
struct rk_pd { int32_t nt; sisal_array_t A1, B1, Re, Rc, ALFA, C0, MASS;
               float dt, endt, tol; };
struct RK_results { sisal_array_t k, beta, sg; };
extern "C" struct RK_results func_MAIN(sisal_array_t S, float H, float TOUT,
                                       sisal_array_t types, sisal_array_t neighbors,
                                       sisal_array_t ncount, rk_pd pd);
#endif
#ifdef TEST_MOLDYN_DIFFUN_DV
struct df_pd { int32_t nt; sisal_array_t A1, B1, Re, Rc, ALFA, C0, MASS;
               float dt, endt, tol; };
struct DF_results { sisal_array_t sdot; };
extern "C" struct DF_results func_MAIN(sisal_array_t S, sisal_array_t types,
                                       sisal_array_t neighbors, sisal_array_t ncount,
                                       df_pd pd, int32_t np);
#endif
#ifdef TEST_MOLDYN_FORCE_DV
struct md_pd { int32_t nt; sisal_array_t A1, B1, Re, Rc, ALFA, C0, MASS;
               float dt, endt, tol; };
struct MD_results { sisal_array_t fx, fy, fz; };
extern "C" struct MD_results func_MAIN(sisal_array_t S, sisal_array_t types,
                                       sisal_array_t neighbors, sisal_array_t ncount,
                                       md_pd pd, int32_t np);
#endif
#ifdef TEST_JOB_DV
struct jb_srec  { float start, finish, dur; int32_t prio; };
struct jb_sortr { float val; int32_t loc; };
struct jb_elem  { float alpha, beta; int32_t prio; };
struct jb_maxr  { int32_t val, job, seg; };
struct jb_segr  { int32_t ecnt; jb_maxr mx; int32_t prio; bool fired, leaf; };
struct jb_arcr  { int32_t job, seg; jb_maxr mx; };
struct JOB_results { sisal_array_t finalptrs, path; };
extern "C" struct JOB_results func_MAIN(int32_t q, sisal_array_t a);
#endif
#ifdef TEST_TRACE_DV
struct tr_maxr { int32_t val, job, seg; };
struct tr_segr { int32_t ecnt; tr_maxr mx; int32_t prio; bool fired, leaf; };
struct tr_arcr { int32_t job, seg; tr_maxr mx; };
extern "C" sisal_array_t func_MAIN(sisal_array_t links, sisal_array_t ptrs,
                                   sisal_array_t vs, sisal_array_t depth,
                                   int32_t n, int32_t q);
#endif
#ifdef TEST_ARCGRID_DV
struct ag_maxr { int32_t val, job, seg; };
struct ag_segr { int32_t ecnt; ag_maxr mx; int32_t prio; bool fired, leaf; };
struct ag_arcr { int32_t job, seg; ag_maxr mx; };
struct AG_results { sisal_array_t grid, maxs, cnts; };
extern "C" struct AG_results func_MAIN(sisal_array_t arcs, sisal_array_t grid,
                                       int32_t n, int32_t q);
#endif
#ifdef TEST_TRACEUTIL_DV
struct tu_maxr { int32_t val, job, seg; };
struct tu_segr { int32_t ecnt; tu_maxr mx; int32_t prio; bool fired, leaf; };
struct TU_results { sisal_array_t st, fin, d; tu_segr ns; };
extern "C" struct TU_results func_MAIN(sisal_array_t sorted, sisal_array_t vals,
                                       int32_t low, int32_t high, tu_segr seg,
                                       int32_t cnt, tu_maxr mx);
#endif
#ifdef TEST_ARRAY_EX_DV
extern "C" sisal_array_t func_MAIN();
#endif
#ifdef TEST_NICO_DV
extern "C" sisal_array_t func_MAIN(int32_t N);
#endif
#ifdef TEST_NICO2_DV
extern "C" sisal_array_t func_MAIN(int32_t N);
#endif
#ifdef TEST_TEST_BIN_DV
extern "C" int32_t func_MAIN(int32_t level);
#endif
#ifdef TEST_IF_COMPLEX_REVIEW_DV
struct ticr_rec { int32_t A; double B; };
struct FUNC_MAIN_results { int32_t res_0; sisal_array_t res_1; struct ticr_rec res_2; };
extern "C" struct FUNC_MAIN_results func_MAIN(int32_t selector, bool flag,
    int32_t outer_scalar, sisal_array_t outer_arr, struct ticr_rec outer_rec);
#endif
#ifdef TEST_TAGCASE_II_DV
struct FUNC_MAIN_results { int32_t res_0, res_1, res_2; };
extern "C" struct FUNC_MAIN_results func_MAIN(int32_t I, int32_t E);
#endif
#ifdef TEST_NESTED_DV
extern "C" int32_t func_OUTER(int32_t I);   // entry is Outer (no main); Outer(I)=Inner(I)=2I
#endif
#ifdef TEST_VECTEST_DV
struct FUNC_MAIN_results {
  sisal_array_t res_0, res_1, res_2, res_3, res_4, res_5;   // Tri/Sum x D/R/I
  int32_t res_6, res_7, res_8, res_9, res_10, res_11;        // min, amin x D/R/I
  int32_t res_12, res_13, res_14, res_15, res_16, res_17;    // max, amax x D/R/I
};
extern "C" struct FUNC_MAIN_results func_MAIN(int32_t n);
#endif
#ifdef TEST_LEGPOLY1_DV
extern "C" sisal_array_t func_LEGENDREPOLYOF1STKIND(int32_t IR, int32_t IRMAX2,
    int32_t JXXMX, float COAS, float SIAS, float DELTAS);
#endif
#ifdef TEST_INTRINSICS_TEST_DV
struct FUNC_ALLINTRINSICS_results { sisal_array_t res_0, res_1, res_2; };
extern "C" struct FUNC_ALLINTRINSICS_results func_ALLINTRINSICS(sisal_array_t A, sisal_array_t B, bool flag);
#endif
#ifdef TEST_TUPLE_HASH_TESTS_DV
struct FUNC_TUPLE_SWAP_results { int32_t res_0, res_1; };
struct FUNC_TUPLE_TYPED_results { int32_t res_0, res_1; };
extern "C" struct FUNC_TUPLE_SWAP_results func_TUPLE_SWAP(int32_t A, int32_t B);
extern "C" struct FUNC_TUPLE_TYPED_results func_TUPLE_TYPED(int32_t A, int32_t B);
extern "C" int32_t func_TUPLE_SUM3(int32_t A, int32_t B, int32_t C);
#endif
#ifdef TEST_TUPLE_KW_TESTS_DV
struct FUNC_TUPLE_KW_SWAP_results { int32_t res_0, res_1; };
struct FUNC_TUPLE_KW_TYPED_results { int32_t res_0, res_1; };
extern "C" struct FUNC_TUPLE_KW_SWAP_results func_TUPLE_KW_SWAP(int32_t A, int32_t B);
extern "C" struct FUNC_TUPLE_KW_TYPED_results func_TUPLE_KW_TYPED(int32_t A, int32_t B);
extern "C" int32_t func_TUPLE_KW_CHAIN(int32_t A, int32_t B, int32_t C);
#endif
#ifdef TEST_CPXCONV_DV
struct cc_rec { float REPART, IMPART; };
struct FUNC_COMPLEXING_CT_E_PT_ZTSP_results { sisal_array_t res_0, res_1, res_2, res_3; };
struct FUNC_DECOMPLEXING_P_ZDIFF_U_V_results { sisal_array_t res_0, res_1, res_2, res_3; };
extern "C" struct FUNC_COMPLEXING_CT_E_PT_ZTSP_results func_COMPLEXING_CT_E_PT_ZTSP(int32_t JXMX, sisal_array_t CT, sisal_array_t E, sisal_array_t PT, sisal_array_t ZT);
extern "C" struct FUNC_DECOMPLEXING_P_ZDIFF_U_V_results func_DECOMPLEXING_P_ZDIFF_U_V(int32_t JXMX, int32_t JXXMX, sisal_array_t P, sisal_array_t ZDIFF, sisal_array_t U, sisal_array_t V);
#endif
#ifdef TEST_BUILTIN_SCALAR_DV
extern "C" int32_t func_SCALAR_ABS_INT(int32_t); extern "C" float func_SCALAR_ABS_REAL(float); extern "C" double func_SCALAR_ABS_DOUBLE(double);
extern "C" int32_t func_SCALAR_MAX_INT(int32_t,int32_t); extern "C" float func_SCALAR_MAX_REAL(float,float);
extern "C" int32_t func_SCALAR_MIN_INT(int32_t,int32_t); extern "C" float func_SCALAR_MIN_REAL(float,float);
extern "C" int32_t func_SCALAR_MOD_INT(int32_t,int32_t);
extern "C" int32_t func_SCALAR_FLOOR_REAL(float); extern "C" int64_t func_SCALAR_FLOOR_DOUBLE(double);
extern "C" int32_t func_SCALAR_TRUNC_REAL(float); extern "C" int64_t func_SCALAR_TRUNC_DOUBLE(double);
extern "C" float func_SCALAR_EXP_REAL(float,int32_t); extern "C" double func_SCALAR_EXP_DOUBLE(double,int32_t);
#endif
#ifdef TEST_INTERPROC_PROVIDED_E2E
extern "C" sisal_array_t func_MAIN(int32_t N, int32_t Steps);
#endif
#ifdef TEST_STREAM_SIMPLE_DV
extern "C" sisal_generator<float> func_MAIN();
#endif
#ifdef TEST_STREAM_LOOP_DV
extern "C" sisal_generator<int32_t> func_MAIN(int32_t N);
#endif
#ifdef TEST_STREAM_SIEVE_DV
extern "C" sisal_generator<int32_t> func_MAIN(int32_t LIMIT);
#endif
#ifdef TEST_STREAM_INTEGERS_DV
extern "C" sisal_generator<int32_t> func_MAIN(int32_t LIMIT);
#endif
#ifdef TEST_STREAM_SIEVE_V2_DV
extern "C" sisal_generator<int32_t> func_MAIN(int32_t LIMIT);
#endif
#ifdef TEST_STREAM_UPRIME2_DV
extern "C" sisal_generator<int32_t> func_MAIN(int32_t LIMIT);
#endif
#ifdef TEST_CPXFUNCS_DV
struct cfx { float re, im; };  // ABI-matches struct_rec_<N> {float RE; float IM;}
extern "C" struct cfx func_CADD(struct cfx a, struct cfx b);
extern "C" struct cfx func_CSUB(struct cfx a, struct cfx b);
extern "C" struct cfx func_CMUL(struct cfx a, struct cfx b);
extern "C" struct cfx func_CDIV(struct cfx a, struct cfx b);
extern "C" struct cfx func_CONJG(struct cfx a);
extern "C" struct cfx func_CNEG(struct cfx a);
extern "C" float func_CABS(struct cfx a);
extern "C" float func_CABSSQR(struct cfx a);
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

#ifdef TEST_KIN16_DV
struct kin16_edit_rec {
  double T;
  double YMEANM;
  double SIGSQM;
  double SIGM;
  double SUM1M;
  double YMEANM2;
  double SIGSQM2;
  double SIGM2;
  double SUM1M2;
  double DIFM;
  double VELOCITYM;
  double DIFM2;
  double VELOCITYM2;
};
struct FUNC_MAIN_results {
  struct kin16_edit_rec res_0;
  struct kin16_edit_rec res_1;
};
extern "C" struct FUNC_MAIN_results func_MAIN(int32_t IT, int32_t N, int32_t NSEG);
extern "C" double func_SQRT(double x) {
  return sqrt(x);
}
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
extern "C" sisal_array_t func_FI_GATHER_ZERO (int32_t N);
extern "C" sisal_array_t func_FI_GATHER_BODY_TEMP (int32_t N);
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
#ifdef TEST_BUBBLE_E2E
extern "C" sisal_array_t func_BUBBLE (int32_t N, sisal_array_t AIN);
#endif
#ifdef TEST_LEGPOLY_DV_E2E
extern "C" sisal_array_t func_LEGENDREPOLYOF1STKIND (int32_t IR, int32_t IRMAX2, int32_t JXXMX, float COAS, float SIAS, float DELTAS);
#endif
#ifdef TEST_NESTED_INIT_MERGE_DV
extern "C" sisal_array_t func_MAIN (int32_t n, sisal_array_t X);
#endif
#ifdef TEST_MUTUAL_BUG_E2E
extern "C" int32_t func_SWAP_BUG (int32_t n);
#endif
#ifdef TEST_LU_NPIV_DV
extern "C" sisal_array_t func_MAIN (int32_t n, sisal_array_t Ain, sisal_array_t Bin);
#endif
#ifdef TEST_LU_PIV_DV
extern "C" sisal_array_t func_MAIN (int32_t n, sisal_array_t Ain, sisal_array_t Bin);
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
#ifdef TEST_MULTIBIND_DV
struct FUNC_MAIN_results {
  sisal_array_t res_0;
  sisal_array_t res_1;
};
extern "C" struct FUNC_MAIN_results func_MAIN(int32_t N);
#endif
#ifdef TEST_TAG_DISPATCH_DV
struct FUNC_MAIN_results {   // Pick(ua,ub), Pick(ua,ua), Pick(ub,ua), Pick(ub,ub)
  int32_t res_0;
  int32_t res_1;
  int32_t res_2;
  int32_t res_3;
};
extern "C" struct FUNC_MAIN_results func_MAIN(int32_t S);
#endif
#ifdef TEST_SIMPSON
extern "C" float func_SIMPSON(float A, float B, int32_t N);
#endif
#ifdef TEST_MINMAX_DV
struct FUNC_MAIN_results {   // imin, iamin, imax, iamax (1-based indices)
  int32_t res_0;
  int32_t res_1;
  int32_t res_2;
  int32_t res_3;
};
extern "C" struct FUNC_MAIN_results func_MAIN(int32_t N, sisal_array_t X);
#endif
#ifdef TEST_INSERTION1_DV
extern "C" sisal_array_t func_MAIN(sisal_array_t INPUT);
#endif
#ifdef TEST_MESORT_DV
extern "C" sisal_array_t func_MAIN(sisal_array_t X);
#endif
#ifdef TEST_FOR_ALL_ARGMAX
extern "C" int32_t func_MAIN(int32_t X);
#endif
#ifdef TEST_TUPLE_MIXED3
struct FUNC_TUPLEMIXED_results {
  int32_t res_0;
  float res_1;
};
extern "C" struct FUNC_TUPLEMIXED_results func_TUPLEMIXED(int32_t X);
#endif
#ifdef TEST_RECORD1
struct struct_rec_96 { float R; };
struct struct_rec_98 { struct struct_rec_96 L; float S; };
extern "C" struct struct_rec_98 func_MAIN(void);
#endif
#ifdef TEST_UNION1
extern "C" float func_MAIN(float X, float EPS);
#endif
#ifdef TEST_TUPLE_MIXED2
struct FUNC_TUPLEMIXED_results {
  int32_t res_0;
  float res_1;
};
extern "C" struct FUNC_TUPLEMIXED_results func_TUPLEMIXED(void);
#endif
#ifdef TEST_UNION0
struct FUNC_MAIN_results { bool res_0; bool res_1; bool res_2; };
extern "C" struct FUNC_MAIN_results func_MAIN(int32_t X, float Y, sisal_array_t Z);
#endif
#ifdef TEST_TUPLE_ADD_DV
extern "C" sisal_array_t func_TUPLE_ADD(sisal_array_t A, sisal_array_t B);
#endif
#ifdef TEST_IDIV
extern "C" int32_t func_IDIV(int32_t A, int32_t B);
#endif
#ifdef TEST_FORALL_SIMPLE_DV
extern "C" sisal_array_t func_MAIN(sisal_array_t A);
#endif
#ifdef TEST_FORALL_DOT_DV
extern "C" int32_t func_MAIN(sisal_array_t A, sisal_array_t B);
#endif
#ifdef TEST_TUPLE_MIXED
struct FUNC_TUPLEMIXED_results { int32_t res_0; float res_1; };
extern "C" struct FUNC_TUPLEMIXED_results func_TUPLEMIXED(void);
#endif
#ifdef TEST_RECORD2
struct struct_rec_96 { int32_t A; int32_t B; };
extern "C" int32_t func_TEST(struct struct_rec_96 R);
#endif
#ifdef TEST_RECORD1_REORDER
struct struct_rec_95r { float R; };
struct struct_rec_98r { float S; struct struct_rec_95r L; };
extern "C" struct struct_rec_98r func_MAIN(void);
#endif
#ifdef TEST_RECORD_REPLACE_E2E
struct cart_rec { float X; float Y; };
extern "C" struct cart_rec func_MAIN(void);
#endif
#ifdef TEST_PARPI1
extern "C" float func_MAIN(int32_t CYCLES);
#endif
#ifdef TEST_FORALL_CROSS_DV
extern "C" sisal_array_t func_MAIN(sisal_array_t A, sisal_array_t B);
#endif
#ifdef TEST_FORALL_SHAPED_GATHER_DV
extern "C" sisal_array_t func_MAIN(int32_t n, int32_t m);
#endif
#ifdef TEST_FOR_INITIAL_SIMPLE
extern "C" int32_t func_MAIN(int32_t N);
#endif
#ifdef TEST_PARPI2
extern "C" float func_MAIN(int32_t CYCLES);
#endif
#ifdef TEST_PARPI_BABB
extern "C" float func_MAIN(int32_t N);
#endif
#ifdef TEST_FOR_INITIAL_LOOPA
extern "C" int32_t func_MAIN(int32_t N);
#endif
#ifdef TEST_LOOPAT2_DV
extern "C" sisal_array_t func_MAIN(int32_t N, sisal_array_t Y);
#endif
#ifdef TEST_TST_LOOP2_DV
extern "C" double func_MAIN(sisal_array_t Y);
#endif
#ifdef TEST_FOR_ALL_REDUCE
extern "C" int32_t func_MAIN(int32_t X);
#endif
#ifdef TEST_SIMPLEBATCHER_DV
extern "C" sisal_array_t func_MAIN(sisal_array_t K);
#endif
#ifdef TEST_SEQBATCHER_DV
extern "C" sisal_array_t func_MAIN(sisal_array_t K);
#endif
#ifdef TEST_BATCHER_DV
extern "C" sisal_array_t func_MAIN(sisal_array_t K);
#endif
#ifdef TEST_ANGMOM_DV
struct ANGMOM_results { float atot, atot_1, wtot, total, total1; };
extern "C" ANGMOM_results func_MAIN(int32_t jx, int32_t jxmx, float zmean, float asq, float ww,
                                    sisal_array_t u, sisal_array_t h, sisal_array_t zm, sisal_array_t z);
#endif
#ifdef TEST_VSPHERE_DV
struct VSPHERE_results { sisal_array_t eg, pug, pvg, zug, zvg; };
extern "C" VSPHERE_results func_MAIN(int32_t lon_end, int32_t ilath,
    sisal_array_t pg, sisal_array_t zg, sisal_array_t ug, sisal_array_t vg);
#endif
#ifdef TEST_ENERGY_DV
struct ENERGY_results { float ptot, ktot, total; };
extern "C" ENERGY_results func_MAIN(int32_t jx, int32_t jxmx, float zmean, float asq,
    sisal_array_t e, sisal_array_t h, sisal_array_t zm);
#endif
#ifdef TEST_SPECAM_DV
struct SPECAM_results { sisal_array_t ampk, ampvor, ampz; };
extern "C" SPECAM_results func_MAIN(int32_t jx, int32_t mx, sisal_array_t kmjx,
    float asq, float ww, float grav,
    sisal_array_t c, sisal_array_t p, sisal_array_t z);
#endif
#ifdef TEST_SAS_DV
extern "C" sisal_array_t func_MAIN(int32_t ir, int32_t irmax2, int32_t jxxmx, int32_t ilath, sisal_array_t alp);
#endif
#ifdef TEST_NOISE_DV
extern "C" sisal_array_t func_MAIN(sisal_array_t M, int32_t rows, int32_t cols);
#endif
#ifdef TEST_TST_LOOPX_DV
struct LOOPX_results { sisal_array_t a, b; };
extern "C" LOOPX_results func_MAIN(int32_t n, int32_t m, sisal_array_t Y, sisal_array_t W, sisal_array_t U);
#endif
#ifdef TEST_TST_LOOPX2_DV
struct LOOPX2_results { sisal_array_t a, b; };
extern "C" LOOPX2_results func_MAIN(int32_t n, int32_t m, sisal_array_t Y);
#endif
#ifdef TEST_INSERTION2_DV
extern "C" sisal_array_t func_MAIN(int32_t N, sisal_array_t Input);
#endif
#ifdef TEST_INSERT_DV
extern "C" sisal_array_t func_MAIN(int32_t N, sisal_array_t Input);
#endif
#ifdef TEST_TST_LOOPAT1_DV
extern "C" sisal_array_t func_MAIN(sisal_array_t Y, int32_t which);
#endif
#ifdef TEST_ADA
extern "C" sisal_array_t func_MAIN(void);
#endif
#ifdef TEST_COMPLEX_TYPES_E2E
struct ct_cfl { float re, im; };
struct ct_soa { sisal_array_t re, im; };
extern "C" ct_cfl func_T_MAKE_CFLOAT(float R, float I);
extern "C" float func_T_RE(ct_cfl C);
extern "C" float func_T_IM(ct_cfl C);
extern "C" ct_soa func_T_SOA_FLOAT(sisal_array_t RE, sisal_array_t IM);
extern "C" sisal_array_t func_T_AOS_FLOAT(sisal_array_t RE, sisal_array_t IM);
#endif
#ifdef TEST_VERIFY_NUMPY_BROADCAST
extern "C" sisal_array_t func_TEST_TRAILING(sisal_array_t A, sisal_array_t B);
extern "C" sisal_array_t func_TEST_UNIT_EXPANSION(sisal_array_t A, sisal_array_t B);
extern "C" sisal_array_t func_TEST_SCALAR_BROADCAST(double S, sisal_array_t M);
extern "C" sisal_array_t func_TEST_MULTI_OP(sisal_array_t A, sisal_array_t B);
#endif
#ifdef TEST_FREQ_DV
struct FREQ_results { sisal_array_t ctri, eri, ptri, ztri; };
extern "C" FREQ_results func_MAIN(int32_t jx, int32_t mx, int32_t mx2, int32_t ilath, int32_t iy,
    sisal_array_t kmjx, sisal_array_t kmjxx, sisal_array_t wocs, sisal_array_t epsi,
    sisal_array_t alp,
    sisal_array_t ef, sisal_array_t puf, sisal_array_t pvf, sisal_array_t zuf, sisal_array_t zvf);
#endif
#ifdef TEST_TSTEP_DV
struct TSTEP_results { int32_t ifirst_r; sisal_array_t c,p,z,cm,pm,zm,ct,pt,zt; };
extern "C" TSTEP_results func_MAIN(int32_t jx, int32_t mx, int32_t delt, int32_t izon, int32_t ifirst,
    int32_t imp, int32_t istart,
    float hdiff, float hdrag, float zmean, float vnu,
    sisal_array_t kmjx, sisal_array_t kmjxx, sisal_array_t ksq, sisal_array_t p1,
    sisal_array_t c, sisal_array_t p, sisal_array_t z,
    sisal_array_t cm, sisal_array_t pm, sisal_array_t zm,
    sisal_array_t ct, sisal_array_t pt, sisal_array_t zt);
#endif
#ifdef TEST_PINSERT_DV
extern "C" sisal_array_t func_MAIN(int32_t m, int32_t n, sisal_array_t A);
#endif
#ifdef TEST_ALPHABETA_DV
struct AB_results { sisal_array_t ab, del; };
extern "C" AB_results func_MAIN(sisal_array_t Sorted, int32_t Q);
#endif
#ifdef TEST_SIFUNCS
extern "C" float func_ASINR(float x);
extern "C" float func_ACOSR(float x);
extern "C" float func_SQRTR(float x);
extern "C" float func_SINR(float x);
extern "C" float func_COSR(float x);
extern "C" float func_ATANR(float x);
#endif
#ifdef TEST_TUPLE_DESTRUCTURE
struct TUD_pair { int32_t a, b; };
extern "C" TUD_pair func_TUPLE_SWAP(int32_t A, int32_t B);
extern "C" TUD_pair func_TUPLE_TYPED(int32_t A, int32_t B);
extern "C" int32_t func_TUPLE_SUM3(int32_t A, int32_t B, int32_t C);
extern "C" TUD_pair func_TUPLE_KW_SWAP(int32_t A, int32_t B);
extern "C" TUD_pair func_TUPLE_KW_TYPED(int32_t A, int32_t B);
extern "C" int32_t func_TUPLE_KW_CHAIN(int32_t A, int32_t B, int32_t C);
#endif
#ifdef TEST_SPEC_DV
struct SPEC_results { sisal_array_t pg, zg, ug, vg; };
extern "C" SPEC_results func_MAIN(int32_t jx, int32_t mx, int32_t jxx, int32_t ilath, int32_t ixh,
    sisal_array_t kmjx, sisal_array_t kmjxx, sisal_array_t alp,
    sisal_array_t pri, sisal_array_t zri, sisal_array_t uri, sisal_array_t vri);
#endif
#ifdef TEST_UVSPEC_DV
struct UVSPEC_results { sisal_array_t u, v; };
extern "C" UVSPEC_results func_MAIN(int32_t mx, int32_t jx, int32_t jxx,
    sisal_array_t epsi, sisal_array_t p, sisal_array_t c);
#endif
#ifdef TEST_LINEAR_DV
struct LINEAR_results { sisal_array_t pt, ct; };
extern "C" LINEAR_results func_MAIN(int32_t mx, int32_t jx,
    sisal_array_t kmjx, sisal_array_t kmjxx, sisal_array_t ksq,
    float tw, sisal_array_t epsi,
    sisal_array_t c, sisal_array_t p, sisal_array_t u, sisal_array_t v,
    sisal_array_t ctin, sisal_array_t e, sisal_array_t ptin);
#endif
#ifdef TEST_LIFE2_DV
extern "C" sisal_array_t func_MAIN(int32_t Num, int32_t Rows, int32_t Columns, sisal_array_t G);
#endif
#ifdef TEST_RICARD_DV
struct FUNC_MAIN_results {   // ricard chromatography: VOL, CTM, CTL, 7 totals, JSTOR, STOR, PERCENT, HL
  double res_0;
  sisal_array_t res_1;
  sisal_array_t res_2;
  double res_3;
  double res_4;
  double res_5;
  double res_6;
  double res_7;
  double res_8;
  double res_9;
  int32_t res_10;
  double res_11;
  double res_12;
  double res_13;
};
extern "C" struct FUNC_MAIN_results func_MAIN();
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
make_nested_double_2d (const double *data, int rows, int cols)
{
  sisal_array_t A = sisal_array_alloc_empty (1, 94, (uint64_t)rows);
  A.dims[0] = rows;
  for (int i = 0; i < rows; i++)
    {
      sisal_array_t row = sisal_array_alloc_empty (1, 4, (uint64_t)cols);
      row.dims[0] = cols;
      memcpy (row.data, data + i * cols, (size_t)cols * sizeof (double));
      ((sisal_array_t*)A.data)[i] = row;
    }
  return A;
}

static void
free_nested_double_2d (sisal_array_t A)
{
  for (int i = 0; i < A.size; i++)
    {
      sisal_array_t row = ((sisal_array_t*)A.data)[i];
      if (row.data) free (row.data);
    }
  if (A.data) free (A.data);
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

#ifdef TEST_BASIC_DV
struct FUNC_MAIN_results {
  sisal_array_t res_0;
  sisal_array_t res_1;
  sisal_array_t res_2;
  sisal_array_t res_3;
  sisal_array_t res_4;
  sisal_array_t res_5;
  sisal_array_t res_6;
  sisal_array_t res_7;
  sisal_array_t res_8;
  sisal_array_t res_9;
  sisal_array_t res_10;
  sisal_array_t res_11;
  sisal_array_t res_12;
  sisal_array_t res_13;
  sisal_array_t res_14;
  sisal_array_t res_15;
  sisal_array_t res_16;
  sisal_array_t res_17;
  sisal_array_t res_18;
  sisal_array_t res_19;
  sisal_array_t res_20;
  sisal_array_t res_21;
  sisal_array_t res_22;
  sisal_array_t res_23;
  sisal_array_t res_24;
  sisal_array_t res_25;
  sisal_array_t res_26;
  sisal_array_t res_27;
  sisal_array_t res_28;
  sisal_array_t res_29;
  sisal_array_t res_30;
  sisal_array_t res_31;
  sisal_array_t res_32;
  sisal_array_t res_33;
  sisal_array_t res_34;
  sisal_array_t res_35;
  sisal_array_t res_36;
  sisal_array_t res_37;
  sisal_array_t res_38;
  sisal_array_t res_39;
  sisal_array_t res_40;
  sisal_array_t res_41;
  sisal_array_t res_42;
  sisal_array_t res_43;
  sisal_array_t res_44;
  sisal_array_t res_45;
  sisal_array_t res_46;
  sisal_array_t res_47;
  sisal_array_t res_48;
  int32_t res_49;
  sisal_array_t res_50;
  sisal_array_t res_51;
  int32_t res_52;
  int32_t res_53;
  int32_t res_54;
  sisal_array_t res_55;
  sisal_array_t res_56;
  sisal_array_t res_57;
  sisal_array_t res_58;
  sisal_array_t res_59;
  sisal_array_t res_60;
  sisal_array_t res_61;
  sisal_array_t res_62;
  sisal_array_t res_63;
  sisal_array_t res_64;
  sisal_array_t res_65;
  sisal_array_t res_66;
  int32_t res_67;
};

extern "C" struct FUNC_MAIN_results func_MAIN(
  sisal_array_t A, sisal_array_t B, sisal_array_t C, sisal_array_t D, 
  sisal_array_t E, sisal_array_t F, sisal_array_t H, sisal_array_t I, 
  sisal_array_t M, sisal_array_t N, sisal_array_t V, sisal_array_t W, 
  sisal_array_t X, int32_t PASS
);

static void
test_basic_dv (void)
{
  printf ("\n=== Group: basic_dv ===\n");

  bool a_data[] = { true, false, true, false };
  bool b_data[] = { true, true, false, false };
  sisal_array_t a = make_bool_arr(a_data, 4);
  sisal_array_t b = make_bool_arr(b_data, 4);

  int32_t c_data[] = { 10, -20, 30, 40 };
  int32_t d_data[] = { 3, 4, -5, 6 };
  sisal_array_t c = make_int_arr(c_data, 4);
  sisal_array_t d = make_int_arr(d_data, 4);

  float e_data[] = { 1.5f, -2.5f, 3.5f, 4.5f };
  float f_data[] = { 0.5f, 2.0f, -1.0f, 1.5f };
  sisal_array_t e = make_float_arr(e_data, 4);
  sisal_array_t f = make_float_arr(f_data, 4);

  double h_data[] = { 1.5, -2.5, 3.5, 4.5 };
  double i_data[] = { 0.5, 2.0, -1.0, 1.5 };
  sisal_array_t h = make_double_arr(h_data, 4);
  sisal_array_t i = make_double_arr(i_data, 4);

  int32_t m_data[] = { 100, 200, 300 };
  int32_t n_data[] = { 400, 500 };
  sisal_array_t m = make_int_arr(m_data, 3);
  sisal_array_t n = make_int_arr(n_data, 2);

  float v_data[] = { 1.2f, -2.7f, 3.5f };
  sisal_array_t v = make_float_arr(v_data, 3);

  double w_data[] = { 1.2, -2.7, 3.5 };
  sisal_array_t w = make_double_arr(w_data, 3);

  int32_t x_data[] = { 10, -20, 30 };
  sisal_array_t x = make_int_arr(x_data, 3);

  struct FUNC_MAIN_results res = func_MAIN(a, b, c, d, e, f, h, i, m, n, v, w, x, 777);

  if (a.data) free(a.data); if (b.data) free(b.data);
  if (c.data) free(c.data); if (d.data) free(d.data);
  if (e.data) free(e.data); if (f.data) free(f.data);
  if (h.data) free(h.data); if (i.data) free(i.data);
  if (m.data) free(m.data); if (n.data) free(n.data);
  if (v.data) free(v.data); if (w.data) free(w.data);
  if (x.data) free(x.data);

  check("basic_dv_res_0_size", res.res_0.size == 4);
  check("basic_dv_res_0", ab(res.res_0, 0) == true && ab(res.res_0, 1) == false && ab(res.res_0, 2) == false && ab(res.res_0, 3) == false);
  check("basic_dv_res_1", ab(res.res_1, 0) == true && ab(res.res_1, 1) == true && ab(res.res_1, 2) == true && ab(res.res_1, 3) == false);
  check("basic_dv_res_2", ab(res.res_2, 0) == false && ab(res.res_2, 1) == true && ab(res.res_2, 2) == false && ab(res.res_2, 3) == true);
  check("basic_dv_res_3", ab(res.res_3, 0) == true && ab(res.res_3, 1) == false && ab(res.res_3, 2) == false && ab(res.res_3, 3) == true);
  check("basic_dv_res_4", ab(res.res_4, 0) == false && ab(res.res_4, 1) == true && ab(res.res_4, 2) == true && ab(res.res_4, 3) == false);

  check("basic_dv_res_5", ai(res.res_5, 0) == 13 && ai(res.res_5, 1) == -16 && ai(res.res_5, 2) == 25 && ai(res.res_5, 3) == 46);
  check("basic_dv_res_6", ai(res.res_6, 0) == 7 && ai(res.res_6, 1) == -24 && ai(res.res_6, 2) == 35 && ai(res.res_6, 3) == 34);
  check("basic_dv_res_7", ai(res.res_7, 0) == 30 && ai(res.res_7, 1) == -80 && ai(res.res_7, 2) == -150 && ai(res.res_7, 3) == 240);
  check("basic_dv_res_8", ai(res.res_8, 0) == 3 && ai(res.res_8, 1) == -5 && ai(res.res_8, 2) == -6 && ai(res.res_8, 3) == 6);
  check("basic_dv_res_9", ai(res.res_9, 0) == 1 && ai(res.res_9, 1) == 0 && ai(res.res_9, 2) == 0 && ai(res.res_9, 3) == 4);
  check("basic_dv_res_10", ai(res.res_10, 0) == -10 && ai(res.res_10, 1) == 20 && ai(res.res_10, 2) == -30 && ai(res.res_10, 3) == -40);
  check("basic_dv_res_11", ai(res.res_11, 0) == 10 && ai(res.res_11, 1) == 20 && ai(res.res_11, 2) == 30 && ai(res.res_11, 3) == 40);
  check("basic_dv_res_12", ai(res.res_12, 0) == 10 && ai(res.res_12, 1) == 4 && ai(res.res_12, 2) == 30 && ai(res.res_12, 3) == 40);
  check("basic_dv_res_13", ai(res.res_13, 0) == 3 && ai(res.res_13, 1) == -20 && ai(res.res_13, 2) == -5 && ai(res.res_13, 3) == 6);
  check("basic_dv_res_14", ab(res.res_14, 0) == false && ab(res.res_14, 1) == false && ab(res.res_14, 2) == false && ab(res.res_14, 3) == false);
  check("basic_dv_res_15", ab(res.res_15, 0) == true && ab(res.res_15, 1) == true && ab(res.res_15, 2) == true && ab(res.res_15, 3) == true);
  check("basic_dv_res_16", ab(res.res_16, 0) == true && ab(res.res_16, 1) == false && ab(res.res_16, 2) == true && ab(res.res_16, 3) == true);
  check("basic_dv_res_17", ab(res.res_17, 0) == false && ab(res.res_17, 1) == true && ab(res.res_17, 2) == false && ab(res.res_17, 3) == false);
  check("basic_dv_res_18", ab(res.res_18, 0) == true && ab(res.res_18, 1) == false && ab(res.res_18, 2) == true && ab(res.res_18, 3) == true);
  check("basic_dv_res_19", ab(res.res_19, 0) == false && ab(res.res_19, 1) == true && ab(res.res_19, 2) == false && ab(res.res_19, 3) == false);

  check("basic_dv_res_20", near_f(af(res.res_20, 0), 2.0f) && near_f(af(res.res_20, 1), -0.5f) && near_f(af(res.res_20, 2), 2.5f) && near_f(af(res.res_20, 3), 6.0f));
  check("basic_dv_res_21", near_f(af(res.res_21, 0), 1.0f) && near_f(af(res.res_21, 1), -4.5f) && near_f(af(res.res_21, 2), 4.5f) && near_f(af(res.res_21, 3), 3.0f));
  check("basic_dv_res_22", near_f(af(res.res_22, 0), 0.75f) && near_f(af(res.res_22, 1), -5.0f) && near_f(af(res.res_22, 2), -3.5f) && near_f(af(res.res_22, 3), 6.75f));
  check("basic_dv_res_23", near_f(af(res.res_23, 0), 3.0f) && near_f(af(res.res_23, 1), -1.25f) && near_f(af(res.res_23, 2), -3.5f) && near_f(af(res.res_23, 3), 3.0f));
  check("basic_dv_res_24", near_f(af(res.res_24, 0), -1.5f) && near_f(af(res.res_24, 1), 2.5f) && near_f(af(res.res_24, 2), -3.5f) && near_f(af(res.res_24, 3), -4.5f));
  check("basic_dv_res_25", near_f(af(res.res_25, 0), 1.5f) && near_f(af(res.res_25, 1), 2.5f) && near_f(af(res.res_25, 2), 3.5f) && near_f(af(res.res_25, 3), 4.5f));
  check("basic_dv_res_26", near_f(af(res.res_26, 0), 1.5f) && near_f(af(res.res_26, 1), 2.0f) && near_f(af(res.res_26, 2), 3.5f) && near_f(af(res.res_26, 3), 4.5f));
  check("basic_dv_res_27", near_f(af(res.res_27, 0), 0.5f) && near_f(af(res.res_27, 1), -2.5f) && near_f(af(res.res_27, 2), -1.0f) && near_f(af(res.res_27, 3), 1.5f));
  check("basic_dv_res_28", ab(res.res_28, 0) == false && ab(res.res_28, 1) == false && ab(res.res_28, 2) == false && ab(res.res_28, 3) == false);
  check("basic_dv_res_29", ab(res.res_29, 0) == true && ab(res.res_29, 1) == true && ab(res.res_29, 2) == true && ab(res.res_29, 3) == true);
  check("basic_dv_res_30", ab(res.res_30, 0) == true && ab(res.res_30, 1) == false && ab(res.res_30, 2) == true && ab(res.res_30, 3) == true);
  check("basic_dv_res_31", ab(res.res_31, 0) == false && ab(res.res_31, 1) == true && ab(res.res_31, 2) == false && ab(res.res_31, 3) == false);
  check("basic_dv_res_32", ab(res.res_32, 0) == true && ab(res.res_32, 1) == false && ab(res.res_32, 2) == true && ab(res.res_32, 3) == true);
  check("basic_dv_res_33", ab(res.res_33, 0) == false && ab(res.res_33, 1) == true && ab(res.res_33, 2) == false && ab(res.res_33, 3) == false);

  check("basic_dv_res_34", near_d(ad(res.res_34, 0), 2.0) && near_d(ad(res.res_34, 1), -0.5) && near_d(ad(res.res_34, 2), 2.5) && near_d(ad(res.res_34, 3), 6.0));
  check("basic_dv_res_35", near_d(ad(res.res_35, 0), 1.0) && near_d(ad(res.res_35, 1), -4.5) && near_d(ad(res.res_35, 2), 4.5) && near_d(ad(res.res_35, 3), 3.0));
  check("basic_dv_res_36", near_d(ad(res.res_36, 0), 0.75) && near_d(ad(res.res_36, 1), -5.0) && near_d(ad(res.res_36, 2), -3.5) && near_d(ad(res.res_36, 3), 6.75));
  check("basic_dv_res_37", near_d(ad(res.res_37, 0), 3.0) && near_d(ad(res.res_37, 1), -1.25) && near_d(ad(res.res_37, 2), -3.5) && near_d(ad(res.res_37, 3), 3.0));
  check("basic_dv_res_38", near_d(ad(res.res_38, 0), -1.5) && near_d(ad(res.res_38, 1), 2.5) && near_d(ad(res.res_38, 2), -3.5) && near_d(ad(res.res_38, 3), -4.5));
  check("basic_dv_res_39", near_d(ad(res.res_39, 0), 1.5) && near_d(ad(res.res_39, 1), 2.5) && near_d(ad(res.res_39, 2), 3.5) && near_d(ad(res.res_39, 3), 4.5));
  check("basic_dv_res_40", near_d(ad(res.res_40, 0), 1.5) && near_d(ad(res.res_40, 1), 2.0) && near_d(ad(res.res_40, 2), 3.5) && near_d(ad(res.res_40, 3), 4.5));
  check("basic_dv_res_41", near_d(ad(res.res_41, 0), 0.5) && near_d(ad(res.res_41, 1), -2.5) && near_d(ad(res.res_41, 2), -1.0) && near_d(ad(res.res_41, 3), 1.5));
  check("basic_dv_res_42", ab(res.res_42, 0) == false && ab(res.res_42, 1) == false && ab(res.res_42, 2) == false && ab(res.res_42, 3) == false);
  check("basic_dv_res_43", ab(res.res_43, 0) == true && ab(res.res_43, 1) == true && ab(res.res_43, 2) == true && ab(res.res_43, 3) == true);
  check("basic_dv_res_44", ab(res.res_44, 0) == true && ab(res.res_44, 1) == false && ab(res.res_44, 2) == true && ab(res.res_44, 3) == true);
  check("basic_dv_res_45", ab(res.res_45, 0) == false && ab(res.res_45, 1) == true && ab(res.res_45, 2) == false && ab(res.res_45, 3) == false);
  check("basic_dv_res_46", ab(res.res_46, 0) == true && ab(res.res_46, 1) == false && ab(res.res_46, 2) == true && ab(res.res_46, 3) == true);
  check("basic_dv_res_47", ab(res.res_47, 0) == false && ab(res.res_47, 1) == true && ab(res.res_47, 2) == false && ab(res.res_47, 3) == false);

  check("basic_dv_res_48", res.res_48.size == 3 && ai(res.res_48, 0) == 0 && ai(res.res_48, 1) == 0 && ai(res.res_48, 2) == 0);
  check("basic_dv_res_49", res.res_49 == 100);
  check("basic_dv_res_50", res.res_50.size == 3 && ai(res.res_50, 0) == 999 && ai(res.res_50, 1) == 200 && ai(res.res_50, 2) == 300);
  check("basic_dv_res_51", res.res_51.size == 5 && ai(res.res_51, 0) == 100 && ai(res.res_51, 1) == 200 && ai(res.res_51, 2) == 300 && ai(res.res_51, 3) == 400 && ai(res.res_51, 4) == 500);
  check("basic_dv_res_52", res.res_52 == 3);
  check("basic_dv_res_53", res.res_53 == 1);
  check("basic_dv_res_54", res.res_54 == 3);
  check("basic_dv_res_55", res.res_55.size == 4 && ai(res.res_55, 0) == 100 && ai(res.res_55, 1) == 200 && ai(res.res_55, 2) == 300 && ai(res.res_55, 3) == 42);
  check("basic_dv_res_56", res.res_56.size == 4 && ai(res.res_56, 0) == 42 && ai(res.res_56, 1) == 100 && ai(res.res_56, 2) == 200 && ai(res.res_56, 3) == 300);
  check("basic_dv_res_57", res.res_57.size == 2 && ai(res.res_57, 0) == 100 && ai(res.res_57, 1) == 200);
  check("basic_dv_res_58", res.res_58.size == 2 && ai(res.res_58, 0) == 200 && ai(res.res_58, 1) == 300);

  check("basic_dv_res_59", res.res_59.size == 3 && ai(res.res_59, 0) == 1 && ai(res.res_59, 1) == -3 && ai(res.res_59, 2) == 3);
  check("basic_dv_res_60", res.res_60.size == 3 && ai(res.res_60, 0) == 1 && ai(res.res_60, 1) == -2 && ai(res.res_60, 2) == 3);
  check("basic_dv_res_61", res.res_61.size == 3 && ai(res.res_61, 0) == 1 && ai(res.res_61, 1) == -2 && ai(res.res_61, 2) == 3);
  check("basic_dv_res_62", res.res_62.size == 3 && ai(res.res_62, 0) == 1 && ai(res.res_62, 1) == -3 && ai(res.res_62, 2) == 3);
  check("basic_dv_res_63", res.res_63.size == 3 && ai(res.res_63, 0) == 1 && ai(res.res_63, 1) == -2 && ai(res.res_63, 2) == 3);
  check("basic_dv_res_64", res.res_64.size == 3 && ai(res.res_64, 0) == 1 && ai(res.res_64, 1) == -2 && ai(res.res_64, 2) == 3);
  check("basic_dv_res_65", res.res_65.size == 3 && near_f(af(res.res_65, 0), 10.0f) && near_f(af(res.res_65, 1), -20.0f) && near_f(af(res.res_65, 2), 30.0f));
  check("basic_dv_res_66", res.res_66.size == 3 && near_d(ad(res.res_66, 0), 10.0) && near_d(ad(res.res_66, 1), -20.0) && near_d(ad(res.res_66, 2), 30.0));

  check("basic_dv_res_67", res.res_67 == 777);

  if (res.res_0.data) free(res.res_0.data); if (res.res_1.data) free(res.res_1.data);
  if (res.res_2.data) free(res.res_2.data); if (res.res_3.data) free(res.res_3.data);
  if (res.res_4.data) free(res.res_4.data); if (res.res_5.data) free(res.res_5.data);
  if (res.res_6.data) free(res.res_6.data); if (res.res_7.data) free(res.res_7.data);
  if (res.res_8.data) free(res.res_8.data); if (res.res_9.data) free(res.res_9.data);
  if (res.res_10.data) free(res.res_10.data); if (res.res_11.data) free(res.res_11.data);
  if (res.res_12.data) free(res.res_12.data); if (res.res_13.data) free(res.res_13.data);
  if (res.res_14.data) free(res.res_14.data); if (res.res_15.data) free(res.res_15.data);
  if (res.res_16.data) free(res.res_16.data); if (res.res_17.data) free(res.res_17.data);
  if (res.res_18.data) free(res.res_18.data); if (res.res_19.data) free(res.res_19.data);
  if (res.res_20.data) free(res.res_20.data); if (res.res_21.data) free(res.res_21.data);
  if (res.res_22.data) free(res.res_22.data); if (res.res_23.data) free(res.res_23.data);
  if (res.res_24.data) free(res.res_24.data); if (res.res_25.data) free(res.res_25.data);
  if (res.res_26.data) free(res.res_26.data); if (res.res_27.data) free(res.res_27.data);
  if (res.res_28.data) free(res.res_28.data); if (res.res_29.data) free(res.res_29.data);
  if (res.res_30.data) free(res.res_30.data); if (res.res_31.data) free(res.res_31.data);
  if (res.res_32.data) free(res.res_32.data); if (res.res_33.data) free(res.res_33.data);
  if (res.res_34.data) free(res.res_34.data); if (res.res_35.data) free(res.res_35.data);
  if (res.res_36.data) free(res.res_36.data); if (res.res_37.data) free(res.res_37.data);
  if (res.res_38.data) free(res.res_38.data); if (res.res_39.data) free(res.res_39.data);
  if (res.res_40.data) free(res.res_40.data); if (res.res_41.data) free(res.res_41.data);
  if (res.res_42.data) free(res.res_42.data); if (res.res_43.data) free(res.res_43.data);
  if (res.res_44.data) free(res.res_44.data); if (res.res_45.data) free(res.res_45.data);
  if (res.res_46.data) free(res.res_46.data); if (res.res_47.data) free(res.res_47.data);
  if (res.res_48.data) free(res.res_48.data);
  if (res.res_50.data) free(res.res_50.data); if (res.res_51.data) free(res.res_51.data);
  if (res.res_55.data) free(res.res_55.data); if (res.res_56.data) free(res.res_56.data);
  if (res.res_57.data) free(res.res_57.data); if (res.res_58.data) free(res.res_58.data);
  if (res.res_59.data) free(res.res_59.data); if (res.res_60.data) free(res.res_60.data);
  if (res.res_61.data) free(res.res_61.data); if (res.res_62.data) free(res.res_62.data);
  if (res.res_63.data) free(res.res_63.data); if (res.res_64.data) free(res.res_64.data);
  if (res.res_65.data) free(res.res_65.data); if (res.res_66.data) free(res.res_66.data);
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
  check ("fi_sum_0", func_FI_SUM (0) == 0); // zero iterations -> returns initial s (0)
  check ("fi_product_5", func_FI_PRODUCT (5) == 120); // 5!
  check ("fi_product_1", func_FI_PRODUCT (1) == 1);
  check ("fi_product_0", func_FI_PRODUCT (0) == 1); // zero iterations -> returns initial p (1)
  check ("fi_final_i_5",
         func_FI_FINAL_I (5) == 6); // i runs 1..n, stops at n+1
  check ("fi_final_i_1", func_FI_FINAL_I (1) == 2);
  check ("fi_final_i_0", func_FI_FINAL_I (0) == 1); // zero iterations -> returns initial i (1)
  // identity-recurrence carry (k := old k) — needs the MERGE-filter fix
  check ("fi_passthru_5", func_FI_PASSTHRU (5) == 42);
  check ("fi_passthru_1", func_FI_PASSTHRU (1) == 42);
  check ("fi_passthru_0", func_FI_PASSTHRU (0) == 42); // zero iterations -> returns initial k (42)
  // mutual old-references — needs the get_symbol_id_old carry-in fix
  check ("fi_swap_1", func_FI_SWAP (1) == 20); // a,b exchange each iter
  check ("fi_swap_2", func_FI_SWAP (2) == 10);
  check ("fi_swap_3", func_FI_SWAP (3) == 20);
  check ("fi_swap_0", func_FI_SWAP (0) == 10); // zero iterations -> returns initial a (10)
  check ("fi_fib_1", func_FI_FIB (1) == 1); // Fibonacci
  check ("fi_fib_5", func_FI_FIB (5) == 5);
  check ("fi_fib_7", func_FI_FIB (7) == 13);
  check ("fi_fib_10", func_FI_FIB (10) == 55);
  check ("fi_fib_0", func_FI_FIB (0) == 0); // zero iterations -> returns initial a (0)
  // LoopA (post-test repeat..until) Fibonacci — same recurrence via the other
  // loop block
  check ("fi_fib_a_1", func_FI_FIB_A (1) == 1);
  check ("fi_fib_a_5", func_FI_FIB_A (5) == 5);
  check ("fi_fib_a_7", func_FI_FIB_A (7) == 13);
  check ("fi_fib_a_10", func_FI_FIB_A (10) == 55);
  check ("fi_fib_a_0", func_FI_FIB_A (0) == 1); // LoopA post-test runs at least once

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

  sisal_array_t s1_zero = make_int_arr (seed, 3);
  sisal_array_t id_zero = func_FI_PARAM_IDENTITY (0, s1_zero); // zero iterations -> unchanged
  check ("fi_param_identity_zero rank=1", id_zero.rank == 1);
  check ("fi_param_identity_zero size=3", (int)id_zero.size == 3);
  check ("fi_param_identity_zero[0]=10", ai (id_zero, 0) == 10);
  check ("fi_param_identity_zero[1]=20", ai (id_zero, 1) == 20);
  check ("fi_param_identity_zero[2]=30", ai (id_zero, 2) == 30);
  if (s1_zero.data)
    free (s1_zero.data);

  sisal_array_t s2 = make_int_arr (seed, 3);
  sisal_array_t bp = func_FI_PARAM_BUMP (3, s2); // +1 per elem, 3 iters
  check ("fi_param_bump size=3", (int)bp.size == 3);
  check ("fi_param_bump[0]=13", ai (bp, 0) == 13);
  check ("fi_param_bump[1]=23", ai (bp, 1) == 23);
  check ("fi_param_bump[2]=33", ai (bp, 2) == 33);
  if (bp.data)
    free (bp.data);
  if (s2.data && s2.data != bp.data)
    free (s2.data);

  sisal_array_t s2_zero = make_int_arr (seed, 3);
  sisal_array_t bp_zero = func_FI_PARAM_BUMP (0, s2_zero); // zero iterations -> unchanged
  check ("fi_param_bump_zero size=3", (int)bp_zero.size == 3);
  check ("fi_param_bump_zero[0]=10", ai (bp_zero, 0) == 10);
  check ("fi_param_bump_zero[1]=20", ai (bp_zero, 1) == 20);
  check ("fi_param_bump_zero[2]=30", ai (bp_zero, 2) == 30);
  if (bp_zero.data)
    free (bp_zero.data);
  if (s2_zero.data && s2_zero.data != bp_zero.data)
    free (s2_zero.data);

  // gather loop variable starting at 1 with zero iterations
  sisal_array_t g_zero = func_FI_GATHER_ZERO (0);
  check ("fi_gather_zero size=1", (int)g_zero.size == 1);
  check ("fi_gather_zero[0]=1", ai (g_zero, 0) == 1);
  if (g_zero.data)
    free (g_zero.data);

  sisal_array_t g_one = func_FI_GATHER_ZERO (1);
  check ("fi_gather_one size=2", (int)g_one.size == 2);
  check ("fi_gather_one[0]=1", ai (g_one, 0) == 1);
  check ("fi_gather_one[1]=2", ai (g_one, 1) == 2);
  if (g_one.data)
    free (g_one.data);

  // gather loop variable k initialized in INIT but assigned in body
  sisal_array_t k_zero = func_FI_GATHER_BODY_TEMP (0);
  check ("fi_gather_body_temp_zero size=1", (int)k_zero.size == 1);
  check ("fi_gather_body_temp_zero[0]=0", ai (k_zero, 0) == 0);
  if (k_zero.data)
    free (k_zero.data);

  sisal_array_t k_one = func_FI_GATHER_BODY_TEMP (1);
  check ("fi_gather_body_temp_one size=2", (int)k_one.size == 2);
  check ("fi_gather_body_temp_one[0]=0", ai (k_one, 0) == 0);
  check ("fi_gather_body_temp_one[1]=2", ai (k_one, 1) == 2);
  if (k_one.data)
    free (k_one.data);
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
#ifdef TEST_BUBBLE_E2E
static void
test_bubble_e2e (void)
{
  printf ("\n=== Group: bubble_e2e ===\n");
  int32_t a[] = { 5, 1, 4, 2, 8 };
  int32_t exp[] = { 1, 2, 4, 5, 8 };
  sisal_array_t va = make_int_arr (a, 5);
  sisal_array_t r = func_BUBBLE (5, va);
  check ("bubble[0] == 1", ai (r, 0) == exp[0]);
  check ("bubble[1] == 2", ai (r, 1) == exp[1]);
  check ("bubble[2] == 4", ai (r, 2) == exp[2]);
  check ("bubble[3] == 5", ai (r, 3) == exp[3]);
  check ("bubble[4] == 8", ai (r, 4) == exp[4]);
  free (va.data);
  free (r.data);
}
#endif
#ifdef TEST_LEGPOLY_DV_E2E
static void
test_legpoly_dv_e2e (void)
{
  printf ("\n=== Group: legpoly_dv_e2e ===\n");
  sisal_array_t r = func_LEGENDREPOLYOF1STKIND (2, 4, 16, 0.5f, 0.8660254f, 1.04719755f);
  check ("legpoly_dv size == 16", r.size == 16);
  check ("legpoly_dv[0] check", fabs (((double*)r.data)[0] - 0.70710678) < 1e-5);
  check ("legpoly_dv[1] check", fabs (((double*)r.data)[1] - 0.6123724) < 1e-5);
  check ("legpoly_dv[2] check", fabs (((double*)r.data)[2] - -0.1976423) < 1e-5);
  check ("legpoly_dv[3] check", fabs (((double*)r.data)[3] - -0.818488) < 1e-5);
  check ("legpoly_dv[4] check", fabs (((double*)r.data)[4] - 0.75) < 1e-5);
  check ("legpoly_dv[5] check", fabs (((double*)r.data)[5] - 0.838525) < 1e-5);
  check ("legpoly_dv[6] check", fabs (((double*)r.data)[6] - 0.17539) < 1e-5);
  check ("legpoly_dv[7] check", fabs (((double*)r.data)[7] - -0.641862) < 1e-5);
  check ("legpoly_dv[8] check", ((double*)r.data)[8] == 0.0);
  free (r.data);
}
#endif
#ifdef TEST_NESTED_INIT_MERGE_DV
static void
test_nested_init_merge_dv (void)
{
  printf ("\n=== Group: nested_init_merge_dv ===\n");
  double d[] = { 1.0, 2.0, 3.0, 4.0, 5.0 };
  sisal_array_t X = make_double_arr (d, 5);
  sisal_array_t r = func_MAIN (3, X);
  check ("nested_init_merge_dv result size == 5", r.size == 5);
  free (X.data);
  free (r.data);
}
#endif
#ifdef TEST_MUTUAL_BUG_E2E
static void
test_mutual_bug_e2e (void)
{
  printf ("\n=== Group: mutual_bug_e2e ===\n");
  check ("swap_bug(1) == 20", func_SWAP_BUG (1) == 20);
  check ("swap_bug(2) == 10", func_SWAP_BUG (2) == 10);
  check ("swap_bug(3) == 20", func_SWAP_BUG (3) == 20);
}
#endif
#ifdef TEST_LU_NPIV_DV
static void
test_lu_npiv_dv (void)
{
  printf ("\n=== Group: lu_npiv_dv ===\n");
  double flat_A[9] = {
    2.0,  1.0, -1.0,
   -3.0, -1.0,  2.0,
   -2.0,  1.0,  2.0
  };
  double flat_B[3] = { 8.0, -11.0, -3.0 };
  sisal_array_t Ain = make_double_2d (flat_A, 3, 3);
  sisal_array_t Bin = make_double_arr (flat_B, 3);
  sisal_array_t r = func_MAIN (3, Ain, Bin);
  check ("lu_npiv_dv result size == 3", r.size == 3);
  check ("lu_npiv_dv x[0] == 2.0", fabs (((double*)r.data)[0] - 2.0) < 1e-5);
  check ("lu_npiv_dv x[1] == 3.0", fabs (((double*)r.data)[1] - 3.0) < 1e-5);
  check ("lu_npiv_dv x[2] == -1.0", fabs (((double*)r.data)[2] - -1.0) < 1e-5);
  free (Ain.data);
  free (Bin.data);
  free (r.data);
}
#endif
#ifdef TEST_LU_PIV_DV
static void
test_lu_piv_dv (void)
{
  printf ("\n=== Group: lu_piv_dv ===\n");
  double flat_A[9] = {
    2.0,  1.0, -1.0,
   -3.0, -1.0,  2.0,
   -2.0,  1.0,  2.0
  };
  double flat_B[3] = { 8.0, -11.0, -3.0 };
  sisal_array_t Ain = make_double_2d (flat_A, 3, 3);
  sisal_array_t Bin = make_double_arr (flat_B, 3);
  sisal_array_t r = func_MAIN (3, Ain, Bin);
  check ("lu_piv_dv result size == 3", r.size == 3);
  check ("lu_piv_dv x[0] == 2.0", fabs (((double*)r.data)[0] - 2.0) < 1e-5);
  check ("lu_piv_dv x[1] == 3.0", fabs (((double*)r.data)[1] - 3.0) < 1e-5);
  check ("lu_piv_dv x[2] == -1.0", fabs (((double*)r.data)[2] - -1.0) < 1e-5);
  free (Ain.data);
  free (Bin.data);
  free (r.data);
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

#ifdef TEST_KIN16_DV
static void
test_kin16_dv (void)
{
  printf ("\n=== Group: kin16_dv (Zone Electrophoresis) ===\n");
  struct FUNC_MAIN_results r = func_MAIN(2, 10, 5);
  check ("r.res_0.T == 0.0", fabs(r.res_0.T - 0.0) < 1e-7);
  check ("r.res_0.YMEANM == 0.0014", fabs(r.res_0.YMEANM - 0.0014) < 1e-7);
  check ("r.res_0.SIGSQM == 6.125e-07", fabs(r.res_0.SIGSQM - 6.125000000000004884e-07) < 1e-15);
  check ("r.res_0.SIGM == 0.0007826238", fabs(r.res_0.SIGM - 0.0007826238) < 1e-7);
  check ("r.res_0.SUM1M == 0.00002", fabs(r.res_0.SUM1M - 0.0000200000) < 1e-7);

  check ("r.res_1.T == 1.0", fabs(r.res_1.T - 1.0) < 1e-7);
  check ("r.res_1.YMEANM == 0.0020250719", fabs(r.res_1.YMEANM - 0.0020250719) < 1e-7);
  check ("r.res_1.SIGSQM == 9.40361229e-07", fabs(r.res_1.SIGSQM - 9.403612285497708558e-07) < 1e-15);
  check ("r.res_1.SIGM == 0.0009697222", fabs(r.res_1.SIGM - 0.0009697222) < 1e-7);
  check ("r.res_1.SUM1M == 2.00002455e-05", fabs(r.res_1.SUM1M - 2.000024554863243377e-05) < 1e-15);
}
#endif

#ifdef TEST_CFFT_DV
struct FUNC_MAIN_results {
  sisal_array_t res_0;
  sisal_array_t res_1;
};
extern "C" struct FUNC_MAIN_results func_MAIN(int32_t LOG2N);

static void
test_cfft_dv (void)
{
  printf ("\n=== Group: cfft_dv (Cray-2 FFT) ===\n");
  // Reference: naive DFT in this FFT's convention (initsfft builds
  // wr = cos, wi = +sin, so X[k] = sum_j x[j] * e^{+2*pi*i*j*k/n}); the
  // Cray FFT leaves the spectrum in scrambled (digit-reversed) order, so
  // the check is permutation-invariant: every DFT bin must appear exactly
  // once in the output (greedy matching).
  // NB the previous hardcoded expected values were snapshots of a compiler
  // bug (let-multi-bind duplicated wr into wi, so the sin table was the
  // cos table); see multibind_dv.
  for (int lg = 2; lg <= 4; lg++) {
    int n = 1 << lg;
    struct FUNC_MAIN_results r = func_MAIN(lg);
    char nm[80];
    sprintf(nm, "cfft(%d) output sizes == %d", lg, n);
    check (nm, (int)r.res_0.size == n && (int)r.res_1.size == n);

    float *gr = (float*)r.res_0.data, *gi = (float*)r.res_1.data;
    bool *used = (bool*)calloc(n, sizeof(bool));
    int unmatched = 0;
    for (int k = 0; k < n; k++) {
      double Xr = 0, Xi = 0;
      for (int j = 0; j < n; j++) {
        double th = 2.0*M_PI*j*k/n;
        Xr += j*cos(th); Xi += j*sin(th);
      }
      double m = fmax(1.0, fmax(fabs(Xr), fabs(Xi)));
      int hit = -1;
      for (int t = 0; t < n && hit < 0; t++)
        if (!used[t] && fabs(gr[t]-Xr) < 5e-3*m && fabs(gi[t]-Xi) < 5e-3*m) hit = t;
      if (hit >= 0) used[hit] = true; else unmatched++;
    }
    sprintf(nm, "cfft(%d) output is a permutation of the DFT spectrum", lg);
    check (nm, unmatched == 0);
    free(used);
    if (r.res_0.data) free(r.res_0.data);
    if (r.res_1.data) free(r.res_1.data);
  }
}
#endif

#ifdef TEST_HILBERT_DV
extern "C" double func_MAIN(sisal_array_t HILBERT, sisal_array_t B);

static void
test_hilbert_dv (void)
{
  printf ("\n=== Group: hilbert_dv ===\n");
  int n = 4;
  // Allocate flat 2D array of rank 2 (element size = sizeof(double) = 8, type ID = 4, size = n * n elements)
  sisal_array_t hilbert = sisal_array_alloc_sized(2, 4, n * n, sizeof(double));
  hilbert.dims[0] = n;
  hilbert.dims[1] = n;
  hilbert.lower_bound[0] = 1;
  hilbert.lower_bound[1] = 1;
  
  double* data = (double*)hilbert.data;
  for (int i = 0; i < n; i++) {
    for (int j = 0; j < n; j++) {
      data[i * n + j] = 1.0 / (double)(i + 1 + j + 1 - 1);
    }
  }
  
  // Allocate B vector (array of double)
  sisal_array_t b = sisal_array_alloc_empty(1, 4, n);
  double* b_data = (double*)b.data;
  for (int i = 0; i < n; i++) {
    b_data[i] = 1.0;
  }
  
  double resid = func_MAIN(hilbert, b);
  check("Residual is small", resid > 0.0 && resid < 1e-12);
  
  if (hilbert.data) free(hilbert.data);
  if (b.data) free(b.data);
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
          ZA = M23 (ZAt, j, k) + 0.175 * (QA - M23 (ZAt, j, k));
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
#ifdef TEST_MULTIBIND_DV
// Regression pin: let-statement multi-bind `a, b := e1, e2` with a LIST of
// single-valued rhs expressions.  The frontend used to re-lower e1 for b,
// making b a structural duplicate of a (to_if1 pop_or_push_to_exp_stack2
// did not consume the rhs head).  a = [1..n, 1.5..], b = 10*a pattern.
static void test_multibind_dv(void) {
    printf("\n=== Group: multibind_dv (let multi-bind of separate exprs) ===\n");
    const int n = 3;
    struct FUNC_MAIN_results r = func_MAIN(n);
    // reference: a = x1 || x2, b = y1 || y2 with x=i, x2=i+0.5, y=10i, y2=10i+0.5
    float ea[6], eb[6];
    for (int i = 1; i <= n; i++) {
        ea[i-1] = (float)i;        ea[n+i-1] = (float)i + 0.5f;
        eb[i-1] = (float)i*10.0f;  eb[n+i-1] = (float)i*10.0f + 0.5f;
    }
    bool ok = ((int)r.res_0.size == 2*n) && ((int)r.res_1.size == 2*n);
    for (int k = 0; ok && k < 2*n; k++)
        ok = fabs(((float*)r.res_0.data)[k] - ea[k]) < 1e-6
          && fabs(((float*)r.res_1.data)[k] - eb[k]) < 1e-6;
    check("multibind a,b := x1||x2, y1||y2 binds each name to its own expr", ok);
    if (r.res_0.data) free(r.res_0.data);
    if (r.res_1.data) free(r.res_1.data);
}
#endif
#ifdef TEST_TAG_DISPATCH_DV
// Regression pin: a nested tagcase must dispatch on ITS OWN scrutinee.
// The dispatch value used to be found "by union type" over the compound's
// in-edges — ambiguous once another same-typed union is imported (eager
// boundary propagation), so both levels dispatched on whichever edge won
// the fold: (A,B) gave 40 and (B,A) gave 10, while same-tag pairs passed
// by luck.  UNION_PORT_<k> on the compound pins the edge.
static void test_tag_dispatch_dv(void) {
    printf("\n=== Group: tag_dispatch_dv (nested tagcase scrutinee pinning) ===\n");
    struct FUNC_MAIN_results r = func_MAIN(7);
    check("Pick(A,B): outer A arm, inner B arm == 20", r.res_0 == 20);
    check("Pick(A,A): outer A arm, inner A arm == 10", r.res_1 == 10);
    check("Pick(B,A): outer B arm, inner A arm == 30", r.res_2 == 30);
    check("Pick(B,B): outer B arm, inner B arm == 40", r.res_3 == 40);
}
#endif
#ifdef TEST_SIMPSON
// Simpson's 1/3 rule over sin on [a,b], n panels — reference mirrors the
// exact summation order in double, float-tolerance compare.
static void test_simpson(void) {
    printf("\n=== Group: simpson (Simpson integration of sin) ===\n");
    double a = 0.0, b = 3.141592653589793; int n = 64;
    double delta = (b - a) / n;
    double s_odd = 0, s_even = 0;
    for (int i = 1; i <= (n + 1) / 2; i++) s_odd += sin(a + (2*(i-1)+1) * delta);
    for (int i = 1; i <= n / 2; i++)       s_even += sin(a + (2*i) * delta);
    double ref = (sin(a) + sin(b) + 4.0*s_odd + 2.0*s_even) * delta / 3.0;
    float got = func_SIMPSON((float)a, (float)b, n);
    check("simpson(0, pi, 64) == reference (~2.0)", fabs(got - ref) < 1e-4);
}
#endif
#ifdef TEST_MINMAX_DV
// First-occurrence argmin/argmax (plain and |.|), 1-based; C mirror.
static void test_minmax_dv(void) {
    printf("\n=== Group: minmax_dv (argmin/argmax first occurrence) ===\n");
    double v[8] = { 3.0, -7.0, 2.0, 9.0, -7.0, 0.5, 9.0, -1.0 };
    int n = 8;
    int imin=1, iamin=1, imax=1, iamax=1;
    for (int k = 2; k <= n; k++) {
        if (v[k-1] < v[imin-1]) imin = k;
        if (fabs(v[k-1]) < fabs(v[iamin-1])) iamin = k;
        if (v[k-1] > v[imax-1]) imax = k;
        if (fabs(v[k-1]) > fabs(v[iamax-1])) iamax = k;
    }
    sisal_array_t X = sisal_array_alloc_empty(1, 4, n);
    for (int i = 0; i < n; i++) ((double*)X.data)[i] = v[i];
    struct FUNC_MAIN_results r = func_MAIN(n, X);
    check("minmax imin == C reference",  r.res_0 == imin);
    check("minmax iamin == C reference", r.res_1 == iamin);
    check("minmax imax == C reference",  r.res_2 == imax);
    check("minmax iamax == C reference", r.res_3 == iamax);
    free(X.data);
}
#endif
#ifdef TEST_INSERTION1_DV
// Insertion sort via multi-value replace swaps; C reference sorts a copy.
static void test_insertion1_dv(void) {
    printf("\n=== Group: insertion1_dv (insertion sort, dv swaps) ===\n");
    double v[9] = { 5.5, -2.0, 9.25, 0.0, 3.5, 3.5, -8.75, 1.0, 7.0 };
    int n = 9;
    double ref[9];
    for (int i = 0; i < n; i++) ref[i] = v[i];
    for (int i = 1; i < n; i++) {           // reference insertion sort
        double x = ref[i]; int j = i - 1;
        while (j >= 0 && ref[j] > x) { ref[j+1] = ref[j]; j--; }
        ref[j+1] = x;
    }
    sisal_array_t in = sisal_array_alloc_empty(1, 4, n);
    for (int i = 0; i < n; i++) ((double*)in.data)[i] = v[i];
    sisal_array_t out = func_MAIN(in);
    bool ok = ((int)out.size == n);
    for (int i = 0; ok && i < n; i++)
        ok = (((double*)out.data)[i] == ref[i]);
    check("insertion1 sorts to C-reference order", ok);
    free(in.data);
    if (out.data && out.data != in.data) free(out.data);
}
#endif
#ifdef TEST_MESORT_DV
// Batcher merge-exchange sort; reference = C qsort on a copy.
static int cmp_i32(const void* a, const void* b) {
    int32_t x = *(const int32_t*)a, y = *(const int32_t*)b;
    return (x > y) - (x < y);
}
static void test_mesort_dv(void) {
    printf("\n=== Group: mesort_dv (Batcher merge-exchange sort) ===\n");
    int32_t v[16] = { 9, -3, 14, 0, 7, 7, -12, 5, 3, 3, 22, -1, 8, 2, 6, 1 };
    int n = 16;   // power of two exercises every stage
    int32_t ref[16];
    for (int i = 0; i < n; i++) ref[i] = v[i];
    qsort(ref, n, sizeof(int32_t), cmp_i32);
    sisal_array_t X = sisal_array_alloc_empty(1, 6, n);
    for (int i = 0; i < n; i++) ((int32_t*)X.data)[i] = v[i];
    sisal_array_t out = func_MAIN(X);
    bool ok = ((int)out.size == n);
    for (int i = 0; ok && i < n; i++) ok = (((int32_t*)out.data)[i] == ref[i]);
    check("mesort(16 mixed ints) == qsort reference", ok);
    free(X.data);
    if (out.data && out.data != X.data) free(out.data);
}
#endif
#ifdef TEST_LIFE2_DV
// life2's exact (quirky) rules mirrored in C over the same padded grid.
static void test_life2_dv(void) {
    printf("\n=== Group: life2_dv (game of life, flat rank-2) ===\n");
    enum { R = 6, C = 6, NUM = 3 };
    static int g[R+2][C+2], t[R+2][C+2];
    // glider-ish seed in a zero border
    memset(g, 0, sizeof g);
    g[2][3] = 1; g[3][4] = 1; g[4][2] = 1; g[4][3] = 1; g[4][4] = 1; g[3][2] = 1;
    sisal_array_t G = sisal_array_alloc_sized(2, 6, (R+2)*(C+2), sizeof(int32_t));
    G.dims[0] = R+2; G.dims[1] = C+2; G.lower_bound[0] = 1; G.lower_bound[1] = 1;
    for (int i = 0; i < R+2; i++)
        for (int j = 0; j < C+2; j++)
            ((int32_t*)G.data)[i*(C+2)+j] = g[i][j];
    for (int it = 0; it < NUM; it++) {           // reference iterations
        for (int i = 0; i < R+2; i++)
            for (int j = 0; j < C+2; j++) {
                if (i == 0 || j == 0 || i == R+1 || j == C+1) { t[i][j] = 0; continue; }
                int tot = g[i+1][j-1]+g[i+1][j]+g[i+1][j+1]
                        + g[i-1][j-1]+g[i-1][j]+g[i-1][j+1]
                        + g[i][j-1]+g[i][j+1];
                t[i][j] = (g[i][j] == 1 && tot > 5) ? 0 : (tot != 3 ? 1 : 0);
            }
        memcpy(g, t, sizeof g);
    }
    sisal_array_t out = func_MAIN(NUM, R, C, G);
    bool ok = (out.rank == 2) && ((int)out.size == (R+2)*(C+2));
    for (int i = 0; ok && i < R+2; i++)
        for (int j = 0; ok && j < C+2; j++)
            ok = (((int32_t*)out.data)[i*(C+2)+j] == g[i][j]);
    check("life2(3 iterations, 6x6 core) == C reference grid", ok);
    free(G.data);
    if (out.data && out.data != G.data) free(out.data);
}
#endif
#ifdef TEST_FOR_ALL_ARGMAX
// argmax reduction: val = 10 - i over i in 1..10 maximizes at i = 1.
static void test_for_all_argmax(void) {
    printf("\n=== Group: for_all_argmax (argmax reduction) ===\n");
    check("argmax of (10 - i), i in 1..10 == 1", func_MAIN(0) == 1);
}
#endif
#ifdef TEST_TUPLE_MIXED3
// THE historic tuple slot-1 bug pin: #(A,B) := #(X, 3.14) mis-bound B to
// slot 0 and returned (11, 20.0) instead of (11, 6.28).  Fixed by the
// parallel-copy binder (tuple items unpack by port).
static void test_tuple_mixed3(void) {
    printf("\n=== Group: tuple_mixed3 (tuple destructure slots) ===\n");
    struct FUNC_TUPLEMIXED_results r = func_TUPLEMIXED(10);
    check("A + 1 == 11", r.res_0 == 11);
    check("B * 2.0 == 6.28 (slot-1 payload, not slot-0)", fabs(r.res_1 - 6.28f) < 1e-5);
}
#endif
#ifdef TEST_RECORD1
// nested-record replace: {L:{R:0.2}, S:3.14} replace [l.r:3.2; s:1.23]
static void test_record1(void) {
    printf("\n=== Group: record1 (nested record replace) ===\n");
    struct struct_rec_98 r = func_MAIN();
    check("bb.L.R replaced to 3.2", fabs(r.L.R - 3.2f) < 1e-6);
    check("bb.S replaced to 1.23", fabs(r.S - 1.23f) < 1e-6);
}
#endif
#ifdef TEST_UNION1
// until-loop Newton sqrt; reference mirrors the exact float iteration.
static void test_union1(void) {
    printf("\n=== Group: union1 (until-loop Newton sqrt + is-tests) ===\n");
    float x = 2.0f, eps = 1e-4f;
    float root = x / 2.0f;
    do { root = (x / root + root) / 2.0f; } while (!((x - root * root) < eps));
    float got = func_MAIN(x, eps);
    check("newton-until sqrt(2) == mirrored float iteration", fabs(got - root) < 1e-6);
}
#endif
#ifdef TEST_TUPLE_MIXED2
static void test_tuple_mixed2(void) {
    printf("\n=== Group: tuple_mixed2 (all-literal tuple destructure) ===\n");
    struct FUNC_TUPLEMIXED_results r = func_TUPLEMIXED();
    check("#(A,B) := #(1, 2.0) gives (1, 2.0)",
          r.res_0 == 1 && fabs(r.res_1 - 2.0f) < 1e-6);
}
#endif
#ifdef TEST_UNION0
// is-tag tests on freshly built unions of all three payload kinds
// (int, real, array_dv) -> all true.
static void test_union0(void) {
    printf("\n=== Group: union0 (is-tests over three union tags) ===\n");
    sisal_array_t z = sisal_array_alloc_empty(1, 6, 2);
    ((int32_t*)z.data)[0] = 4; ((int32_t*)z.data)[1] = 5;
    struct FUNC_MAIN_results r = func_MAIN(7, 2.5f, z);
    check("is a(union[a:x]) == true", r.res_0);
    check("is b(union[b:y]) == true", r.res_1);
    check("is d(union[d:z]) == true", r.res_2);
    free(z.data);
}
#endif
#ifdef TEST_TUPLE_ADD_DV
// broadcasting elementwise add: equal sizes zip; a 1-element side splats.
static void test_tuple_add_dv(void) {
    printf("\n=== Group: tuple_add_dv (broadcasting elementwise add) ===\n");
    float av[3] = { 1, 2, 3 }, bv[3] = { 10, 20, 30 }, s1[1] = { 5 };
    sisal_array_t A = sisal_array_alloc_empty(1, 8, 3);
    sisal_array_t B = sisal_array_alloc_empty(1, 8, 3);
    sisal_array_t S = sisal_array_alloc_empty(1, 8, 1);
    for (int i = 0; i < 3; i++) { ((float*)A.data)[i] = av[i]; ((float*)B.data)[i] = bv[i]; }
    ((float*)S.data)[0] = s1[0];
    sisal_array_t r1 = func_TUPLE_ADD(A, B);
    sisal_array_t r2 = func_TUPLE_ADD(S, B);
    sisal_array_t r3 = func_TUPLE_ADD(A, S);
    bool ok1 = (int)r1.size == 3, ok2 = (int)r2.size == 3, ok3 = (int)r3.size == 3;
    for (int i = 0; i < 3 && ok1; i++) ok1 = fabs(((float*)r1.data)[i] - (av[i] + bv[i])) < 1e-6;
    for (int i = 0; i < 3 && ok2; i++) ok2 = fabs(((float*)r2.data)[i] - (5 + bv[i])) < 1e-6;
    for (int i = 0; i < 3 && ok3; i++) ok3 = fabs(((float*)r3.data)[i] - (av[i] + 5)) < 1e-6;
    check("equal sizes: [1,2,3]+[10,20,30]", ok1);
    check("splat left: 5+[10,20,30]", ok2);
    check("splat right: [1,2,3]+5", ok3);
    free(A.data); free(B.data); free(S.data);
    if (r1.data) free(r1.data); if (r2.data) free(r2.data); if (r3.data) free(r3.data);
}
#endif
#ifdef TEST_IDIV
// integer division semantics incl. negatives (truncation toward zero)
static void test_idiv(void) {
    printf("\n=== Group: idiv (integer division semantics) ===\n");
    check("7/2 == 3",   func_IDIV(7, 2) == 3);
    check("-7/2 == -3 (truncate toward zero)", func_IDIV(-7, 2) == -3);
    check("7/-2 == -3", func_IDIV(7, -2) == -3);
    check("-7/-2 == 3", func_IDIV(-7, -2) == 3);
}
#endif
#if defined(TEST_FORALL_SIMPLE_DV) || defined(TEST_FORALL_CROSS_DV) || defined(TEST_FORALL_DOT_DV)
static sisal_array_t mk_i32v(const int32_t* v, int n) {
    sisal_array_t a = sisal_array_alloc_empty(1, 6, n);
    for (int i = 0; i < n; i++) ((int32_t*)a.data)[i] = v[i];
    return a;
}
#endif
#ifdef TEST_FORALL_SIMPLE_DV
static void test_forall_simple_dv(void) {
    printf("\n=== Group: forall_simple_dv (scatter map x*2) ===\n");
    int32_t v[4] = { 1, 5, -3, 7 };
    sisal_array_t A = mk_i32v(v, 4);
    sisal_array_t r = func_MAIN(A);
    bool ok = (int)r.size == 4;
    for (int i = 0; ok && i < 4; i++) ok = (((int32_t*)r.data)[i] == v[i] * 2);
    check("map x*2 over [1,5,-3,7]", ok);
    free(A.data); if (r.data && r.data != A.data) free(r.data);
}
#endif
#ifdef TEST_FORALL_DOT_DV
static void test_forall_dot_dv(void) {
    printf("\n=== Group: forall_dot_dv (dot-zip inner product) ===\n");
    int32_t av[3] = { 1, 2, 3 }, bv[3] = { 4, 5, 6 };
    sisal_array_t A = mk_i32v(av, 3), B = mk_i32v(bv, 3);
    check("dot([1,2,3],[4,5,6]) == 32", func_MAIN(A, B) == 32);
    free(A.data); free(B.data);
}
#endif
#ifdef TEST_TUPLE_MIXED
static void test_tuple_mixed(void) {
    printf("\n=== Group: tuple_mixed (tuple literal as multi-result) ===\n");
    struct FUNC_TUPLEMIXED_results r = func_TUPLEMIXED();
    check("#(1, 2.0) returns (1, 2.0)", r.res_0 == 1 && fabs(r.res_1 - 2.0f) < 1e-6);
}
#endif
#ifdef TEST_RECORD2
static void test_record2(void) {
    printf("\n=== Group: record2 (record param field access) ===\n");
    struct struct_rec_96 r; r.A = 11; r.B = 31;
    check("Test({a:11, b:31}) == 42", func_TEST(r) == 42);
}
#endif
#ifdef TEST_RECORD1_REORDER
// record1 with field order swapped (S before nested L)
static void test_record1_reorder(void) {
    printf("\n=== Group: record1_reorder (field-order-swapped replace) ===\n");
    struct struct_rec_98r r = func_MAIN();
    check("bb.S replaced to 1.23", fabs(r.S - 1.23f) < 1e-6);
    check("bb.L.R replaced to 3.2", fabs(r.L.R - 3.2f) < 1e-6);
}
#endif
#ifdef TEST_RECORD_REPLACE_E2E
// Cart record: field read (Origin.X * 2.0) feeding a replace [Y: XX]
static void test_record_replace_e2e(void) {
    printf("\n=== Group: record_replace_e2e (read-then-replace) ===\n");
    struct cart_rec r = func_MAIN();
    check("HOME.X == 4.2", fabs(r.X - 4.2f) < 1e-6);
    check("HOME.Y == 8.4 (Origin.X * 2)", fabs(r.Y - 8.4f) < 1e-6);
}
#endif
#ifdef TEST_PARPI1
// forall-parallel Leibniz pi (pairwise terms); reference mirrors in double
static void test_parpi1(void) {
    printf("\n=== Group: parpi1 (forall Leibniz pi) ===\n");
    int cycles = 2000;
    double s = 0;
    for (int i = 1; i <= cycles / 2; i++) s += 1.0/(4.0*i-3) - 1.0/(4.0*i-1);
    float got = func_MAIN(cycles);
    check("parpi1(2000) ~ pi (vs mirrored series)", fabs(got - (float)(s*4.0)) < 1e-4);
}
#endif
#ifdef TEST_FORALL_CROSS_DV
// outer product over INDEPENDENT cross axes of different sizes (3 x 2) —
// regression pin for the dot-conformance diamond mis-zipping cross axes.
static void test_forall_cross_dv(void) {
    printf("\n=== Group: forall_cross_dv (element-scatter cross, rank-2) ===\n");
    int32_t av[3] = { 1, 2, 3 }, bv[2] = { 10, 20 };
    sisal_array_t A = sisal_array_alloc_empty(1, 6, 3);
    sisal_array_t B = sisal_array_alloc_empty(1, 6, 2);
    for (int i = 0; i < 3; i++) ((int32_t*)A.data)[i] = av[i];
    for (int i = 0; i < 2; i++) ((int32_t*)B.data)[i] = bv[i];
    sisal_array_t r = func_MAIN(A, B);
    bool ok = r.rank == 2 && (int)r.dims[0] == 3 && (int)r.dims[1] == 2;
    for (int i = 0; ok && i < 3; i++)
        for (int j = 0; ok && j < 2; j++)
            ok = (((int32_t*)r.data)[i*2+j] == av[i] * bv[j]);
    check("outer product [1,2,3] x [10,20] rank-2", ok);
    free(A.data); free(B.data); if (r.data) free(r.data);
}
#endif
#ifdef TEST_FORALL_SHAPED_GATHER_DV
static void test_forall_shaped_gather_dv(void) {
    printf("\n=== Group: forall_shaped_gather_dv (pre-allocated nested gather) ===\n");
    int32_t n = 4, m = 3;
    sisal_array_t r = func_MAIN(n, m);
    bool ok = r.rank == 2 && (int)r.dims[0] == 4 && (int)r.dims[1] == 3;
    if (ok) {
        for (int i = 0; i < 4; i++) {
            for (int j = 0; j < 3; j++) {
                float got = ((float*)r.data)[i*3+j];
                float expected = (float)((i+1) * 10 + (j+1));
                if (fabs(got - expected) > 1e-5) {
                    ok = false;
                }
            }
        }
    }
    check("forall shaped gather pre-allocated flat rank-2", ok);
    if (r.data) free(r.data);
}
#endif
#ifdef TEST_FOR_INITIAL_SIMPLE
// `;` = let-in nesting: stmt1 reads carry s; stmt2 reads carry (old i)
// AND stmt1's new i.  Reference mirrors exactly that.
static void test_for_initial_simple(void) {
    printf("\n=== Group: for_initial_simple (sequential body scoping) ===\n");
    bool ok = true;
    for (int n = 3; n <= 24 && ok; n += 7) {
        int i = 1, s = 0;
        while (i <= n) { int i1 = i + s + 1; s = s + i + i1; i = i1; }
        ok = (func_MAIN(n) == s);
    }
    check("i := old i + s + 1; s := old s + old i + i (n=3..24)", ok);
}
#endif
#ifdef TEST_PARPI2
// Leibniz pi via a TWO-RESULT forall (separate + and - sums), (a-b)*4
static void test_parpi2(void) {
    printf("\n=== Group: parpi2 (two-sum forall pi) ===\n");
    int cycles = 2000; double a = 0, b = 0;
    for (int i = 1; i <= cycles / 2; i++) { a += 1.0/(4.0*i-3); b += 1.0/(4.0*i-1); }
    check("parpi2(2000) == mirrored (a-b)*4", fabs(func_MAIN(cycles) - (float)((a-b)*4.0)) < 1e-4);
}
#endif
#ifdef TEST_PARPI_BABB
// Karp-Babb midpoint-rule pi: (4/N) * sum 1/(1+x_j^2), x_j = (j-1/2)/N
static void test_parpi_babb(void) {
    printf("\n=== Group: parpi_babb (midpoint-rule pi) ===\n");
    int n = 1000; double s = 0;
    for (int j = 1; j <= n; j++) { double x = (j - 0.5) / n; s += 1.0/(1.0 + x*x); }
    check("parpi_babb(1000) == mirrored series", fabs(func_MAIN(n) - (float)(4.0/n*s)) < 1e-4);
}
#endif
#ifdef TEST_FOR_INITIAL_LOOPA
// POST-TEST loop (repeat ... while): body runs once, then tests i < n.
static void test_for_initial_loopa(void) {
    printf("\n=== Group: for_initial_loopa (repeat..while post-test) ===\n");
    bool ok = true;
    for (int n = 0; n <= 12 && ok; n += 3) {
        int i = 0, s = 0;
        do { int i1 = i + 1; s = s + i; i = i1; } while (i < n);
        ok = (func_MAIN(n) == s);
    }
    check("post-test sum incl. n=0 (one mandatory trip)", ok);
}
#endif
#ifdef TEST_LOOPAT2_DV
// indexed map Y[I]*Y[I] over 1..N
static void test_loopat2_dv(void) {
    printf("\n=== Group: loopat2_dv (indexed square map) ===\n");
    double v[5] = { 1.5, -2.0, 0.0, 3.0, -0.5 };
    sisal_array_t Y = sisal_array_alloc_empty(1, 4, 5);
    for (int i = 0; i < 5; i++) ((double*)Y.data)[i] = v[i];
    sisal_array_t r = func_MAIN(5, Y);
    bool ok = (int)r.size == 5;
    for (int i = 0; ok && i < 5; i++) ok = fabs(((double*)r.data)[i] - v[i]*v[i]) < 1e-12;
    check("Y[I]*Y[I] over 1..5", ok);
    free(Y.data); if (r.data && r.data != Y.data) free(r.data);
}
#endif
#ifdef TEST_TST_LOOP2_DV
// scatter-sum: sum of K+K over the elements
static void test_tst_loop2_dv(void) {
    printf("\n=== Group: tst_loop2_dv (scatter sum of 2K) ===\n");
    double v[4] = { 1.5, -2.0, 3.25, 10.0 }, s = 0;
    for (int i = 0; i < 4; i++) s += v[i] + v[i];
    sisal_array_t Y = sisal_array_alloc_empty(1, 4, 4);
    for (int i = 0; i < 4; i++) ((double*)Y.data)[i] = v[i];
    check("sum(K+K) over [1.5,-2,3.25,10]", fabs(func_MAIN(Y) - s) < 1e-12);
    free(Y.data);
}
#endif
#ifdef TEST_FOR_ALL_REDUCE
// MASKED reduction: sum 100/(i-5) WHEN i > 5 == 228 (i=6..10 only).
// The unmasked bug returned 20 (all i, with ARM64 100/0 = 0) — this value
// pins the mask being honored.  (Body still evaluates 100/(i-5) at i=5;
// benign on ARM64 where integer div-by-zero does not trap.)
static void test_for_all_reduce(void) {
    printf("\n=== Group: for_all_reduce (masked sum reduction) ===\n");
    check("sum 100/(i-5) when i>5 == 228", func_MAIN(0) == 228);
}
#endif
#ifdef TEST_SIMPLEBATCHER_DV
// Batcher merge-exchange sort.  The program rebases its input to 0-based
// (array_setl(K,0)) and drives the exchange network off the `at` index, so
// it pins both the LoopA (repeat..until runs at least once) do-while
// lowering and gathers inheriting the source's lower bound.  Reference =
// qsort.
static int sb_cmp(const void* a, const void* b) {
    int32_t x = *(const int32_t*)a, y = *(const int32_t*)b;
    return (x > y) - (x < y);
}
static void sb_case(const char* label, const int32_t* v, int n) {
    int32_t ref[16];
    for (int i = 0; i < n; i++) ref[i] = v[i];
    qsort(ref, n, sizeof(int32_t), sb_cmp);
    sisal_array_t K = sisal_array_alloc_empty(1, 6, n);
    for (int i = 0; i < n; i++) ((int32_t*)K.data)[i] = v[i];
    sisal_array_t r = func_MAIN(K);
    int ok = (int)r.size == n && (int)r.lower_bound[0] == 0;
    for (int i = 0; ok && i < n; i++) ok = ((int32_t*)r.data)[i] == ref[i];
    check(label, ok);
}
static void test_simplebatcher_dv(void) {
    printf("\n=== Group: simplebatcher_dv (Batcher merge-exchange sort, 0-based dv) ===\n");
    const int32_t a[8] = { 9, -3, 14, 0, 7, 7, -12, 5 };
    const int32_t b[5] = { 5, 1, 4, 1, 3 };
    sb_case("sort 8 (power of two, negatives+dups) == qsort", a, 8);
    sb_case("sort 5 (non-power size, dups) == qsort", b, 5);
}
#endif
#ifdef TEST_SEQBATCHER_DV
// DATAFLOW-MIRROR test: seqbatcher is NOT a correct sort (its skeleton skips
// the R-subpasses — see the .sis header); the reference is a C mirror of the
// program's exact dataflow.  Pins the cross-scope `old P` ruling (enclosing
// loop's previous-iteration value), a repeat..until outer loop, the 3-deep
// for-initial nest with in-place CSwap replaces, and the BITWISE_AND
// intrinsic.
static int sq_clog2(int n) { int l = 0, t = 1; while (t < n) { l++; t *= 2; } return l; }
static void sq_mirror(int32_t* c, int n) {
    int ttm1 = 1 << (sq_clog2(n) - 1);
    int P = ttm1;
    do {
        int Pold = P; P = Pold / 2;
        int Q = ttm1, R = 0, D = Pold;
        do {
            for (int I = 0; I + D < n; I++)
                if ((I & Pold) == R && c[I] > c[I + D]) {
                    int32_t t = c[I]; c[I] = c[I + D]; c[I + D] = t;
                }
            int Qold = Q;
            D = Qold - Pold; Q = Qold / 2; R = Pold;
        } while (!(Q <= Pold));
    } while (!(P <= 0));
}
static void sq_case(const char* label, const int32_t* v, int n) {
    int32_t ref[16];
    for (int i = 0; i < n; i++) ref[i] = v[i];
    sq_mirror(ref, n);
    sisal_array_t K = sisal_array_alloc_empty(1, 6, n);
    for (int i = 0; i < n; i++) ((int32_t*)K.data)[i] = v[i];
    sisal_array_t r = func_MAIN(K);
    int ok = (int)r.size == n;
    for (int i = 0; ok && i < n; i++) ok = ((int32_t*)r.data)[i] == ref[i];
    check(label, ok);
}
static void test_seqbatcher_dv(void) {
    printf("\n=== Group: seqbatcher_dv (exchange network vs C dataflow mirror) ===\n");
    const int32_t a[8]  = { 9, -3, 14, 0, 7, 7, -12, 5 };
    const int32_t b[5]  = { 5, 1, 4, 1, 3 };
    const int32_t c[16] = { 12, -1, 0, 99, -50, 3, 3, 7, 2, 8, -8, 41, 6, 6, -2, 17 };
    sq_case("n=8 == mirror", a, 8);
    sq_case("n=5 == mirror", b, 5);
    sq_case("n=16 == mirror", c, 16);
}
#endif
#ifdef TEST_BATCHER_DV
// Batcher merge-exchange sort of RECORDS (SortRec {Val: real; Loc: integer},
// Sort_OneDim = array_dv[SortRec]) — records as sized dope-vector elements.
// Distinct keys (Batcher is not stable), so qsort on Val is the unique
// expected order; Loc must carry each element's original 1-based position.
struct bat_sortrec { float val; int32_t loc; };
static int bat_cmp(const void* a, const void* b) {
    float x = ((const bat_sortrec*)a)->val, y = ((const bat_sortrec*)b)->val;
    return (x > y) - (x < y);
}
static void bat_case(const char* label, const float* v, int n) {
    bat_sortrec ref[16];
    for (int i = 0; i < n; i++) { ref[i].val = v[i]; ref[i].loc = i + 1; }
    qsort(ref, n, sizeof(bat_sortrec), bat_cmp);
    sisal_array_t K = sisal_array_alloc_sized(1, 96, n, sizeof(bat_sortrec));
    K.lower_bound[0] = 1;
    for (int i = 0; i < n; i++) {
        ((bat_sortrec*)K.data)[i].val = v[i];
        ((bat_sortrec*)K.data)[i].loc = i + 1;
    }
    sisal_array_t r = func_MAIN(K);
    int ok = (int)r.size == n && (int)r.lower_bound[0] == 1;
    for (int i = 0; ok && i < n; i++) {
        bat_sortrec x = ((bat_sortrec*)r.data)[i];
        ok = x.val == ref[i].val && x.loc == ref[i].loc;
    }
    check(label, ok);
}
static void test_batcher_dv(void) {
    printf("\n=== Group: batcher_dv (record sort, array_dv[SortRec]) ===\n");
    const float a[8] = { 9.5f, -3.25f, 14.0f, 0.5f, 7.75f, 6.5f, -12.0f, 5.25f };
    const float b[5] = { 5.5f, 1.25f, 4.0f, 1.75f, 3.5f };
    bat_case("n=8 records sorted on Val, Loc provenance", a, 8);
    bat_case("n=5 records sorted on Val, Loc provenance", b, 5);
}
#endif

#ifdef TEST_ANGMOM_DV
// Spectral shallow-water angular-momentum diagnostics over complex-record
// arrays (CplexReal {Repart, Impart: real}, ArrCplexReal = array_dv[record]).
// Reference = C mirror with the same float order of operations.  Pins nested
// record-returning calls (Cmul(Csub(..), Conjg(..)).Repart) — the invocation
// arg re-lowering bug produced dead record INVOCATIONs that broke C emission.
struct am_cplx { float re, im; };
static sisal_array_t am_mk(const am_cplx* v, int n) {
    sisal_array_t a = sisal_array_alloc_sized(1, 96, n, sizeof(am_cplx));
    a.lower_bound[0] = 1;
    for (int i = 0; i < n; i++) ((am_cplx*)a.data)[i] = v[i];
    return a;
}
static void test_angmom_dv(void) {
    printf("\n=== Group: angmom_dv (complex-record diagnostics, array_dv[record]) ===\n");
    const int jx = 3, jxmx = 6, N = 8;
    const float zmean = 1.5f, asq = 2.0f, ww = 0.7f;
    am_cplx u[N], h[N], zm[N], z[N];
    for (int i = 0; i < N; i++) {
        u[i]  = { 0.3f + 0.1f*i, 0.05f*i };
        h[i]  = { 0.2f + 0.02f*i, -0.03f*i };
        zm[i] = { 0.5f - 0.04f*i, 0.06f*i };
        z[i]  = { 0.1f*i, 0.02f + 0.01f*i };
    }
    const float c2 = 0.421637f, c3 = 1.4142136f, c4 = 1e-5f;
    float gmass = 4.0f*(zmean - h[0].re)/asq;
    float atot1 = u[0].re * c3 * (zmean - h[0].re);
    int backdown = 2 + jxmx;
    float atotup = 0.0f;
    for (int j = 2; j <= jxmx; j++) {
        int k = backdown - j;
        am_cplx cu = { u[k-1].re, -u[k-1].im };
        am_cplx d  = { zm[k-1].re - h[k-1].re, zm[k-1].im - h[k-1].im };
        float relative = d.re*cu.re - d.im*cu.im;
        atotup += (k > jx) ? 2.0f*relative : relative;
    }
    float atot = (atot1 + atotup)/gmass*c4;
    float atot_1 = atot1/gmass*c4;
    float wtot = ww*(-c2*(z[2].re - h[2].re))/gmass*c4;
    ANGMOM_results r = func_MAIN(jx, jxmx, zmean, asq, ww,
                                 am_mk(u, N), am_mk(h, N), am_mk(zm, N), am_mk(z, N));
    auto near = [](float got, float want) {
        return fabsf(got - want) <= 1e-6f*fmaxf(1.0f, fabsf(want));
    };
    check("atot", near(r.atot, atot));
    check("atot_1", near(r.atot_1, atot_1));
    check("wtot", near(r.wtot, wtot));
    check("total", near(r.total, atot + wtot));
    check("total1", near(r.total1, atot_1 + wtot));
}
#endif

#ifdef TEST_VSPHERE_DV
// Shallow-water grid products: five rank-3 elementwise outputs from a
// hemi CROSS latlev nest of rank-1 multi-output gathers (box-flatten to
// rank-3 (2, ilath, 2*lon+2)).  Reference = elementwise C mirror.
enum { VS_LON = 4, VS_ILATH = 3, VS_NP = VS_LON*2 + 2, VS_TOT = 2*VS_ILATH*VS_NP };
static sisal_array_t vs_mk3(const float* v) {
    sisal_array_t a = sisal_array_alloc_empty(3, 8, VS_TOT);
    a.dims[0] = 2; a.dims[1] = VS_ILATH; a.dims[2] = VS_NP;
    a.lower_bound[0] = a.lower_bound[1] = a.lower_bound[2] = 1;
    for (int i = 0; i < VS_TOT; i++) ((float*)a.data)[i] = v[i];
    return a;
}
static int vs_ck(sisal_array_t r, const float* want) {
    int ok = (int)r.size == VS_TOT && r.rank == 3
          && (int)r.dims[0] == 2 && (int)r.dims[1] == VS_ILATH && (int)r.dims[2] == VS_NP;
    for (int i = 0; ok && i < VS_TOT; i++)
        ok = fabsf(((float*)r.data)[i] - want[i]) <= 1e-6f*fmaxf(1.0f, fabsf(want[i]));
    return ok;
}
static void test_vsphere_dv(void) {
    printf("\n=== Group: vsphere_dv (rank-3 grid products, 5 outputs) ===\n");
    float pg[VS_TOT], zg[VS_TOT], ug[VS_TOT], vg[VS_TOT];
    for (int i = 0; i < VS_TOT; i++) {
        pg[i] = 0.5f + 0.01f*i; zg[i] = 1.0f - 0.02f*i;
        ug[i] = 0.3f + 0.03f*i; vg[i] = -0.2f + 0.02f*i;
    }
    float eg[VS_TOT], pvg[VS_TOT], pug[VS_TOT], zvg[VS_TOT], zug[VS_TOT];
    for (int i = 0; i < VS_TOT; i++) {
        eg[i] = ug[i]*ug[i] + vg[i]*vg[i];
        pvg[i] = pg[i]*vg[i]; pug[i] = pg[i]*ug[i];
        zvg[i] = zg[i]*vg[i]; zug[i] = zg[i]*ug[i];
    }
    VSPHERE_results r = func_MAIN(VS_LON, VS_ILATH, vs_mk3(pg), vs_mk3(zg), vs_mk3(ug), vs_mk3(vg));
    check("eg  == ug^2+vg^2 (rank-3)", vs_ck(r.eg, eg));
    check("pug == pg*ug", vs_ck(r.pug, pug));
    check("pvg == pg*vg", vs_ck(r.pvg, pvg));
    check("zug == zg*ug", vs_ck(r.zug, zug));
    check("zvg == zg*vg", vs_ck(r.zvg, zvg));
}
#endif

#ifdef TEST_ENERGY_DV
// Spectral shallow-water potential/kinetic energy: two-output sum reduction
// over complex-record arrays with nested record-returning calls.  Reference
// = C mirror, same float order of operations.
struct en_cplx { float re, im; };
static sisal_array_t en_mk(const en_cplx* v, int n) {
    sisal_array_t a = sisal_array_alloc_sized(1, 96, n, sizeof(en_cplx));
    a.lower_bound[0] = 1;
    for (int i = 0; i < n; i++) ((en_cplx*)a.data)[i] = v[i];
    return a;
}
static void test_energy_dv(void) {
    printf("\n=== Group: energy_dv (complex-record energy diagnostics) ===\n");
    const int jx = 3, jxmx = 6, N = 8;
    const float zmean = 1.5f, asq = 2.0f;
    en_cplx e[N], h[N], zm[N];
    for (int i = 0; i < N; i++) {
        e[i]  = { 0.25f + 0.07f*i, 0.04f*i };
        h[i]  = { 0.2f + 0.02f*i, -0.03f*i };
        zm[i] = { 0.5f - 0.04f*i, 0.06f*i };
    }
    float gmass = 4.0f*(zmean - h[0].re)/asq;
    int backdown = 2 + jxmx;
    float ptot1 = 0.0f, ktot1 = 0.0f;
    for (int j = 2; j <= jxmx; j++) {
        int k = backdown - j;
        float zr = zm[k-1].re, zi = zm[k-1].im;
        en_cplx ce = { e[k-1].re, -e[k-1].im };
        float pot = zr*zr + zi*zi;
        en_cplx d = { zm[k-1].re - h[k-1].re, zm[k-1].im - h[k-1].im };
        float kin = d.re*ce.re - d.im*ce.im;
        ptot1 += (k > jx) ? 2.0f*pot : pot;
        ktot1 += (k > jx) ? 2.0f*kin : kin;
    }
    float ptot = ptot1/gmass;
    float ktot = (ktot1 + e[0].re*1.4142136f*(zmean - h[0].re))/gmass;
    ENERGY_results r = func_MAIN(jx, jxmx, zmean, asq, en_mk(e, N), en_mk(h, N), en_mk(zm, N));
    auto near = [](float got, float want) {
        return fabsf(got - want) <= 1e-6f*fmaxf(1.0f, fabsf(want));
    };
    check("ptot", near(r.ptot, ptot));
    check("ktot", near(r.ktot, ktot));
    check("total", near(r.total, ptot + ktot));
}
#endif
#ifdef TEST_SPECAM_DV
// Spectral amplitudes per zonal wavenumber: indexed gather (kmjx offsets)
// over complex-record arrays, 3-output inner sum reduction, outer gathers
// through SQRTR (Fortran-style sqrt alias intrinsic).  Reference = C mirror.
struct spm_cplx { float re, im; };
enum { SPM_JX = 4, SPM_MX = 3, SPM_NC = 20 };
static sisal_array_t spm_mkc(const spm_cplx* v, int n) {
    sisal_array_t a = sisal_array_alloc_sized(1, 96, n, sizeof(spm_cplx));
    a.lower_bound[0] = 1;
    for (int i = 0; i < n; i++) ((spm_cplx*)a.data)[i] = v[i];
    return a;
}
static void test_specam_dv(void) {
    printf("\n=== Group: specam_dv (spectral amplitudes, SQRTR) ===\n");
    const float asq = 2.5f, ww = 0.7f, grav = 9.8f;
    int32_t kmjx[SPM_MX] = { 0, 5, 11 };
    spm_cplx c[SPM_NC], p[SPM_NC], z[SPM_NC];
    for (int i = 0; i < SPM_NC; i++) {
        c[i] = { 0.1f + 0.02f*i, -0.05f + 0.01f*i };
        p[i] = { 0.3f - 0.01f*i, 0.02f*i };
        z[i] = { 0.05f*i, 0.4f - 0.03f*i };
    }
    float ampk[SPM_MX], ampvor[SPM_MX], ampz[SPM_MX];
    for (int m = 1; m <= SPM_MX; m++) {
        float sk = 0, sv = 0, sz = 0;
        for (int j = 1; j <= SPM_JX; j++) {
            int jm = kmjx[m-1] + j;
            const spm_cplx *pc = &c[jm-1], *pp = &p[jm-1], *pz = &z[jm-1];
            float dv = pc->re*pc->re + pc->im*pc->im;
            float vo = pp->re*pp->re + pp->im*pp->im;
            float sq = pz->re*pz->re + pz->im*pz->im;
            if (m > 1) { dv *= 2.0f; vo *= 2.0f; sq *= 2.0f; }
            sk += dv; sv += vo; sz += sq;
        }
        ampk[m-1] = sqrtf(sk)/ww*10.0f;
        ampvor[m-1] = sqrtf(sv)/ww;
        ampz[m-1] = sqrtf(sz)*asq/grav;
    }
    sisal_array_t K = sisal_array_alloc_empty(1, 6, SPM_MX);
    K.lower_bound[0] = 1;
    for (int i = 0; i < SPM_MX; i++) ((int32_t*)K.data)[i] = kmjx[i];
    SPECAM_results r = func_MAIN(SPM_JX, SPM_MX, K, asq, ww, grav,
                                 spm_mkc(c, SPM_NC), spm_mkc(p, SPM_NC), spm_mkc(z, SPM_NC));
    auto cka = [](sisal_array_t a, const float* want) {
        int ok = (int)a.size == SPM_MX;
        for (int i = 0; ok && i < SPM_MX; i++)
            ok = fabsf(((float*)a.data)[i] - want[i]) <= 1e-6f*fmaxf(1.0f, fabsf(want[i]));
        return ok;
    };
    check("ampk", cka(r.ampk, ampk));
    check("ampvor", cka(r.ampvor, ampvor));
    check("ampz", cka(r.ampz, ampz));
}
#endif

#ifdef TEST_SAS_DV
// SasAlfaSphere: southern-hemisphere mirror of associated-Legendre
// coefficients with odd-order sign flip.  Rank-2 double input (NB double =
// tid 4 — tid 9 poisons elem_bytes to descriptor size), rank-3 real output
// via an IF-of-nested-gathers box-flatten; South rows built by a CATENATE
// reduction of per-order gathers.  Reference = C mirror.
static void test_sas_dv(void) {
    printf("\n=== Group: sas_dv (Legendre hemisphere mirror, catenate gather) ===\n");
    enum { IR = 3, IRMAX2 = 4, JXXMX = (IR+1)*IRMAX2, ILATH = 3, TOT = ILATH*JXXMX };
    double alp[TOT];
    for (int i = 0; i < TOT; i++) alp[i] = 0.25*(i+1) - 0.001*i*i;
    sisal_array_t A = sisal_array_alloc_empty(2, 4, TOT);
    A.dims[0] = ILATH; A.dims[1] = JXXMX; A.lower_bound[0] = A.lower_bound[1] = 1;
    for (int i = 0; i < TOT; i++) ((double*)A.data)[i] = alp[i];
    float want[2*ILATH*JXXMX];
    for (int hemi = 1; hemi <= 2; hemi++)
        for (int lat = 1; lat <= ILATH; lat++)
            for (int k = 1; k <= JXXMX; k++) {
                int oi = ((hemi-1)*ILATH + (lat-1))*JXXMX + (k-1);
                double v = alp[(lat-1)*JXXMX + (k-1)];
                if (hemi == 1) want[oi] = (float)v;
                else {
                    int lp = (k-1) % IRMAX2 + 1;
                    want[oi] = (lp == 1 || lp % 2 != 0) ? (float)v : (float)(-v);
                }
            }
    sisal_array_t r = func_MAIN(IR, IRMAX2, JXXMX, ILATH, A);
    int ok = (int)r.size == 2*ILATH*JXXMX && r.rank == 3
          && (int)r.dims[0] == 2 && (int)r.dims[1] == ILATH && (int)r.dims[2] == JXXMX;
    for (int i = 0; ok && i < 2*ILATH*JXXMX; i++)
        ok = fabsf(((float*)r.data)[i] - want[i]) <= 1e-6f*fmaxf(1.0f, fabsf(want[i]));
    check("alfa (2,ilath,jxxmx) == mirror with South sign flips", ok);
}
#endif

#ifdef TEST_LINEAR_DV
// Linear terms of the spectral time-derivatives: deep Cadd/Csub/Crmul record
// call chains, IF-selected neighbor elements (zero record at the truncation
// edges), per-m gathers catenated to rank-1, and a ksq array indexed from 0
// (passed with lower bound 0 — dv honors lb).  Reference = C mirror.
struct lin_cplx { float re, im; };
static sisal_array_t lin_mki(const int32_t* w, int n, int lb) {
    sisal_array_t a = sisal_array_alloc_empty(1, 6, n); a.lower_bound[0] = lb;
    for (int i = 0; i < n; i++) ((int32_t*)a.data)[i] = w[i];
    return a;
}
static sisal_array_t lin_mkf(const float* w, int n) {
    sisal_array_t a = sisal_array_alloc_empty(1, 8, n); a.lower_bound[0] = 1;
    for (int i = 0; i < n; i++) ((float*)a.data)[i] = w[i];
    return a;
}
static sisal_array_t lin_mkc(const lin_cplx* w, int n) {
    sisal_array_t a = sisal_array_alloc_sized(1, 96, n, sizeof(lin_cplx)); a.lower_bound[0] = 1;
    for (int i = 0; i < n; i++) ((lin_cplx*)a.data)[i] = w[i];
    return a;
}
static lin_cplx lin_add(lin_cplx a, lin_cplx b) { return { a.re + b.re, a.im + b.im }; }
static lin_cplx lin_sub(lin_cplx a, lin_cplx b) { return { a.re - b.re, a.im - b.im }; }
static lin_cplx lin_rm(float s, lin_cplx a) { return { s*a.re, s*a.im }; }
static void test_linear_dv(void) {
    printf("\n=== Group: linear_dv (spectral linear terms, catenate) ===\n");
    enum { MX = 3, JX = 4, NTOT = MX*JX + 2, NX = MX*JX + 3, NK = MX + JX };
    const float tw = 0.35f;
    int32_t kmjx[MX], kmjxx[MX], ksq[NK];
    for (int m = 0; m < MX; m++) { kmjx[m] = m*JX; kmjxx[m] = m*(JX+1); }
    for (int i = 0; i < NK; i++) ksq[i] = i*i + 2;
    float epsi[NX];
    for (int i = 0; i < NX; i++) epsi[i] = 0.1f + 0.03f*i;
    lin_cplx c[NTOT], p[NTOT], u[NX], v[NX], ctin[NTOT], e[NTOT], ptin[NTOT];
    for (int i = 0; i < NTOT; i++) {
        c[i] = { 0.2f + 0.01f*i, -0.1f + 0.02f*i }; p[i] = { 0.5f - 0.02f*i, 0.03f*i };
        ctin[i] = { 0.05f*i, 0.3f - 0.01f*i }; e[i] = { 0.15f + 0.02f*i, -0.05f*i };
        ptin[i] = { 0.4f - 0.01f*i, 0.02f + 0.02f*i };
    }
    for (int i = 0; i < NX; i++) { u[i] = { 0.1f*i, 0.07f - 0.01f*i }; v[i] = { 0.25f - 0.015f*i, 0.04f*i }; }
    lin_cplx wpt[MX*JX], wct[MX*JX];
    int o = 0;
    for (int m = 1; m <= MX; m++) for (int j = 1; j <= JX; j++, o++) {
        int l = j + m - 2;
        float kl = (float)ksq[l];
        int jm = kmjx[m-1] + j, jmx = kmjxx[m-1] + j;
        lin_cplx zero = { 0, 0 };
        lin_cplx pj1 = (j == JX) ? zero : p[jm], cj1 = (j == JX) ? zero : c[jm];
        lin_cplx pjm1 = (j == 1) ? zero : p[jm-2], cjm1 = (j == 1) ? zero : c[jm-2];
        wpt[o] = lin_sub(ptin[jm-1], lin_rm(tw, lin_add(lin_rm(epsi[jmx-1], cjm1),
                     lin_add(lin_rm(epsi[jmx], cj1), v[jmx-1]))));
        wct[o] = lin_add(ctin[jm-1], lin_add(lin_rm(tw, lin_sub(lin_add(lin_rm(epsi[jmx-1], pjm1),
                     lin_rm(epsi[jmx], pj1)), u[jmx-1])), lin_rm(0.5f*kl, e[jm-1])));
    }
    LINEAR_results r = func_MAIN(MX, JX, lin_mki(kmjx, MX, 1), lin_mki(kmjxx, MX, 1), lin_mki(ksq, NK, 0),
                                 tw, lin_mkf(epsi, NX), lin_mkc(c, NTOT), lin_mkc(p, NTOT),
                                 lin_mkc(u, NX), lin_mkc(v, NX), lin_mkc(ctin, NTOT),
                                 lin_mkc(e, NTOT), lin_mkc(ptin, NTOT));
    auto cka = [](sisal_array_t a, const lin_cplx* w) {
        int ok = (int)a.size == MX*JX;
        for (int i = 0; ok && i < MX*JX; i++) {
            lin_cplx g = ((lin_cplx*)a.data)[i];
            ok = fabsf(g.re - w[i].re) <= 1e-6f*fmaxf(1.0f, fabsf(w[i].re))
              && fabsf(g.im - w[i].im) <= 1e-6f*fmaxf(1.0f, fabsf(w[i].im));
        }
        return ok;
    };
    check("pt (12 complex records)", cka(r.pt, wpt));
    check("ct (12 complex records)", cka(r.ct, wct));
}
#endif

#ifdef TEST_UVSPEC_DV
// U/V wind components from vorticity/divergence spectra: a 4-way IF/ELSEIF
// ladder multibinding NINE record values per point (truncation-edge zeros),
// deep Cmul/Cadd/Csub/Crmul chains, per-m CATENATE gathers.  Reference =
// C mirror.
struct uv_cplx { float re, im; };
static uv_cplx uv_add(uv_cplx a, uv_cplx b) { return { a.re + b.re, a.im + b.im }; }
static uv_cplx uv_sub(uv_cplx a, uv_cplx b) { return { a.re - b.re, a.im - b.im }; }
static uv_cplx uv_mul(uv_cplx a, uv_cplx b) { return { a.re*b.re - a.im*b.im, a.re*b.im + a.im*b.re }; }
static uv_cplx uv_rm(float s, uv_cplx a) { return { s*a.re, s*a.im }; }
static void test_uvspec_dv(void) {
    printf("\n=== Group: uvspec_dv (U/V spectral, 9-value elseif multibind) ===\n");
    enum { MX = 3, JX = 3, JXX = 4, NP = MX*JX, NE = MX*JXX + 1, NO = MX*JXX };
    float epsi[NE];
    for (int i = 0; i < NE; i++) epsi[i] = 0.2f + 0.05f*i;
    uv_cplx p[NP], c[NP];
    for (int i = 0; i < NP; i++) { p[i] = { 0.4f - 0.03f*i, 0.02f*i }; c[i] = { 0.1f + 0.02f*i, -0.05f + 0.01f*i }; }
    uv_cplx wu[NO], wv[NO];
    int o = 0;
    for (int m = 1; m <= MX; m++) {
        float realm = (float)(m - 1);
        for (int j = 1; j <= JXX; j++, o++) {
            int nreal = j + m - 2;
            float realn = (float)nreal, realn1 = realn + 1.0f;
            int jm = (m-1)*JX + j, jmx = (m-1)*JXX + j;
            uv_cplx zero = { 0, 0 };
            uv_cplx coeffd, coeffc, coeffu, pd, pc, pu, cd, cc, cu;
            if (j == 1) {
                coeffd = zero;
                coeffc = (nreal == 0) ? zero : uv_cplx{ 0.0f, realm/realn/realn1 };
                coeffu = { epsi[jmx]/realn1, 0.0f };
                pd = zero; pc = p[jm-1]; pu = p[jm]; cd = zero; cc = c[jm-1]; cu = c[jm];
            } else if (j == JX) {
                coeffd = { epsi[jmx-1]/realn, 0.0f };
                coeffc = { 0.0f, realm/realn/realn1 };
                coeffu = { epsi[jmx]/realn1, 0.0f };
                pd = p[jm-2]; pc = p[jm-1]; pu = zero; cd = c[jm-2]; cc = c[jm-1]; cu = zero;
            } else if (j == JXX) {
                coeffd = { epsi[jmx-1]/realn, 0.0f };
                coeffc = zero; coeffu = zero;
                pd = p[jm-2]; pc = zero; pu = zero; cd = c[jm-2]; cc = zero; cu = zero;
            } else {
                coeffd = { epsi[jmx-1]/realn, 0.0f };
                coeffc = { 0.0f, realm/realn/realn1 };
                coeffu = { epsi[jmx]/realn1, 0.0f };
                pd = p[jm-2]; pc = p[jm-1]; pu = p[jm]; cd = c[jm-2]; cc = c[jm-1]; cu = c[jm];
            }
            wu[o] = uv_add(uv_rm(-1.0f, uv_mul(coeffd, pd)), uv_sub(uv_mul(coeffu, pu), uv_mul(coeffc, cc)));
            wv[o] = uv_sub(uv_sub(uv_mul(coeffd, cd), uv_mul(coeffu, cu)), uv_mul(coeffc, pc));
        }
    }
    sisal_array_t E = sisal_array_alloc_empty(1, 8, NE); E.lower_bound[0] = 1;
    for (int i = 0; i < NE; i++) ((float*)E.data)[i] = epsi[i];
    sisal_array_t Pa = sisal_array_alloc_sized(1, 96, NP, sizeof(uv_cplx)); Pa.lower_bound[0] = 1;
    sisal_array_t Ca = sisal_array_alloc_sized(1, 96, NP, sizeof(uv_cplx)); Ca.lower_bound[0] = 1;
    for (int i = 0; i < NP; i++) { ((uv_cplx*)Pa.data)[i] = p[i]; ((uv_cplx*)Ca.data)[i] = c[i]; }
    UVSPEC_results r = func_MAIN(MX, JX, JXX, E, Pa, Ca);
    auto cka = [](sisal_array_t a, const uv_cplx* w) {
        int ok = (int)a.size == NO;
        for (int i = 0; ok && i < NO; i++) {
            uv_cplx g = ((uv_cplx*)a.data)[i];
            ok = fabsf(g.re - w[i].re) <= 1e-5f*fmaxf(1.0f, fabsf(w[i].re))
              && fabsf(g.im - w[i].im) <= 1e-5f*fmaxf(1.0f, fabsf(w[i].im));
        }
        return ok;
    };
    check("u (12 complex records)", cka(r.u, wu));
    check("v (12 complex records)", cka(r.v, wv));
}
#endif

#ifdef TEST_SPEC_DV
// SpecToFreqSphere: inverse Legendre transform (spectral -> per-latitude
// Fourier coefficients).  Rank-3 alp reads indexed by all three loop levels,
// four sum-reductions per point, inner same-name rebinds (pg, zg := ...)
// pinning the let-in body-scoping ruling in a 3-deep nest, rank-3 outputs
// (2, ilath, 2*mx).  Reference = C mirror.
enum { SPC_JX = 3, SPC_MX = 2, SPC_JXX = 4, SPC_ILATH = 2,
       SPC_NA = SPC_MX*SPC_JXX + 1, SPC_ATOT = 2*SPC_ILATH*SPC_NA,
       SPC_NPR = 2*(SPC_MX*SPC_JX + 1), SPC_NUR = 2*(SPC_MX*SPC_JXX + 1),
       SPC_MR = SPC_MX*2, SPC_OTOT = 2*SPC_ILATH*SPC_MR };
static sisal_array_t spc_mkf(const float* w, int n) {
    sisal_array_t a = sisal_array_alloc_empty(1, 8, n); a.lower_bound[0] = 1;
    for (int i = 0; i < n; i++) ((float*)a.data)[i] = w[i];
    return a;
}
static void test_spec_dv(void) {
    printf("\n=== Group: spec_dv (inverse Legendre transform, 4 rank-3 outputs) ===\n");
    int32_t kmjx[SPC_MX], kmjxx[SPC_MX];
    for (int m = 0; m < SPC_MX; m++) { kmjx[m] = m*SPC_JX; kmjxx[m] = m*SPC_JXX; }
    float alp[SPC_ATOT], pri[SPC_NPR], zri[SPC_NPR], uri[SPC_NUR], vri[SPC_NUR];
    for (int i = 0; i < SPC_ATOT; i++) alp[i] = 0.3f + 0.02f*i;
    for (int i = 0; i < SPC_NPR; i++) { pri[i] = 0.1f + 0.03f*i; zri[i] = 0.5f - 0.02f*i; }
    for (int i = 0; i < SPC_NUR; i++) { uri[i] = 0.2f + 0.01f*i; vri[i] = -0.1f + 0.02f*i; }
    float wpg[SPC_OTOT], wzg[SPC_OTOT], wug[SPC_OTOT], wvg[SPC_OTOT];
    int o = 0;
    for (int hemi = 1; hemi <= 2; hemi++) for (int lat = 1; lat <= SPC_ILATH; lat++)
        for (int mrmi = 1; mrmi <= SPC_MR; mrmi++, o++) {
            int m = (mrmi + 1)/2;
            float spg = 0, szg = 0, sug = 0, svg = 0;
            for (int j = 1; j <= SPC_JX; j++) {
                int jm = kmjx[m-1] + j, jmx = kmjxx[m-1] + j;
                int jmrjmi = jm*2 - (mrmi % 2);
                float a = alp[((hemi-1)*SPC_ILATH + (lat-1))*SPC_NA + (jmx-1)];
                if (!(m == 1 && j == 1)) { spg += a*pri[jmrjmi-1]; szg += a*zri[jmrjmi-1]; }
            }
            for (int j = 1; j <= SPC_JXX; j++) {
                int jmx = kmjxx[m-1] + j;
                int jmrjmi = jmx*2 - (mrmi % 2);
                float a = alp[((hemi-1)*SPC_ILATH + (lat-1))*SPC_NA + (jmx-1)];
                sug += a*uri[jmrjmi-1]; svg += a*vri[jmrjmi-1];
            }
            wpg[o] = spg; wzg[o] = szg; wug[o] = sug; wvg[o] = svg;
        }
    sisal_array_t K1 = sisal_array_alloc_empty(1, 6, SPC_MX); K1.lower_bound[0] = 1;
    sisal_array_t K2 = sisal_array_alloc_empty(1, 6, SPC_MX); K2.lower_bound[0] = 1;
    for (int i = 0; i < SPC_MX; i++) { ((int32_t*)K1.data)[i] = kmjx[i]; ((int32_t*)K2.data)[i] = kmjxx[i]; }
    sisal_array_t A = sisal_array_alloc_empty(3, 8, SPC_ATOT);
    A.dims[0] = 2; A.dims[1] = SPC_ILATH; A.dims[2] = SPC_NA;
    A.lower_bound[0] = A.lower_bound[1] = A.lower_bound[2] = 1;
    for (int i = 0; i < SPC_ATOT; i++) ((float*)A.data)[i] = alp[i];
    SPEC_results r = func_MAIN(SPC_JX, SPC_MX, SPC_JXX, SPC_ILATH, 4, K1, K2, A,
                               spc_mkf(pri, SPC_NPR), spc_mkf(zri, SPC_NPR),
                               spc_mkf(uri, SPC_NUR), spc_mkf(vri, SPC_NUR));
    auto cka = [](sisal_array_t a, const float* w) {
        int ok = (int)a.size == SPC_OTOT && a.rank == 3
              && (int)a.dims[0] == 2 && (int)a.dims[1] == SPC_ILATH && (int)a.dims[2] == SPC_MR;
        for (int i = 0; ok && i < SPC_OTOT; i++)
            ok = fabsf(((float*)a.data)[i] - w[i]) <= 1e-5f*fmaxf(1.0f, fabsf(w[i]));
        return ok;
    };
    check("pg", cka(r.pg, wpg));
    check("zg", cka(r.zg, wzg));
    check("ug", cka(r.ug, wug));
    check("vg", cka(r.vg, wvg));
}
#endif

#ifdef TEST_NOISE_DV
// Binary-image noise removal: 5x5 neighborhood stencil clearing isolated
// 1-pixels — 27 distinct 2-index reads per point through boolean elseif
// ladders; interior-only iteration shrinks the result to (R-4, C-4).
// Reference = C mirror on a PRNG 0/1 image.
static void test_noise_dv(void) {
    printf("\n=== Group: noise_dv (5x5 despeckle stencil) ===\n");
    enum { R = 8, C = 9 };
    int32_t m[R*C];
    unsigned sd = 12345;
    for (int i = 0; i < R*C; i++) { sd = sd*1103515245u + 12345u; m[i] = (sd >> 16) & 1; }
    auto g = [&](int i, int y) { return m[(i-1)*C + (y-1)]; };
    int32_t want[(R-4)*(C-4)];
    int o = 0;
    for (int I = 3; I <= R-2; I++) for (int Y = 3; Y <= C-2; Y++, o++) {
        int nos1, nos2, nos3;
        if (g(I,Y) == 1) {
            if (g(I-1,Y+1) == 1) nos1 = !(g(I+1,Y-1) + g(I-2,Y+2) >= 1);
            else if (g(I+1,Y-1) + g(I+2,Y-2) == 2) nos1 = 0;
            else nos1 = 1;
        } else nos1 = 0;
        if (g(I,Y) == 1) {
            if (g(I+1,Y+1) == 1) nos2 = !(g(I-1,Y-1) + g(I+2,Y+2) >= 1);
            else if (g(I-1,Y-1) + g(I-2,Y-2) == 2) nos2 = 0;
            else nos2 = 1;
        } else nos2 = 0;
        if (g(I,Y) == 1) {
            if (g(I+1,Y-1)+g(I+2,Y)+g(I+1,Y)+g(I+1,Y+1) == 4) nos3 = 0;
            else if (g(I-1,Y-1)+g(I-2,Y)+g(I-1,Y)+g(I-1,Y+1) == 4) nos3 = 0;
            else if (g(I,Y+1)+g(I,Y+2)+g(I-1,Y+1)+g(I+1,Y+1) == 4) nos3 = 0;
            else if (g(I-1,Y-1)+g(I+1,Y-1)+g(I,Y-1)+g(I,Y-2) == 4) nos3 = 0;
            else if (g(I+1,Y)+g(I-1,Y)+g(I,Y+1)+g(I,Y-1) == 4) nos3 = 0;
            else nos3 = 1;
        } else nos3 = 0;
        want[o] = (nos1 && nos2 && nos3) ? 0 : g(I,Y);
    }
    sisal_array_t A = sisal_array_alloc_empty(2, 6, R*C);
    A.dims[0] = R; A.dims[1] = C; A.lower_bound[0] = A.lower_bound[1] = 1;
    for (int i = 0; i < R*C; i++) ((int32_t*)A.data)[i] = m[i];
    sisal_array_t r = func_MAIN(A, R, C);
    int ok = (int)r.size == (R-4)*(C-4) && r.rank == 2
          && (int)r.dims[0] == R-4 && (int)r.dims[1] == C-4;
    for (int i = 0; ok && i < (R-4)*(C-4); i++) ok = ((int32_t*)r.data)[i] == want[i];
    check("despeckled interior (4,5) == mirror", ok);
}
#endif

#ifdef TEST_TST_LOOPX_DV
// Hydro fragment, rank-3 cross: pins a PERMUTED 3-index read (w[K,J,I]) and
// a non-1 lower bound on the outer gather axis (I in 4,n -> lb (4,1,1)).
// Reference = C mirror.
static void test_tst_loopx_dv(void) {
    printf("\n=== Group: tst_loopx_dv (rank-3 permuted read, lb=4 axis) ===\n");
    enum { N = 6, M = 3, TOT = N*M*N };
    sisal_array_t Y = sisal_array_alloc_empty(3, 4, TOT);
    Y.dims[0] = N; Y.dims[1] = M; Y.dims[2] = N;
    Y.lower_bound[0] = Y.lower_bound[1] = Y.lower_bound[2] = 1;
    sisal_array_t W = Y, U = Y;
    W.data = malloc(TOT*8); U.data = malloc(TOT*8);
    for (int i = 0; i < TOT; i++) {
        ((double*)Y.data)[i] = 1.0 + 0.01*i;
        ((double*)W.data)[i] = 2.0 + 0.01*i;
        ((double*)U.data)[i] = 3.0 + 0.01*i;
    }
    double *y = (double*)Y.data, *w = (double*)W.data, *u = (double*)U.data;
    auto at = [&](double* p, int i, int j, int k) { return p[((i-1)*M + (j-1))*N + (k-1)]; };
    LOOPX_results r = func_MAIN(N, M, Y, W, U);
    int on = N - 3;
    int ok1 = (int)r.a.size == on*M*N && r.a.rank == 3 && (int)r.a.lower_bound[0] == 4
           && (int)r.a.dims[0] == on && (int)r.a.dims[1] == M && (int)r.a.dims[2] == N;
    int ok2 = (int)r.b.size == on*M*N && (int)r.b.lower_bound[0] == 4;
    int o = 0;
    for (int I = 4; I <= N && ok1; I++) for (int J = 1; J <= M; J++) for (int K = 1; K <= N; K++, o++) {
        ok1 = ok1 && fabs(((double*)r.a.data)[o] - at(y,I,J,K)*at(w,K,J,I)) < 1e-12;
        ok2 = ok2 && fabs(((double*)r.b.data)[o] - (at(y,I,J,K) - at(u,I,J,K))) < 1e-12;
    }
    check("Y[I,J,K]*w[K,J,I] (lb 4,1,1)", ok1);
    check("Y - u elementwise", ok2);
}
#endif
#ifdef TEST_TST_LOOPX2_DV
// Hydro fragment rank 2: inner axis starts at 2 (result lb (1,2)).
static void test_tst_loopx2_dv(void) {
    printf("\n=== Group: tst_loopx2_dv (rank-2, lb=2 inner axis) ===\n");
    enum { N = 4, M = 5, TOT = N*M };
    sisal_array_t Y = sisal_array_alloc_empty(2, 4, TOT);
    Y.dims[0] = N; Y.dims[1] = M; Y.lower_bound[0] = Y.lower_bound[1] = 1;
    for (int i = 0; i < TOT; i++) ((double*)Y.data)[i] = 0.5 + 0.03*i;
    double* y = (double*)Y.data;
    LOOPX2_results r = func_MAIN(N, M, Y);
    int ok = (int)r.a.size == N*(M-1) && r.a.rank == 2
          && (int)r.a.lower_bound[0] == 1 && (int)r.a.lower_bound[1] == 2
          && (int)r.a.dims[0] == N && (int)r.a.dims[1] == M-1
          && (int)r.b.lower_bound[1] == 2;
    int o = 0;
    for (int K = 1; K <= N && ok; K++) for (int J = 2; J <= M; J++, o++) {
        double v = y[(K-1)*M + (J-1)];
        ok = fabs(((double*)r.a.data)[o] - v*v) < 1e-12 && fabs(((double*)r.b.data)[o]) < 1e-12;
    }
    check("Y*Y and Y-Y with lb (1,2)", ok);
}
#endif
#ifdef TEST_INSERTION2_DV
// Insertion sort with early-exit inner walk: nested for-initial whiles, a
// two-value multibind mixing a multi-value replace swap against identity.
// Reference = qsort.
static int ins2_cmp(const void* a, const void* b) {
    double x = *(const double*)a, y = *(const double*)b;
    return (x > y) - (x < y);
}
static void ins2_case(const char* label, const double* v, int n) {
    double ref[16]; for (int i = 0; i < n; i++) ref[i] = v[i];
    qsort(ref, n, sizeof(double), ins2_cmp);
    sisal_array_t A = sisal_array_alloc_empty(1, 4, n); A.lower_bound[0] = 1;
    for (int i = 0; i < n; i++) ((double*)A.data)[i] = v[i];
    sisal_array_t r = func_MAIN(n, A);
    int ok = (int)r.size == n;
    for (int i = 0; ok && i < n; i++) ok = fabs(((double*)r.data)[i] - ref[i]) < 1e-12;
    check(label, ok);
}
static void test_insertion2_dv(void) {
    printf("\n=== Group: insertion2_dv (early-exit insertion sort, doubles) ===\n");
    const double a[8] = { 9.5, -3.25, 14.0, 0.5, 7.75, 7.75, -12.0, 5.25 };
    const double b[5] = { 5.5, 1.25, 4.0, 1.25, 3.5 };
    ins2_case("sort 8 doubles (dups) == qsort", a, 8);
    ins2_case("sort 5 doubles (dups) == qsort", b, 5);
}
#endif

#ifdef TEST_INSERT_DV
// Classic shift-and-insert insertion sort (save Y, shift prefix up while
// Y < X[I], insert once at the hole).  Pins array-valued `value of`
// (FinalValue of an ARRAY carry) plus a mixed (array, integer) FinalValue
// pair from the inner loop.  The original's OneDime/OneDim typo is fixed in
// the port (declaration now matches use).  Reference = qsort.
static int ins_cmp(const void* a, const void* b) {
    double x = *(const double*)a, y = *(const double*)b;
    return (x > y) - (x < y);
}
static void ins_case(const char* label, const double* v, int n) {
    double ref[16]; for (int i = 0; i < n; i++) ref[i] = v[i];
    qsort(ref, n, sizeof(double), ins_cmp);
    sisal_array_t A = sisal_array_alloc_empty(1, 4, n); A.lower_bound[0] = 1;
    for (int i = 0; i < n; i++) ((double*)A.data)[i] = v[i];
    sisal_array_t r = func_MAIN(n, A);
    int ok = (int)r.size == n;
    for (int i = 0; ok && i < n; i++) ok = fabs(((double*)r.data)[i] - ref[i]) < 1e-12;
    check(label, ok);
}
static void test_insert_dv(void) {
    printf("\n=== Group: insert_dv (shift-and-insert insertion sort) ===\n");
    const double a[8] = { 9.5, -3.25, 14.0, 0.5, 7.75, 7.75, -12.0, 5.25 };
    const double b[5] = { 5.5, 1.25, 4.0, 1.25, 3.5 };
    ins_case("sort 8 doubles (dups) == qsort", a, 8);
    ins_case("sort 5 doubles (dups) == qsort", b, 5);
}
#endif

#ifdef TEST_TST_LOOPAT1_DV
// Strict dot lengths (53c0681): Good = corrected shifted-diagonal gather
// (I in 2,10 dot J in 1,9 — equal trip counts); Bad = the original
// malformed 9-vs-10 dot, pinned to take the conformance diamond's ERROR
// arm and yield the error value (empty result).
static void test_tst_loopat1_dv(void) {
    printf("\n=== Group: tst_loopat1_dv (strict dot-length diamond) ===\n");
    enum { N = 10, TOT = N*N };
    sisal_array_t Y = sisal_array_alloc_empty(2, 4, TOT);
    Y.dims[0] = N; Y.dims[1] = N; Y.lower_bound[0] = Y.lower_bound[1] = 1;
    for (int i = 0; i < TOT; i++) ((double*)Y.data)[i] = 0.25*(i + 1);
    double* y = (double*)Y.data;
    sisal_array_t g = func_MAIN(Y, 0);
    int ok = (int)g.size == 9;
    for (int k = 0; ok && k < 9; k++) {
        int I = 2 + k, J = 1 + k;
        ok = fabs(((double*)g.data)[k] - y[(J-1)*N + (I-1)]) < 1e-12;
    }
    check("equal dot: Y[J,I] shifted diagonal (9 values)", ok);
    sisal_array_t b = func_MAIN(Y, 1);
    check("mismatched dot (9 vs 10) yields the error value", (int)b.size == 0);
}
#endif

#ifdef TEST_TUPLE_DESTRUCTURE
// Parallel-copy binder Tuple items in BOTH spellings — #(x,y) := #(...)
// and tuple(x,y) := tuple(...) — plain, typed, chained.  Ground truth by
// construction.
static void test_tuple_destructure(void) {
    printf("\n=== Group: tuple_destructure (#() and tuple() binder forms) ===\n");
    TUD_pair s = func_TUPLE_SWAP(3, 7);
    TUD_pair t = func_TUPLE_TYPED(3, 7);
    TUD_pair ks = func_TUPLE_KW_SWAP(3, 7);
    TUD_pair kt = func_TUPLE_KW_TYPED(3, 7);
    check("#() swap (3,7) -> (7,3)", s.a == 7 && s.b == 3);
    check("#() typed (3,7) -> (4,8)", t.a == 4 && t.b == 8);
    check("#() chained sum3(3,7,10) == 20", func_TUPLE_SUM3(3, 7, 10) == 20);
    check("tuple() swap (3,7) -> (7,3)", ks.a == 7 && ks.b == 3);
    check("tuple() typed (3,7) -> (4,8)", kt.a == 4 && kt.b == 8);
    check("tuple() chained (3,7,10) == 20", func_TUPLE_KW_CHAIN(3, 7, 10) == 20);
}
#endif

#ifdef TEST_SIFUNCS
// The physics corpus's R-suffixed real wrappers over double intrinsics
// (real -> double_real -> intrinsic -> real).  Reference = libm.
static void test_sifuncs(void) {
    printf("\n=== Group: sifuncs (R-suffixed intrinsic wrappers) ===\n");
    float x = 0.6f;
    auto near = [](float got, double want) {
        return fabs((double)got - want) <= 1e-6*fmax(1.0, fabs(want));
    };
    check("ASINR", near(func_ASINR(x), asin((double)x)));
    check("ACOSR", near(func_ACOSR(x), acos((double)x)));
    check("SQRTR", near(func_SQRTR(x), sqrt((double)x)));
    check("SINR",  near(func_SINR(x),  sin((double)x)));
    check("COSR",  near(func_COSR(x),  cos((double)x)));
    check("ATANR", near(func_ATANR(x), atan((double)x)));
}
#endif

#ifdef TEST_ADA
// Forall keep-last FINALVALUE: `value of local` (no reduction op) over an
// inner counted loop returning the enclosing axis value.  By construction
// the result is [1..5].
static void test_ada(void) {
    printf("\n=== Group: ada (forall keep-last FinalValue) ===\n");
    sisal_array_t r = func_MAIN();
    int ok = (int)r.size == 5;
    for (int i = 0; ok && i < 5; i++) ok = ((int32_t*)r.data)[i] == i + 1;
    check("value of local over 1..5 == [1..5]", ok);
}
#endif
#ifdef TEST_PINSERT_DV
// Parallel insertion: each row of a rank-2 matrix sorted independently by
// the shift-and-insert Insertion over an A[i, ..] slice; the row gather
// box-flattens back to rank-2.  Reference = per-row qsort.
static int pins_cmp(const void* a, const void* b) {
    double x = *(const double*)a, y = *(const double*)b;
    return (x > y) - (x < y);
}
static void test_pinsert_dv(void) {
    printf("\n=== Group: pinsert_dv (per-row insertion sort of a matrix) ===\n");
    enum { M = 3, N = 6, TOT = M*N };
    double v[TOT];
    unsigned sd = 987;
    for (int i = 0; i < TOT; i++) { sd = sd*1103515245u + 12345u; v[i] = (double)((sd >> 16) % 1000)/8.0 - 50.0; }
    double ref[TOT]; for (int i = 0; i < TOT; i++) ref[i] = v[i];
    for (int r = 0; r < M; r++) qsort(ref + r*N, N, sizeof(double), pins_cmp);
    sisal_array_t A = sisal_array_alloc_empty(2, 4, TOT);
    A.dims[0] = M; A.dims[1] = N; A.lower_bound[0] = A.lower_bound[1] = 1;
    for (int i = 0; i < TOT; i++) ((double*)A.data)[i] = v[i];
    sisal_array_t r = func_MAIN(M, N, A);
    int ok = (int)r.size == TOT && r.rank == 2 && (int)r.dims[0] == M && (int)r.dims[1] == N;
    for (int i = 0; ok && i < TOT; i++) ok = fabs(((double*)r.data)[i] - ref[i]) < 1e-12;
    check("each row sorted == per-row qsort", ok);
}
#endif
#ifdef TEST_ALPHABETA_DV
// Job Shop Scheduler segment times: iterates a record dv (SRec jobs), builds
// per-job rows of Element records — the suite's first RANK-2 RECORD result
// (box-flatten with sized elements) — plus a parallel real gather (Del).
// Reference = C mirror.
struct ab_srec { float start, finish, duration; int32_t prio; };
struct ab_elem { float alpha, beta; int32_t prio; };
static void test_alphabeta_dv(void) {
    printf("\n=== Group: alphabeta_dv (rank-2 record result) ===\n");
    enum { NJ = 4, Q = 3 };
    ab_srec jobs[NJ];
    for (int i = 0; i < NJ; i++) jobs[i] = { 1.0f + 0.5f*i, 10.0f + 1.25f*i, 2.0f + 0.25f*i, 7 - i };
    ab_elem wab[NJ*(Q+1)]; float wdel[NJ];
    for (int j = 0; j < NJ; j++) {
        float last_start = jobs[j].finish - jobs[j].duration;
        float del = (last_start - jobs[j].start) / (float)Q;
        wdel[j] = del;
        for (int i = 1; i <= Q+1; i++) {
            float alpha = jobs[j].start + (float)(i-1)*del;
            wab[j*(Q+1) + (i-1)] = { alpha, alpha + jobs[j].duration, jobs[j].prio };
        }
    }
    sisal_array_t S = sisal_array_alloc_sized(1, 96, NJ, sizeof(ab_srec)); S.lower_bound[0] = 1;
    for (int i = 0; i < NJ; i++) ((ab_srec*)S.data)[i] = jobs[i];
    AB_results r = func_MAIN(S, Q);
    int ok1 = (int)r.ab.size == NJ*(Q+1) && r.ab.rank == 2
           && (int)r.ab.dims[0] == NJ && (int)r.ab.dims[1] == Q+1;
    for (int i = 0; ok1 && i < NJ*(Q+1); i++) {
        ab_elem g = ((ab_elem*)r.ab.data)[i];
        ok1 = fabsf(g.alpha - wab[i].alpha) < 1e-5f && fabsf(g.beta - wab[i].beta) < 1e-5f
           && g.prio == wab[i].prio;
    }
    int ok2 = (int)r.del.size == NJ;
    for (int i = 0; ok2 && i < NJ; i++) ok2 = fabsf(((float*)r.del.data)[i] - wdel[i]) < 1e-6f;
    check("AB (jobs, Q+1) record matrix == mirror", ok1);
    check("Del vector == mirror", ok2);
}
#endif

#ifdef TEST_TSTEP_DV
// Spectral leapfrog time step (Robert/Asselin filter): nine complex-record
// outputs multibound through nested IF regimes (izon passthrough /
// implicit-imp / first-step istart), nine gathers CATENATEd per m; ksq
// indexed from 0 (lb=0 dv).  Reference = C mirror; three regime cases.
struct ts_cplx { float re, im; };
enum { TS_JX=3, TS_MX=2, TS_NT=TS_MX*TS_JX, TS_NK=TS_JX+TS_MX-1 };
static ts_cplx ts_ca(ts_cplx a,ts_cplx b){return {a.re+b.re,a.im+b.im};}
static ts_cplx ts_cs(ts_cplx a,ts_cplx b){return {a.re-b.re,a.im-b.im};}
static ts_cplx ts_rm(float s,ts_cplx a){return {s*a.re,s*a.im};}
static ts_cplx ts_rs(ts_cplx a,float s){return {a.re-s,a.im};}
static ts_cplx ts_rd(ts_cplx a,float s){return {a.re/s,a.im/s};}
struct ts_In { ts_cplx c[TS_NT],p[TS_NT],z[TS_NT],cm[TS_NT],pm[TS_NT],zm[TS_NT],ct[TS_NT],pt[TS_NT],zt[TS_NT]; };
static void ts_mirror(const ts_In& I, int delt,int izon,int ifirst,int imp,int istart,
                   float hdiff,float hdrag,float zmean,float vnu,
                   const int* kmjx,const int* ksq0,const float* p1,
                   ts_cplx out[9][TS_NT]) {
  float deltt2 = (ifirst==0) ? (float)delt*2.0f : (float)delt;
  float deltt = deltt2*0.5f;
  ts_cplx zero{0,0};
  for (int m=1;m<=TS_MX;m++) for (int j=1;j<=TS_JX;j++) {
    int jm = kmjx[m-1]+j; int q = jm-1;
    float kl = (float)ksq0[j+m-2];
    float dkl = kl - 2.0f;
    ts_cplx c_j,p_j,z_j,cm_j,pm_j,zm_j,ct_j,pt_j,zt_j;
    if ((m==1 && izon==1) || jm==1) {
      c_j=I.c[q]; p_j=I.p[q]; z_j=I.z[q]; cm_j=I.cm[q]; pm_j=I.pm[q];
      zm_j=I.zm[q]; ct_j=I.ct[q]; pt_j=I.pt[q]; zt_j=I.zt[q];
    } else {
      ts_cplx ptjm = ts_cs(ts_cs(I.pt[q], ts_rm(dkl*hdiff, I.pm[q])), ts_rm(hdrag, ts_rs(I.pm[q], p1[q])));
      ts_cplx ctjm = ts_cs(I.ct[q], ts_rm(hdrag + dkl*hdiff, I.cm[q]));
      ts_cplx ztjm = ts_cs(I.zt[q], ts_rm(dkl*hdiff, I.zm[q]));
      ts_cplx ppv = ts_ca(I.pm[q], ts_rm(deltt2, I.pt[q]));
      ts_cplx ccv, zzv;
      if (imp==1) {
        ccv = ts_rd(ts_ca(I.cm[q], ts_rm(deltt2, ts_ca(ctjm, ts_rm(kl, ts_ca(I.zm[q], ts_rm(deltt,
                ts_cs(ztjm, ts_rm(0.5f*zmean, I.cm[q])))))))),
                1.0f + deltt*deltt*kl*zmean);
        zzv = ts_ca(I.zm[q], ts_rm(deltt2, ts_cs(ztjm, ts_rm(0.5f*zmean, ts_ca(I.cm[q], ccv)))));
      } else {
        ccv = ts_ca(I.cm[q], ts_rm(deltt2, ts_ca(ctjm, ts_rm(kl, I.z[q]))));
        zzv = ts_ca(I.zm[q], ts_rm(deltt2, ts_cs(ztjm, ts_rm(zmean, I.c[q]))));
      }
      ts_cplx pmjm,cmjm,zmjm,pjm,cjm,zjm;
      if (ifirst==0) {
        pmjm = ts_ca(I.p[q], ts_rm(vnu, ts_ca(ts_cs(I.pm[q], ts_rm(2.0f, I.p[q])), ppv)));
        cmjm = ts_ca(I.c[q], ts_rm(vnu, ts_ca(ts_cs(I.cm[q], ts_rm(2.0f, I.c[q])), ccv)));
        zmjm = ts_ca(I.z[q], ts_rm(vnu, ts_ca(ts_cs(I.zm[q], ts_rm(2.0f, I.z[q])), zzv)));
        pjm = ppv; cjm = ccv; zjm = zzv;
      } else {
        pmjm = I.pm[q]; cmjm = I.cm[q];
        zmjm = (istart==0) ? ts_rd(ctjm, -kl) : I.zm[q];
        pjm = ppv;
        cjm = (istart==0) ? zero : ccv;
        zjm = (istart==0) ? ts_rd(ctjm, -kl) : zzv;
      }
      c_j=cjm; p_j=pjm; z_j=zjm; cm_j=cmjm; pm_j=pmjm; zm_j=zmjm;
      ct_j=ctjm; pt_j=ptjm; zt_j=ztjm;
    }
    out[0][q]=c_j; out[1][q]=p_j; out[2][q]=z_j; out[3][q]=cm_j; out[4][q]=pm_j;
    out[5][q]=zm_j; out[6][q]=ct_j; out[7][q]=pt_j; out[8][q]=zt_j;
  }
}
static sisal_array_t ts_mkc(const ts_cplx* w) {
  sisal_array_t a = sisal_array_alloc_sized(1,96,TS_NT,sizeof(ts_cplx)); a.lower_bound[0]=1;
  for (int i=0;i<TS_NT;i++) ((ts_cplx*)a.data)[i]=w[i];
  return a;
}
static int ts_case(const char* nm, int izon,int ifirst,int imp,int istart) {
  const int delt=2;
  const float hdiff=0.01f, hdrag=0.02f, zmean=1.5f, vnu=0.05f;
  int kmjx[TS_MX], kmjxx[TS_MX]; int ksq0[TS_NK];
  for (int m=0;m<TS_MX;m++){ kmjx[m]=m*TS_JX; kmjxx[m]=m*(TS_JX+1); }
  for (int i=0;i<TS_NK;i++) ksq0[i]=i+2;
  float p1[TS_NT];
  for (int i=0;i<TS_NT;i++) p1[i]=0.1f+0.02f*i;
  ts_In I;
  for (int i=0;i<TS_NT;i++) {
    I.c[i]={0.2f+0.01f*i,-0.1f+0.02f*i}; I.p[i]={0.5f-0.02f*i,0.03f*i};
    I.z[i]={0.1f*i,0.4f-0.03f*i}; I.cm[i]={0.15f+0.02f*i,-0.05f*i};
    I.pm[i]={0.45f-0.01f*i,0.02f+0.01f*i}; I.zm[i]={0.05f*i,0.3f-0.02f*i};
    I.ct[i]={0.12f+0.03f*i,0.07f-0.01f*i}; I.pt[i]={0.33f-0.02f*i,0.04f*i};
    I.zt[i]={0.08f*i,0.22f+0.02f*i};
  }
  ts_cplx want[9][TS_NT];
  ts_mirror(I,delt,izon,ifirst,imp,istart,hdiff,hdrag,zmean,vnu,kmjx,ksq0,p1,want);
  sisal_array_t K1=sisal_array_alloc_empty(1,6,TS_MX), K2=sisal_array_alloc_empty(1,6,TS_MX), K3=sisal_array_alloc_empty(1,6,TS_NK);
  K1.lower_bound[0]=K2.lower_bound[0]=1; K3.lower_bound[0]=0;
  for (int i=0;i<TS_MX;i++){ ((int32_t*)K1.data)[i]=kmjx[i]; ((int32_t*)K2.data)[i]=kmjxx[i]; }
  for (int i=0;i<TS_NK;i++) ((int32_t*)K3.data)[i]=ksq0[i];
  sisal_array_t P1=sisal_array_alloc_empty(1,8,TS_NT); P1.lower_bound[0]=1;
  for (int i=0;i<TS_NT;i++) ((float*)P1.data)[i]=p1[i];
  TSTEP_results r = func_MAIN(TS_JX,TS_MX,delt,izon,ifirst,imp,istart,hdiff,hdrag,zmean,vnu,
                    K1,K2,K3,P1,
                    ts_mkc(I.c),ts_mkc(I.p),ts_mkc(I.z),ts_mkc(I.cm),ts_mkc(I.pm),ts_mkc(I.zm),
                    ts_mkc(I.ct),ts_mkc(I.pt),ts_mkc(I.zt));
  sisal_array_t got[9] = { r.c,r.p,r.z,r.cm,r.pm,r.zm,r.ct,r.pt,r.zt };
  int ok = r.ifirst_r==0;
  for (int a=0;a<9 && ok;a++) {
    ok = (int)got[a].size==TS_NT;
    for (int i=0;ok&&i<TS_NT;i++) {
      ts_cplx g=((ts_cplx*)got[a].data)[i];
      ok = fabsf(g.re-want[a][i].re)<=2e-5f*fmaxf(1.0f,fabsf(want[a][i].re))
        && fabsf(g.im-want[a][i].im)<=2e-5f*fmaxf(1.0f,fabsf(want[a][i].im));
    }
  }
  check(nm, ok);
  return ok;
}

static void test_tstep_dv(void) {
    printf("\n=== Group: tstep_dv (9-output leapfrog step, 3 regimes) ===\n");
    ts_case("leapfrog (ifirst=0, imp=1)", 1, 0, 1, 0);
    ts_case("first step istart=0 (imp=0)", 0, 1, 0, 0);
    ts_case("first step istart=1 (imp=1)", 0, 1, 1, 1);
}
#endif

#ifdef TEST_FREQ_DV
// FreqToSpecSphere: forward Legendre transform.  Rank-3 inputs, TEN rank-2
// symmetric/antisymmetric intermediates from one cross gather, a parity
// IF-ladder over 2-index reads, four sum reductions, per-m CATENATEs.
// Reference = C mirror.
enum { FQ_JX=3, FQ_MX=2, FQ_MX2=2*FQ_MX, FQ_ILATH=2, FQ_IY=2,
       FQ_NA=FQ_MX*(FQ_JX+1), FQ_F3=2*FQ_ILATH*FQ_MX2, FQ_OT=FQ_MX*FQ_JX*2 };
static float FQ_EF[FQ_F3],FQ_PUF[FQ_F3],FQ_PVF[FQ_F3],FQ_ZUF[FQ_F3],FQ_ZVF[FQ_F3];
static float FQ_ALP[FQ_ILATH*FQ_NA], FQ_WOCS[FQ_ILATH], FQ_EPSI[FQ_NA];
static int FQ_KMJX[FQ_MX], FQ_KMJXX[FQ_MX];
static float fq_f3(const float* p,int h,int l,int m){ return p[((h-1)*FQ_ILATH+(l-1))*FQ_MX2+(m-1)]; }
static void fq_mirror(float* octri,float* oeri,float* optri,float* oztri) {
  float eP[FQ_ILATH*FQ_MX2],puP[FQ_ILATH*FQ_MX2],pvP[FQ_ILATH*FQ_MX2],zuP[FQ_ILATH*FQ_MX2],zvP[FQ_ILATH*FQ_MX2];
  float eM[FQ_ILATH*FQ_MX2],puM[FQ_ILATH*FQ_MX2],pvM[FQ_ILATH*FQ_MX2],zuM[FQ_ILATH*FQ_MX2],zvM[FQ_ILATH*FQ_MX2];
  for (int l=1;l<=FQ_ILATH;l++) for (int m=1;m<=FQ_MX2;m++) {
    int q=(l-1)*FQ_MX2+(m-1);
    eP[q]=fq_f3(FQ_EF,1,l,m)+fq_f3(FQ_EF,2,l,m);   eM[q]=fq_f3(FQ_EF,1,l,m)-fq_f3(FQ_EF,2,l,m);
    puP[q]=fq_f3(FQ_PUF,1,l,m)+fq_f3(FQ_PUF,2,l,m); puM[q]=fq_f3(FQ_PUF,1,l,m)-fq_f3(FQ_PUF,2,l,m);
    pvP[q]=fq_f3(FQ_PVF,1,l,m)+fq_f3(FQ_PVF,2,l,m); pvM[q]=fq_f3(FQ_PVF,1,l,m)-fq_f3(FQ_PVF,2,l,m);
    zuP[q]=fq_f3(FQ_ZUF,1,l,m)+fq_f3(FQ_ZUF,2,l,m); zuM[q]=fq_f3(FQ_ZUF,1,l,m)-fq_f3(FQ_ZUF,2,l,m);
    zvP[q]=fq_f3(FQ_ZVF,1,l,m)+fq_f3(FQ_ZVF,2,l,m); zvM[q]=fq_f3(FQ_ZVF,1,l,m)-fq_f3(FQ_ZVF,2,l,m);
  }
  auto R2=[&](float* p,int l,int m){ return p[(l-1)*FQ_MX2+(m-1)]; };
  int o=0;
  for (int m=1;m<=FQ_MX;m++) {
    int mi=m*2, mr=mi-1, realm=m-1;
    for (int jj=1;jj<=FQ_JX*2;jj++,o++) {
      int j=(jj+1)/2;
      int jm=FQ_KMJX[m-1]+j;
      int jmrjmi=jm*2-(jj%2);
      int jmx=FQ_KMJXX[m-1]+j;
      float realn=(float)(j+m-2);
      float sc=0,se=0,sp=0,sz=0;
      for (int l=1;l<=FQ_ILATH;l++) {
        int ihem=FQ_IY+1-l;
        float gwplm=FQ_ALP[(l-1)*FQ_NA+(jmx-1)]*FQ_WOCS[ihem-1];
        float b=(float)realm*gwplm;
        float alpm=(j!=1)?FQ_ALP[(l-1)*FQ_NA+(jmx-2)]:0.0f;
        float alpp=FQ_ALP[(l-1)*FQ_NA+(jmx)];
        float a=((realn+1.0f)*FQ_EPSI[jmx-1]*alpm - realn*FQ_EPSI[jmx]*alpp)*FQ_WOCS[ihem-1];
        float c_,e_,p_,z_;
        if (!(j==1 && m==1)) {
          if (jm%2==0) {
            if (jmrjmi%2==0) {
              c_=a*R2(puP,l,mi)+b*R2(pvM,l,mr); e_=gwplm*R2(eM,l,mi);
              p_=a*R2(pvP,l,mi)-b*R2(puM,l,mr); z_=a*R2(zvP,l,mi)-b*R2(zuM,l,mr);
            } else {
              c_=a*R2(puP,l,mr)-b*R2(pvM,l,mi); e_=gwplm*R2(eM,l,mr);
              p_=a*R2(pvP,l,mr)+b*R2(puM,l,mi); z_=a*R2(zvP,l,mr)+b*R2(zuM,l,mi);
            }
          } else if (jmrjmi%2==0) {
            c_=a*R2(puM,l,mi)+b*R2(pvP,l,mr); e_=gwplm*R2(eP,l,mi);
            p_=a*R2(pvM,l,mi)-b*R2(puP,l,mr); z_=a*R2(zvM,l,mi)-b*R2(zuP,l,mr);
          } else {
            c_=a*R2(puM,l,mr)-b*R2(pvP,l,mi); e_=gwplm*R2(eP,l,mr);
            p_=a*R2(pvM,l,mr)+b*R2(puP,l,mi); z_=a*R2(zvM,l,mr)+b*R2(zuP,l,mi);
          }
        } else {
          c_=0.0f; p_=0.0f; z_=0.0f;
          e_=(jj==1)?R2(eP,l,1)*FQ_WOCS[ihem-1]*FQ_ALP[(l-1)*FQ_NA+0]:0.0f;
        }
        sc+=c_; se+=e_; sp+=p_; sz+=z_;
      }
      octri[o]=sc; oeri[o]=se; optri[o]=sp; oztri[o]=sz;
    }
  }
}
static sisal_array_t fq_mk1f(const float* w, int n) {
  sisal_array_t a=sisal_array_alloc_empty(1,8,n); a.lower_bound[0]=1;
  for (int i=0;i<n;i++) ((float*)a.data)[i]=w[i];
  return a;
}
static sisal_array_t fq_mk1i(const int* w, int n) {
  sisal_array_t a=sisal_array_alloc_empty(1,6,n); a.lower_bound[0]=1;
  for (int i=0;i<n;i++) ((int32_t*)a.data)[i]=w[i];
  return a;
}
static sisal_array_t fq_mk3(const float* w) {
  sisal_array_t a=sisal_array_alloc_empty(3,8,FQ_F3);
  a.dims[0]=2; a.dims[1]=FQ_ILATH; a.dims[2]=FQ_MX2;
  a.lower_bound[0]=a.lower_bound[1]=a.lower_bound[2]=1;
  for (int i=0;i<FQ_F3;i++) ((float*)a.data)[i]=w[i];
  return a;
}

static void test_freq_dv(void) {
    printf("\n=== Group: freq_dv (forward Legendre transform) ===\n");
    for (int m = 0; m < FQ_MX; m++) { FQ_KMJX[m] = m*FQ_JX; FQ_KMJXX[m] = m*(FQ_JX+1); }
    for (int i = 0; i < FQ_ILATH; i++) FQ_WOCS[i] = 0.4f + 0.1f*i;
    for (int i = 0; i < FQ_NA; i++) FQ_EPSI[i] = 0.15f + 0.04f*i;
    for (int i = 0; i < FQ_ILATH*FQ_NA; i++) FQ_ALP[i] = 0.2f + 0.03f*i;
    for (int i = 0; i < FQ_F3; i++) {
        FQ_EF[i] = 0.1f + 0.02f*i; FQ_PUF[i] = 0.5f - 0.03f*i; FQ_PVF[i] = -0.2f + 0.04f*i;
        FQ_ZUF[i] = 0.3f + 0.01f*i; FQ_ZVF[i] = 0.05f*i - 0.15f;
    }
    float wc[FQ_OT], we[FQ_OT], wp[FQ_OT], wz[FQ_OT];
    fq_mirror(wc, we, wp, wz);
    sisal_array_t AL = sisal_array_alloc_empty(2, 8, FQ_ILATH*FQ_NA);
    AL.dims[0] = FQ_ILATH; AL.dims[1] = FQ_NA; AL.lower_bound[0] = AL.lower_bound[1] = 1;
    for (int i = 0; i < FQ_ILATH*FQ_NA; i++) ((float*)AL.data)[i] = FQ_ALP[i];
    FREQ_results r = func_MAIN(FQ_JX, FQ_MX, FQ_MX2, FQ_ILATH, FQ_IY,
                               fq_mk1i(FQ_KMJX, FQ_MX), fq_mk1i(FQ_KMJXX, FQ_MX),
                               fq_mk1f(FQ_WOCS, FQ_ILATH), fq_mk1f(FQ_EPSI, FQ_NA), AL,
                               fq_mk3(FQ_EF), fq_mk3(FQ_PUF), fq_mk3(FQ_PVF),
                               fq_mk3(FQ_ZUF), fq_mk3(FQ_ZVF));
    auto cka = [](sisal_array_t a, const float* w) {
        int ok = (int)a.size == FQ_OT;
        for (int i = 0; ok && i < FQ_OT; i++)
            ok = fabsf(((float*)a.data)[i] - w[i]) <= 2e-5f*fmaxf(1.0f, fabsf(w[i]));
        return ok;
    };
    check("ctri", cka(r.ctri, wc));
    check("eri", cka(r.eri, we));
    check("ptri", cka(r.ptri, wp));
    check("ztri", cka(r.ztri, wz));
}
#endif

#ifdef TEST_COMPLEX_TYPES_E2E
// Built-in complex types: complex_float record construction/field access,
// BUILD_COMPLEX_SOA (record of two arrays) and BUILD_COMPLEX_AOS
// (array_dv[complex_float] zip).  Ground truth by construction.
static sisal_array_t ct_mkf(const float* w, int n) {
    sisal_array_t a = sisal_array_alloc_empty(1, 8, n); a.lower_bound[0] = 1;
    for (int i = 0; i < n; i++) ((float*)a.data)[i] = w[i];
    return a;
}
static void test_complex_types_e2e(void) {
    printf("\n=== Group: complex_types_e2e (complex records, SOA/AOS builders) ===\n");
    enum { N = 4 };
    ct_cfl c = func_T_MAKE_CFLOAT(2.5f, -1.25f);
    check("make/re/im roundtrip", c.re == 2.5f && c.im == -1.25f
          && func_T_RE(c) == 2.5f && func_T_IM(c) == -1.25f);
    float re[N] = { 1, 2, 3, 4 }, im[N] = { -1, -2, -3, -4 };
    ct_soa s = func_T_SOA_FLOAT(ct_mkf(re, N), ct_mkf(im, N));
    int ok = (int)s.re.size == N && (int)s.im.size == N;
    for (int i = 0; ok && i < N; i++)
        ok = ((float*)s.re.data)[i] == re[i] && ((float*)s.im.data)[i] == im[i];
    check("SOA bundle (record of arrays)", ok);
    sisal_array_t a = func_T_AOS_FLOAT(ct_mkf(re, N), ct_mkf(im, N));
    ok = (int)a.size == N;
    for (int i = 0; ok && i < N; i++) {
        ct_cfl e = ((ct_cfl*)a.data)[i];
        ok = e.re == re[i] && e.im == im[i];
    }
    check("AOS zip (array_dv[complex_float])", ok);
}
#endif
#ifdef TEST_VERIFY_NUMPY_BROADCAST
// NumPy-style broadcasting over dv doubles: trailing-axis alignment
// [2,3]+[3], unit-dimension expansion [10,1]+[1,5] -> [10,5], scalar
// broadcast, and multi-op lifting (A+B)*2-A.  Reference = C mirrors of the
// numpy rules.
static sisal_array_t vnb_mk2(int r, int c, double base, double step) {
    sisal_array_t a = sisal_array_alloc_empty(2, 4, r*c);
    a.dims[0] = r; a.dims[1] = c; a.lower_bound[0] = a.lower_bound[1] = 1;
    for (int i = 0; i < r*c; i++) ((double*)a.data)[i] = base + step*i;
    return a;
}
static sisal_array_t vnb_mk1(int n, double base, double step) {
    sisal_array_t a = sisal_array_alloc_empty(1, 4, n); a.lower_bound[0] = 1;
    for (int i = 0; i < n; i++) ((double*)a.data)[i] = base + step*i;
    return a;
}
static void test_verify_numpy_broadcast(void) {
    printf("\n=== Group: verify_numpy_broadcast (dv broadcasting rules) ===\n");
    sisal_array_t r1 = func_TEST_TRAILING(vnb_mk2(2, 3, 1.0, 0.5), vnb_mk1(3, 10.0, 1.0));
    int ok = (int)r1.size == 6 && r1.rank == 2 && (int)r1.dims[0] == 2 && (int)r1.dims[1] == 3;
    for (int i = 0; ok && i < 6; i++)
        ok = fabs(((double*)r1.data)[i] - ((1.0 + 0.5*i) + (10.0 + (i % 3)))) < 1e-12;
    check("[2,3] + [3] trailing-axis", ok);
    sisal_array_t r2 = func_TEST_UNIT_EXPANSION(vnb_mk2(10, 1, 0.0, 1.0), vnb_mk2(1, 5, 100.0, 10.0));
    ok = (int)r2.size == 50 && r2.rank == 2 && (int)r2.dims[0] == 10 && (int)r2.dims[1] == 5;
    for (int i = 0; ok && i < 50; i++) {
        int row = i/5, col = i%5;
        ok = fabs(((double*)r2.data)[i] - ((double)row + (100.0 + 10.0*col))) < 1e-12;
    }
    check("[10,1] + [1,5] -> [10,5] unit expansion", ok);
    sisal_array_t r3 = func_TEST_SCALAR_BROADCAST(7.5, vnb_mk2(3, 3, 0.5, 0.25));
    ok = (int)r3.size == 9 && r3.rank == 2;
    for (int i = 0; ok && i < 9; i++)
        ok = fabs(((double*)r3.data)[i] - (7.5 + 0.5 + 0.25*i)) < 1e-12;
    check("scalar + [3,3]", ok);
    sisal_array_t r4 = func_TEST_MULTI_OP(vnb_mk2(2, 3, 1.0, 1.0), vnb_mk2(2, 3, 0.5, 0.5));
    ok = (int)r4.size == 6;
    for (int i = 0; ok && i < 6; i++) {
        double a = 1.0 + i, b = 0.5 + 0.5*i;
        ok = fabs(((double*)r4.data)[i] - ((a + b)*2.0 - a)) < 1e-12;
    }
    check("(A+B)*2 - A multi-op lift", ok);
}
#endif
#ifdef TEST_RICARD_DV
// Reference C mirror of the ricard chromatography simulation (scaled config:
// N=315, NV=6000, KELUTE=350, IELUTE=20, OUT min-scan window 220..290).
static void test_ricard_dv(void) {
    printf("\n=== Group: ricard_dv (chromatography benchmark, flat 2-D array_dv) ===\n");
    enum { NV=6000, Nc=315, NSEG=46, KEL=350, IEL=20 };
    static double LNr[6][Nc+2], LT[6][Nc+2], L2[6][Nc+2], CEL[6][KEL+1];
    const double DX=0.02, XI[6]={0,0.8,0.54,0.54,0.54,0.54};
    const double AX1[6]={0,2.0e-2,6.0e-2,6.0e-2,6.0e-2,6.0e-2};
    const double GZ[6]={0,0.4038637706e-05,0.7454342552e-05,0.6623185565e-05,
                          0.0070055980e-05,0.1401119600e-05};
    const double RATIO=XI[2]/XI[1], DVc=XI[1]*DX/(double)IEL;
    double VEL[6], LAM[6];
    for (int m=1;m<=5;m++) {
        double v1=(1.0/XI[m])-(1.0/XI[1]);
        double ax=AX1[m]-0.5*v1*DX;
        VEL[m]=DVc*v1/DX; LAM[m]=DVc*ax/pow(DX,2.0);
    }
    const double VSEG=XI[1]*DX, F=20.6/3600.0;
    const double EK0=1.1e05, RDML=0.5, RAML=2.0*EK0*RDML, EKISOM=20.0;
    const double EKAPP=0.5*EK0/(1.0+EKISOM), RDML2=1.0, RAML2=EKAPP*RDML2;
    const double RRISOM=1.0e-03, RFISOM=EKISOM*RRISOM;
    const double C1=-RAML*DVc/F, C2=RDML*DVc/F, C3=RAML2*DVc/F,
                 C4=-RDML2*DVc/F, C5=RFISOM*DVc/F, C6=-RRISOM*DVc/F;
    for (int m=1;m<=5;m++) {                                     // FILLUP
        LNr[m][1]=0.0;
        for (int j=2;j<=NSEG;j++) LNr[m][j]=GZ[m];
        for (int j=NSEG+1;j<=Nc;j++) LNr[m][j]=0.0;
        for (int k=1;k<=KEL;k++) CEL[m][k]=0.0;
    }
    double VOL=0.0;
    for (int I=1;I<=NV;I++) {
        for (int m=1;m<=5;m++) {                                 // diffusion step -> LT
            LT[m][1]=0.0;
            LT[m][2]=LNr[m][2]+LAM[m]*(LNr[m][3]-LNr[m][2])-VEL[m]*LNr[m][2];
            for (int j=3;j<=Nc-1;j++)
                LT[m][j]=LNr[m][j]+LAM[m]*(LNr[m][j+1]-LNr[m][j]-LNr[m][j]+LNr[m][j-1])
                        -VEL[m]*(LNr[m][j]-LNr[m][j-1]);
            LT[m][Nc]=LNr[m][Nc]+LAM[m]*(LNr[m][Nc-1]-LNr[m][Nc]);
        }
        for (int m=1;m<=5;m++) L2[m][1]=0.0;                     // RUNKUT (RK4) -> L2
        for (int j=2;j<=Nc;j++) {
            double CLI=LT[1][j], CMI=LT[2][j], CMLI=LT[3][j], CML2I=LT[4][j], CISO=LT[5][j];
            double RKK1=C1*CMI*CLI+C2*CMLI;
            double RKL1=-(RKK1+C3*CMLI*CLI+C4*CML2I);
            double RKP1=RATIO*(RKK1+RKK1+RKL1);
            double RKM1=C5*CML2I+C6*CISO;
            double U=CLI+0.5*RKP1, W=CML2I+0.5*(-(RKK1+RKL1+RKM1)), XX=CMLI+0.5*RKL1;
            double RKK2=C1*(CMI+0.5*RKK1)*U+C2*XX;
            double RKL2=-(RKK2+C3*XX*U+C4*W);
            double RKP2=RATIO*(RKK2+RKK2+RKL2);
            double RKM2=C5*W+C6*(CISO+0.5*RKM1);
            double VV=CLI+0.5*RKP2, Y=CMLI+0.5*RKL2, Z=CML2I+0.5*(-(RKK2+RKL2+RKM2));
            double RKK3=C1*(CMI+0.5*RKK2)*VV+C2*Y;
            double RKL3=-(RKK3+C3*Y*VV+C4*Z);
            double RKP3=RATIO*(RKK3+RKK3+RKL3);
            double RKM3=C5*Z+C6*(CISO+0.5*RKM2);
            double Rr=CLI+RKP3, S=CMLI+RKL3, T=CML2I+(-(RKK3+RKL3+RKM3));
            double RKK4=C1*(CMI+RKK3)*Rr+C2*S;
            double RKL4=-(RKK4+C3*S*Rr+C4*T);
            double RKM4=C5*T+C6*(CISO+RKM3);
            double DELK=(RKK1+RKK2+RKK2+RKK3+RKK3+RKK4)/6.0;
            double DELL=(RKL1+RKL2+RKL2+RKL3+RKL3+RKL4)/6.0;
            double DELM=(RKM1+RKM2+RKM2+RKM3+RKM3+RKM4)/6.0;
            L2[1][j]=CLI+RATIO*(DELK+DELK+DELL);
            L2[2][j]=CMI+DELK;
            L2[3][j]=CMLI+DELL;
            L2[4][j]=CML2I-(DELK+DELL+DELM);
            L2[5][j]=CISO+DELM;
        }
        if ((I/IEL)*IEL == I) {                                  // RENUM
            int K=I/IEL; VOL=(double)K*VSEG;
            for (int m=1;m<=5;m++) CEL[m][K]=L2[m][Nc];
            for (int m=1;m<=5;m++) {
                LNr[m][1]=0.0; LNr[m][2]=0.0;
                for (int j=3;j<=Nc;j++) LNr[m][j]=L2[m][j-1];
            }
        } else {
            for (int m=1;m<=5;m++) for (int j=1;j<=Nc;j++) LNr[m][j]=L2[m][j];
        }
    }
    static double CTL[KEL+1], CTM[KEL+1];                        // OUT
    double TOTM=0, TOTML=0, TOTML2=0, TOTML2I=0;
    for (int j=1;j<=KEL;j++) {
        CTL[j]=CEL[1][j]+CEL[3][j]+2.0*CEL[4][j]+2.0*CEL[5][j];
        CTM[j]=CEL[2][j]+CEL[3][j]+CEL[4][j]+CEL[5][j];
        TOTM+=CEL[2][j]; TOTML+=CEL[3][j]; TOTML2+=CEL[4][j]; TOTML2I+=CEL[5][j];
    }
    double TOT=TOTM+TOTML+TOTML2+TOTML2I;
    double TOTMA=1.554870369e-05*0.486;
    double PERML=0, STOR=0, PERCENT=0, HL=0; int JSTOR=0;
    if (TOT != 0.0) {
        PERML=100.0*(TOTML+TOTML2+TOTML2I)/TOT;
        STOR=CTL[220]; JSTOR=220;
        for (int j=220;j<=290;j++)               // min-scan, keep-last on ties
            if (!(STOR < CTL[j])) { STOR=CTL[j]; JSTOR=j; }
        double T1=0,T2=0;
        for (int j=1;j<=KEL;j++) T1+=CTL[j];
        for (int j=1;j<=JSTOR;j++) T2+=CTL[j];
        PERCENT=100.0*T2/T1;
        HL=-log(2.0)*(double)JSTOR*0.016/(F*log(PERCENT/18.02233));
    }
    struct FUNC_MAIN_results r = func_MAIN();
    bool ok = true;
    auto eq=[&](double g,double ref){
        double m=fmax(fabs(g),fabs(ref));
        return m==0.0 || fabs(g-ref) <= 1e-9*m;
    };
    ok = ok && eq(r.res_0,VOL) && eq(r.res_3,TOTM) && eq(r.res_4,TOTML)
            && eq(r.res_5,TOTML2) && eq(r.res_6,TOTML2I) && eq(r.res_7,TOT)
            && eq(r.res_8,PERML) && eq(r.res_9,TOTMA) && (r.res_10==JSTOR)
            && eq(r.res_11,STOR) && eq(r.res_12,PERCENT) && eq(r.res_13,HL)
            && TOT != 0.0;                       // guard: run must not be degenerate
    check("ricard_dv scalars (VOL, totals, PERML, JSTOR, STOR, PERCENT, HL) == reference C", ok);
    bool okv = ((int)r.res_1.size==KEL) && ((int)r.res_2.size==KEL);
    for (int j=1; okv && j<=KEL; j++)
        okv = eq(((double*)r.res_1.data)[j-1],CTM[j]) && eq(((double*)r.res_2.data)[j-1],CTL[j]);
    check("ricard_dv CTM/CTL elution curves (350 pts) == reference C", okv);
    if (r.res_1.data) free(r.res_1.data);
    if (r.res_2.data) free(r.res_2.data);
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

#ifdef TEST_ARRAY_ADD_DV
static void test_array_add_dv(void) {
    printf("\n=== Group: array_add_dv (element-wise add, 0-based indexing; vs C reference) ===\n");
    const int n = 5;
    sisal_array_t a = sisal_array_alloc_empty(1, 8, n), b = sisal_array_alloc_empty(1, 8, n);
    a.lower_bound[0] = 0; b.lower_bound[0] = 0;   // the .sis loop runs 0 .. size-1
    for (int i = 0; i < n; i++) { ((float*)a.data)[i] = (float)(i*i + 1); ((float*)b.data)[i] = (float)(7*i - 3); }
    // reference C implementation
    float ref[n];
    for (int i = 0; i < n; i++) ref[i] = ((float*)a.data)[i] + ((float*)b.data)[i];
    sisal_array_t r = func_MAIN(a, b);
    bool ok = ((int)r.size == n);
    for (int i = 0; ok && i < n; i++) ok = (((float*)r.data)[i] == ref[i]);
    check("A + B matches C reference", ok);
    free(a.data); free(b.data); if (r.data) free(r.data);
}
#endif
#ifdef TEST_XFA_B4_REDUCE
static void test_xfa_b4_reduce(void) {
    printf("\n=== Group: xfa_b4_reduce (cross-forall sum; vs C reference) ===\n");
    int n = 5, m = 7; int32_t ref = 0;
    for (int i = 1; i <= n; i++) for (int j = 1; j <= m; j++) ref += i * j;
    check("sum i*j over cross matches C reference", func_MAIN(n, m) == ref);
}
#endif
#ifdef TEST_XFA_C4_DEP2
static void test_xfa_c4_dep2(void) {
    printf("\n=== Group: xfa_c4_dep2 (dependent cross `i in 1,n cross j in i,n`, Fortran-DO; vs C reference) ===\n");
    const int n = 6;
    // reference C implementation: triangular nest, row-major flat order
    int32_t ref[64]; int cnt = 0;
    for (int i = 1; i <= n; i++)
        for (int j = i; j <= n; j++) ref[cnt++] = i * j;
    sisal_array_t r = func_MAIN(n);
    check("flat rank-1, size = n*(n+1)/2",
          r.rank == 1 && (int)r.size == cnt && (int)r.dims[0] == cnt);
    bool ok = true;
    for (int k = 0; ok && k < cnt; k++) ok = (((int32_t*)r.data)[k] == ref[k]);
    check("i*j elements match C reference", ok);
    if (r.data) free(r.data);
}
#endif
#ifdef TEST_XFA_C5_DEP3
static void test_xfa_c5_dep3(void) {
    printf("\n=== Group: xfa_c5_dep3 (3-deep dependent cross, Fortran-DO; vs C reference) ===\n");
    const int n = 5;
    // reference C implementation: tetrahedral nest, row-major flat order
    int32_t ref[128]; int cnt = 0;
    for (int i = 1; i <= n; i++)
        for (int j = i; j <= n; j++)
            for (int k = j; k <= n; k++) ref[cnt++] = i + j + k;
    sisal_array_t r = func_MAIN(n);
    check("flat rank-1, size = C(n+2,3)",
          r.rank == 1 && (int)r.size == cnt && (int)r.dims[0] == cnt);
    bool ok = true;
    for (int k = 0; ok && k < cnt; k++) ok = (((int32_t*)r.data)[k] == ref[k]);
    check("i+j+k elements match C reference", ok);
    if (r.data) free(r.data);
}
#endif
#ifdef TEST_FORALL_GPU_DV
static void test_forall_gpu(void) {
    printf("\n=== Group: forall_gpu (negate gather Main_GPU; vs C reference) ===\n");
    const int n = 7;
    // reference C implementation
    float ref[n];
    for (int i = 0; i < n; i++) ref[i] = -(float)(i + 1);
    sisal_array_t r = func_MAIN_GPU(n);
    check("rank 1, size n", r.rank == 1 && (int)r.size == n);
    bool ok = true;
    for (int i = 0; ok && i < n; i++) ok = (((float*)r.data)[i] == ref[i]);
    check("-X elements match C reference", ok);
    if (r.data) free(r.data);
}
#endif
#ifdef TEST_MIX_ARRAY_DV_IF
static void test_mix_array_dv_if(void) {
    printf("\n=== Group: test_mix_array_dv_if (IF returning monolithic array + array_dv) ===\n");
    // both IF arms return (array[integer], array_dv[integer]) literals
    FUNC_MAIN_results a = func_MAIN(true);
    check("then-arm: array [1,2] and dv [10,20]",
          (int)a.r0.size == 2 && ((int32_t*)a.r0.data)[0] == 1
          && ((int32_t*)a.r0.data)[1] == 2
          && (int)a.r1.size == 2 && ((int32_t*)a.r1.data)[0] == 10
          && ((int32_t*)a.r1.data)[1] == 20);
    FUNC_MAIN_results b = func_MAIN(false);
    check("else-arm: array [0] and dv [0]",
          (int)b.r0.size == 1 && ((int32_t*)b.r0.data)[0] == 0
          && (int)b.r1.size == 1 && ((int32_t*)b.r1.data)[0] == 0);
    if (a.r0.data) free(a.r0.data);
    if (a.r1.data) free(a.r1.data);
    if (b.r0.data) free(b.r0.data);
    if (b.r1.data) free(b.r1.data);
}
#endif
#ifdef TEST_QUEENS_DV
// reference C: enumerate N-queens depth-first, columns left to right,
// candidate rows ascending -- the same order the Sisal recursion visits,
// so solutions compare element-for-element.
static int q_nref = 0;
static int q_refsol[1024][8];
static void q_enum(int n, int col, int *rows) {
    if (col == n) {
        for (int c = 0; c < n; c++) q_refsol[q_nref][c] = rows[c];
        q_nref++;
        return;
    }
    for (int r = 1; r <= n; r++) {
        bool ok = true;
        for (int c = 0; c < col && ok; c++)
            ok = (rows[c] != r && rows[c] + (c+1) != r + (col+1)
                  && rows[c] - (c+1) != r - (col+1));
        if (ok) { rows[col] = r; q_enum(n, col+1, rows); }
    }
}
static void test_8queens_dv(void) {
    printf("\n=== Group: 8queens_dv (rank-2 solution slab, COMPRESS + catenate; vs C reference) ===\n");
    for (int n = 4; n <= 8; n++) {
        q_nref = 0; int rows[8];
        q_enum(n, 0, rows);
        sisal_array_t s = func_MAIN(n);
        bool ok = (s.rank == 2 && (int)s.dims[0] == q_nref && (int)s.dims[1] == n
                   && (int)s.size == q_nref * n);
        for (int k = 0; ok && k < q_nref; k++)
            for (int c = 0; ok && c < n; c++)
                ok = (((int32_t*)s.data)[k*n + c] == q_refsol[k][c]);
        char label[64];
        snprintf(label, sizeof label, "n=%d: %d solutions match C reference", n, q_nref);
        check(label, ok);
        if (s.data) free(s.data);
    }
}
#endif
#ifdef TEST_GAUSSJ_PERM_DV
static void test_gaussj_perm_dv(void) {
    printf("\n=== Group: gaussj_perm_dv (Gauss-Jordan, permutation-free pivoting, float; vs C reference) ===\n");
    // Also the regression test for the for-initial FinalVal ZERO-TRIP bug:
    // find_pivot(N,N,..) never enters its while loop and must return the
    // INIT seed (the MERGE carry), not a zeroed bodycap.
    const int N = 4;
    double Ad[N][N] = {{2,1,-1,3},{-3,-1,2,-11},{-2,1,2,-3},{1,2,3,4}};
    double bd[N]    = {13, -34, -4, 20};
    // reference C: Gaussian elimination, partial pivoting, back-substitution
    double M[N][N+1];
    for (int i=0;i<N;i++){ for(int j=0;j<N;j++) M[i][j]=Ad[i][j]; M[i][N]=bd[i]; }
    for (int k=0;k<N;k++){
        int p=k; for(int i=k+1;i<N;i++) if (fabs(M[i][k])>fabs(M[p][k])) p=i;
        for(int j=0;j<=N;j++){ double t=M[k][j]; M[k][j]=M[p][j]; M[p][j]=t; }
        for(int i=0;i<N;i++) if(i!=k){ double f=M[i][k]/M[k][k];
            for(int j=k;j<=N;j++) M[i][j]-=f*M[k][j]; }
    }
    double ref[N]; for(int i=0;i<N;i++) ref[i]=M[i][N]/M[i][i];
    // inputs are array_dv[real] = FLOAT (tid 8)
    sisal_array_t A = sisal_array_alloc_empty(2, 8, N*N);
    A.dims[0]=N; A.dims[1]=N; A.lower_bound[0]=1; A.lower_bound[1]=1;
    for(int i=0;i<N;i++) for(int j=0;j<N;j++) ((float*)A.data)[i*N+j]=(float)Ad[i][j];
    sisal_array_t B = sisal_array_alloc_empty(1, 8, N);
    for(int i=0;i<N;i++) ((float*)B.data)[i]=(float)bd[i];
    sisal_array_t x = func_GAUSSJ_PERM(N, A, B);
    bool ok = (x.rank == 1 && (int)x.size == N);
    for (int i = 0; ok && i < N; i++)
        ok = fabs(((float*)x.data)[i] - ref[i]) < 1e-4;   // float arithmetic
    check("4x4 solve matches C reference (1e-4)", ok);
    free(A.data); free(B.data); if (x.data) free(x.data);
}
#endif
#ifdef TEST_FORINIT_HISTORY_DV
static void test_forinit_history_dv(void) {
    printf("\n=== Group: forinit_history_dv (1.2 history: seed = body_0 of the gather; vs C reference) ===\n");
    // reference C mirrors the SISAL 1.2 history model: the initial clause is
    // body_0, so the sequence is seed, then each body iteration's value.
    {
        const int n = 13;
        int32_t ref[16]; int cnt = 0;
        int i = 10;
        ref[cnt++] = i;                    // body_0: the seed
        while (i < n) { i = i + 1; ref[cnt++] = i; }
        sisal_array_t r = func_MAIN(n);
        bool ok = ((int)r.size == cnt);
        for (int k = 0; ok && k < cnt; k++) ok = (((int32_t*)r.data)[k] == ref[k]);
        check("n=13: gather = [10,11,12,13] (seed included)", ok);
        if (r.data) free(r.data);
    }
    {
        sisal_array_t r = func_MAIN(10);   // guard false on entry: zero body trips
        bool ok = ((int)r.size == 1 && ((int32_t*)r.data)[0] == 10);
        check("n=10 zero-trip: gather = [seed]", ok);
        if (r.data) free(r.data);
    }
    {
        // value-of zero-trip pin (was gaussj_perm's find_pivot(N,N) case
        // before its if-guard rewrite): reference C mirrors the history
        // model -- the seed, then a doubling per body iteration.
        int32_t ref0 = 42;                 // n=0: body never runs -> seed
        int32_t ref3;
        { int i = 42, k = 1; while (k <= 3) { k++; i *= 2; } ref3 = i; }
        check("value-of zero-trip = seed (42)", func_LAST_VAL(0) == ref0);
        check("value-of n=3 = last body value", func_LAST_VAL(3) == ref3);
    }
}
#endif
#ifdef TEST_MATMULT_DV
static void test_matmult_dv(void) {
    printf("\n=== Group: matmult_dv (rank-2 dv matmul across a call boundary; vs C reference) ===\n");
    const int X=2, Y=3, Z=2;
    double Av[X*Y] = {1,2,3, 4,5,6};
    double Bv[Y*Z] = {7,8, 9,10, 11,12};
    // reference C implementation
    double ref[X*Z];
    for (int i=0;i<X;i++) for (int j=0;j<Z;j++) {
        double s=0; for (int k=0;k<Y;k++) s += Av[i*Y+k]*Bv[k*Z+j];
        ref[i*Z+j]=s;
    }
    sisal_array_t A = sisal_array_alloc_empty(2, 4, X*Y);
    A.dims[0]=X; A.dims[1]=Y;
    for (int i=0;i<X*Y;i++) ((double*)A.data)[i]=Av[i];
    sisal_array_t B = sisal_array_alloc_empty(2, 4, Y*Z);
    B.dims[0]=Y; B.dims[1]=Z;
    for (int i=0;i<Y*Z;i++) ((double*)B.data)[i]=Bv[i];
    sisal_array_t r = func_MULTIPLY(X, Y, Z, A, B);
    bool ok = ((int)r.size == X*Z);
    for (int i=0;ok&&i<X*Z;i++) ok = fabs(((double*)r.data)[i]-ref[i])<1e-12;
    check("2x3 * 3x2 matches C reference", ok);
    free(A.data); free(B.data); if (r.data) free(r.data);
}
#endif
#ifdef TEST_MM_DV
static void test_mm_dv(void) {
    printf("\n=== Group: mm_dv (dv matmul of constant matrices; vs C reference) ===\n");
    const int n = 5;
    // reference C: every entry of the product is sum of n 1.1*1.1 terms (float)
    float acc = 0; for (int i=0;i<n;i++) acc += 1.1f*1.1f;
    check("rmc[1,1] matches C reference", fabsf(func_MAIN(n) - acc) < 1e-5f);
}
#endif
#ifdef TEST_TRANSPOSE_DV
static void test_transpose_dv(void) {
    printf("\n=== Group: transpose_dv (rank-2 dv transpose by permuted read; vs C reference) ===\n");
    const int N=2, M=3;
    double Av[N*M] = {1,2,3, 4,5,6};
    // reference C implementation
    double ref[M*N];
    for (int i=0;i<M;i++) for (int j=0;j<N;j++) ref[i*N+j] = Av[j*M+i];
    sisal_array_t A = sisal_array_alloc_empty(2, 4, N*M);
    A.dims[0]=N; A.dims[1]=M;
    for (int i=0;i<N*M;i++) ((double*)A.data)[i]=Av[i];
    sisal_array_t r = func_TRANSPOSE(N, M, A);
    bool ok = (r.rank==2 && (int)r.dims[0]==M && (int)r.dims[1]==N);
    for (int i=0;ok&&i<M*N;i++) ok = (((double*)r.data)[i]==ref[i]);
    check("2x3 -> 3x2, elements a[i,j]=b[j,i]", ok);
    free(A.data); if (r.data) free(r.data);
}
#endif
#ifdef TEST_SP_DV
static void test_sp_dv(void) {
    printf("\n=== Group: sp_dv (sparse matvec, 10 repeat-until iterations; vs C reference) ===\n");
    const int n = 5;
    float Av[4*n]; int32_t AJv[4*n]; float x0v[n], gv[n];
    for (int k=0;k<4;k++) for (int i=0;i<n;i++) {
        Av[k*n+i]  = 0.1f*(k+1) + 0.01f*i;
        AJv[k*n+i] = (i + k) % n + 1;          // 1-based column index
    }
    for (int i=0;i<n;i++) { x0v[i]=1.0f+i; gv[i]=0.5f*i; }
    // reference C: 10 iterations of x = g + sum_k A[k,i]*x[AJ[k,i]]
    float x[n], xn[n]; for (int i=0;i<n;i++) x[i]=x0v[i];
    for (int it=0;it<10;it++) {
        for (int i=0;i<n;i++) {
            float ax=0; for (int k=0;k<4;k++) ax += Av[k*n+i]*x[AJv[k*n+i]-1];
            xn[i]=gv[i]+ax;
        }
        for (int i=0;i<n;i++) x[i]=xn[i];
    }
    sisal_array_t A = sisal_array_alloc_empty(2, 8, 4*n);
    A.dims[0]=4; A.dims[1]=n;
    for (int i=0;i<4*n;i++) ((float*)A.data)[i]=Av[i];
    sisal_array_t AJ = sisal_array_alloc_empty(2, 6, 4*n);
    AJ.dims[0]=4; AJ.dims[1]=n;
    for (int i=0;i<4*n;i++) ((int32_t*)AJ.data)[i]=AJv[i];
    sisal_array_t x0 = sisal_array_alloc_empty(1, 8, n);
    for (int i=0;i<n;i++) ((float*)x0.data)[i]=x0v[i];
    sisal_array_t g = sisal_array_alloc_empty(1, 8, n);
    for (int i=0;i<n;i++) ((float*)g.data)[i]=gv[i];
    FUNC_MAIN_results r = func_MAIN(n, A, AJ, x0, g);
    bool ok = (r.res_0 == 10 && (int)r.res_1.size == n);
    for (int i=0;ok&&i<n;i++)
        ok = fabsf(((float*)r.res_1.data)[i]-x[i]) < 1e-3f * fabsf(x[i]);
    check("ncount=10 and final x matches C reference (rel 1e-3, float)", ok);
    free(A.data); free(AJ.data); free(x0.data); free(g.data);
    if (r.res_1.data) free(r.res_1.data);
}
#endif
#ifdef TEST_INVERSE_DV
static void test_inverse_dv(void) {
    printf("\n=== Group: inverse_dv (Gauss-Jordan matrix inverse, full pivoting, rank-2 dv; vs C reference) ===\n");
    const int N = 4;
    double Ad[N][N] = {{4,2,1,3},{2,5,2,1},{1,2,6,2},{3,1,2,7}};
    // reference C: Gauss-Jordan inverse with partial pivoting, in double
    double M[N][2*N];
    for (int i=0;i<N;i++) { for (int j=0;j<N;j++) M[i][j]=Ad[i][j];
        for (int j=0;j<N;j++) M[i][N+j] = (i==j) ? 1.0 : 0.0; }
    for (int k=0;k<N;k++) {
        int p=k; for (int i=k+1;i<N;i++) if (fabs(M[i][k])>fabs(M[p][k])) p=i;
        for (int j=0;j<2*N;j++) { double t=M[k][j]; M[k][j]=M[p][j]; M[p][j]=t; }
        double d = M[k][k];
        for (int j=0;j<2*N;j++) M[k][j] /= d;
        for (int i=0;i<N;i++) if (i!=k) {
            double f=M[i][k];
            for (int j=0;j<2*N;j++) M[i][j] -= f*M[k][j];
        }
    }
    sisal_array_t A = sisal_array_alloc_empty(2, 8, N*N);
    A.dims[0]=N; A.dims[1]=N; A.lower_bound[0]=1; A.lower_bound[1]=1;
    for (int i=0;i<N;i++) for (int j=0;j<N;j++) ((float*)A.data)[i*N+j]=(float)Ad[i][j];
    sisal_array_t r = func_FIND_INVERSE(A, N);
    bool ok = (r.rank == 2 && (int)r.size == N*N);
    for (int i=0;i<N && ok;i++) for (int j=0;j<N && ok;j++)
        ok = fabs(((float*)r.data)[i*N+j] - M[i][N+j]) < 1e-4;
    check("4x4 inverse matches C reference (1e-4, float)", ok);
    free(A.data); if (r.data) free(r.data);
}
#endif
#ifdef TEST_FLOAT_SCATTER_DV
static void test_float_scatter_dv(void) {
    printf("\n=== Group: float_scatter_dv (element scatter over array_dv[real]; vs C reference) ===\n");
    float vv[2] = {1.5f, 2.5f}, wv[1] = {10.0f};
    sisal_array_t v = sisal_array_alloc_empty(1, 8, 2);
    ((float*)v.data)[0] = vv[0]; ((float*)v.data)[1] = vv[1];
    sisal_array_t w = sisal_array_alloc_empty(1, 8, 1);
    ((float*)w.data)[0] = wv[0];
    sisal_array_t r = func_F(v, w);
    // reference C: g(x) = x + 1; r[i] = v[i] + 1 + w[1]
    bool ok = ((int)r.size == 2);
    for (int i = 0; i < 2 && ok; i++)
        ok = fabsf(((float*)r.data)[i] - (vv[i] + 1.0f + wv[0])) < 1e-6f;
    check("g(vel) + w[1] over float elements matches C reference", ok);
    free(v.data); free(w.data); if (r.data) free(r.data);
}
#endif
#ifdef TEST_BADFFT_DV
static void test_badfft_dv(void) {
    printf("\n=== Group: badfft_dv (Cooley-Tukey FFT over array_dv[complex record]; analytic reference) ===\n");
    // The .sis main is self-checking against the ANALYTIC reference: for the
    // signal sin(j*pi/8) of length n = 2^m, |F| at bins n/16 and n - n/16 is
    // exactly n/2.  Verified against OSC 13.0.3 (original badfft.sis -> T).
    for (int m = 4; m <= 7; m++) {
        char label[64];
        snprintf(label, sizeof label, "m=%d (n=%d): FFT peaks = n/2", m, 1 << m);
        check(label, func_MAIN(m));
    }
}
#endif
#ifdef TEST_SUB_R3_PERM
static void test_sub_r3_perm(void) {
    printf("\n=== Group: sub_r3_perm (rank-3 permuted subscript a[i,j,k]=b[k,j,i]; vs C reference) ===\n");
    // reference C: b[i,j,k] = i*100+j*10+k; a[1,2,3] = b[3,2,1]
    int32_t ref = 3*100 + 2*10 + 1;
    check("a[1,2,3] == b[3,2,1]", func_MAIN(3) == ref);
}
#endif
#ifdef TEST_SUB_R4_PERM
static void test_sub_r4_perm(void) {
    printf("\n=== Group: sub_r4_perm (rank-4 two-source permute; vs C reference) ===\n");
    // reference C: b[i,j,k,l]=i*1000+j*100+k*10+l; c[..]=i+j+k+l;
    // a[1,2,1,2] = b[2,1,1,2] + c[1,2,2,1]
    int32_t ref = (2*1000 + 1*100 + 1*10 + 2) + (1 + 2 + 2 + 1);
    check("a[1,2,1,2] == b[2,1,1,2] + c[1,2,2,1]", func_MAIN(2) == ref);
}
#endif
#ifdef TEST_SUB_R5_PERM
static void test_sub_r5_perm(void) {
    printf("\n=== Group: sub_r5_perm (rank-5 full index reverse; vs C reference) ===\n");
    // reference C: b[i,j,k,l,m]=i*10000+j*1000+k*100+l*10+m; a[1,2,3,1,2]=b[2,1,3,2,1]
    int32_t ref = 2*10000 + 1*1000 + 3*100 + 2*10 + 1;
    check("a[1,2,3,1,2] == b[2,1,3,2,1]", func_MAIN(3) == ref);
}
#endif
#ifdef TEST_IF_ARRAY_DV
static void test_if_array_dv(void) {
    printf("\n=== Group: test_if_array_dv (IF arms return dv literals) ===\n");
    sisal_array_t a = func_MAIN(true), b = func_MAIN(false);
    int32_t refa[3] = {1,2,3}, refb[3] = {4,5,6};
    bool ok = ((int)a.size == 3 && (int)b.size == 3);
    for (int i = 0; i < 3 && ok; i++)
        ok = (((int32_t*)a.data)[i] == refa[i] && ((int32_t*)b.data)[i] == refb[i]);
    check("then [1,2,3] / else [4,5,6]", ok);
    if (a.data) free(a.data);
    if (b.data) free(b.data);
}
#endif
#ifdef TEST_MIX_SCALAR_ARRAY_DV
static void test_mix_scalar_array_dv(void) {
    printf("\n=== Group: test_mix_scalar_array_dv (IF returning scalar + dv + real) ===\n");
    FUNC_MAIN_results a = func_MAIN(true), b = func_MAIN(false);
    int32_t refa[3] = {1,2,3};
    bool ok = (a.res_0 == 42 && (int)a.res_1.size == 3
               && fabsf(a.res_2 - 3.14f) < 1e-6f);
    for (int i = 0; i < 3 && ok; i++) ok = (((int32_t*)a.res_1.data)[i] == refa[i]);
    ok = ok && b.res_0 == 0 && (int)b.res_1.size == 1
         && ((int32_t*)b.res_1.data)[0] == 0 && b.res_2 == 0.0f;
    check("then (42,[1,2,3],3.14) / else (0,[0],0.0)", ok);
    if (a.res_1.data) free(a.res_1.data);
    if (b.res_1.data) free(b.res_1.data);
}
#endif
#ifdef TEST_IF_MULTI_ARRAY_DV
static void test_if_multi_array_dv(void) {
    printf("\n=== Group: test_if_multi_array_dv (IF returning dvi + dvd) ===\n");
    FUNC_MAIN_results a = func_MAIN(true), b = func_MAIN(false);
    int32_t refi[3] = {1,2,3};   double refd[3] = {1.1, 2.2, 3.3};
    int32_t refi2[2] = {10,20};  double refd2[2] = {10.1, 20.2};
    bool ok = ((int)a.res_0.size == 3 && (int)a.res_1.size == 3
               && (int)b.res_0.size == 2 && (int)b.res_1.size == 2);
    // 1e-5 tolerance: double literals are currently emitted through FLOAT
    // precision (the C printer suffixes every literal with 'f'), so 20.2d0
    // arrives as (double)20.2f = 20.200001.
    for (int i = 0; i < 3 && ok; i++)
        ok = (((int32_t*)a.res_0.data)[i] == refi[i]
              && fabs(((double*)a.res_1.data)[i] - refd[i]) < 1e-5);
    for (int i = 0; i < 2 && ok; i++)
        ok = (((int32_t*)b.res_0.data)[i] == refi2[i]
              && fabs(((double*)b.res_1.data)[i] - refd2[i]) < 1e-5);
    check("then ([1,2,3],[1.1,2.2,3.3]) / else ([10,20],[10.1,20.2])", ok);
    if (a.res_0.data) free(a.res_0.data);
    if (a.res_1.data) free(a.res_1.data);
    if (b.res_0.data) free(b.res_0.data);
    if (b.res_1.data) free(b.res_1.data);
}
#endif
#ifdef TEST_MULTI_ARRAY_IF_DV
static void test_multi_array_if_dv(void) {
    printf("\n=== Group: test_multi_array_if_dv (forall with IF body, dvd + dvi outputs; vs C reference) ===\n");
    const int n = 6;
    // reference C implementation
    double refd[n]; int32_t refi[n];
    for (int i = 1; i <= n; i++) {
        refd[i-1] = (i % 2 == 0) ? i * 1.5 : i * 0.5;
        refi[i-1] = i * i;
    }
    FUNC_MAIN_results r = func_MAIN(n);
    bool ok = ((int)r.res_0.size == n && (int)r.res_1.size == n);
    for (int i = 0; i < n && ok; i++)
        ok = (fabs(((double*)r.res_0.data)[i] - refd[i]) < 1e-9
              && ((int32_t*)r.res_1.data)[i] == refi[i]);
    check("dvd = i*1.5/i*0.5 and dvi = i*i match C reference", ok);
    if (r.res_0.data) free(r.res_0.data);
    if (r.res_1.data) free(r.res_1.data);
}
#endif
#ifdef TEST_UNION_ARRAY_IF_DV
static void test_union_array_if_dv(void) {
    printf("\n=== Group: test_union_array_if_dv (array_dv of tagged unions; vs C reference) ===\n");
    // ABI of the emitted union_un_<N>: {int32 tag; union {int32 I; double D};}
    // tag values: I-arm = 95, D-arm = 94 (see the emitted enum).
    struct un { int32_t tag; union { int32_t I; double D; } val; };
    const int n = 6;
    FUNC_MAIN_results r = func_MAIN(n);
    bool ok = ((int)r.res_0.size == n && (int)r.res_1.size == n
               && r.res_1.elem_bytes == sizeof(struct un));
    for (int i = 1; i <= n && ok; i++) {
        // reference C: even i -> 1.5*i and union[i: i]; odd -> 0.5*i and union[d: i]
        double refd = (i % 2 == 0) ? i * 1.5 : i * 0.5;
        ok = fabs(((double*)r.res_0.data)[i-1] - refd) < 1e-9;
        struct un u = ((struct un*)r.res_1.data)[i-1];
        if (ok) {
            if (i % 2 == 0) ok = (u.tag == 95 && u.val.I == i);
            else            ok = (u.tag == 94 && fabs(u.val.D - (double)i) < 1e-9);
        }
    }
    check("dvd values + union tags/payloads match C reference", ok);
    if (r.res_0.data) free(r.res_0.data);
    if (r.res_1.data) free(r.res_1.data);
}
#endif
#ifdef TEST_CPXFUNCS_DV
static void test_cpxfuncs_dv(void) {
    printf("\n=== Group: cpxfuncs_dv (complex records BY VALUE across calls; vs C reference) ===\n");
    struct cfx a = {3.0f, -4.0f}, b = {-1.5f, 2.0f};
    // reference C implementations
    struct cfx radd = {a.re+b.re, a.im+b.im}, rsub = {a.re-b.re, a.im-b.im};
    struct cfx rmul = {a.re*b.re - a.im*b.im, a.re*b.im + a.im*b.re};
    float den = b.re*b.re + b.im*b.im;
    struct cfx rdiv = {(a.re*b.re + a.im*b.im)/den, (a.im*b.re - a.re*b.im)/den};
    struct cfx rcj = {a.re, -a.im}, rng = {-a.re, -a.im};
    float rabs = 5.0f, rabs2 = 25.0f;
    struct cfx g;
    bool ok = true;
    #define EQ(x,y) (fabsf((x)-(y)) < 1e-5f)
    g = func_CADD(a,b);  ok = ok && EQ(g.re,radd.re) && EQ(g.im,radd.im);
    g = func_CSUB(a,b);  ok = ok && EQ(g.re,rsub.re) && EQ(g.im,rsub.im);
    g = func_CMUL(a,b);  ok = ok && EQ(g.re,rmul.re) && EQ(g.im,rmul.im);
    g = func_CDIV(a,b);  ok = ok && EQ(g.re,rdiv.re) && EQ(g.im,rdiv.im);
    g = func_CONJG(a);   ok = ok && EQ(g.re,rcj.re)  && EQ(g.im,rcj.im);
    g = func_CNEG(a);    ok = ok && EQ(g.re,rng.re)  && EQ(g.im,rng.im);
    ok = ok && EQ(func_CABS(a), rabs) && EQ(func_CABSSQR(a), rabs2);
    #undef EQ
    check("Cadd/Csub/Cmul/Cdiv/Conjg/Cneg/Cabs/CabsSqr match C reference", ok);
}
#endif
#ifdef TEST_ZERO_ARRAYS
static void test_zero_arrays(void) {
    printf("\n=== Group: zero_arrays (array literals per element type; vs C reference) ===\n");
    // Regression for the literal-builder bug: float (and any non-int32/double)
    // element literals were staged into a sisal_array_t[] -- miscompile.
    struct FUNC_MAIN_results r = func_MAIN(0);
    float rf[3] = {0, 0, 0}; double rd[3] = {0, 0, 0}; int32_t ri[3] = {0, 0, 0};
    bool ok = r.r0.size == 3 && r.r1.size == 3 && r.r2.size == 3;
    for (int i = 0; ok && i < 3; i++)
      ok = ((float*)r.r0.data)[i] == rf[i] && ((double*)r.r1.data)[i] == rd[i]
        && ((int32_t*)r.r2.data)[i] == ri[i];
    check("real/double/int literal arrays match C reference", ok);
}
#endif
#ifdef TEST_PICK_DV
static void test_pick_dv(void) {
    printf("\n=== Group: pick_dv (if/elseif with array_dv results; vs C reference) ===\n");
    const int n = 4;
    sisal_array_t a = sisal_array_alloc_empty(1, 6, n);
    for (int i = 0; i < n; i++) ((int32_t*)a.data)[i] = 3*i - 1;
    // reference C implementation of pick(mode, A)
    int32_t ref[3][n];
    for (int i = 0; i < n; i++) {
        int32_t v = ((int32_t*)a.data)[i];
        ref[0][i] = v; ref[1][i] = -v; ref[2][i] = 2*v;
    }
    bool ok = true;
    for (int m = 0; m < 3; m++) {
        sisal_array_t r = func_PICK(m, a);
        ok = ok && ((int)r.size == n);
        for (int i = 0; ok && i < n; i++) ok = (((int32_t*)r.data)[i] == ref[m][i]);
        if (r.data && r.data != a.data) free(r.data);
    }
    check("pick(0/1/2) matches C reference (identity/negate/double)", ok);
    free(a.data);
}
#endif

#ifdef TEST_ARRAY_SWAP_E2E
static void test_array_swap_e2e() {
  printf("\n=== Group: array_swap_e2e (synthetic array swap test) ===\n");
  int32_t dataA[] = {10, 20, 30};
  int32_t dataB[] = {100, 200};
  sisal_array_t A = sisal_array_alloc_empty(1, 6, 3);
  for (int i = 0; i < 3; i++) ((int32_t*)A.data)[i] = dataA[i];

  sisal_array_t B = sisal_array_alloc_empty(1, 6, 2);
  for (int i = 0; i < 2; i++) ((int32_t*)B.data)[i] = dataB[i];

  struct FUNC_MAIN_results res = func_MAIN(A, B);

  int size0 = (int)res.res_0.size;
  int size1 = (int)res.res_1.size;

  int32_t* ptr0 = (int32_t*)res.res_0.data;
  int32_t* ptr1 = (int32_t*)res.res_1.data;

  printf("Array 0 size=%d: [%d, %d]\n", size0, ptr0[0], ptr0[1]);
  printf("Array 1 size=%d: [%d, %d, %d]\n", size1, ptr1[0], ptr1[1], ptr1[2]);

  if (size0 == 2 && size1 == 3 &&
      ptr0[0] == 100 && ptr0[1] == 200 &&
      ptr1[0] == 10 && ptr1[1] == 20 && ptr1[2] == 30) {
    printf("ARRAY_SWAP_E2E: SUCCESS\n");
  } else {
    printf("ARRAY_SWAP_E2E: FAILED\n");
    exit(1);
  }
}
#endif
#if defined(TEST_QUICKSORT_DV) || defined(TEST_HEAPSORT_DV)
// Shared sort driver: build a 1-indexed array_dv, run func_MAIN, compare against
// std::sort of a copy.  quicksort exercises the masked-gather Split (array_dv of
// E when ...) + nested fn + recursion + ||; heapsort exercises nested-fn array
// carry + recursion where the nested params SHADOW captured outer vars of the
// same name (the capture-clobber this arc fixed).
static void run_sort_case(const char *tag, const int32_t *v, int n) {
  sisal_array_t a = sisal_array_alloc_empty(1, 6, (uint64_t)n);
  a.lower_bound[0] = 1; a.dims[0] = n;          // Sisal 1-indexed
  for (int i = 0; i < n; i++) ((int32_t*)a.data)[i] = v[i];
  int32_t ref[64];
  for (int i = 0; i < n; i++) ref[i] = v[i];
  std::sort(ref, ref + n);
  sisal_array_t r = func_MAIN(a);
  int ok = (int)r.size == n;
  for (int i = 0; ok && i < n; i++) ok = ((int32_t*)r.data)[i] == ref[i];
  check(tag, ok);
}
#endif
// A 40-element scramble with negatives, duplicates and a wide value range --
// the substantive stress case; std::sort is the reference so any input is fair.
static const int32_t sort_big40[] = {
   37, -12,  85,   4,  85,  -7,  63,  21,  -99,  50,
    0,  17,  63,  -1,  42,  99, -55,   8,   8,  -3,
   71,  30, -40,  12,  60,  60,   5, -88,  33,  19,
  -12,  77,  46,  -6,  91,  24,  24, -70,  15,  -2,
};
#ifdef TEST_QUICKSORT_DV
static void test_quicksort_dv() {
  printf("\n=== Group: quicksort_dv (masked-gather Split + recursion) ===\n");
  run_sort_case("quicksort 40 mixed +/- dups", sort_big40, 40);
  int32_t a[] = {5, 3, 8, 1, 9, 2, 7, 4, 6};
  run_sort_case("quicksort 9 shuffled", a, 9);
  int32_t b[] = {1};                    run_sort_case("quicksort singleton", b, 1);
  int32_t c[] = {2, 1};                 run_sort_case("quicksort pair", c, 2);
  int32_t d[] = {4, 4, 1, 4, 2, 4};     run_sort_case("quicksort duplicates", d, 6);
  int32_t e[] = {1, 2, 3, 4, 5};        run_sort_case("quicksort already sorted", e, 5);
  int32_t f[] = {5, 4, 3, 2, 1};        run_sort_case("quicksort reversed", f, 5);
}
#endif
#ifdef TEST_HEAPSORT_DV
static void test_heapsort_dv() {
  printf("\n=== Group: heapsort_dv (nested-fn capture/param shadow) ===\n");
  run_sort_case("heapsort 40 mixed +/- dups", sort_big40, 40);
  int32_t a[] = {5, 3, 8, 1, 9, 2, 7, 4, 6};
  run_sort_case("heapsort 9 shuffled", a, 9);
  int32_t d[] = {4, 4, 1, 4, 2, 4};     run_sort_case("heapsort duplicates", d, 6);
  int32_t e[] = {1, 2, 3, 4, 5, 6, 7};  run_sort_case("heapsort already sorted", e, 7);
  int32_t f[] = {7, 6, 5, 4, 3, 2, 1};  run_sort_case("heapsort reversed", f, 7);
}
#endif
#ifdef TEST_NESTED_CAPTURE_DV
// Nested functions capturing OUTER-SCOPE values (not their own args):
//   AddBase captures Main's n (parent); Inner captures Outer's base AND Main's n
//   (parent + grandparent).  Captured values are results computed earlier in the
//   let.  Regression for the capture/param-shadow fix: params must NOT be
//   clobbered, yet genuine captures (trailing boundary ports) must still flow.
static int nested_capture_ref(int n) {
  int seed = n * n;
  int a = seed + n;                              // AddBase(seed)
  int b = (seed + seed + n) + (1 + seed + n);    // Outer(seed) = Inner(seed)+Inner(1)
  return a + b;
}
static void test_nested_capture_dv() {
  printf("\n=== Group: nested_capture_dv (nested-fn outer-scope capture) ===\n");
  for (int n : {3, 5, 0, -4, 10, 100}) {
    char tag[64]; snprintf(tag, sizeof tag, "nested_capture n=%d", n);
    check(tag, func_MAIN(n) == nested_capture_ref(n));
  }
}
#endif
#ifdef TEST_STREAM_GURD_DV
// Stream sieve: StartList = 2..N*N; Filter drops multiples of each prime P<=N
// then recurses, prepending P; once P>N the tail is passed through unfiltered.
// Result = all primes in [2, N*N].  Exercises stream `||` catenation
// (sisal_stream_concat) -- the op that used to leak to array addh and hang.
static void test_stream_gurd_dv() {
  printf("\n=== Group: stream_gurd_dv (stream sieve, stream `||`) ===\n");
  auto run = [](int N) {
    int hi = N * N;
    std::vector<int32_t> ref;
    std::vector<char> sieve(hi + 1, 1);
    for (int p = 2; p <= hi; p++)
      if (sieve[p]) { ref.push_back(p); for (int m = 2*p; m <= hi; m += p) sieve[m] = 0; }
    std::vector<int32_t> got;
    for (sisal_generator<int32_t> r = func_MAIN(N); !sisal_stream_empty_pred(r);
         r = sisal_stream_rest(r))
      got.push_back(sisal_stream_first<int32_t>(r));
    int ok = got.size() == ref.size();
    for (size_t i = 0; ok && i < ref.size(); i++) ok = got[i] == ref[i];
    char tag[64]; snprintf(tag, sizeof tag, "primes in [2,%d] (N=%d)", hi, N);
    check(tag, ok);
  };
  run(2); run(3); run(5); run(10); run(13);
}
#endif
#ifdef TEST_TEST_IF_NESTED_CAPTURE_DV
// Nested if returning a captured outer scalar; pure scalar control flow.
static int if_nested_capture_ref(int sel, bool flag, int cap) {
  if (sel == 1) return flag ? cap : 42;
  return 0;
}
static void test_test_if_nested_capture_dv() {
  printf("\n=== Group: test_if_nested_capture_dv (nested if, captured scalar) ===\n");
  int sels[] = {1, 1, 2, 0}; bool fls[] = {true, false, true, false};
  int caps[] = {77, 77, 5, 9};
  for (int i = 0; i < 4; i++) {
    char tag[64]; snprintf(tag, sizeof tag, "sel=%d flag=%d cap=%d", sels[i], fls[i], caps[i]);
    check(tag, func_MAIN(sels[i], fls[i], caps[i]) == if_nested_capture_ref(sels[i], fls[i], caps[i]));
  }
}
#endif
#ifdef TEST_TEST_IF_LET_CASCADE_DV
// let-bound nested-if result feeding a second if; pure scalar.
static int if_let_cascade_ref(int sel, bool flag, int v1, int v2, int v3) {
  int fr = (sel == 1) ? (flag ? v1 : v2) : v3;
  return (fr > 50) ? fr * 2 : fr + 100;
}
static void test_test_if_let_cascade_dv() {
  printf("\n=== Group: test_if_let_cascade_dv (let-bound if cascade) ===\n");
  struct { int sel; bool fl; int v1, v2, v3; } cs[] = {
    {1, true, 60, 5, 9}, {1, false, 60, 5, 9}, {2, true, 60, 5, 9},
    {1, true, 10, 5, 9}, {3, false, 99, 1, 51},
  };
  for (auto &c : cs) {
    char tag[80]; snprintf(tag, sizeof tag, "sel=%d fl=%d v=%d,%d,%d", c.sel, c.fl, c.v1, c.v2, c.v3);
    check(tag, func_MAIN(c.sel, c.fl, c.v1, c.v2, c.v3)
              == if_let_cascade_ref(c.sel, c.fl, c.v1, c.v2, c.v3));
  }
}
#endif
#ifdef TEST_TAGCASE_BARE_DV
// Bare tagcase (no payload binding) over union[A:int;B:real;C:bool].
// Mk(s) = tag A iff s==1, else tag B (A's payload is always 42).
static void test_tagcase_bare_dv() {
  printf("\n=== Group: tagcase_bare_dv (bare tagcase dispatch) ===\n");
  for (int s : {1, 2, 0, 5}) {
    struct FUNC_MAIN_results r = func_MAIN(s);
    int e0 = (s == 1) ? 10 : 20;      // tagcase u = Mk(s)
    int e1 = (s == 0) ? 100 : 200;    // tagcase Mk(s+1)  (A iff s+1==1)
    int e2 = (s == 1) ? 1 : 2;        // DispatchParam(u)
    bool e3 = (s == 1);               // is A(u)
    char tag[48]; snprintf(tag, sizeof tag, "s=%d", s);
    check(tag, r.res_0 == e0 && r.res_1 == e1 && r.res_2 == e2 && r.res_3 == e3);
  }
}
#endif
#ifdef TEST_TAGCASE_BARE_MIXED_DV
// Bare/bound tagcase nesting; classification is per-instance.  Both helpers
// return 2 when s==1, else 3.
static void test_tagcase_bare_mixed_dv() {
  printf("\n=== Group: tagcase_bare_mixed_dv (mixed bare/bound nesting) ===\n");
  for (int s : {1, 2, 0, 3}) {
    struct FUNC_MAIN_results r = func_MAIN(s);
    int e = (s == 1) ? 2 : 3;
    char tag[48]; snprintf(tag, sizeof tag, "s=%d", s);
    check(tag, r.res_0 == e && r.res_1 == e);
  }
}
#endif
#ifdef TEST_TAGCASE_BARE_NESTED_DV
// Nested bare tagcases over an array_dv of unions.  u[1]=A(s), u[2]=B, so the
// outer A arm -> inner B arm -> 2, for every s.
static void test_tagcase_bare_nested_dv() {
  printf("\n=== Group: tagcase_bare_nested_dv (nested bare tagcase, array_dv of union) ===\n");
  for (int s : {1, 7, 0, -3}) {
    char tag[48]; snprintf(tag, sizeof tag, "s=%d", s);
    check(tag, func_MAIN(s) == 2);
  }
}
#endif
#ifdef TEST_CRYPTO_DV
// crypto string-equality over array_dv[character]: sizes equal AND every char
// equal (dot-zip + boolean `product a=b`).  Reference = strcmp.
static sisal_array_t crypto_mkstr(const char *s) {
  int n = (int)strlen(s);
  sisal_array_t a = sisal_array_alloc_empty(1, 3, (uint64_t)n);  // type_id 3 = char
  a.lower_bound[0] = 1; a.dims[0] = n;
  for (int i = 0; i < n; i++) ((char *)a.data)[i] = s[i];
  return a;
}
static void test_crypto_dv() {
  printf("\n=== Group: crypto_dv (array_dv[char] equality: dot-zip + product) ===\n");
  const char *pairs[][2] = {
    {"hello", "hello"}, {"hello", "world"}, {"abc", "ab"},
    {"a", "a"}, {"", ""}, {"abc", "abd"}, {"password", "password"},
  };
  for (auto &pr : pairs) {
    bool got = func_MAIN(crypto_mkstr(pr[0]), crypto_mkstr(pr[1]));
    bool exp = strcmp(pr[0], pr[1]) == 0;
    char tag[80]; snprintf(tag, sizeof tag, "crypto(\"%s\",\"%s\")", pr[0], pr[1]);
    check(tag, got == exp);
  }
}
#endif
#ifdef TEST_SQRT_DV
// Newton-iteration sqrt (for-initial convergence) + external `global sqrt`
// (libm).  Both must match std::sqrt: Newton to its epsilon, libm exactly.
static void test_sqrt_dv() {
  printf("\n=== Group: sqrt_dv (Newton for-initial + external sqrt) ===\n");
  for (double x : {2.0, 4.0, 100.0, 0.25, 1000.0, 1.0}) {
    struct FUNC_MAIN_results r = func_MAIN(x, 1e-9);
    double e = std::sqrt(x);
    char tag[64]; snprintf(tag, sizeof tag, "sqrt(%g)", x);
    check(tag, std::fabs(r.res_0 - e) < 1e-3 && std::fabs(r.res_1 - e) < 1e-9);
  }
}
#endif
#ifdef TEST_REC_FIELD_DV
// Record holding an array_dv field: r.v[i] must rank-reduce to a scalar.
static void test_rec_field_dv() {
  printf("\n=== Group: rec_field_dv (record-held array_dv, field subscript) ===\n");
  check("r.v[1]+r.v[2]+r.v[3]+r.w == 65", std::fabs(func_MAIN() - 65.0) < 1e-12);
}
#endif
#ifdef TEST_REC_AOS_DV
// array_dv of records-holding-arrays: forall build + array_addh + iterate.
static void test_rec_aos_dv() {
  printf("\n=== Group: rec_aos_dv (array_dv of record-holding-array) ===\n");
  check("sum over build+addh of (r.w + r.v[2]) == 143", func_MAIN() == 143);
}
#endif
#ifdef TEST_REC_SOA_DV
// Struct-of-Arrays (nucleic nuc layout): record of dense rank-2 array_dv fields
// of differing widths, cross-forall built, read via s.field[k,j].
static void test_rec_soa_dv() {
  printf("\n=== Group: rec_soa_dv (struct-of-arrays: record of dense rank-2 fields) ===\n");
  check("typ + dgf[k,j] + params[k,j] SoA reads == 1812", func_MAIN() == 1812);
}
#endif
#ifdef TEST_RESHAPE_DV
// reshape(A,d0..): flat 1-D array_dv reshaped to rank-2 and rank-3, indexed [k,j].
static void test_reshape_dv() {
  printf("\n=== Group: reshape_dv (DV_RESHAPE: flat 1-D -> rank-2/3 dope) ===\n");
  check("reshape rank-2 + rank-3 indexed == 91", func_MAIN() == 91);
}
#endif
#ifdef TEST_SOA_INIT_DV
// nucleic init_A in Struct-of-Arrays form built from REAL data: each ragged row
// (typ,dgf,p275,p180,p60,params,uniontype) is a flat 1-D array_dv reshaped to a
// dense rank-2 (11 x width) and stored as a record field; main sums six probes
// s.field[k,j].  Reference = the same six raw constants from the nucleic literal
// (rA typ[1]; dgf[1,1]; params[1,1]; uniontype[1,1]; last dgf; last params).
static void test_soa_init_dv() {
  printf("\n=== Group: soa_init_dv (nucleic init_A SoA: reshape flat -> rank-2 record fields) ===\n");
  const double typ_1_1   = 0.0;      // rA typ  (nuc 1, elem 1)
  const double dgf_1_1   = -0.0018;  // rA dgf  [1,1]
  const double par_1_1   = 2.8930;   // rA params [1,1]
  const double uni_1_1   = 2.4280;   // rA uniontype [1,1]
  const double dgf_11_12 = 30.8246;  // rA10 dgf  [11,12]  (last dgf)
  const double par_11_75 = 49.4985;  // rA10 params [11,75] (last params)
  const double ref = typ_1_1 + dgf_1_1 + par_1_1 + uni_1_1 + dgf_11_12 + par_11_75;
  check("SoA init_A six-probe sum == nucleic reference", std::fabs(func_MAIN() - ref) < 1e-4);
}
#endif
#ifdef TEST_NUCLEIC_SOA_DV
// nucleic access patterns on the SoA: reshape -> rank-2 record fields, s.typ[k]
// dispatch, and atom_pos_soa (rank-2 params field + threaded row index k,
// full-indexed params[k,i], returned as a 3-tuple through a function).  With an
// identity tfo, atom_pos_soa returns the raw c1_ coords.  Reference = those raw
// params values (nucleic rA/rC c1_ atom, 1-based col 31/32/33).
static void test_nucleic_soa_dv() {
  printf("\n=== Group: nucleic_soa_dv (SoA access: typ dispatch + row-threaded atom_pos) ===\n");
  const double c1_A_x = 6.5400, c1_A_y = 5.1200, c1_A_z = -1.4190;  // nuc A c1_ (rA)
  const double c1_C_x = 6.4190;                                     // nuc C c1_ x (rC)
  const double a   = c1_A_x + c1_C_x;                 // s.params[1,31] + s.params[2,31]
  const double xyz = c1_A_x + c1_A_y + c1_A_z;        // base_c1(s,1,identity)
  const double ref = a + xyz;                         // = 23.2000
  check("SoA atom_pos + typ dispatch == nucleic c1_ reference", std::fabs(func_MAIN() - ref) < 1e-4);
}
#endif
#ifdef TEST_NUCLEIC_MAKET_DV
// nucleic make_t on the SoA: reference-frame pipeline
//   make_t = tfo_inv_ortho(tfo_align(atom_pos ×3 over s.params[k, ..]))
// over nuc A's o3_/c3_/c4_ atoms with an identity tfo.  Reference = the exact
// kernels replicated here (pt_phi/pt_theta/tfo_align/tfo_inv_ortho), same
// position-weighted digest as main.
static void test_nucleic_maket_dv() {
  printf("\n=== Group: nucleic_maket_dv (SoA make_t: atom_pos row-slice -> tfo_align -> inv_ortho) ===\n");
  auto pt_theta = [](double x, double z){ return std::atan2(x, z); };
  auto pt_phi   = [](double x, double y, double z){
    double b = std::atan2(x, z); return std::atan2(std::cos(b)*z + std::sin(b)*x, y); };
  // nuc A atoms via identity tfo (raw coords)
  double p0=7.3801,p1=6.3562,p2=-4.7350;   // o3_
  double p3=6.5720,p4=6.0040,p5=-3.6090;   // c3_
  double p6=6.4970,p7=7.1480,p8=-2.5980;   // c4_
  double x31=p6-p0, y31=p7-p1, z31=p8-p2;
  double rotpy0=p3-p0, rotpy1=p4-p1, rotpy2=p5-p2;
  double phi=pt_phi(rotpy0,rotpy1,rotpy2), theta=pt_theta(rotpy0,rotpy2);
  double sinp=std::sin(phi),sint=std::sin(theta),cosp=std::cos(phi),cost=std::cos(theta);
  double sinpsint=sinp*sint, sinpcost=sinp*cost, cospsint=cosp*sint, cospcost=cosp*cost;
  double rotpz0=cost*x31 - sint*z31;
  double rotpz1=sinpsint*x31 + cosp*y31 + sinpcost*z31;
  double rotpz2=cospsint*x31 - sinp*y31 + cospcost*z31;
  double rho=pt_theta(rotpz0,rotpz2), cosr=std::cos(rho), sinr=std::sin(rho);
  double x=-p0*cost + p2*sint;
  double y=-p0*sinpsint - p1*cosp - p2*sinpcost;
  double z=-p0*cospsint + p1*sinp - p2*cospcost;
  double A[12]={ cost*cosr - cospsint*sinr, sinpsint, cost*sinr + cospsint*cosr,
                 sinp*sinr, cosp, -sinp*cosr,
                 -sint*cosr - cospcost*sinr, sinpcost, -sint*sinr + cospcost*cosr,
                 x*cosr - z*sinr, y, x*sinr + z*cosr };
  double t0=A[0],t1=A[1],t2=A[2],t3=A[3],t4=A[4],t5=A[5],t6=A[6],t7=A[7],t8=A[8],t9=A[9],t10=A[10],t11=A[11];
  double T[12]={ t0,t3,t6, t1,t4,t7, t2,t5,t8,
                 -(t9*t0+t10*t1+t11*t2), -(t9*t3+t10*t4+t11*t5), -(t9*t6+t10*t7+t11*t8) };
  double ref=0; for(int i=0;i<12;i++) ref += (i+1)*T[i];
  check("SoA make_t reference-frame == nucleic tfo pipeline", std::fabs(func_MAIN() - ref) < 1e-4);
}
#endif
#ifdef TEST_NUCLEIC_DGFBASE_DV
// nucleic dgf_base on the SoA: tfo2_combine(dgf_row, t, tfo_inv_ortho(tfo_align(
// atom_pos x3))), type-A atoms c1_/n9/c4 of nuc A, identity t and ref.tfo.
// Reference = the kernels (tfo_align/tfo_inv_ortho/tfo2_combine) replicated here.
static void nd_pt(double x,double z,double* r){ *r=std::atan2(x,z); }
static double nd_phi(double x,double y,double z){ double b=std::atan2(x,z); return std::atan2(std::cos(b)*z+std::sin(b)*x,y); }
static void nd_align(double p0,double p1,double p2,double p3,double p4,double p5,
                     double p6,double p7,double p8,double O[12]){
  double x31=p6-p0,y31=p7-p1,z31=p8-p2, r0=p3-p0,r1=p4-p1,r2=p5-p2;
  double phi=nd_phi(r0,r1,r2), theta; nd_pt(r0,r2,&theta);
  double sinp=std::sin(phi),sint=std::sin(theta),cosp=std::cos(phi),cost=std::cos(theta);
  double sinpsint=sinp*sint,sinpcost=sinp*cost,cospsint=cosp*sint,cospcost=cosp*cost;
  double z0=cost*x31-sint*z31,z1=sinpsint*x31+cosp*y31+sinpcost*z31,z2=cospsint*x31-sinp*y31+cospcost*z31;(void)z1;
  double rho; nd_pt(z0,z2,&rho); double cosr=std::cos(rho),sinr=std::sin(rho);
  double x=-p0*cost+p2*sint,y=-p0*sinpsint-p1*cosp-p2*sinpcost,z=-p0*cospsint+p1*sinp-p2*cospcost;
  double A[12]={cost*cosr-cospsint*sinr,sinpsint,cost*sinr+cospsint*cosr,sinp*sinr,cosp,-sinp*cosr,
    -sint*cosr-cospcost*sinr,sinpcost,-sint*sinr+cospcost*cosr,x*cosr-z*sinr,y,x*sinr+z*cosr};
  for(int i=0;i<12;i++)O[i]=A[i];
}
static void nd_inv(const double t[12],double O[12]){
  double r[12]={t[0],t[3],t[6],t[1],t[4],t[7],t[2],t[5],t[8],
    -(t[9]*t[0]+t[10]*t[1]+t[11]*t[2]),-(t[9]*t[3]+t[10]*t[4]+t[11]*t[5]),-(t[9]*t[6]+t[10]*t[7]+t[11]*t[8])};
  for(int i=0;i<12;i++)O[i]=r[i];
}
static void nd_comb(const double a[12],const double b[12],const double t[12],double O[12]){
  double n0=b[0]*t[0]+b[1]*t[3]+b[2]*t[6],n1=b[0]*t[1]+b[1]*t[4]+b[2]*t[7],n2=b[0]*t[2]+b[1]*t[5]+b[2]*t[8];
  double n3=b[3]*t[0]+b[4]*t[3]+b[5]*t[6],n4=b[3]*t[1]+b[4]*t[4]+b[5]*t[7],n5=b[3]*t[2]+b[4]*t[5]+b[5]*t[8];
  double n6=b[6]*t[0]+b[7]*t[3]+b[8]*t[6],n7=b[6]*t[1]+b[7]*t[4]+b[8]*t[7],n8=b[6]*t[2]+b[7]*t[5]+b[8]*t[8];
  double n9=b[9]*t[0]+b[10]*t[3]+b[11]*t[6]+t[9],n10=b[9]*t[1]+b[10]*t[4]+b[11]*t[7]+t[10],n11=b[9]*t[2]+b[10]*t[5]+b[11]*t[8]+t[11];
  double R[12]={a[0]*n0+a[1]*n3+a[2]*n6,a[0]*n1+a[1]*n4+a[2]*n7,a[0]*n2+a[1]*n5+a[2]*n8,
    a[3]*n0+a[4]*n3+a[5]*n6,a[3]*n1+a[4]*n4+a[5]*n7,a[3]*n2+a[4]*n5+a[5]*n8,
    a[6]*n0+a[7]*n3+a[8]*n6,a[6]*n1+a[7]*n4+a[8]*n7,a[6]*n2+a[7]*n5+a[8]*n8,
    a[9]*n0+a[10]*n3+a[11]*n6+n9,a[9]*n1+a[10]*n4+a[11]*n7+n10,a[9]*n2+a[10]*n5+a[11]*n8+n11};
  for(int i=0;i<12;i++)O[i]=R[i];
}
static void test_nucleic_dgfbase_dv() {
  printf("\n=== Group: nucleic_dgfbase_dv (SoA dgf_base: typ dispatch + tfo2_combine) ===\n");
  double al[12]; nd_align(6.5400,5.1200,-1.4190, 5.3170,4.2990,-1.1930, 5.2900,2.9790,-0.8260, al);
  double iv[12]; nd_inv(al, iv);
  double dgf[12]={-0.0018,-0.8207,0.5714, 0.2679,-0.5509,-0.7904, 0.9634,0.1517,0.2209, 0.0073,8.4030,0.6232};
  double id[12]={1,0,0, 0,1,0, 0,0,1, 0,0,0};
  double out[12]; nd_comb(dgf, id, iv, out);
  double ref=0; for(int i=0;i<12;i++) ref += (i+1)*out[i];
  check("SoA dgf_base (typ dispatch + tfo2_combine) == nucleic reference", std::fabs(func_MAIN() - ref) < 1e-4);
}
#endif
#ifdef TEST_NUCLEIC_GETVAR_DV
// nucleic get_var on solution = array_dv[var] (non-recursive record -> lives in
// a dope).  Backward for-initial search by .label returns the whole var; check
// the returned var's scalar + array fields.  labels 10/20/30, k=i, params[100,200];
// get_var(20) -> var 2 -> 20 + 1000*2 + params[1]=100 = 2120.
static void test_nucleic_getvar_dv() {
  printf("\n=== Group: nucleic_getvar_dv (solution=array_dv[var]; get_var backward search) ===\n");
  check("get_var(20) returns the label-20 var (2120)", func_MAIN() == 2120);
}
#endif
#ifdef TEST_MEMBER_DV
// Paraffins structural equality/membership over a RECURSIVE UNION that recurses
// through an array_dv (Radical = Hydrogen | Carbon: array_dv[Radical]).  Sizable:
// the dope is a fixed-size handle, so size(Radical) = tag + max(arms) terminates
// and the recursive arm is a sisal_array_t, never expanded inline.
// masks: bit3 (P1,P1)=eq, bit2 (P1,P2)=neq, bit1 (P2,P2b)=eq, bit0 (P2,P3)=neq
// -> 8 + 0 + 2 + 0 = 10 on BOTH the dot-iteration and for-initial paths.
static void test_member_dv() {
  printf("\n=== Group: member_dv (recursive union through array_dv; tagcase recursion) ===\n");
  auto r = func_MAIN();
  check("AreEqualDot mask == 10 (P1=P1, P1!=P2, P2=P2b, P2!=P3)", r.res_0 == 10);
  check("AreEqualSeq mask == 10 (same, sequential walk)",          r.res_1 == 10);
  check("IsMember(Set, P2b) == true",                              r.res_2 == true);
  check("IsMember(Set, P3)  == false",                             r.res_3 == false);
}
#endif
#ifdef TEST_ML_LIST_DV
// The ML list written as the ML type: Stack = empty | node(hd, tl: Stack).  The
// tail is the list ITSELF -- no handle in the source -- so the backend BOXES the
// cycle-closing field (pointer to a heap cons-cell), as OCaml/Haskell do.
// Stack is 10,20,30 (30 on top): GetVar(20) walks the spine -> 20 + 1000*2;
// Depth = 3 cells; Top(Pop) = 20; popping past the end yields the empty arm.
static void test_ml_list_dv() {
  printf("\n=== Group: ml_list_dv (recursive union = ML cons-list; boxed arm) ===\n");
  auto r = func_MAIN();
  check("GetVar(20) walks the spine -> 2020", r.res_0 == 2020);
  check("Depth == 3 cons cells",              r.res_1 == 3);
  check("Top(Pop(s)) == 20",                  r.res_2 == 20);
  check("popping to empty -> -1",             r.res_3 == -1);
}
#endif
#ifdef TEST_NUCLEIC_SEARCH_DV
// nucleic pseudoknot_domains: backtracking domain search over the SoA data with
// the ML cons-list stack -- push / recurse / (persistent) pop, and a
// pseudoknot_constraint that looks BACK through the stack via get_var.
// Reference: the same search written directly here.  Coordinates are the real
// rA / rC c1_ atoms, so dist(A,A)=dist(C,C)=0 and dist(A,C)~10.673: a tight
// limit keeps only the same-nucleotide chains, a loose one keeps all 2^3.
static double ns_coords[2][3] = {{6.5400, 5.1200, -1.4190},
                                 {6.4190, -5.1840, 1.3620}};
static double ns_dist(int a, int b) {
  double dx = ns_coords[a][0] - ns_coords[b][0];
  double dy = ns_coords[a][1] - ns_coords[b][1];
  double dz = ns_coords[a][2] - ns_coords[b][2];
  return std::sqrt(dx * dx + dy * dy + dz * dz);
}
// stack[] holds the placement chosen at each level (the cons-list spine)
static int ns_domains(int k, int nlev, double lim, int *stack) {
  if (k == nlev) return 1;
  int total = 0;
  for (int cand = 0; cand < 2; cand++) {
    bool ok = (k == 0) || (ns_dist(stack[k - 1], cand) <= lim);
    if (ok) { stack[k] = cand; total += ns_domains(k + 1, nlev, lim, stack); }
  }
  return total;
}
static void test_nucleic_search_dv() {
  printf("\n=== Group: nucleic_search_dv (pseudoknot_domains backtracking on the ML stack) ===\n");
  int stack[8];
  int tight = ns_domains(0, 3, 4.0, stack);
  int loose = ns_domains(0, 3, 12.0, stack);
  auto r = func_MAIN();
  check("tight limit: only same-nucleotide chains survive", r.res_0 == tight);
  check("loose limit: every chain survives",                r.res_1 == loose);
}
#endif
#ifdef TEST_ML_LIST_REPLACE_DV
// `r replace [f: v]` on a recursive (boxed) type = OCaml's { r with f = v }.
// Must ALLOCATE a new cell (never write through the old pointer), while fields
// left alone copy their pointers -- i.e. SHARE the substructure (path copying).
// Stack is [3,2,1].  SetHead swaps the non-boxed field: tail stays shared, so
// depth is still 3.  SetTail swaps the boxed field for empty: depth 1.  Neither
// may disturb the original.
static void test_ml_list_replace_dv() {
  printf("\n=== Group: ml_list_replace_dv (replace on a boxed field; path copying) ===\n");
  auto r = func_MAIN();
  check("SetHead: head replaced (99)",               r.res_0 == 99);
  check("SetHead: tail SHARED, depth still 3",       r.res_1 == 3);
  check("SetTail: head kept (3)",                    r.res_2 == 3);
  check("SetTail: boxed field replaced, depth 1",    r.res_3 == 1);
  check("ORIGINAL untouched: top still 3",           r.res_4 == 3);
  check("ORIGINAL untouched: depth still 3",         r.res_5 == 3);
}
#endif
#ifdef TEST_NUCLEIC_KERNELS_DV
// nucleic pure-math kernels: distance, atom_pos_pt (transform as 12 loose
// scalars -- how pseudoknot_constraint calls it), tfo_combine (single-transform
// compose, the one P_O3a uses).  Real rA data: params c1_/h1_/c2_, dgf_base_tfo
// as `a`, p_o3_275_tfo as the loose scalars.  Reference computed here.
static void test_nucleic_kernels_dv() {
  printf("\n=== Group: nucleic_kernels_dv (distance, atom_pos_pt, tfo_combine) ===\n");
  double prm[9] = {6.5400,5.1200,-1.4190, 7.2763,4.9681,-0.6297, 7.1940,4.8830,-2.7770};
  double a[12]  = {-0.0018,-0.8207,0.5714, 0.2679,-0.5509,-0.7904,
                    0.9634,0.1517,0.2209, 0.0073,8.4030,0.6232};
  double t[12]  = {-0.8143,-0.5091,-0.2788, -0.0433,-0.4257,0.9038,
                   -0.5788,0.7480,0.3246, 1.5227,6.9114,-7.0765};
  double d = std::sqrt(prm[0]*prm[0] + prm[1]*prm[1] + prm[2]*prm[2]);
  double px = prm[0]*t[0] + prm[1]*t[3] + prm[2]*t[6] + t[9];
  double py = prm[0]*t[1] + prm[1]*t[4] + prm[2]*t[7] + t[10];
  double pz = prm[0]*t[2] + prm[1]*t[5] + prm[2]*t[8] + t[11];
  double c[12] = {
    a[0]*t[0]+a[1]*t[3]+a[2]*t[6], a[0]*t[1]+a[1]*t[4]+a[2]*t[7], a[0]*t[2]+a[1]*t[5]+a[2]*t[8],
    a[3]*t[0]+a[4]*t[3]+a[5]*t[6], a[3]*t[1]+a[4]*t[4]+a[5]*t[7], a[3]*t[2]+a[4]*t[5]+a[5]*t[8],
    a[6]*t[0]+a[7]*t[3]+a[8]*t[6], a[6]*t[1]+a[7]*t[4]+a[8]*t[7], a[6]*t[2]+a[7]*t[5]+a[8]*t[8],
    a[9]*t[0]+a[10]*t[3]+a[11]*t[6]+t[9],
    a[9]*t[1]+a[10]*t[4]+a[11]*t[7]+t[10],
    a[9]*t[2]+a[10]*t[5]+a[11]*t[8]+t[11] };
  double w = 0; for (int i = 0; i < 12; i++) w += (i + 1) * c[i];
  auto r = func_MAIN();
  check("distance(c1_) matches", std::fabs(r.res_0 - d) < 1e-6);
  check("atom_pos_pt through loose 12-scalar transform", std::fabs(r.res_1 - (px+py+pz)) < 1e-6);
  check("tfo_combine 12-entry digest", std::fabs(r.res_2 - w) < 1e-6);
}
#endif
#ifdef TEST_NUCLEIC_BUILDERS_DV
// nucleic constraint builders: try, the real pseudoknot_constraint (both
// distance branches), reference and wc_dumas.  With identity transforms the
// constraint compares nuc A's `p` atom (params idx 0) against its `o3_` atom
// (params idx 54); reference computes that distance directly.  i=18 admits
// <= 4.0, i=6 admits <= 4.5, every other i is unconstrained.  The 2-level
// search runs reference (k=0, i=23) then wc_dumas (k=1, i=8) -- both on
// unconstrained i -- so exactly one complete placement is produced.
static void test_nucleic_builders_dv() {
  printf("\n=== Group: nucleic_builders_dv (try / pseudoknot_constraint / reference / wc_dumas) ===\n");
  // rA params: p = cols 1..3, o3_ = cols 55..57 (1-based) = idx 0 / idx 54
  double p[3]  = {2.8930, 8.5380, -3.3280};
  double o3[3] = {7.3801, 6.3562, -4.7350};
  double dx = p[0]-o3[0], dy = p[1]-o3[1], dz = p[2]-o3[2];
  double d = std::sqrt(dx*dx + dy*dy + dz*dz);
  auto r = func_MAIN();
  check("constraint i=18 uses the 4.0 limit", r.res_0 == (d <= 4.0 ? 1 : 0));
  check("constraint i=6  uses the 4.5 limit", r.res_1 == (d <= 4.5 ? 1 : 0));
  check("every other i is unconstrained",     r.res_2 == 1);
  check("reference + wc_dumas yield one complete placement", r.res_3 == 1);
  // P_O3 tries all THREE O3' rotamers (p60/p180/p275) per nucleotide, each
  // folded into make_t via tfo_combine; at an unconstrained i each completes.
  check("P_O3 enumerates 3 O3' rotamers -> 3 placements", r.res_4 == 3);
}
#endif
#ifdef TEST_NUCLEIC_BASES_DV
// All four nucleic base tables (init_A/C/G/U) transposed to SoA: 11 nucleotides
// each, every nucleotide within a base having identical row widths, so each base
// is a set of rectangular rank-2 tables.  Only `uniontype` differs between bases
// (A 24 / C 18 / G 27 / U 15 columns = 8/6/9/5 atoms).  All 6380 values were
// verified element-for-element against nucleic.sis when the tables were
// generated; here one probe per base pins typ + a dgf corner + the params corner
// + the uniontype corner (whose column index differs per base).
static void test_nucleic_bases_dv() {
  printf("\n=== Group: nucleic_bases_dv (init_A/C/G/U tables in SoA) ===\n");
  // typ, dgf[1,1], params[11,75], uniontype[11,last] straight from nucleic.sis
  const double refA = 0.0 + -0.0018 + 49.4985 + 49.0452;
  const double refC = 1.0 + -0.0359 + 48.3432 + 49.0839;
  const double refG = 2.0 + -0.0018 + 44.0958 + 48.2059;
  const double refU = 3.0 + -0.0359 + 51.8416 + 47.4975;
  auto r = func_MAIN();
  check("init_A table (typ 0, uniontype 24 wide)", std::fabs(r.res_0 - refA) < 1e-6);
  check("init_C table (typ 1, uniontype 18 wide)", std::fabs(r.res_1 - refC) < 1e-6);
  check("init_G table (typ 2, uniontype 27 wide)", std::fabs(r.res_2 - refG) < 1e-6);
  check("init_U table (typ 3, uniontype 15 wide)", std::fabs(r.res_3 - refU) < 1e-6);
  // init_tfo: the 7 named transforms (identity first, a38_g37 last), 7x12 rank-2
  check("init_tfo: tfo_id[1,1] + a38_g37[7,12]",
        std::fabs(r.res_4 - (1.0 + -2.5321)) < 1e-6);
  // init_nucleotides: the 6 GROUPS, selected by nucs[g] -- an array_dv OF SoA
  // records (they have different uniontype widths, so not a rank-3 table).
  // Group order A,C,G,U,rG_,rU_ has typs 0,1,2,3,2,3 -> 11.
  check("init_nucleotides: 6 groups in order (typ sum 11)",
        std::fabs(r.res_5 - 11.0) < 1e-6);
}
#endif
#ifdef TEST_NUCLEIC_DV
// NUCLEIC -- the whole Pseudoknot benchmark on the SoA port: all four base
// tables + the two inline groups + the 7 transforms, the real 23-level
// pseudoknot_domains dispatch, the six constraint builders, and the
// most_distant_atom reduction (folded into the search as a max).
// Expected value is the PUBLISHED Pseudoknot result, 33.7976 -- nothing in the
// port was tuned toward it.
static void test_nucleic_dv() {
  printf("\n=== Group: nucleic_dv (WHOLE Pseudoknot benchmark) ===\n");
  auto r = func_MAIN();
  printf("    most distant atom = %.9f, solutions = %.0f\n", r.dist, r.count);
  // Both figures come from Feeley's reference C implementation of the same
  // benchmark (oldsisal programs.dir/pseudoknots.dir/nucleic2.c), run directly.
  check("most distant atom == 33.797594891", std::fabs(r.dist - 33.797594891) < 1e-8);
  check("50 solutions found",                std::fabs(r.count - 50.0) < 1e-9);
}
#endif
#ifdef TEST_BINTREE_DV
// A directly recursive union whose payload record has TWO recursive fields
// (record[L, R: BTree]) -- both boxed.  Build folds an array into a balanced
// tree, collapsing a pair of EQUAL leaves into one, so the shape depends on the
// data and the leaf count is a real check on the recursion.
static void test_bintree_dv() {
  printf("\n=== Group: bintree_dv (recursive union, two boxed fields) ===\n");
  auto r = func_MAIN();
  check("[1,2,3,4] -> 4 leaves (nothing collapses)", r.res_0 == 4);
  check("[5,5]     -> 1 leaf   (equal pair collapses)", r.res_1 == 1);
  check("[2,2,2,2] -> 1 leaf   (collapses recursively)", r.res_2 == 1);
  check("[1,1,2,2] -> 2 leaves (pairs collapse, 1 != 2)", r.res_3 == 2);
  check("leaf values survive boxing (sum 10)", r.res_4 == 10);
}
#endif
#ifdef TEST_PARA_DEARRAY_DV
// Turner's paraffins with the nucleic playbook: para.sis's "always three" /
// "always four" arrays are records in disguise, so they DE-ARRAY into records
// (recursive -> boxed), and Class -- grown by array_addh, taken apart by
// FirstRest (hd/tl) and array_reml (tail) -- becomes the ML cons-list.
// Reference: para.sis builds each Carbon with a full `cross` (ORDERED triples),
// so |Para(N)| = 1,1,1,2,4,8,17,40.  Computed here with the same recurrence.
static void test_para_dearray_dv() {
  printf("\n=== Group: para_dearray_dv (de-arrayed Radical + cons-list enumeration) ===\n");
  int a[8];
  for (int n = 0; n < 8; n++) {
    if (n == 0) { a[0] = 1; continue; }
    int tot = 0;
    for (int i = 0; i <= (n-1)/3; i++)
      for (int j = i; j <= (n-1-i)/2; j++)
        tot += a[i] * a[j] * a[n-1-i-j];      // full cross product
    a[n] = tot;
  }
  auto r = func_MAIN();
  const int got[8] = {r.n0,r.n1,r.n2,r.n3,r.n4,r.n5,r.n6,r.n7};
  for (int n = 0; n < 8; n++) {
    char msg[80];
    snprintf(msg, sizeof msg, "|Para(%d)| == %d", n, a[n]);
    check(msg, got[n] == a[n]);
  }
}
#endif
#ifdef TEST_LIST_ITER_DV
// A cons-list iterated by a for-initial that CARRIES the list (is empty / Hd /
// Tl) -- the shape the stream sieves use.  Previously a loop-carried
// union/record was declared sisal_array_t and the body failed on `.tag`, so
// list traversal had to be tagcase+recursion and depth bounded the length.
// No recursion here, so it is constant-stack whatever the C optimiser does.
static void test_list_iter_dv() {
  printf("\n=== Group: list_iter_dv (for-initial carrying a cons-list) ===\n");
  auto r = func_MAIN();
  check("sum 1..100 iteratively == 5050",        r.s1 == 5050);
  check("length of the 100-list == 100",         r.l1 == 100);
  check("sum 1..50000 == 1250025000",            r.s2 == 1250025000);
  check("length of the 50000-list == 50000",     r.l2 == 50000);
}
#endif
#ifdef TEST_FORINIT_REDUCE_DV
// Reductions in a SEQUENTIAL loop.  A forall always had them; a for-initial had
// only FINALVALUE and gathers, so `returns value of sum X` failed on the REDUCE
// node.  The operator statements are shared with the forall path.
// Correctness bar: a reduction must agree with a GATHER over the same loop --
// the gather collects the value history (seed first, for a carry), so the fold
// must cover the same elements.
static void test_forinit_reduce_dv() {
  printf("\n=== Group: forinit_reduce_dv (reductions in a for-initial) ===\n");
  auto r = func_MAIN();
  long gs = 0;
  for (long long i = 0; i < r.gath.size; i++) gs += ((int32_t *)r.gath.data)[i];
  check("gather history is the seed + each update (11 values)", r.gath.size == 11);
  check("sum == sum(gather over the same loop)", (long)r.s == gs);
  check("sum      == 66",       r.s == 66);
  check("product  == 11!",      r.p == 39916800);
  check("greatest == 11",       r.g == 11);
  check("least    == 1",        r.l == 1);
  check("sum of a BODY-computed value == 2", r.par == 2);
}
#endif
#ifdef TEST_WORDCOUNT_DV
// A for-initial that REDUCES (`value of sum count`) over a character array,
// with is_char driving a word/gap state machine.  Needed both sequential-loop
// reductions and character literals surviving to C -- the literal lowering had
// no CHARACTER case, so ' ' became 0, is_char called a space "not a space", and
// every input counted exactly 1 word.
static void test_wordcount_dv() {
  printf("\n=== Group: wordcount_dv (for-initial reduction + char literals) ===\n");
  struct { const char *s; int words; } cases[] = {
    {"the quick fox", 3}, {"hello", 1}, {"   ", 0}, {"a b\tc\nd", 4},
    {"", 0}, {"  spaced  out  ", 2},
  };
  for (auto &c : cases) {
    int n = (int)strlen(c.s);
    sisal_array_t a = sisal_array_build_elems<char>(1, n, c.s, 3);
    char msg[96];
    snprintf(msg, sizeof msg, "wordcount(%.20s) == %d", c.s, c.words);
    check(msg, func_MAIN(a) == c.words);
  }
}
#endif
#ifdef TEST_BACKTRACK_DV
// BackTrack's sentinel-terminated pointer chase: FinalPtrs stays a rank-2
// array_dv of records (rectangular, sizable), while the trace result -- whose
// length is unknown until the walk ends -- accumulates as a LIST and is packed
// into an array_dv at the end.  Chain (3,2) -> (2,1) -> (1,2) -> sentinel.
// Consing leaves the last node visited at the head, so the result is already in
// schedule order (the original gathers then reverses).
static void test_backtrack_dv() {
  printf("\n=== Group: backtrack_dv (array_dv graph + list-accumulated trace) ===\n");
  auto r = func_MAIN();
  const int ej[3] = {1, 2, 3}, es[3] = {2, 1, 2};
  check("trace length is the path length (3)", r.jobs.size == 3 && r.segs.size == 3);
  bool okj = r.jobs.size == 3, oks = r.segs.size == 3;
  for (int i = 0; i < 3 && okj && oks; i++) {
    okj = okj && ((int32_t *)r.jobs.data)[i] == ej[i];
    oks = oks && ((int32_t *)r.segs.data)[i] == es[i];
  }
  check("jobs in schedule order [1,2,3]", okj);
  check("segs follow the same links [2,1,2]", oks);
  // the leaf sweep: two Leaf nodes, (3,2) Val 50 and (1,1) Val 10.  Consing
  // reverses, so the list comes out [50,10].  BestLeaf must pick the Val-50
  // one -- not merely the first leaf it meets -- for the trace above to start
  // at (3,2) and produce [1,2,3].
  bool okl = r.leafvals.size == 2
             && ((int32_t *)r.leafvals.data)[0] == 50
             && ((int32_t *)r.leafvals.data)[1] == 10;
  check("leaf sweep collects both leaves [50,10]", okl);
}
#endif
#ifdef TEST_SUCCESSOR_DV
// Job Shop successor index: for each segment of job I, the index of the first
// segment of job I+1 that can follow it; RowSum folds a row to detect jobs in
// COMPLETE conflict with their successor (sum 0).  AB is a FLAT rank-2
// array_dv[Element] and each row is taken with the `..` slice AB[I,..], which
// rank-reduces 2 -> 1 -- the nested array_dv[AB_OneDim] of the original is
// malformed under the dope-vector model.  Trailing `|| [1:0]` flags row N.
struct su_elem { float alpha, beta; int32_t prio; };
static int su_rowsum(const su_elem* r1, const su_elem* r2, float del, int Q) {
  int sum = 0;
  for (int i = 1; i <= Q + 1; i++) {
    float diff = r1[i - 1].beta - r2[0].alpha;
    int indx;
    if (diff > 0.0f && del == 0.0f) indx = 0;
    else if (diff <= 0.0f) indx = 1;
    else {
      float rindx = diff / del + 1.0f;
      int iindx = (int)std::floor(rindx);
      int t = ((rindx - (float)iindx) == 0.0f) ? iindx : iindx + 1;
      indx = (t > Q + 1) ? 0 : t;
    }
    sum += indx;
  }
  return sum;
}
static void test_successor_dv(void) {
  printf("\n=== Group: successor_dv (rank-2 `..` row slice + fold) ===\n");
  enum { NJ = 4, Q = 3 };
  su_elem ab[NJ * (Q + 1)]; float del[NJ];
  for (int j = 0; j < NJ; j++) {
    float start = 1.0f + 1.0f * j, dur = 6.0f;
    del[j] = 0.75f + 0.5f * j;
    for (int i = 1; i <= Q + 1; i++) {
      float a = start + (float)(i - 1) * del[j];
      ab[j * (Q + 1) + (i - 1)] = { a, a + dur, 7 - j };
    }
  }
  sisal_array_t A = sisal_array_alloc_sized(2, 96, NJ * (Q + 1), sizeof(su_elem));
  A.rank = 2; A.dims[0] = NJ; A.dims[1] = Q + 1;
  A.lower_bound[0] = 1; A.lower_bound[1] = 1;
  A.stride[0] = Q + 1; A.stride[1] = 1;
  for (int i = 0; i < NJ * (Q + 1); i++) ((su_elem*)A.data)[i] = ab[i];
  sisal_array_t D = sisal_array_alloc_sized(1, 96, NJ, sizeof(float));
  D.lower_bound[0] = 1;
  for (int i = 0; i < NJ; i++) ((float*)D.data)[i] = del[i];

  sisal_array_t R = func_MAIN(A, D, Q, NJ);
  check("result is one flag per job (N)", (int)R.size == NJ);
  int ok = (int)R.size == NJ;
  for (int j = 1; ok && j <= NJ - 1; j++)
    ok = ((int32_t*)R.data)[j - 1] == su_rowsum(&ab[(j - 1) * (Q + 1)], &ab[j * (Q + 1)], del[j], Q);
  check("per-row successor sums == C mirror", ok);
  check("row 1 is in COMPLETE conflict (sum 0)", (int)R.size == NJ && ((int32_t*)R.data)[0] == 0);
  check("trailing flag for row N is 0", (int)R.size == NJ && ((int32_t*)R.data)[NJ - 1] == 0);
}
#endif
#ifdef TEST_GENLINKS_DV
// Job Shop GenLinks: the successor-link structure Trace/BackTrack later walk.
// In the original, job I's layer has InitDepth[I] rows and InitDepth varies per
// job -- a ragged array-of-array-of-array with no array_dv spelling.  But the
// original already RETURNS Depth alongside Links and every consumer loops
// `for J in 1, Depth[I]`, so the representation is dense-plus-counts in
// disguise; the port makes that explicit, padding each layer to MaxD = N-1.
// Nothing outside the Depth-bounded region is read, so the mirror below runs
// the ORIGINAL ragged algorithm and compares only where Depth says it counts.
// Two datasets: one with NumZeros == 0 throughout (padding only) and one that
// drives the leading-zero-row compression, which is a SHIFT on a padded plane
// rather than repeated array_reml.
struct gl_elem { float alpha, beta; int32_t prio; };
struct gl_maxrec { int32_t val, job, seg; };
struct gl_segrec { int32_t ecnt; gl_maxrec mx; int32_t prio; bool fired, leaf; };
static std::vector<int> gl_compare(const gl_elem* r1, const gl_elem* r2, float del, int Q) {
  std::vector<int> out(Q + 1);
  for (int i = 1; i <= Q + 1; i++) {
    float diff = r1[i - 1].beta - r2[0].alpha;
    int indx;
    if (diff > 0.0f && del == 0.0f) indx = 0;
    else if (diff <= 0.0f) indx = 1;
    else { float ri = diff / del + 1.0f; int ii = (int)std::floor(ri);
           int t = ((ri - (float)ii) == 0.0f) ? ii : ii + 1; indx = (t > Q + 1) ? 0 : t; }
    out[i - 1] = indx;
  }
  return out;
}
static void gl_case(float sp, float dstep, float dur, const char* tag) {
  const int N = 5, Q = 2, MaxD = N - 1;
  gl_elem ab[N * (Q + 1)]; float del[N]; int zeros[N] = { 0, 0, 0, 0, 0 };
  for (int j = 0; j < N; j++) {
    float start = 1.0f + sp * j; del[j] = 0.75f + dstep * j;
    for (int i = 1; i <= Q + 1; i++) {
      float a = start + (float)(i - 1) * del[j];
      ab[j * (Q + 1) + (i - 1)] = { a, a + dur, 7 - j };
    }
  }
  // ---- mirror: the ORIGINAL ragged algorithm ----
  std::vector<int> initDepth(N, 0);
  std::vector<std::vector<std::vector<int>>> layer(N + 1);
  std::vector<std::vector<int>> flags(N + 1), ivs(N + 1);
  for (int I = 1; I <= N - 1; I++) {
    int cnt = 1;
    while ((I + cnt) < N && zeros[I + cnt - 1] == 0) cnt++;
    initDepth[I - 1] = cnt;
    for (int J = 1; J <= cnt; J++) {
      int dest = I + J;
      std::vector<int> row = gl_compare(&ab[(I - 1) * (Q + 1)], &ab[(dest - 1) * (Q + 1)], del[dest - 1], Q);
      int s2 = 0; for (int v : row) s2 += v;
      layer[I].push_back(row); flags[I].push_back(s2); ivs[I].push_back(dest);
    }
  }
  std::vector<std::vector<std::vector<int>>> sLinks(N + 1);
  std::vector<std::vector<int>> sVs(N + 1); std::vector<int> sDepth(N + 1, 0);
  for (int I = 1; I <= N - 1; I++) {
    int nz = 0;
    for (int J = 1; J <= initDepth[I - 1] - 1; J++) if (flags[I][J - 1] == 0) nz++;
    int shift = nz > 0 ? nz - 1 : 0;   // `while (J < NumZeros)` runs NumZeros-1 times
    for (size_t j = shift; j < layer[I].size(); j++) { sLinks[I].push_back(layer[I][j]); sVs[I].push_back(ivs[I][j]); }
    sDepth[I] = initDepth[I - 1] - nz;
  }
  std::vector<int> mDepth(N + 1);
  for (int I = 1; I <= N - 1; I++) mDepth[I] = sDepth[I];
  mDepth[N] = 1;
  auto mLinks = [&](int I, int J, int K) -> int { return (I == N) ? 0 : sLinks[I][J - 1][K - 1]; };
  auto mVs = [&](int I, int J) -> int { return (I == N) ? ((J == 1) ? 1 : 0) : sVs[I][J - 1]; };
  std::vector<std::vector<int>> ec(N + 1, std::vector<int>(Q + 2, 0));
  for (int Job = 2; Job <= N; Job++)
    for (int Seg = 1; Seg <= Q + 1; Seg++) {
      int tot = 0;
      for (int I = 1; I <= Job - 1; I++)
        for (int J = 1; J <= mDepth[I]; J++)
          if (mVs(I, J) == Job) { int c = 0; for (int K = 1; K <= Q + 1; K++) if (mLinks(I, J, K) == Seg) c++; tot += c; }
      ec[Job][Seg] = tot;
    }
  // ---- the compiled Sisal ----
  sisal_array_t A = sisal_array_alloc_sized(2, 96, N * (Q + 1), sizeof(gl_elem));
  A.rank = 2; A.dims[0] = N; A.dims[1] = Q + 1;
  A.lower_bound[0] = 1; A.lower_bound[1] = 1; A.stride[0] = Q + 1; A.stride[1] = 1;
  for (int i = 0; i < N * (Q + 1); i++) ((gl_elem*)A.data)[i] = ab[i];
  sisal_array_t Z = sisal_array_alloc_sized(1, 96, N, sizeof(int32_t)); Z.lower_bound[0] = 1;
  for (int i = 0; i < N; i++) ((int32_t*)Z.data)[i] = zeros[i];
  sisal_array_t D = sisal_array_alloc_sized(1, 96, N, sizeof(float)); D.lower_bound[0] = 1;
  for (int i = 0; i < N; i++) ((float*)D.data)[i] = del[i];

  GL_results r = func_MAIN(A, Z, N, Q, D);
  char msg[160];
  snprintf(msg, sizeof msg, "%s: Links is rank-3 (N, MaxD, Q+1)", tag);
  check(msg, r.links.rank == 3 && (int)r.links.dims[0] == N
         && (int)r.links.dims[1] == MaxD && (int)r.links.dims[2] == Q + 1);
  int okD = (int)r.depth.size == N;
  for (int I = 1; okD && I <= N; I++) okD = ((int32_t*)r.depth.data)[I - 1] == mDepth[I];
  snprintf(msg, sizeof msg, "%s: Depth == ragged mirror", tag);
  check(msg, okD);
  int okL = 1, okV = 1;
  for (int I = 1; I <= N; I++) for (int J = 1; J <= mDepth[I]; J++) {
    okV &= ((int32_t*)r.vs.data)[(I - 1) * MaxD + (J - 1)] == mVs(I, J);
    for (int K = 1; K <= Q + 1; K++)
      okL &= ((int32_t*)r.links.data)[((I - 1) * MaxD + (J - 1)) * (Q + 1) + (K - 1)] == mLinks(I, J, K);
  }
  snprintf(msg, sizeof msg, "%s: Links over the Depth-bounded region == mirror", tag);
  check(msg, okL);
  snprintf(msg, sizeof msg, "%s: Vs over the Depth-bounded region == mirror", tag);
  check(msg, okV);
  int okP = 1;
  for (int I = 1; I <= N; I++) for (int J = 1; J <= Q + 1; J++) {
    gl_segrec g = ((gl_segrec*)r.ptrs.data)[(I - 1) * (Q + 1) + (J - 1)];
    okP &= g.ecnt == ec[I][J] && g.prio == ab[(I - 1) * (Q + 1) + (J - 1)].prio
        && g.mx.val == 0 && g.mx.job == 0 && g.mx.seg == 0 && !g.fired && !g.leaf;
  }
  snprintf(msg, sizeof msg, "%s: Ptrs enable counts + priorities == mirror", tag);
  check(msg, okP);
}
static void test_genlinks_dv(void) {
  printf("\n=== Group: genlinks_dv (ragged layers as padded rank-3 + Depth) ===\n");
  gl_case(0.5f,  0.5f, 1.0f, "padding only (Depth 4 3 2 1 1)");
  gl_case(0.25f, 0.0f, 2.0f, "shift active (Depth 3 2 1 1 1)");
}
#endif
#ifdef TEST_GENARCS_DV
// One wavefront step of the Job Shop trace: fan out from every (job, segment)
// of the Grid, keep only arcs leaving an ENABLED, not-yet-fired segment that
// actually go somewhere, and mark those segments fired -- and leaf, when some
// of their candidate arcs were dropped.
//
// This is the forall shape a CROSS could not express until the RETURNS port
// classifier learned to follow the nested relay: `array_dv of NewSeg` is a
// gather and `value of catenate Arcs` is a reduction, on the same cross.  The
// `when` mask sits on the inner single generator, where masking is legal --
// the surviving arc count is data-dependent, so Arcs is ragged, but it is
// CATENATEd rather than gathered, which flattens the ragged pieces into one
// 1-D array_dv.  array_size(Arcs) then drives the leaf marking.
struct ga_maxr { int32_t val, job, seg; };
struct ga_segr { int32_t ecnt; ga_maxr mx; int32_t prio; bool fired, leaf; };
struct ga_arcr { int32_t job, seg; ga_maxr mx; };
static void test_genarcs_dv(void) {
  printf("\n=== Group: genarcs_dv (cross carrying gather + catenate) ===\n");
  const int N = 3, Q = 1, S = Q + 1, MaxD = 2;
  int depth[N] = { 2, 1, 1 };
  int vs[N * MaxD] = { 2, 3,  3, 0,  0, 0 };
  int links[N * MaxD * S] = { 1, 0,  2, 1,   0, 2,  0, 0,   0, 0,  0, 0 };
  ga_segr grid[N * S];
  for (int i = 0; i < N; i++) for (int k = 0; k < S; k++) {
    ga_segr g{};
    g.ecnt = (i == 2 && k == 1) ? 1 : 0;   // one segment not enabled
    g.mx = { i + 1, 0, 0 }; g.prio = 10 * (i + 1) + k;
    g.fired = (i == 1 && k == 0);          // one segment already fired
    g.leaf = false; grid[i * S + k] = g;
  }
  // ---- mirror ----
  std::vector<ga_segr> mgrid(N * S); std::vector<ga_arcr> marcs;
  for (int I = 1; I <= N; I++) for (int K = 1; K <= S; K++) {
    ga_segr seg = grid[(I - 1) * S + (K - 1)];
    int newval = seg.prio + seg.mx.val;
    std::vector<ga_arcr> arcs;
    for (int J = 1; J <= depth[I - 1]; J++) {
      int lk = links[((I - 1) * MaxD + (J - 1)) * S + (K - 1)];
      if ((seg.ecnt == 0 && !seg.fired) && lk != 0)
        arcs.push_back({ vs[(I - 1) * MaxD + (J - 1)], lk, { newval, I, K } });
    }
    ga_segr ns = seg;
    if (seg.ecnt == 0 && !seg.fired) {
      ns.mx.val = newval; ns.fired = true;
      if ((int)arcs.size() != depth[I - 1]) ns.leaf = true;
    }
    mgrid[(I - 1) * S + (K - 1)] = ns;
    for (auto& a : arcs) marcs.push_back(a);
  }
  // ---- compiled Sisal ----
  auto mk = [&](int rank, int d0, int d1, int d2, size_t esz, const void* src, size_t n) {
    sisal_array_t A = sisal_array_alloc_sized(rank, 96, n, esz);
    A.rank = rank; A.dims[0] = d0; A.lower_bound[0] = 1;
    if (rank > 1) { A.dims[1] = d1; A.lower_bound[1] = 1; }
    if (rank > 2) { A.dims[2] = d2; A.lower_bound[2] = 1; }
    if (rank == 1) A.stride[0] = 1;
    if (rank == 2) { A.stride[0] = d1; A.stride[1] = 1; }
    if (rank == 3) { A.stride[0] = d1 * d2; A.stride[1] = d2; A.stride[2] = 1; }
    memcpy(A.data, src, esz * n); return A;
  };
  sisal_array_t L = mk(3, N, MaxD, S, sizeof(int32_t), links, N * MaxD * S);
  sisal_array_t G = mk(2, N, S, 0, sizeof(ga_segr), grid, N * S);
  sisal_array_t V = mk(2, N, MaxD, 0, sizeof(int32_t), vs, N * MaxD);
  sisal_array_t Dp = mk(1, N, 0, 0, sizeof(int32_t), depth, N);

  GA_results r = func_MAIN(L, G, V, Dp, N, Q);
  check("updated Grid stays rank-2 (N, Q+1)",
        r.grid.rank == 2 && (int)r.grid.dims[0] == N && (int)r.grid.dims[1] == S);
  int okg = (int)r.grid.size == N * S;
  for (int i = 0; okg && i < N * S; i++) {
    ga_segr a = ((ga_segr*)r.grid.data)[i], b = mgrid[i];
    okg = a.ecnt == b.ecnt && a.mx.val == b.mx.val && a.prio == b.prio
       && a.fired == b.fired && a.leaf == b.leaf;
  }
  check("Grid (fired / leaf / Max.Val) == mirror", okg);
  check("catenated Arcs length is the surviving count",
        (int)r.arcs.size == (int)marcs.size());
  int oka = (int)r.arcs.size == (int)marcs.size();
  for (int i = 0; oka && i < (int)marcs.size(); i++) {
    ga_arcr a = ((ga_arcr*)r.arcs.data)[i], b = marcs[i];
    oka = a.job == b.job && a.seg == b.seg && a.mx.val == b.mx.val
       && a.mx.job == b.mx.job && a.mx.seg == b.mx.seg;
  }
  check("Arcs content and cross order == mirror", oka);
  int anyleaf = 0; for (int i = 0; i < N * S; i++) anyleaf |= mgrid[i].leaf;
  check("the mask actually bites (some segment marked leaf)", anyleaf != 0);
}
#endif
#ifdef TEST_TRACEUTIL_DV
// The utility layer at the head of trace.sis, which SortArcs and ExpandToGrid
// are built on: FindMax (max of two MaxRec by .Val, ties to the LOWER .Job),
// UpdateSeg, Unique and Diffs.
//
// Unique is the one with teeth: TWO masked gathers sharing one mask on a
// SINGLE generator, finding the start and end index of each run of equal keys.
// Masking on one generator is legal -- survivors are counted once and both
// outputs come out the same length -- unlike a mask across a cross, where the
// surviving shape would be ragged.  The run boundaries are then stitched with
// `||` onto a one-element array_dv at each end.
struct tu_sortr { float val; int32_t loc; };
static void test_traceutil_dv(void) {
  printf("\n=== Group: traceutil_dv (masked run-boundary gather + FindMax) ===\n");
  const int NS = 6, NV = 3;
  float keys[NS] = { 1, 1, 1, 2, 2, 3 };      // three runs
  std::vector<tu_sortr> sorted(NS);
  for (int i = 0; i < NS; i++) sorted[i] = { keys[i], i + 1 };
  int32_t vals[NV] = { 2, 5, 6 };
  int32_t low = 1, high = 9;
  tu_segr seg{}; seg.ecnt = 5; seg.mx = { 7, 4, 1 }; seg.prio = 3;
  seg.fired = false; seg.leaf = false;
  int32_t cnt = 2;
  tu_maxr mx = { 7, 2, 9 };                   // ties on Val -> lower Job wins

  // ---- mirror ----
  std::vector<tu_sortr> mst, mfin;
  mst.push_back({ sorted[0].val, 1 });
  for (int I = 1; I <= NS - 1; I++)
    if (sorted[I - 1].val != sorted[I].val) mst.push_back({ sorted[I].val, I + 1 });
  for (int I = 1; I <= NS - 1; I++)
    if (sorted[I - 1].val != sorted[I].val) mfin.push_back({ sorted[I - 1].val, I });
  mfin.push_back({ sorted[NS - 1].val, NS });
  std::vector<int> md;
  for (int I = 1; I <= NV; I++) md.push_back(I == 1 ? vals[0] - low : vals[I - 1] - vals[I - 2] - 1);
  md.push_back(high - vals[NV - 1]);
  tu_maxr wmax = (seg.mx.val > mx.val) ? seg.mx : (mx.val > seg.mx.val) ? mx
               : (seg.mx.job < mx.job) ? seg.mx : mx;
  tu_segr mns = seg; mns.ecnt = seg.ecnt - cnt; mns.mx = wmax;

  // ---- compiled Sisal ----
  sisal_array_t S = sisal_array_alloc_sized(1, 96, NS, sizeof(tu_sortr));
  S.lower_bound[0] = 1; memcpy(S.data, sorted.data(), sizeof(tu_sortr) * NS);
  sisal_array_t V = sisal_array_alloc_sized(1, 96, NV, sizeof(int32_t));
  V.lower_bound[0] = 1; memcpy(V.data, vals, sizeof(int32_t) * NV);
  TU_results r = func_MAIN(S, V, low, high, seg, cnt, mx);

  auto same = [](sisal_array_t a, std::vector<tu_sortr>& m) {
    if ((int)a.size != (int)m.size()) return 0;
    for (int i = 0; i < (int)m.size(); i++) {
      tu_sortr s = ((tu_sortr*)a.data)[i];
      if (s.val != m[i].val || s.loc != m[i].loc) return 0;
    }
    return 1;
  };
  check("run STARTS == mirror (one per run of equal keys)", same(r.st, mst));
  check("run ENDS == mirror", same(r.fin, mfin));
  check("both masked outputs have the same length",
        r.st.size == r.fin.size && (int)r.st.size == (int)mst.size());
  int okd = (int)r.d.size == (int)md.size();
  for (int i = 0; okd && i < (int)md.size(); i++) okd = ((int32_t*)r.d.data)[i] == md[i];
  check("Diffs expansion deltas == mirror", okd);
  check("UpdateSeg: enable count decremented", r.ns.ecnt == mns.ecnt);
  check("FindMax tie on .Val resolves to the LOWER .Job",
        r.ns.mx.val == mns.mx.val && r.ns.mx.job == mns.mx.job && r.ns.mx.seg == mns.mx.seg);
}
#endif
#ifdef TEST_ARCGRID_DV
// SortArcs + ExpandToGrid + UpdateGrid: fold a wavefront's arcs back into the
// Grid.  The original gets there by sorting the arcs by Job (Batcher),
// splitting into runs with Unique, sorting each run by Segment, splitting
// again, sorting each segment's arcs by Max.Val and keeping the last -- a
// COMPRESSED ragged pair of tables -- and then spending ExpandToGrid putting
// the holes back to recover the dense N x (Q+1) grid UpdateGrid consumes.
//
// That round trip is an artifact of the array-of-array representation, so the
// port fuses it into one cross over (job, segment) with a per-cell fold.  The
// mirror below runs the ORIGINAL three-stage pipeline -- Batcher-order sorts,
// ragged compressed tables, re-expansion -- so the fusion is CHECKED, not just
// restated in two places.  Test data gives every cell distinct Max.Vals, so
// the answer never rests on how equal keys happen to be ordered.
static ag_maxr ag_findmax(ag_maxr a, ag_maxr b) {
  if (a.val > b.val) return a;
  if (b.val > a.val) return b;
  return (a.job < b.job) ? a : b;
}
static void test_arcgrid_dv(void) {
  printf("\n=== Group: arcgrid_dv (sort/group/expand fused to a dense fold) ===\n");
  const int N = 3, Q = 1, S = Q + 1;
  std::vector<ag_arcr> arcs = {
    { 1, 1, { 5, 9, 9 } }, { 1, 1, { 8, 7, 7 } },                       // (1,1): 2 arcs
    { 1, 2, { 3, 1, 1 } },                                              // (1,2): 1 arc
    { 2, 2, { 9, 2, 2 } }, { 2, 2, { 4, 3, 3 } }, { 2, 2, { 6, 4, 4 } },// (2,2): 3 arcs
    { 3, 1, { 2, 5, 5 } },                                              // (3,1): 1 arc
  };                                                                    // (2,1),(3,2): none
  std::vector<ag_segr> grid(N * S);
  for (int i = 0; i < N; i++) for (int k = 0; k < S; k++) {
    ag_segr g{}; g.ecnt = 4; g.mx = { (i + k) % 3, 6, 6 }; g.prio = 10 * (i + 1) + k;
    g.fired = false; g.leaf = false; grid[i * S + k] = g;
  }
  // ---- mirror: the ORIGINAL pipeline ----
  std::vector<ag_arcr> byJob = arcs;
  std::stable_sort(byJob.begin(), byJob.end(),
                   [](const ag_arcr& a, const ag_arcr& b) { return a.job < b.job; });
  std::vector<int> jobLocs; std::vector<std::vector<int>> segLocs, arcCnts;
  std::vector<std::vector<ag_maxr>> maxArcs;
  for (size_t i = 0; i < byJob.size();) {
    size_t j = i; while (j < byJob.size() && byJob[j].job == byJob[i].job) j++;
    std::vector<ag_arcr> aJob(byJob.begin() + i, byJob.begin() + j);
    std::stable_sort(aJob.begin(), aJob.end(),
                     [](const ag_arcr& a, const ag_arcr& b) { return a.seg < b.seg; });
    std::vector<int> sl, ac; std::vector<ag_maxr> ma;
    for (size_t p = 0; p < aJob.size();) {
      size_t q2 = p; while (q2 < aJob.size() && aJob[q2].seg == aJob[p].seg) q2++;
      std::vector<ag_arcr> cell(aJob.begin() + p, aJob.begin() + q2);
      std::stable_sort(cell.begin(), cell.end(),
                       [](const ag_arcr& a, const ag_arcr& b) { return a.mx.val < b.mx.val; });
      ma.push_back(cell.back().mx); ac.push_back((int)cell.size()); sl.push_back(aJob[p].seg);
      p = q2;
    }
    jobLocs.push_back(byJob[i].job); segLocs.push_back(sl);
    arcCnts.push_back(ac); maxArcs.push_back(ma);
    i = j;
  }
  ag_maxr zero{ 0, 0, 0 };
  std::vector<ag_maxr> mMax(N * S, zero); std::vector<int> mCnt(N * S, 0);
  for (size_t r = 0; r < jobLocs.size(); r++) {
    int I = jobLocs[r];
    for (size_t c = 0; c < segLocs[r].size(); c++) {
      int K = segLocs[r][c];
      mMax[(I - 1) * S + (K - 1)] = maxArcs[r][c];
      mCnt[(I - 1) * S + (K - 1)] = arcCnts[r][c];
    }
  }
  std::vector<ag_segr> mGrid(N * S);
  for (int I = 1; I <= N; I++) for (int K = 1; K <= S; K++) {
    ag_segr g = grid[(I - 1) * S + (K - 1)]; int c = mCnt[(I - 1) * S + (K - 1)];
    if (c != 0) { g.ecnt = g.ecnt - c; g.mx = ag_findmax(g.mx, mMax[(I - 1) * S + (K - 1)]); }
    mGrid[(I - 1) * S + (K - 1)] = g;
  }
  // ---- compiled Sisal ----
  sisal_array_t A = sisal_array_alloc_sized(1, 96, arcs.size(), sizeof(ag_arcr));
  A.lower_bound[0] = 1; memcpy(A.data, arcs.data(), sizeof(ag_arcr) * arcs.size());
  sisal_array_t G = sisal_array_alloc_sized(2, 96, N * S, sizeof(ag_segr));
  G.rank = 2; G.dims[0] = N; G.dims[1] = S; G.lower_bound[0] = 1; G.lower_bound[1] = 1;
  G.stride[0] = S; G.stride[1] = 1; memcpy(G.data, grid.data(), sizeof(ag_segr) * N * S);
  AG_results r = func_MAIN(A, G, N, Q);

  int okc = (int)r.cnts.size == N * S, okm = 1, okg = 1;
  for (int i = 0; i < N * S; i++) {
    okc &= ((int32_t*)r.cnts.data)[i] == mCnt[i];
    ag_maxr a = ((ag_maxr*)r.maxs.data)[i];
    okm &= a.val == mMax[i].val && a.job == mMax[i].job && a.seg == mMax[i].seg;
    ag_segr g = ((ag_segr*)r.grid.data)[i];
    okg &= g.ecnt == mGrid[i].ecnt && g.mx.val == mGrid[i].mx.val
        && g.mx.job == mGrid[i].mx.job && g.prio == mGrid[i].prio
        && g.fired == mGrid[i].fired;
  }
  check("per-cell arc counts == original pipeline", okc);
  check("per-cell best Max == original pipeline", okm);
  check("updated Grid (enable counts + folded Max) == original pipeline", okg);
  check("cells with no arcs keep a zero Max and count",
        ((int32_t*)r.cnts.data)[2] == 0 && ((ag_maxr*)r.maxs.data)[2].val == 0);
  check("a cell with several arcs keeps the greatest Max.Val",
        ((int32_t*)r.cnts.data)[3] == 3 && ((ag_maxr*)r.maxs.data)[3].val == 9);
}
#endif
#ifdef TEST_TRACE_DV
// The whole Job Shop wavefront to fixpoint, and the last function of
// trace.sis: fan arcs out of every enabled unfired segment, fold them back
// into the Grid (decrementing enable counts, which is what enables the next
// wave), repeat until a pass yields no arcs.  What propagates is the
// longest-path value: a segment's Max.Val becomes its own priority plus the
// best value arriving at it.
//
// The loop is SENTINEL-terminated -- `while (array_size(Arcs) ~= 0)`, no
// derivable trip count.  That is fatal for a for-initial GATHER, which must
// size its allocation up front (backtrack_dv had to accumulate into a list
// and pack once at the end).  Here it costs nothing: `value of Grid` is a
// FINALVALUE, which keeps the last iteration's value and allocates nothing,
// so the sentinel loop lowers directly.
//
// The mirror runs the ORIGINAL staging throughout -- GenArcs, then the
// Batcher-order sorts / ragged compressed tables / re-expansion that the port
// fuses -- so the whole pipeline is checked end to end, not just its pieces.
enum { TR_N = 3, TR_Q = 1, TR_S = TR_Q + 1, TR_MAXD = 2 };
static int tr_depth[TR_N] = { 2, 1, 1 };
static int tr_vs[TR_N * TR_MAXD] = { 2, 3,  3, 0,  0, 0 };
static int tr_links[TR_N * TR_MAXD * TR_S];
static tr_maxr tr_findmax(tr_maxr a, tr_maxr b) {
  if (a.val > b.val) return a;
  if (b.val > a.val) return b;
  return (a.job < b.job) ? a : b;
}
static void tr_genarcs(std::vector<tr_segr>& grid, std::vector<tr_arcr>& out) {
  std::vector<tr_segr> ng(TR_N * TR_S); out.clear();
  for (int I = 1; I <= TR_N; I++) for (int K = 1; K <= TR_S; K++) {
    tr_segr seg = grid[(I - 1) * TR_S + (K - 1)];
    int newval = seg.prio + seg.mx.val;
    std::vector<tr_arcr> arcs;
    for (int J = 1; J <= tr_depth[I - 1]; J++) {
      int lk = tr_links[((I - 1) * TR_MAXD + (J - 1)) * TR_S + (K - 1)];
      if ((seg.ecnt == 0 && !seg.fired) && lk != 0)
        arcs.push_back({ tr_vs[(I - 1) * TR_MAXD + (J - 1)], lk, { newval, I, K } });
    }
    tr_segr ns = seg;
    if (seg.ecnt == 0 && !seg.fired) {
      ns.mx.val = newval; ns.fired = true;
      if ((int)arcs.size() != tr_depth[I - 1]) ns.leaf = true;
    }
    ng[(I - 1) * TR_S + (K - 1)] = ns;
    for (auto& a : arcs) out.push_back(a);
  }
  grid = ng;
}
static void tr_arcgrid(const std::vector<tr_arcr>& arcs, std::vector<tr_segr>& grid) {
  std::vector<tr_arcr> byJob = arcs;
  std::stable_sort(byJob.begin(), byJob.end(),
                   [](const tr_arcr& a, const tr_arcr& b) { return a.job < b.job; });
  tr_maxr zero{ 0, 0, 0 };
  std::vector<tr_maxr> mMax(TR_N * TR_S, zero); std::vector<int> mCnt(TR_N * TR_S, 0);
  for (size_t i = 0; i < byJob.size();) {
    size_t j = i; while (j < byJob.size() && byJob[j].job == byJob[i].job) j++;
    std::vector<tr_arcr> aJob(byJob.begin() + i, byJob.begin() + j);
    std::stable_sort(aJob.begin(), aJob.end(),
                     [](const tr_arcr& a, const tr_arcr& b) { return a.seg < b.seg; });
    for (size_t p = 0; p < aJob.size();) {
      size_t q2 = p; while (q2 < aJob.size() && aJob[q2].seg == aJob[p].seg) q2++;
      std::vector<tr_arcr> cell(aJob.begin() + p, aJob.begin() + q2);
      std::stable_sort(cell.begin(), cell.end(),
                       [](const tr_arcr& a, const tr_arcr& b) { return a.mx.val < b.mx.val; });
      int I = byJob[i].job, K = aJob[p].seg;
      mMax[(I - 1) * TR_S + (K - 1)] = cell.back().mx;
      mCnt[(I - 1) * TR_S + (K - 1)] = (int)cell.size();
      p = q2;
    }
    i = j;
  }
  for (int I = 1; I <= TR_N; I++) for (int K = 1; K <= TR_S; K++) {
    int c = mCnt[(I - 1) * TR_S + (K - 1)];
    if (c != 0) {
      tr_segr& g = grid[(I - 1) * TR_S + (K - 1)];
      g.ecnt -= c; g.mx = tr_findmax(g.mx, mMax[(I - 1) * TR_S + (K - 1)]);
    }
  }
}
static void test_trace_dv(void) {
  printf("\n=== Group: trace_dv (sentinel wavefront to fixpoint) ===\n");
  memset(tr_links, 0, sizeof tr_links);
  auto L = [&](int I, int J, int K) -> int& {
    return tr_links[((I - 1) * TR_MAXD + (J - 1)) * TR_S + (K - 1)]; };
  L(1,1,1) = 1; L(1,1,2) = 2;      // job1 -> job2, segment-wise
  L(1,2,1) = 1; L(1,2,2) = 1;      // job1 -> job3 seg1 from both segments
  L(2,1,1) = 2; L(2,1,2) = 2;      // job2 -> job3 seg2
  int ecnt[TR_N * TR_S] = { 0, 0,  1, 1,  2, 2 };   // incoming arc counts
  std::vector<tr_segr> grid0(TR_N * TR_S);
  for (int i = 0; i < TR_N; i++) for (int k = 0; k < TR_S; k++) {
    tr_segr g{}; g.ecnt = ecnt[i * TR_S + k]; g.mx = { 0, 0, 0 };
    g.prio = 10 * (i + 1) + (k + 1); g.fired = false; g.leaf = false;
    grid0[i * TR_S + k] = g;
  }
  // ---- mirror: wavefront to fixpoint, original staging ----
  std::vector<tr_segr> mg = grid0; std::vector<tr_arcr> arcs;
  tr_genarcs(mg, arcs);
  int waves = 0;
  while (!arcs.empty()) {
    waves++;
    std::vector<tr_segr> tmp = mg; tr_arcgrid(arcs, tmp);
    mg = tmp; tr_genarcs(mg, arcs);
  }
  // ---- compiled Sisal ----
  auto mk = [&](int rank, int d0, int d1, int d2, size_t esz, const void* src, size_t n) {
    sisal_array_t A = sisal_array_alloc_sized(rank, 96, n, esz);
    A.rank = rank; A.dims[0] = d0; A.lower_bound[0] = 1;
    if (rank > 1) { A.dims[1] = d1; A.lower_bound[1] = 1; }
    if (rank > 2) { A.dims[2] = d2; A.lower_bound[2] = 1; }
    if (rank == 1) A.stride[0] = 1;
    if (rank == 2) { A.stride[0] = d1; A.stride[1] = 1; }
    if (rank == 3) { A.stride[0] = d1 * d2; A.stride[1] = d2; A.stride[2] = 1; }
    memcpy(A.data, src, esz * n); return A;
  };
  sisal_array_t Lk = mk(3, TR_N, TR_MAXD, TR_S, sizeof(int32_t), tr_links, TR_N * TR_MAXD * TR_S);
  sisal_array_t P  = mk(2, TR_N, TR_S, 0, sizeof(tr_segr), grid0.data(), TR_N * TR_S);
  sisal_array_t V  = mk(2, TR_N, TR_MAXD, 0, sizeof(int32_t), tr_vs, TR_N * TR_MAXD);
  sisal_array_t Dp = mk(1, TR_N, 0, 0, sizeof(int32_t), tr_depth, TR_N);
  sisal_array_t r = func_MAIN(Lk, P, V, Dp, TR_N, TR_Q);

  check("result is the rank-2 Grid", r.rank == 2 && (int)r.size == TR_N * TR_S);
  int ok = (int)r.size == TR_N * TR_S;
  for (int i = 0; ok && i < TR_N * TR_S; i++) {
    tr_segr a = ((tr_segr*)r.data)[i], b = mg[i];
    ok = a.ecnt == b.ecnt && a.fired == b.fired && a.leaf == b.leaf
      && a.mx.val == b.mx.val && a.mx.job == b.mx.job && a.mx.seg == b.mx.seg
      && a.prio == b.prio;
  }
  check("converged Grid == original staged pipeline", ok);
  int allfired = 1, anyleaf = 0;
  for (int i = 0; i < TR_N * TR_S; i++) {
    allfired &= ((tr_segr*)r.data)[i].fired;
    anyleaf |= ((tr_segr*)r.data)[i].leaf;
  }
  check("the sentinel loop ran to fixpoint (every segment fired)", allfired);
  check("terminal segments are marked leaf", anyleaf);
  check("longest-path value propagated: (2,1) = prio 21 + best incoming 11",
        ((tr_segr*)r.data)[2].mx.val == 32);
  check("longest-path value propagated: (3,2) = prio 32 + max(32,34)",
        ((tr_segr*)r.data)[5].mx.val == 66);
  check("mirror needed more than one wavefront", waves >= 2);
}
#endif
#ifdef TEST_JOB_DV
// The Job Shop Scheduler END TO END -- unit/job.sis with its six includes
// assembled: sort jobs by window start (Batcher), cut each into Q+1 segments
// (AlphaBeta), find pairwise conflicts (Successors), build the Link/Ptr
// arrays (GenLinks), trace all paths to fixpoint (Trace), pick the max-valued
// leaf and walk back (BackTrack), then map the schedule to ORIGINAL job
// numbers.  Every stage is separately checked against the original in its own
// group; this one checks that the composition is right.
//
// The mirror re-runs all seven stages independently.  GenLinks is mirrored in
// the original RAGGED form and then materialised into the padded layout the
// port uses -- genlinks_dv is what establishes those agree inside Depth.
// Job Start times are distinct, so Batcher's order is unambiguous and the
// answer does not depend on how it breaks ties.
static jb_maxr jb_findmax(jb_maxr a, jb_maxr b) {
  if (a.val > b.val) return a;
  if (b.val > a.val) return b;
  return (a.job < b.job) ? a : b;
}
static void test_job_dv(void) {
  printf("\n=== Group: job_dv (Job Shop Scheduler, end to end) ===\n");
  const int N = 4, Q = 2, S = Q + 1, MaxD = N - 1;
  std::vector<jb_srec> A = { { 5.0f, 20.0f, 4.0f, 3 }, { 1.0f, 12.0f, 3.0f, 5 },
                             { 8.0f, 25.0f, 5.0f, 2 }, { 3.0f, 16.0f, 2.0f, 7 } };
  auto cmp_row = [&](const jb_elem* r1, const jb_elem* r2, float del) {
    std::vector<int> o(Q + 1);
    for (int i = 1; i <= Q + 1; i++) {
      float diff = r1[i - 1].beta - r2[0].alpha; int ix;
      if (diff > 0.0f && del == 0.0f) ix = 0;
      else if (diff <= 0.0f) ix = 1;
      else { float ri = diff / del + 1.0f; int ii = (int)std::floor(ri);
             int t = ((ri - (float)ii) == 0.0f) ? ii : ii + 1; ix = (t > Q + 1) ? 0 : t; }
      o[i - 1] = ix;
    }
    return o;
  };
  auto rsum = [](const std::vector<int>& v) { int s2 = 0; for (int x : v) s2 += x; return s2; };

  // 1) Batcher
  std::vector<jb_sortr> sorted(N);
  for (int i = 0; i < N; i++) sorted[i] = { A[i].start, i + 1 };
  std::stable_sort(sorted.begin(), sorted.end(),
                   [](const jb_sortr& a, const jb_sortr& b) { return a.val < b.val; });
  std::vector<jb_srec> sortedA(N);
  for (int i = 0; i < N; i++) sortedA[i] = A[sorted[i].loc - 1];
  // 2) AlphaBeta
  std::vector<jb_elem> ab(N * S); std::vector<float> del(N);
  for (int j = 0; j < N; j++) {
    float ls = sortedA[j].finish - sortedA[j].dur;
    float d = (ls - sortedA[j].start) / (float)Q; del[j] = d;
    for (int i = 1; i <= S; i++) {
      float a = sortedA[j].start + (float)(i - 1) * d;
      ab[j * S + (i - 1)] = { a, a + sortedA[j].dur, sortedA[j].prio };
    }
  }
  // 3) Successors
  std::vector<int> zeros(N, 0);
  for (int I = 1; I <= N - 1; I++) zeros[I - 1] = rsum(cmp_row(&ab[(I - 1) * S], &ab[I * S], del[I]));
  zeros[N - 1] = 0;
  // 4) GenLinks (ragged, then materialised padded)
  std::vector<int> initDepth(N, 0);
  std::vector<std::vector<std::vector<int>>> layer(N + 1);
  std::vector<std::vector<int>> flags(N + 1), ivsv(N + 1);
  for (int I = 1; I <= N - 1; I++) {
    int cnt = 1; while ((I + cnt) < N && zeros[I + cnt - 1] == 0) cnt++;
    initDepth[I - 1] = cnt;
    for (int J = 1; J <= cnt; J++) {
      int dest = I + J;
      std::vector<int> row = cmp_row(&ab[(I - 1) * S], &ab[(dest - 1) * S], del[dest - 1]);
      layer[I].push_back(row); flags[I].push_back(rsum(row)); ivsv[I].push_back(dest);
    }
  }
  std::vector<int> mDepth(N + 1, 0);
  std::vector<std::vector<std::vector<int>>> sL(N + 1);
  std::vector<std::vector<int>> sV(N + 1);
  for (int I = 1; I <= N - 1; I++) {
    int nz = 0; for (int J = 1; J <= initDepth[I - 1] - 1; J++) if (flags[I][J - 1] == 0) nz++;
    int sh = nz > 0 ? nz - 1 : 0;
    for (size_t j2 = sh; j2 < layer[I].size(); j2++) { sL[I].push_back(layer[I][j2]); sV[I].push_back(ivsv[I][j2]); }
    mDepth[I] = initDepth[I - 1] - nz;
  }
  mDepth[N] = 1;
  std::vector<int> links(N * MaxD * S, 0), vs(N * MaxD, 0);
  for (int I = 1; I <= N - 1; I++) for (int J = 1; J <= MaxD; J++) {
    if (J <= (int)sV[I].size()) vs[(I - 1) * MaxD + (J - 1)] = sV[I][J - 1];
    for (int K = 1; K <= S; K++)
      if (J <= (int)sL[I].size()) links[((I - 1) * MaxD + (J - 1)) * S + (K - 1)] = sL[I][J - 1][K - 1];
  }
  vs[(N - 1) * MaxD + 0] = 1;
  std::vector<int> ecnts(N * S, 0);
  for (int Job = 2; Job <= N; Job++) for (int Seg = 1; Seg <= S; Seg++) {
    int tot = 0;
    for (int I = 1; I <= Job - 1; I++) for (int J = 1; J <= mDepth[I]; J++)
      if (vs[(I - 1) * MaxD + (J - 1)] == Job)
        for (int K = 1; K <= S; K++) if (links[((I - 1) * MaxD + (J - 1)) * S + (K - 1)] == Seg) tot++;
    ecnts[(Job - 1) * S + (Seg - 1)] = tot;
  }
  std::vector<jb_segr> ptrs(N * S);
  for (int I = 1; I <= N; I++) for (int J = 1; J <= S; J++) {
    jb_segr g{}; g.ecnt = ecnts[(I - 1) * S + (J - 1)]; g.mx = { 0, 0, 0 };
    g.prio = ab[(I - 1) * S + (J - 1)].prio; g.fired = false; g.leaf = false;
    ptrs[(I - 1) * S + (J - 1)] = g;
  }
  // 5) Trace
  auto genarcs = [&](std::vector<jb_segr>& grid, std::vector<jb_arcr>& out) {
    std::vector<jb_segr> ng(N * S); out.clear();
    for (int I = 1; I <= N; I++) for (int K = 1; K <= S; K++) {
      jb_segr seg = grid[(I - 1) * S + (K - 1)]; int nv = seg.prio + seg.mx.val;
      std::vector<jb_arcr> arcs;
      for (int J = 1; J <= mDepth[I]; J++) {
        int lk = links[((I - 1) * MaxD + (J - 1)) * S + (K - 1)];
        if ((seg.ecnt == 0 && !seg.fired) && lk != 0)
          arcs.push_back({ vs[(I - 1) * MaxD + (J - 1)], lk, { nv, I, K } });
      }
      jb_segr ns = seg;
      if (seg.ecnt == 0 && !seg.fired) { ns.mx.val = nv; ns.fired = true;
        if ((int)arcs.size() != mDepth[I]) ns.leaf = true; }
      ng[(I - 1) * S + (K - 1)] = ns;
      for (auto& a : arcs) out.push_back(a);
    }
    grid = ng;
  };
  auto arcgrid = [&](const std::vector<jb_arcr>& arcs, std::vector<jb_segr>& grid) {
    jb_maxr zero{ 0, 0, 0 };
    std::vector<jb_maxr> mm(N * S, zero); std::vector<int> mc(N * S, 0);
    for (auto& a : arcs) {
      int i2 = (a.job - 1) * S + (a.seg - 1);
      if (mc[i2] == 0 || a.mx.val > mm[i2].val) mm[i2] = a.mx;
      mc[i2]++;
    }
    for (int i2 = 0; i2 < N * S; i2++)
      if (mc[i2] != 0) { grid[i2].ecnt -= mc[i2]; grid[i2].mx = jb_findmax(grid[i2].mx, mm[i2]); }
  };
  std::vector<jb_segr> mg = ptrs; std::vector<jb_arcr> arcs; genarcs(mg, arcs);
  int waves = 0;
  while (!arcs.empty()) { waves++; std::vector<jb_segr> t = mg; arcgrid(arcs, t); mg = t; genarcs(mg, arcs); }
  // 6) BackTrack
  int bv = -1, bj = 1, bs = 1;
  for (int k = 1; k <= N * S; k++) {
    int j2 = ((k - 1) / S) + 1, s2 = ((k - 1) % S) + 1;
    if (mg[(j2 - 1) * S + (s2 - 1)].leaf) {
      int v = mg[(j2 - 1) * S + (s2 - 1)].mx.val;
      if (v > bv) { bv = v; bj = j2; bs = s2; }
    }
  }
  std::vector<int> chain;
  { int nj = bj, ns2 = bs; chain.push_back(nj);
    while (mg[(nj - 1) * S + (ns2 - 1)].mx.job != 0) {
      int pj = mg[(nj - 1) * S + (ns2 - 1)].mx.job, ps = mg[(nj - 1) * S + (ns2 - 1)].mx.seg;
      nj = pj; ns2 = ps; chain.push_back(nj);
    } }
  std::reverse(chain.begin(), chain.end());
  // 7) original job numbers
  std::vector<int> mpath; for (int e : chain) mpath.push_back(sorted[e - 1].loc);

  // ---- compiled Sisal ----
  sisal_array_t Aa = sisal_array_alloc_sized(1, 96, N, sizeof(jb_srec));
  Aa.lower_bound[0] = 1; memcpy(Aa.data, A.data(), sizeof(jb_srec) * N);
  JOB_results r = func_MAIN(Q, Aa);

  check("FinalPtrs is the rank-2 job x segment grid",
        r.finalptrs.rank == 2 && (int)r.finalptrs.size == N * S);
  int okf = (int)r.finalptrs.size == N * S;
  for (int i = 0; okf && i < N * S; i++) {
    jb_segr a = ((jb_segr*)r.finalptrs.data)[i], b = mg[i];
    okf = a.ecnt == b.ecnt && a.fired == b.fired && a.leaf == b.leaf
       && a.mx.val == b.mx.val && a.mx.job == b.mx.job && a.mx.seg == b.mx.seg
       && a.prio == b.prio;
  }
  check("FinalPtrs == the seven-stage mirror", okf);
  int okp = (int)r.path.size == (int)mpath.size();
  for (int i = 0; okp && i < (int)mpath.size(); i++) okp = ((int32_t*)r.path.data)[i] == mpath[i];
  check("job schedule (in ORIGINAL job numbers) == mirror", okp);
  int allfired = 1; for (int i = 0; i < N * S; i++) allfired &= ((jb_segr*)r.finalptrs.data)[i].fired;
  check("trace reached fixpoint (every segment fired)", allfired);
  check("the trace took several wavefronts", waves >= 2);
  // priorities are 3,5,2,7; the best path chains all four jobs, so 17
  check("best path value is the sum of all four priorities (17)", bv == 17);
  check("schedule is a permutation of the four jobs", (int)r.path.size == N);
}
#endif
#ifdef TEST_MOLDYN_FORCE_DV
// The force core of moldyn -- T. M. DeBoni's Newtonian pairwise particle
// dynamics modeller -- and the inner loop of that simulation: for every
// particle, the total force its neighbours exert under a Morse potential with
// a numerical adjustment term.
//
// Three things are being exercised.  The state vector S is FLAT with stride 6
// per particle (x,y,z,vx,vy,vz), so particle P starts at (P-1)*6+1.  The six
// Morse parameter tables are indexed by a PAIR of particle types, A1[Tp,Tn],
// carried as flat rank-2 array_dv fields inside one record -- struct of
// arrays, the shape moldyn's ENSEMBLE record already used.  And the neighbour
// lists are ragged (how many neighbours a particle has is a property of the
// configuration), so they are a rectangular padded NEIGHBORS with NCOUNT
// giving each row's valid extent, as GenLinks' layers are.
//
// Force also selects its component with CHARACTER literals 'X'/'Y'/'Z', which
// is why the test data gives all three components distinct values -- a mix-up
// between them would show.  One particle is placed far outside the cutoff so
// it has NO neighbours, taking the zero-trip path where the sum reductions
// must yield 0 rather than garbage.
//
// FIDELITY: the original never calls the exp intrinsic; it defines e_to_power
// as `exp(e, X)`, e-to-the-X via the two-argument power, with e written to
// nine digits.  The mirror uses powf(2.718281828f, x) to match, since that is
// not bit-identical to expf(x).
enum { MD_NP = 5, MD_NT = 2, MD_MAXN = MD_NP - 1 };
static float md_a1[MD_NT * MD_NT], md_b1[MD_NT * MD_NT], md_re[MD_NT * MD_NT];
static float md_rc[MD_NT * MD_NT], md_alfa[MD_NT * MD_NT], md_c0[MD_NT * MD_NT];
static float md_S[MD_NP * 6]; static int md_types[MD_NP];
static float md_e_to_power(float x) { return powf(2.718281828f, x); }
static float md_sep(float x1, float y1, float z1, float x2, float y2, float z2) {
  float dx = x1 - x2, dy = y1 - y2, dz = z1 - z2;
  return sqrtf(dx * dx + dy * dy + dz * dz);
}
static float md_basic_morse(float R, float A1, float B1, float Re) {
  return (-1.0f / B1) * md_e_to_power(-2.0f * A1 * (R - Re))
       + ( 1.0f / B1) * md_e_to_power(-A1 * (R - Re));
}
static float md_f_adjust(float R, int t1, int t2) {
  float A = md_alfa[(t1 - 1) * MD_NT + (t2 - 1)], C = md_c0[(t1 - 1) * MD_NT + (t2 - 1)];
  return A * md_e_to_power(A * (R - C));
}
static float md_morse_force(float R, int tp, int tn, float dq) {
  float A = md_a1[(tp - 1) * MD_NT + (tn - 1)], B = md_b1[(tp - 1) * MD_NT + (tn - 1)];
  float Re = md_re[(tp - 1) * MD_NT + (tn - 1)];
  return -(md_basic_morse(R, A, B, Re) - md_f_adjust(R, tp, tn)) * dq / R;
}
static float md_force(int p, int n, char dim) {
  int j = (p - 1) * 6, k = (n - 1) * 6;
  float xp = md_S[j], yp = md_S[j + 1], zp = md_S[j + 2];
  float xn = md_S[k], yn = md_S[k + 1], zn = md_S[k + 2];
  int tp = md_types[p - 1], tn = md_types[n - 1];
  float R = md_sep(xp, yp, zp, xn, yn, zn);
  float dq = (dim == 'X') ? (xp - xn) : (dim == 'Y') ? (yp - yn) : (zp - zn);
  return md_morse_force(R, tp, tn, dq);
}
static void test_moldyn_force_dv(void) {
  printf("\n=== Group: moldyn_force_dv (Morse force over ragged neighbours) ===\n");
  float pos[MD_NP][3] = { { 0.0f, 0.0f, 0.0f }, { 1.1f, 0.2f, 0.0f },
                          { 0.3f, 1.0f, 0.4f }, { 2.0f, 1.6f, 0.5f },
                          { 9.0f, 9.0f, 9.0f } };   // last one is isolated
  for (int p = 0; p < MD_NP; p++) {
    md_S[p * 6] = pos[p][0]; md_S[p * 6 + 1] = pos[p][1]; md_S[p * 6 + 2] = pos[p][2];
    md_S[p * 6 + 3] = 0.1f * p; md_S[p * 6 + 4] = 0.0f; md_S[p * 6 + 5] = -0.05f * p;
  }
  int t[MD_NP] = { 1, 2, 1, 2, 1 }; memcpy(md_types, t, sizeof t);
  for (int i = 0; i < MD_NT; i++) for (int j = 0; j < MD_NT; j++) {
    int x = i * MD_NT + j;
    md_a1[x] = 1.0f + 0.1f * x; md_b1[x] = 2.0f + 0.2f * x;
    md_re[x] = 1.0f + 0.05f * x; md_rc[x] = 3.0f;
    md_alfa[x] = 0.5f + 0.1f * x; md_c0[x] = 2.5f + 0.1f * x;
  }
  const float CUT = 2.0f;
  std::vector<int> nb(MD_NP * MD_MAXN, 0), nc(MD_NP, 0);
  for (int p = 1; p <= MD_NP; p++) {
    int c = 0;
    for (int q = 1; q <= MD_NP; q++) if (q != p) {
      float R = md_sep(pos[p - 1][0], pos[p - 1][1], pos[p - 1][2],
                       pos[q - 1][0], pos[q - 1][1], pos[q - 1][2]);
      if (R <= CUT) nb[(p - 1) * MD_MAXN + (c++)] = q;
    }
    nc[p - 1] = c;
  }
  // ---- mirror ----
  std::vector<float> mfx(MD_NP, 0), mfy(MD_NP, 0), mfz(MD_NP, 0);
  for (int p = 1; p <= MD_NP; p++) {
    float fx = 0, fy = 0, fz = 0;
    for (int i = 0; i < nc[p - 1]; i++) {
      int n = nb[(p - 1) * MD_MAXN + i];
      fx += md_force(p, n, 'X'); fy += md_force(p, n, 'Y'); fz += md_force(p, n, 'Z');
    }
    mfx[p - 1] = fx; mfy[p - 1] = fy; mfz[p - 1] = fz;
  }
  // ---- compiled Sisal ----
  auto mk1 = [&](const void* src, size_t n, size_t esz) {
    sisal_array_t A = sisal_array_alloc_sized(1, 96, n, esz);
    A.lower_bound[0] = 1; A.stride[0] = 1; memcpy(A.data, src, esz * n); return A;
  };
  auto mk2 = [&](const void* src, int d0, int d1, size_t esz) {
    sisal_array_t A = sisal_array_alloc_sized(2, 96, (size_t)d0 * d1, esz);
    A.rank = 2; A.dims[0] = d0; A.dims[1] = d1;
    A.lower_bound[0] = 1; A.lower_bound[1] = 1; A.stride[0] = d1; A.stride[1] = 1;
    memcpy(A.data, src, esz * (size_t)d0 * d1); return A;
  };
  md_pd pd; pd.nt = MD_NT;
  pd.A1 = mk2(md_a1, MD_NT, MD_NT, sizeof(float));
  pd.B1 = mk2(md_b1, MD_NT, MD_NT, sizeof(float));
  pd.Re = mk2(md_re, MD_NT, MD_NT, sizeof(float));
  pd.Rc = mk2(md_rc, MD_NT, MD_NT, sizeof(float));
  pd.ALFA = mk2(md_alfa, MD_NT, MD_NT, sizeof(float));
  pd.C0 = mk2(md_c0, MD_NT, MD_NT, sizeof(float));
  float mass[MD_NT] = { 1.0f, 2.0f };
  pd.MASS = mk1(mass, MD_NT, sizeof(float));
  pd.dt = 0.01f; pd.endt = 1.0f; pd.tol = 1e-6f;
  sisal_array_t S = mk1(md_S, MD_NP * 6, sizeof(float));
  sisal_array_t T = mk1(md_types, MD_NP, sizeof(int32_t));
  sisal_array_t NB = mk2(nb.data(), MD_NP, MD_MAXN, sizeof(int32_t));
  sisal_array_t NC = mk1(nc.data(), MD_NP, sizeof(int32_t));
  MD_results r = func_MAIN(S, T, NB, NC, pd, MD_NP);

  check("one force triple per particle",
        (int)r.fx.size == MD_NP && (int)r.fy.size == MD_NP && (int)r.fz.size == MD_NP);
  int ok = (int)r.fx.size == MD_NP;
  for (int p = 0; ok && p < MD_NP; p++) {
    float sx = ((float*)r.fx.data)[p], sy = ((float*)r.fy.data)[p], sz = ((float*)r.fz.data)[p];
    float tol = 1e-4f * (1.0f + fabsf(mfx[p]) + fabsf(mfy[p]) + fabsf(mfz[p]));
    ok = fabsf(sx - mfx[p]) < tol && fabsf(sy - mfy[p]) < tol && fabsf(sz - mfz[p]) < tol;
  }
  check("Morse forces == C mirror (all three components)", ok);
  check("neighbour counts genuinely vary (2 3 3 2 0)",
        nc[0] == 2 && nc[1] == 3 && nc[2] == 3 && nc[3] == 2 && nc[4] == 0);
  check("isolated particle gets exactly zero force (zero-trip sum)",
        ((float*)r.fx.data)[4] == 0.0f && ((float*)r.fy.data)[4] == 0.0f
        && ((float*)r.fz.data)[4] == 0.0f);
  int distinct = 1;
  for (int p = 0; p < MD_NP - 1; p++)
    if (mfx[p] == mfy[p] || mfy[p] == mfz[p]) distinct = 0;
  check("X/Y/Z components differ, so a character mix-up would show", distinct);
}
#endif
#ifdef TEST_MOLDYN_DIFFUN_DV
// moldyn's Diffun: the DERIVATIVE the ODE solver calls.  For each particle the
// state derivative is (vx, vy, vz, ax, ay, az) -- the velocity components read
// straight out of the state vector, the accelerations the Morse forces divided
// by the particle's mass.  Built on the force core, so this stage adds only the
// per-particle assembly.
//
// The original builds each 6-slot chunk with array_fill + a multi-element
// replace (fill every slot with 0.0, then overwrite all six); under a dope
// vector the chunk is written out and catenated, with no scratch buffer.
// Masses differ per type, so a wrong MASS[TYPES[I]] lookup would show.
enum { DF_NP = 5, DF_NT = 2, DF_MAXN = DF_NP - 1 };
static float df_a1[DF_NT * DF_NT], df_b1[DF_NT * DF_NT], df_re[DF_NT * DF_NT];
static float df_alfa[DF_NT * DF_NT], df_c0[DF_NT * DF_NT];
static float df_S[DF_NP * 6]; static int df_types[DF_NP];
static float df_e2p(float x) { return powf(2.718281828f, x); }
static float df_sep(float x1, float y1, float z1, float x2, float y2, float z2) {
  float dx = x1 - x2, dy = y1 - y2, dz = z1 - z2;
  return sqrtf(dx * dx + dy * dy + dz * dz);
}
static float df_force(int p, int n, char dim) {
  int j = (p - 1) * 6, k = (n - 1) * 6;
  float xp = df_S[j], yp = df_S[j + 1], zp = df_S[j + 2];
  float xn = df_S[k], yn = df_S[k + 1], zn = df_S[k + 2];
  int tp = df_types[p - 1], tn = df_types[n - 1];
  int x = (tp - 1) * DF_NT + (tn - 1);
  float R = df_sep(xp, yp, zp, xn, yn, zn);
  float basic = (-1.0f / df_b1[x]) * df_e2p(-2.0f * df_a1[x] * (R - df_re[x]))
              + ( 1.0f / df_b1[x]) * df_e2p(-df_a1[x] * (R - df_re[x]));
  float fadj = df_alfa[x] * df_e2p(df_alfa[x] * (R - df_c0[x]));
  float dq = (dim == 'X') ? (xp - xn) : (dim == 'Y') ? (yp - yn) : (zp - zn);
  return -(basic - fadj) * dq / R;
}
static void test_moldyn_diffun_dv(void) {
  printf("\n=== Group: moldyn_diffun_dv (state derivative: v and F/mass) ===\n");
  float pos[DF_NP][3] = { { 0.0f, 0.0f, 0.0f }, { 1.1f, 0.2f, 0.0f },
                          { 0.3f, 1.0f, 0.4f }, { 2.0f, 1.6f, 0.5f },
                          { 9.0f, 9.0f, 9.0f } };
  for (int p = 0; p < DF_NP; p++) {
    df_S[p * 6] = pos[p][0]; df_S[p * 6 + 1] = pos[p][1]; df_S[p * 6 + 2] = pos[p][2];
    df_S[p * 6 + 3] = 0.1f * p; df_S[p * 6 + 4] = 0.02f * p; df_S[p * 6 + 5] = -0.05f * p;
  }
  int t[DF_NP] = { 1, 2, 1, 2, 1 }; memcpy(df_types, t, sizeof t);
  float rc[DF_NT * DF_NT];
  for (int i = 0; i < DF_NT; i++) for (int j = 0; j < DF_NT; j++) {
    int x = i * DF_NT + j;
    df_a1[x] = 1.0f + 0.1f * x; df_b1[x] = 2.0f + 0.2f * x;
    df_re[x] = 1.0f + 0.05f * x; rc[x] = 3.0f;
    df_alfa[x] = 0.5f + 0.1f * x; df_c0[x] = 2.5f + 0.1f * x;
  }
  float mass[DF_NT] = { 1.5f, 2.5f };   // distinct, so a bad MASS lookup shows
  const float CUT = 2.0f;
  std::vector<int> nb(DF_NP * DF_MAXN, 0), nc(DF_NP, 0);
  for (int p = 1; p <= DF_NP; p++) {
    int c = 0;
    for (int q = 1; q <= DF_NP; q++) if (q != p) {
      float R = df_sep(pos[p-1][0], pos[p-1][1], pos[p-1][2],
                       pos[q-1][0], pos[q-1][1], pos[q-1][2]);
      if (R <= CUT) nb[(p - 1) * DF_MAXN + (c++)] = q;
    }
    nc[p - 1] = c;
  }
  // ---- mirror ----
  std::vector<float> want(DF_NP * 6, 0);
  for (int p = 1; p <= DF_NP; p++) {
    int j = (p - 1) * 6; float fx = 0, fy = 0, fz = 0;
    for (int i = 0; i < nc[p - 1]; i++) {
      int n = nb[(p - 1) * DF_MAXN + i];
      fx += df_force(p, n, 'X'); fy += df_force(p, n, 'Y'); fz += df_force(p, n, 'Z');
    }
    float m = mass[df_types[p - 1] - 1];
    want[j] = df_S[j+3]; want[j+1] = df_S[j+4]; want[j+2] = df_S[j+5];
    want[j+3] = fx / m;  want[j+4] = fy / m;    want[j+5] = fz / m;
  }
  auto mk1 = [&](const void* s2, size_t n, size_t esz) {
    sisal_array_t A = sisal_array_alloc_sized(1, 96, n, esz);
    A.lower_bound[0] = 1; A.stride[0] = 1; memcpy(A.data, s2, esz * n); return A;
  };
  auto mk2 = [&](const void* s2, int d0, int d1, size_t esz) {
    sisal_array_t A = sisal_array_alloc_sized(2, 96, (size_t)d0 * d1, esz);
    A.rank = 2; A.dims[0] = d0; A.dims[1] = d1;
    A.lower_bound[0] = 1; A.lower_bound[1] = 1; A.stride[0] = d1; A.stride[1] = 1;
    memcpy(A.data, s2, esz * (size_t)d0 * d1); return A;
  };
  df_pd pd; pd.nt = DF_NT;
  pd.A1 = mk2(df_a1, DF_NT, DF_NT, 4); pd.B1 = mk2(df_b1, DF_NT, DF_NT, 4);
  pd.Re = mk2(df_re, DF_NT, DF_NT, 4); pd.Rc = mk2(rc, DF_NT, DF_NT, 4);
  pd.ALFA = mk2(df_alfa, DF_NT, DF_NT, 4); pd.C0 = mk2(df_c0, DF_NT, DF_NT, 4);
  pd.MASS = mk1(mass, DF_NT, 4);
  pd.dt = 0.01f; pd.endt = 1.0f; pd.tol = 1e-6f;
  sisal_array_t S = mk1(df_S, DF_NP * 6, 4), T = mk1(df_types, DF_NP, 4);
  sisal_array_t NB = mk2(nb.data(), DF_NP, DF_MAXN, 4), NC = mk1(nc.data(), DF_NP, 4);
  DF_results r = func_MAIN(S, T, NB, NC, pd, DF_NP);

  check("S_DOT has one 6-slot chunk per particle",
        (int)r.sdot.size == DF_NP * 6);
  int okv = 1, oka = 1;
  for (int p = 0; p < DF_NP; p++) {
    int j = p * 6;
    for (int k = 0; k < 3; k++)
      if (fabsf(((float*)r.sdot.data)[j+k] - want[j+k]) > 1e-5f) okv = 0;
    for (int k = 3; k < 6; k++)
      if (fabsf(((float*)r.sdot.data)[j+k] - want[j+k])
          > 1e-4f * (1.0f + fabsf(want[j+k]))) oka = 0;
  }
  check("velocity half == the state vector's own v components", okv);
  check("acceleration half == Morse force / MASS[TYPES[I]]", oka);
  check("isolated particle has zero acceleration",
        ((float*)r.sdot.data)[4*6+3] == 0.0f
        && ((float*)r.sdot.data)[4*6+4] == 0.0f
        && ((float*)r.sdot.data)[4*6+5] == 0.0f);
}
#endif
#ifdef TEST_MOLDYN_RK_DV
// moldyn's Runge-Kutta-Fehlberg core: the coefficient tables, S_Augmented,
// Sum_Beta_K, Sum_Gamma_Ks and Calc_Ks.
//
// RANK 2 WITHOUT PADDING.  Both 2-D objects have FORMULAIC extents -- BETA is a
// constant 6 x 5 table, K is SYSTEM_SIZE x 6 -- so they are ordinary flat rank-2
// dope vectors, with none of the worst-case padding or valid-extent vector the
// ragged neighbour lists needed.  Raggedness comes from a data-dependent extent
// (a `when` that compacts), not from having two dimensions.
//
// Calc_Ks is genuinely sequential: stage i reads stages 1..i-1 through
// S_Augmented, so it is a for-initial carrying the whole table, each stage
// rewriting it with column i filled.  The mirror runs the six Fehlberg stages
// independently from the published coefficients.
enum { RK_NP = 5, RK_NT = 2, RK_MAXN = RK_NP - 1, RK_SS = RK_NP * 6 };
static float rk_a1[RK_NT*RK_NT], rk_b1[RK_NT*RK_NT], rk_re[RK_NT*RK_NT];
static float rk_alfa[RK_NT*RK_NT], rk_c0[RK_NT*RK_NT];
static float rk_S[RK_SS]; static int rk_types[RK_NP];
static float rk_mass[RK_NT] = { 1.5f, 2.5f };
static std::vector<int> rk_nb, rk_nc;
static float rk_e2p(float x){ return powf(2.718281828f, x); }
static float rk_sep(float x1,float y1,float z1,float x2,float y2,float z2){
  float dx=x1-x2,dy=y1-y2,dz=z1-z2; return sqrtf(dx*dx+dy*dy+dz*dz); }
static float rk_force(const float* S,int p,int n,char dim){
  int j=(p-1)*6,k=(n-1)*6;
  float xp=S[j],yp=S[j+1],zp=S[j+2],xn=S[k],yn=S[k+1],zn=S[k+2];
  int x=(rk_types[p-1]-1)*RK_NT+(rk_types[n-1]-1);
  float R=rk_sep(xp,yp,zp,xn,yn,zn);
  float basic=(-1.0f/rk_b1[x])*rk_e2p(-2.0f*rk_a1[x]*(R-rk_re[x]))
             +( 1.0f/rk_b1[x])*rk_e2p(-rk_a1[x]*(R-rk_re[x]));
  float fadj=rk_alfa[x]*rk_e2p(rk_alfa[x]*(R-rk_c0[x]));
  float dq=(dim=='X')?(xp-xn):(dim=='Y')?(yp-yn):(zp-zn);
  return -(basic-fadj)*dq/R; }
static std::vector<float> rk_diffun(const std::vector<float>& S){
  std::vector<float> d(S.size(),0.0f);
  for(int p=1;p<=RK_NP;p++){ int j=(p-1)*6; float fx=0,fy=0,fz=0;
    for(int i=0;i<rk_nc[p-1];i++){ int q=rk_nb[(p-1)*RK_MAXN+i];
      fx+=rk_force(S.data(),p,q,'X'); fy+=rk_force(S.data(),p,q,'Y');
      fz+=rk_force(S.data(),p,q,'Z'); }
    float m=rk_mass[rk_types[p-1]-1];
    d[j]=S[j+3]; d[j+1]=S[j+4]; d[j+2]=S[j+5];
    d[j+3]=fx/m; d[j+4]=fy/m;   d[j+5]=fz/m; }
  return d; }
static void test_moldyn_rk_dv(void) {
  printf("\n=== Group: moldyn_rk_dv (RKF45 stages; rank-2 without padding) ===\n");
  float pos[RK_NP][3]={{0.0f,0.0f,0.0f},{1.1f,0.2f,0.0f},{0.3f,1.0f,0.4f},
                       {2.0f,1.6f,0.5f},{9.0f,9.0f,9.0f}};
  std::vector<float> S0(RK_SS);
  for(int p=0;p<RK_NP;p++){ S0[p*6]=pos[p][0];S0[p*6+1]=pos[p][1];S0[p*6+2]=pos[p][2];
    S0[p*6+3]=0.1f*p;S0[p*6+4]=0.02f*p;S0[p*6+5]=-0.05f*p; }
  int t[RK_NP]={1,2,1,2,1}; memcpy(rk_types,t,sizeof t);
  float rc[RK_NT*RK_NT];
  for(int i=0;i<RK_NT;i++) for(int j=0;j<RK_NT;j++){ int x=i*RK_NT+j;
    rk_a1[x]=1.0f+0.1f*x; rk_b1[x]=2.0f+0.2f*x; rk_re[x]=1.0f+0.05f*x;
    rc[x]=3.0f; rk_alfa[x]=0.5f+0.1f*x; rk_c0[x]=2.5f+0.1f*x; }
  const float CUT=2.0f;
  rk_nb.assign(RK_NP*RK_MAXN,0); rk_nc.assign(RK_NP,0);
  for(int p=1;p<=RK_NP;p++){ int c=0;
    for(int q=1;q<=RK_NP;q++) if(q!=p){
      float R=rk_sep(pos[p-1][0],pos[p-1][1],pos[p-1][2],
                     pos[q-1][0],pos[q-1][1],pos[q-1][2]);
      if(R<=CUT) rk_nb[(p-1)*RK_MAXN+(c++)]=q; }
    rk_nc[p-1]=c; }
  const float H=0.01f, TOUT=0.0f;
  float BETA[6][5]={{0,0,0,0,0},{1.f/4,0,0,0,0},{3.f/32,9.f/32,0,0,0},
    {1932.f/2197,-7200.f/2197,7296.f/2197,0,0},
    {439.f/216,-8.f,3680.f/513,-845.f/4104,0},
    {-8.f/27,2.f,-3544.f/2565,1859.f/4104,-11.f/40}};
  float GAMMA[6]={16.f/135,0,6656.f/12825,28561.f/56430,-9.f/50,2.f/55};
  std::vector<std::vector<float>> K(RK_SS, std::vector<float>(6,0.0f));
  for(int I=1;I<=6;I++){
    std::vector<float> Saug(RK_SS);
    for(int L=0;L<RK_SS;L++){ float s2=0;
      for(int J=1;J<I;J++) s2+=BETA[I-1][J-1]*K[L][J-1];
      Saug[L]=S0[L]+s2; }
    std::vector<float> sd=rk_diffun(Saug);
    for(int L=0;L<RK_SS;L++) K[L][I-1]=H*sd[L]; }
  std::vector<float> SG(RK_SS,0.f);
  for(int L=0;L<RK_SS;L++){ float s2=0; for(int I=0;I<6;I++) s2+=GAMMA[I]*K[L][I]; SG[L]=s2; }

  auto mk1=[&](const void* s2,size_t n,size_t esz){
    sisal_array_t A=sisal_array_alloc_sized(1,96,n,esz); A.lower_bound[0]=1;
    A.stride[0]=1; memcpy(A.data,s2,esz*n); return A; };
  auto mk2=[&](const void* s2,int d0,int d1,size_t esz){
    sisal_array_t A=sisal_array_alloc_sized(2,96,(size_t)d0*d1,esz);
    A.rank=2;A.dims[0]=d0;A.dims[1]=d1;A.lower_bound[0]=1;A.lower_bound[1]=1;
    A.stride[0]=d1;A.stride[1]=1; memcpy(A.data,s2,esz*(size_t)d0*d1); return A; };
  rk_pd pd; pd.nt=RK_NT;
  pd.A1=mk2(rk_a1,RK_NT,RK_NT,4); pd.B1=mk2(rk_b1,RK_NT,RK_NT,4);
  pd.Re=mk2(rk_re,RK_NT,RK_NT,4); pd.Rc=mk2(rc,RK_NT,RK_NT,4);
  pd.ALFA=mk2(rk_alfa,RK_NT,RK_NT,4); pd.C0=mk2(rk_c0,RK_NT,RK_NT,4);
  pd.MASS=mk1(rk_mass,RK_NT,4); pd.dt=0.01f; pd.endt=1.0f; pd.tol=1e-6f;
  sisal_array_t Sa=mk1(S0.data(),RK_SS,4), T=mk1(rk_types,RK_NP,4);
  sisal_array_t NB=mk2(rk_nb.data(),RK_NP,RK_MAXN,4), NC=mk1(rk_nc.data(),RK_NP,4);
  RK_results r=func_MAIN(Sa,H,TOUT,T,NB,NC,pd);

  check("BETA is a flat rank-2 6 x 5 (formulaic, so no padding)",
        r.beta.rank==2 && (int)r.beta.dims[0]==6 && (int)r.beta.dims[1]==5);
  int okb=1;
  for(int i=0;i<6;i++) for(int j=0;j<5;j++)
    if(fabsf(((float*)r.beta.data)[i*5+j]-BETA[i][j])>1e-6f) okb=0;
  check("BETA == the published Fehlberg coefficients", okb);
  check("K is a flat rank-2 SYSTEM_SIZE x 6",
        r.k.rank==2 && (int)r.k.dims[0]==RK_SS && (int)r.k.dims[1]==6);
  int okk=1;
  for(int L=0;L<RK_SS;L++) for(int I=0;I<6;I++){
    float g=((float*)r.k.data)[L*6+I], w=K[L][I];
    if(fabsf(g-w)>1e-4f*(1.0f+fabsf(w))) okk=0; }
  check("all six RK stages == an independent Fehlberg mirror", okk);
  int oks=(int)r.sg.size==RK_SS;
  for(int L=0;oks&&L<RK_SS;L++)
    if(fabsf(((float*)r.sg.data)[L]-SG[L])>1e-4f*(1.0f+fabsf(SG[L]))) oks=0;
  check("Sum_Gamma_Ks over every slot == mirror", oks);
  check("stage 1 is H*Diffun(S) -- later stages differ, so the sequence is real",
        fabsf(((float*)r.k.data)[1*6+0] - K[1][0]) < 1e-6f
        && fabsf(((float*)r.k.data)[1*6+3] - K[1][3]) < 1e-6f
        && K[1][0] != K[1][3]);
}
#endif
#ifdef TEST_MOLDYN_RKF45_DV
// moldyn's RKF45 solver: the FMM error estimate plus the adaptive step.
//
// RKF45 is RECURSIVE, not a loop.  Inside tolerance it takes the step;
// otherwise it halves H and takes TWO half steps, the second fed by the first,
// and returns the INNER call's H and error -- the first half step's are
// discarded.  Recursion depth is data-dependent and there is NO depth guard, so
// a tolerance the error can never meet is a stack overflow rather than a wrong
// answer.  The retry tolerance below is therefore taken FROM THE DATA, strictly
// between the error at H and at H/2, so the first call must halve and the
// halved call then succeeds.
//
// The error estimate itself is a difference of nearly-equal coefficients
// (GAMMA - GAMMA_STAR), so it loses precision to cancellation; it is checked
// loosely while the evolved state and the accepted H are checked tightly.
// Note also there is no absolute value in the original -- `value of greatest`
// takes the SIGNED maximum -- so a large negative discrepancy never triggers a
// retry.  Kept as written.
enum { F45_NP = 5, F45_NT = 2, F45_MAXN = F45_NP - 1, F45_SS = F45_NP * 6 };
static float f45_a1[F45_NT*F45_NT], f45_b1[F45_NT*F45_NT], f45_re[F45_NT*F45_NT];
static float f45_alfa[F45_NT*F45_NT], f45_c0[F45_NT*F45_NT];
static int f45_types[F45_NP];
static float f45_mass[F45_NT] = { 1.5f, 2.5f };
static std::vector<int> f45_nb, f45_nc;
static float f45_BETA[6][5]={{0,0,0,0,0},{1.f/4,0,0,0,0},{3.f/32,9.f/32,0,0,0},
  {1932.f/2197,-7200.f/2197,7296.f/2197,0,0},
  {439.f/216,-8.f,3680.f/513,-845.f/4104,0},
  {-8.f/27,2.f,-3544.f/2565,1859.f/4104,-11.f/40}};
static float f45_GAMMA[6]={16.f/135,0,6656.f/12825,28561.f/56430,-9.f/50,2.f/55};
static float f45_GSTAR[6]={25.f/216,0,1408.f/2565,2197.f/4104,-1.f/5,0};
static float f45_e2p(float x){ return powf(2.718281828f,x); }
static float f45_sep(float x1,float y1,float z1,float x2,float y2,float z2){
  float dx=x1-x2,dy=y1-y2,dz=z1-z2; return sqrtf(dx*dx+dy*dy+dz*dz); }
static float f45_force(const float* S,int p,int n,char dim){
  int j=(p-1)*6,k=(n-1)*6;
  float xp=S[j],yp=S[j+1],zp=S[j+2],xn=S[k],yn=S[k+1],zn=S[k+2];
  int x=(f45_types[p-1]-1)*F45_NT+(f45_types[n-1]-1);
  float R=f45_sep(xp,yp,zp,xn,yn,zn);
  float basic=(-1.0f/f45_b1[x])*f45_e2p(-2.0f*f45_a1[x]*(R-f45_re[x]))
             +( 1.0f/f45_b1[x])*f45_e2p(-f45_a1[x]*(R-f45_re[x]));
  float fadj=f45_alfa[x]*f45_e2p(f45_alfa[x]*(R-f45_c0[x]));
  float dq=(dim=='X')?(xp-xn):(dim=='Y')?(yp-yn):(zp-zn);
  return -(basic-fadj)*dq/R; }
static std::vector<float> f45_diffun(const std::vector<float>& S){
  std::vector<float> d(S.size(),0.0f);
  for(int p=1;p<=F45_NP;p++){ int j=(p-1)*6; float fx=0,fy=0,fz=0;
    for(int i=0;i<f45_nc[p-1];i++){ int q=f45_nb[(p-1)*F45_MAXN+i];
      fx+=f45_force(S.data(),p,q,'X'); fy+=f45_force(S.data(),p,q,'Y');
      fz+=f45_force(S.data(),p,q,'Z'); }
    float m=f45_mass[f45_types[p-1]-1];
    d[j]=S[j+3]; d[j+1]=S[j+4]; d[j+2]=S[j+5];
    d[j+3]=fx/m; d[j+4]=fy/m;   d[j+5]=fz/m; }
  return d; }
static void f45_calc_ks(const std::vector<float>& S,float H,
                        std::vector<std::vector<float>>& K){
  int SS=(int)S.size(); K.assign(SS,std::vector<float>(6,0.f));
  for(int I=1;I<=6;I++){
    std::vector<float> Sa(SS);
    for(int L=0;L<SS;L++){ float s2=0;
      for(int J=1;J<I;J++) s2+=f45_BETA[I-1][J-1]*K[L][J-1];
      Sa[L]=S[L]+s2; }
    std::vector<float> sd=f45_diffun(Sa);
    for(int L=0;L<SS;L++) K[L][I-1]=H*sd[L]; } }
static float f45_err(const std::vector<float>& S,float H,
                     std::vector<std::vector<float>>& K){
  f45_calc_ks(S,H,K);
  float mx=-3.4e38f;
  for(int L=0;L<(int)S.size();L++){ float s2=0;
    for(int I=0;I<6;I++) s2+=K[L][I]*(f45_GAMMA[I]-f45_GSTAR[I]);
    if(s2>mx) mx=s2; }
  return mx; }
static int f45_depth=0;
static std::vector<float> f45_rkf45(const std::vector<float>& S,float H,float TOL,
                                    float& oH,float& oE,int depth){
  if(depth>f45_depth) f45_depth=depth;
  if(depth>12){ oH=H; oE=0; return S; }          // mirror-only guard
  std::vector<std::vector<float>> K; float e=f45_err(S,H,K);
  if(e<TOL){ std::vector<float> ns(S.size());
    for(int L=0;L<(int)S.size();L++){ float s2=0;
      for(int I=0;I<6;I++) s2+=f45_GAMMA[I]*K[L][I]; ns[L]=S[L]+s2; }
    oH=H; oE=e; return ns; }
  float h1,e1; std::vector<float> S1=f45_rkf45(S,0.5f*H,TOL,h1,e1,depth+1);
  return f45_rkf45(S1,0.5f*H,TOL,oH,oE,depth+1); }
static void test_moldyn_rkf45_dv(void) {
  printf("\n=== Group: moldyn_rkf45_dv (recursive adaptive step) ===\n");
  float pos[F45_NP][3]={{0.0f,0.0f,0.0f},{1.1f,0.2f,0.0f},{0.3f,1.0f,0.4f},
                        {2.0f,1.6f,0.5f},{9.0f,9.0f,9.0f}};
  std::vector<float> S0(F45_SS);
  for(int p=0;p<F45_NP;p++){ S0[p*6]=pos[p][0];S0[p*6+1]=pos[p][1];S0[p*6+2]=pos[p][2];
    S0[p*6+3]=0.1f*p;S0[p*6+4]=0.02f*p;S0[p*6+5]=-0.05f*p; }
  int t[F45_NP]={1,2,1,2,1}; memcpy(f45_types,t,sizeof t);
  float rc[F45_NT*F45_NT];
  for(int i=0;i<F45_NT;i++) for(int j=0;j<F45_NT;j++){ int x=i*F45_NT+j;
    f45_a1[x]=1.0f+0.1f*x; f45_b1[x]=2.0f+0.2f*x; f45_re[x]=1.0f+0.05f*x;
    rc[x]=3.0f; f45_alfa[x]=0.5f+0.1f*x; f45_c0[x]=2.5f+0.1f*x; }
  const float CUT=2.0f;
  f45_nb.assign(F45_NP*F45_MAXN,0); f45_nc.assign(F45_NP,0);
  for(int p=1;p<=F45_NP;p++){ int c=0;
    for(int q=1;q<=F45_NP;q++) if(q!=p){
      float R=f45_sep(pos[p-1][0],pos[p-1][1],pos[p-1][2],
                      pos[q-1][0],pos[q-1][1],pos[q-1][2]);
      if(R<=CUT) f45_nb[(p-1)*F45_MAXN+(c++)]=q; }
    f45_nc[p-1]=c; }
  auto mk1=[&](const void* s2,size_t n,size_t esz){
    sisal_array_t A=sisal_array_alloc_sized(1,96,n,esz); A.lower_bound[0]=1;
    A.stride[0]=1; memcpy(A.data,s2,esz*n); return A; };
  auto mk2=[&](const void* s2,int d0,int d1,size_t esz){
    sisal_array_t A=sisal_array_alloc_sized(2,96,(size_t)d0*d1,esz);
    A.rank=2;A.dims[0]=d0;A.dims[1]=d1;A.lower_bound[0]=1;A.lower_bound[1]=1;
    A.stride[0]=d1;A.stride[1]=1; memcpy(A.data,s2,esz*(size_t)d0*d1); return A; };
  f45_pd pd; pd.nt=F45_NT;
  pd.A1=mk2(f45_a1,F45_NT,F45_NT,4); pd.B1=mk2(f45_b1,F45_NT,F45_NT,4);
  pd.Re=mk2(f45_re,F45_NT,F45_NT,4); pd.Rc=mk2(rc,F45_NT,F45_NT,4);
  pd.ALFA=mk2(f45_alfa,F45_NT,F45_NT,4); pd.C0=mk2(f45_c0,F45_NT,F45_NT,4);
  pd.MASS=mk1(f45_mass,F45_NT,4); pd.dt=0.01f; pd.endt=1.0f; pd.tol=1e-6f;
  sisal_array_t T=mk1(f45_types,F45_NP,4);
  sisal_array_t NB=mk2(f45_nb.data(),F45_NP,F45_MAXN,4);
  sisal_array_t NC=mk1(f45_nc.data(),F45_NP,4);
  sisal_array_t Sa=mk1(S0.data(),F45_SS,4);

  std::vector<std::vector<float>> Kt;
  float e_full=f45_err(S0,0.01f,Kt), e_half=f45_err(S0,0.005f,Kt);
  const float H=0.01f;
  for (int c=0;c<2;c++){
    float TOL = (c==0) ? 1.0f : 0.5f*(e_full+e_half);
    f45_depth=0;
    float wh,we; std::vector<float> ws=f45_rkf45(S0,H,TOL,wh,we,0);
    F45_results r=func_MAIN(Sa,H,0.0f,TOL,T,NB,NC,pd);
    char msg[160];
    snprintf(msg,sizeof msg,"%s: accepted step H == %g",
             c==0?"inside tolerance":"one retry", wh);
    check(msg, fabsf(r.h-wh) < 1e-9f);
    int okc=(int)r.s.size==(int)ws.size();
    for(size_t L=0;okc&&L<ws.size();L++)
      if(fabsf(((float*)r.s.data)[L]-ws[L])>1e-4f*(1.0f+fabsf(ws[L]))) okc=0;
    snprintf(msg,sizeof msg,"%s: evolved state == mirror",
             c==0?"inside tolerance":"one retry");
    check(msg, okc);
    snprintf(msg,sizeof msg,"%s: error estimate ~= mirror (cancellation-limited)",
             c==0?"inside tolerance":"one retry");
    check(msg, fabsf(r.err-we) <= 0.05f*fabsf(we) + 1e-15f);
    if (c==1) check("the retry branch was actually taken (mirror depth >= 1)",
                    f45_depth >= 1);
  }
  check("halving the step lowers the error estimate", e_half < e_full);
}
#endif
#ifdef TEST_MOLDYN_SOLVE_DV
// moldyn's Solve_Systems: the step that wraps the solver.  It packs the
// ensemble's struct-of-arrays state into the flat stride-6 system vector, hands
// that to RKF45, and unpacks the result back into the ensemble record.
//
// Both directions are pure shape work -- the ensemble keeps coordinates as SIX
// separate arrays while the solver wants one interleaved vector -- and the
// result goes home through a NESTED FIELD REPLACE, writing through a dotted
// path (`POSITIONS.X`, `VELOCITIES.VZ`) into a record of records.  The checks
// below pin that the untouched fields really are untouched: ENSEMBLE_SIZE and
// TYPES must survive, and TOUT must advance by exactly DELTA_T.
enum { SV_NP = 5, SV_NT = 2, SV_MAXN = SV_NP - 1, SV_SS = SV_NP * 6 };
static float sv_a1[SV_NT*SV_NT], sv_b1[SV_NT*SV_NT], sv_re[SV_NT*SV_NT];
static float sv_alfa[SV_NT*SV_NT], sv_c0[SV_NT*SV_NT];
static int sv_types[SV_NP];
static float sv_mass[SV_NT] = { 1.5f, 2.5f };
static std::vector<int> sv_nb, sv_nc;
static float sv_BETA[6][5]={{0,0,0,0,0},{1.f/4,0,0,0,0},{3.f/32,9.f/32,0,0,0},
  {1932.f/2197,-7200.f/2197,7296.f/2197,0,0},
  {439.f/216,-8.f,3680.f/513,-845.f/4104,0},
  {-8.f/27,2.f,-3544.f/2565,1859.f/4104,-11.f/40}};
static float sv_GAMMA[6]={16.f/135,0,6656.f/12825,28561.f/56430,-9.f/50,2.f/55};
static float sv_GSTAR[6]={25.f/216,0,1408.f/2565,2197.f/4104,-1.f/5,0};
static float sv_e2p(float x){ return powf(2.718281828f,x); }
static float sv_sep(float x1,float y1,float z1,float x2,float y2,float z2){
  float dx=x1-x2,dy=y1-y2,dz=z1-z2; return sqrtf(dx*dx+dy*dy+dz*dz); }
static float sv_force(const float* S,int p,int n,char dim){
  int j=(p-1)*6,k=(n-1)*6;
  float xp=S[j],yp=S[j+1],zp=S[j+2],xn=S[k],yn=S[k+1],zn=S[k+2];
  int x=(sv_types[p-1]-1)*SV_NT+(sv_types[n-1]-1);
  float R=sv_sep(xp,yp,zp,xn,yn,zn);
  float basic=(-1.0f/sv_b1[x])*sv_e2p(-2.0f*sv_a1[x]*(R-sv_re[x]))
             +( 1.0f/sv_b1[x])*sv_e2p(-sv_a1[x]*(R-sv_re[x]));
  float fadj=sv_alfa[x]*sv_e2p(sv_alfa[x]*(R-sv_c0[x]));
  float dq=(dim=='X')?(xp-xn):(dim=='Y')?(yp-yn):(zp-zn);
  return -(basic-fadj)*dq/R; }
static std::vector<float> sv_diffun(const std::vector<float>& S){
  std::vector<float> d(S.size(),0.0f);
  for(int p=1;p<=SV_NP;p++){ int j=(p-1)*6; float fx=0,fy=0,fz=0;
    for(int i=0;i<sv_nc[p-1];i++){ int q=sv_nb[(p-1)*SV_MAXN+i];
      fx+=sv_force(S.data(),p,q,'X'); fy+=sv_force(S.data(),p,q,'Y');
      fz+=sv_force(S.data(),p,q,'Z'); }
    float m=sv_mass[sv_types[p-1]-1];
    d[j]=S[j+3]; d[j+1]=S[j+4]; d[j+2]=S[j+5];
    d[j+3]=fx/m; d[j+4]=fy/m;   d[j+5]=fz/m; }
  return d; }
static std::vector<float> sv_step(const std::vector<float>& S,float H,float TOL,
                                  float& oH){
  int SS=(int)S.size();
  std::vector<std::vector<float>> K(SS,std::vector<float>(6,0.f));
  for(int I=1;I<=6;I++){
    std::vector<float> Sa(SS);
    for(int L=0;L<SS;L++){ float s2=0;
      for(int J=1;J<I;J++) s2+=sv_BETA[I-1][J-1]*K[L][J-1];
      Sa[L]=S[L]+s2; }
    std::vector<float> sd=sv_diffun(Sa);
    for(int L=0;L<SS;L++) K[L][I-1]=H*sd[L]; }
  float mx=-3.4e38f;
  for(int L=0;L<SS;L++){ float s2=0;
    for(int I=0;I<6;I++) s2+=K[L][I]*(sv_GAMMA[I]-sv_GSTAR[I]);
    if(s2>mx) mx=s2; }
  if (mx >= TOL) { oH = H; return S; }   // TOL is loose here; no retry expected
  std::vector<float> ns(SS);
  for(int L=0;L<SS;L++){ float s2=0;
    for(int I=0;I<6;I++) s2+=sv_GAMMA[I]*K[L][I]; ns[L]=S[L]+s2; }
  oH=H; return ns; }
static void test_moldyn_solve_dv(void) {
  printf("\n=== Group: moldyn_solve_dv (pack, solve, nested-replace unpack) ===\n");
  float pos[SV_NP][3]={{0.0f,0.0f,0.0f},{1.1f,0.2f,0.0f},{0.3f,1.0f,0.4f},
                       {2.0f,1.6f,0.5f},{9.0f,9.0f,9.0f}};
  float px[SV_NP],py[SV_NP],pz[SV_NP],vx[SV_NP],vy[SV_NP],vz[SV_NP];
  for(int p=0;p<SV_NP;p++){ px[p]=pos[p][0];py[p]=pos[p][1];pz[p]=pos[p][2];
    vx[p]=0.1f*p; vy[p]=0.02f*p; vz[p]=-0.05f*p; }
  int t[SV_NP]={1,2,1,2,1}; memcpy(sv_types,t,sizeof t);
  float rc[SV_NT*SV_NT];
  for(int i=0;i<SV_NT;i++) for(int j=0;j<SV_NT;j++){ int x=i*SV_NT+j;
    sv_a1[x]=1.0f+0.1f*x; sv_b1[x]=2.0f+0.2f*x; sv_re[x]=1.0f+0.05f*x;
    rc[x]=3.0f; sv_alfa[x]=0.5f+0.1f*x; sv_c0[x]=2.5f+0.1f*x; }
  const float CUT=2.0f;
  sv_nb.assign(SV_NP*SV_MAXN,0); sv_nc.assign(SV_NP,0);
  for(int p=1;p<=SV_NP;p++){ int c=0;
    for(int q=1;q<=SV_NP;q++) if(q!=p){
      float R=sv_sep(pos[p-1][0],pos[p-1][1],pos[p-1][2],
                     pos[q-1][0],pos[q-1][1],pos[q-1][2]);
      if(R<=CUT) sv_nb[(p-1)*SV_MAXN+(c++)]=q; }
    sv_nc[p-1]=c; }
  const float TOUT0=0.5f, STEP0=0.01f, DT=0.25f, TOL=1.0f;
  std::vector<float> S0(SV_SS);
  for(int p=0;p<SV_NP;p++){ S0[p*6]=px[p];S0[p*6+1]=py[p];S0[p*6+2]=pz[p];
    S0[p*6+3]=vx[p];S0[p*6+4]=vy[p];S0[p*6+5]=vz[p]; }
  float wh; std::vector<float> ws=sv_step(S0,STEP0,TOL,wh);

  auto mk1=[&](const void* s2,size_t n,size_t esz){
    sisal_array_t A=sisal_array_alloc_sized(1,96,n,esz); A.lower_bound[0]=1;
    A.stride[0]=1; memcpy(A.data,s2,esz*n); return A; };
  auto mk2=[&](const void* s2,int d0,int d1,size_t esz){
    sisal_array_t A=sisal_array_alloc_sized(2,96,(size_t)d0*d1,esz);
    A.rank=2;A.dims[0]=d0;A.dims[1]=d1;A.lower_bound[0]=1;A.lower_bound[1]=1;
    A.stride[0]=d1;A.stride[1]=1; memcpy(A.data,s2,esz*(size_t)d0*d1); return A; };
  sv_pd pd; pd.nt=SV_NT;
  pd.A1=mk2(sv_a1,SV_NT,SV_NT,4); pd.B1=mk2(sv_b1,SV_NT,SV_NT,4);
  pd.Re=mk2(sv_re,SV_NT,SV_NT,4); pd.Rc=mk2(rc,SV_NT,SV_NT,4);
  pd.ALFA=mk2(sv_alfa,SV_NT,SV_NT,4); pd.C0=mk2(sv_c0,SV_NT,SV_NT,4);
  pd.MASS=mk1(sv_mass,SV_NT,4); pd.dt=DT; pd.endt=10.0f; pd.tol=TOL;
  sv_ens e; e.tout=TOUT0; e.step=STEP0; e.err=-1.0f; e.size=SV_NP;
  e.pos.X=mk1(px,SV_NP,4); e.pos.Y=mk1(py,SV_NP,4); e.pos.Z=mk1(pz,SV_NP,4);
  e.vel.VX=mk1(vx,SV_NP,4); e.vel.VY=mk1(vy,SV_NP,4); e.vel.VZ=mk1(vz,SV_NP,4);
  e.types=mk1(sv_types,SV_NP,4);
  sisal_array_t NB=mk2(sv_nb.data(),SV_NP,SV_MAXN,4);
  sisal_array_t NC=mk1(sv_nc.data(),SV_NP,4);
  sv_ens r=func_MAIN(e,NB,NC,pd);

  check("TOUT advanced by exactly DELTA_T",
        fabsf(r.tout - (TOUT0 + DT)) < 1e-6f);
  check("CURRENT_STEP is the step RKF45 accepted", fabsf(r.step - wh) < 1e-9f);
  const float* got[6] = {(const float*)r.pos.X.data,(const float*)r.pos.Y.data,
                         (const float*)r.pos.Z.data,(const float*)r.vel.VX.data,
                         (const float*)r.vel.VY.data,(const float*)r.vel.VZ.data};
  int okc=1;
  for(int p=0;p<SV_NP;p++) for(int k=0;k<6;k++){
    float g=got[k][p], w=ws[p*6+k];
    if(fabsf(g-w)>1e-4f*(1.0f+fabsf(w))) okc=0; }
  check("all six coordinate arrays unpacked from the flat state == mirror", okc);
  check("ENSEMBLE_SIZE survived the nested replace untouched", r.size == SV_NP);
  int okt=1;
  for(int p=0;p<SV_NP;p++) if(((int32_t*)r.types.data)[p]!=t[p]) okt=0;
  check("TYPES survived the nested replace untouched", okt);
  check("the isolated particle moved by velocity alone",
        fabsf(got[0][4] - (9.0f + 0.4f*STEP0)) < 1e-3f);
}
#endif
#ifdef TEST_MOLDYN_DV
// moldyn END TO END: Evolve_Ensemble and the driver, running the simulation.
//
// NOT A STREAM.  moldyn declares STATE_STREAM / TIME_POS_STREAM, but every
// `returns stream of ...` line is COMMENTED OUT in the original -- Main returns
// TIME_POS_ARRAY_ARRAY, gathering a [TOUT, X1] pair per step.  Ported as
// written rather than as the dead type declarations suggest.
//
// The driver RECOMPUTES the force-adjustment parameters before starting: ALFA
// and C0 derived from the Morse constants and the cutoff, replaced into
// PROBLEM_DATA.  Two quirks kept: it reads Rc/Re/A1/B1 at [1,1] for every
// (I,J), so both tables come out uniform, and it uses log_base_10 where the
// derivation wants a natural log.  The mirror reproduces both, so the check
// would fail if the port quietly "fixed" either.
//
// The trajectory gather is also worth noting: its trip count comes from
// `TOUT <= ENDTIME`, where TOUT is a REAL advancing by DELTA_T rather than an
// integer counter, and it sizes correctly -- seed plus one entry per step.
enum { MDY_NP = 5, MDY_NT = 2, MDY_MAXN = MDY_NP - 1 };
static float mdy_a1[MDY_NT*MDY_NT], mdy_b1[MDY_NT*MDY_NT], mdy_re[MDY_NT*MDY_NT];
static float mdy_alfa[MDY_NT*MDY_NT], mdy_c0[MDY_NT*MDY_NT], mdy_rc[MDY_NT*MDY_NT];
static int mdy_types[MDY_NP];
static float mdy_mass[MDY_NT] = { 1.5f, 2.5f };
static std::vector<int> mdy_nb, mdy_nc;
static float mdy_BETA[6][5]={{0,0,0,0,0},{1.f/4,0,0,0,0},{3.f/32,9.f/32,0,0,0},
  {1932.f/2197,-7200.f/2197,7296.f/2197,0,0},
  {439.f/216,-8.f,3680.f/513,-845.f/4104,0},
  {-8.f/27,2.f,-3544.f/2565,1859.f/4104,-11.f/40}};
static float mdy_GAMMA[6]={16.f/135,0,6656.f/12825,28561.f/56430,-9.f/50,2.f/55};
static float mdy_GSTAR[6]={25.f/216,0,1408.f/2565,2197.f/4104,-1.f/5,0};
static float mdy_e2p(float x){ return powf(2.718281828f,x); }
static float mdy_sep(float x1,float y1,float z1,float x2,float y2,float z2){
  float dx=x1-x2,dy=y1-y2,dz=z1-z2; return sqrtf(dx*dx+dy*dy+dz*dz); }
static float mdy_force(const float* S,int p,int n,char dim){
  int j=(p-1)*6,k=(n-1)*6;
  float xp=S[j],yp=S[j+1],zp=S[j+2],xn=S[k],yn=S[k+1],zn=S[k+2];
  int x=(mdy_types[p-1]-1)*MDY_NT+(mdy_types[n-1]-1);
  float R=mdy_sep(xp,yp,zp,xn,yn,zn);
  float basic=(-1.0f/mdy_b1[x])*mdy_e2p(-2.0f*mdy_a1[x]*(R-mdy_re[x]))
             +( 1.0f/mdy_b1[x])*mdy_e2p(-mdy_a1[x]*(R-mdy_re[x]));
  float fadj=mdy_alfa[x]*mdy_e2p(mdy_alfa[x]*(R-mdy_c0[x]));
  float dq=(dim=='X')?(xp-xn):(dim=='Y')?(yp-yn):(zp-zn);
  return -(basic-fadj)*dq/R; }
static std::vector<float> mdy_diffun(const std::vector<float>& S){
  std::vector<float> d(S.size(),0.0f);
  for(int p=1;p<=MDY_NP;p++){ int j=(p-1)*6; float fx=0,fy=0,fz=0;
    for(int i=0;i<mdy_nc[p-1];i++){ int q=mdy_nb[(p-1)*MDY_MAXN+i];
      fx+=mdy_force(S.data(),p,q,'X'); fy+=mdy_force(S.data(),p,q,'Y');
      fz+=mdy_force(S.data(),p,q,'Z'); }
    float m=mdy_mass[mdy_types[p-1]-1];
    d[j]=S[j+3]; d[j+1]=S[j+4]; d[j+2]=S[j+5];
    d[j+3]=fx/m; d[j+4]=fy/m;   d[j+5]=fz/m; }
  return d; }
static std::vector<float> mdy_step(const std::vector<float>& S,float H){
  int SS=(int)S.size();
  std::vector<std::vector<float>> K(SS,std::vector<float>(6,0.f));
  for(int I=1;I<=6;I++){
    std::vector<float> Sa(SS);
    for(int L=0;L<SS;L++){ float s2=0;
      for(int J=1;J<I;J++) s2+=mdy_BETA[I-1][J-1]*K[L][J-1];
      Sa[L]=S[L]+s2; }
    std::vector<float> sd=mdy_diffun(Sa);
    for(int L=0;L<SS;L++) K[L][I-1]=H*sd[L]; }
  std::vector<float> ns(SS);
  for(int L=0;L<SS;L++){ float s2=0;
    for(int I=0;I<6;I++) s2+=mdy_GAMMA[I]*K[L][I]; ns[L]=S[L]+s2; }
  return ns; }
static void test_moldyn_dv(void) {
  printf("\n=== Group: moldyn_dv (the whole simulation, end to end) ===\n");
  float pos[MDY_NP][3]={{0.0f,0.0f,0.0f},{1.1f,0.2f,0.0f},{0.3f,1.0f,0.4f},
                        {2.0f,1.6f,0.5f},{9.0f,9.0f,9.0f}};
  float px[MDY_NP],py[MDY_NP],pz[MDY_NP],vx[MDY_NP],vy[MDY_NP],vz[MDY_NP];
  for(int p=0;p<MDY_NP;p++){ px[p]=pos[p][0];py[p]=pos[p][1];pz[p]=pos[p][2];
    vx[p]=0.1f*p; vy[p]=0.02f*p; vz[p]=-0.05f*p; }
  int t[MDY_NP]={1,2,1,2,1}; memcpy(mdy_types,t,sizeof t);
  for(int i=0;i<MDY_NT;i++) for(int j=0;j<MDY_NT;j++){ int x=i*MDY_NT+j;
    mdy_a1[x]=1.0f+0.1f*x; mdy_b1[x]=2.0f+0.2f*x; mdy_re[x]=1.0f+0.05f*x;
    mdy_rc[x]=3.0f; mdy_alfa[x]=0.5f+0.1f*x; mdy_c0[x]=2.5f+0.1f*x; }
  const float CUT=2.0f;
  mdy_nb.assign(MDY_NP*MDY_MAXN,0); mdy_nc.assign(MDY_NP,0);
  for(int p=1;p<=MDY_NP;p++){ int c=0;
    for(int q=1;q<=MDY_NP;q++) if(q!=p){
      float R=mdy_sep(pos[p-1][0],pos[p-1][1],pos[p-1][2],
                      pos[q-1][0],pos[q-1][1],pos[q-1][2]);
      if(R<=CUT) mdy_nb[(p-1)*MDY_MAXN+(c++)]=q; }
    mdy_nc[p-1]=c; }
  auto mk1=[&](const void* s2,size_t n,size_t esz){
    sisal_array_t A=sisal_array_alloc_sized(1,96,n,esz); A.lower_bound[0]=1;
    A.stride[0]=1; memcpy(A.data,s2,esz*n); return A; };
  auto mk2=[&](const void* s2,int d0,int d1,size_t esz){
    sisal_array_t A=sisal_array_alloc_sized(2,96,(size_t)d0*d1,esz);
    A.rank=2;A.dims[0]=d0;A.dims[1]=d1;A.lower_bound[0]=1;A.lower_bound[1]=1;
    A.stride[0]=d1;A.stride[1]=1; memcpy(A.data,s2,esz*(size_t)d0*d1); return A; };
  const float TOUT0=0.0f, STEP0=0.01f, DT=0.25f, ENDT=1.0f;
  mdy_pd pd; pd.nt=MDY_NT;
  pd.A1=mk2(mdy_a1,MDY_NT,MDY_NT,4); pd.B1=mk2(mdy_b1,MDY_NT,MDY_NT,4);
  pd.Re=mk2(mdy_re,MDY_NT,MDY_NT,4); pd.Rc=mk2(mdy_rc,MDY_NT,MDY_NT,4);
  pd.ALFA=mk2(mdy_alfa,MDY_NT,MDY_NT,4); pd.C0=mk2(mdy_c0,MDY_NT,MDY_NT,4);
  pd.MASS=mk1(mdy_mass,MDY_NT,4); pd.dt=DT; pd.endt=ENDT; pd.tol=1.0f;
  mdy_ens e; e.tout=TOUT0; e.step=STEP0; e.err=-1.0f; e.size=MDY_NP;
  e.pos.X=mk1(px,MDY_NP,4); e.pos.Y=mk1(py,MDY_NP,4); e.pos.Z=mk1(pz,MDY_NP,4);
  e.vel.VX=mk1(vx,MDY_NP,4); e.vel.VY=mk1(vy,MDY_NP,4); e.vel.VZ=mk1(vz,MDY_NP,4);
  e.types=mk1(mdy_types,MDY_NP,4);
  sisal_array_t NB=mk2(mdy_nb.data(),MDY_NP,MDY_MAXN,4);
  sisal_array_t NC=mk1(mdy_nc.data(),MDY_NP,4);

  // mirror the ALFA/C0 recomputation, quirks and all
  float Rc=mdy_rc[0], Re=mdy_re[0], A1=mdy_a1[0], B1=mdy_b1[0], eps=1.0e-8f;
  float basic=(-1.0f/B1)*mdy_e2p(-2.0f*A1*(Rc-Re))+( 1.0f/B1)*mdy_e2p(-A1*(Rc-Re));
  const float L10=0.434294482f;
  float na=(L10*logf(fabsf(basic)/eps))/(Rc-Re);
  float nc=Re-(1.0f/na)*(L10*logf(eps/na));
  for(int i=0;i<MDY_NT*MDY_NT;i++){ mdy_alfa[i]=na; mdy_c0[i]=nc; }
  std::vector<float> mS(MDY_NP*6);
  for(int p=0;p<MDY_NP;p++){ mS[p*6]=px[p];mS[p*6+1]=py[p];mS[p*6+2]=pz[p];
    mS[p*6+3]=vx[p];mS[p*6+4]=vy[p];mS[p*6+5]=vz[p]; }
  std::vector<std::pair<float,float>> mtraj;
  { float T=TOUT0; mtraj.push_back({T,mS[0]});
    while(T<=ENDT){ mS=mdy_step(mS,STEP0); T+=DT; mtraj.push_back({T,mS[0]}); } }

  MDY_results r=func_MAIN(e,NB,NC,pd);

  check("trajectory is rank-2, one [TOUT, X1] pair per step",
        r.traj.rank==2 && (int)r.traj.dims[1]==2
        && (int)r.traj.dims[0]==(int)mtraj.size());
  int okt=(int)r.traj.dims[0]==(int)mtraj.size();
  for(int i=0;okt&&i<(int)mtraj.size();i++){
    float gt=((float*)r.traj.data)[i*2], gx=((float*)r.traj.data)[i*2+1];
    if(fabsf(gt-mtraj[i].first)>1e-5f) okt=0;
    if(fabsf(gx-mtraj[i].second)>1e-4f*(1.0f+fabsf(mtraj[i].second))) okt=0; }
  check("whole trajectory == an independent seven-stage mirror", okt);
  check("the seed state is entry 0 (1.2 history: initial is body_0)",
        fabsf(((float*)r.traj.data)[0]-TOUT0)<1e-6f);
  check("final TOUT is the first past ENDTIME (Rule 2: out-of-bound gathered)",
        fabsf(r.e.tout-(ENDT+DT))<1e-5f);
  check("particle 1 actually moved under the force",
        fabsf(((float*)r.traj.data)[(mtraj.size()-1)*2+1]) > 1e-6f);
  check("ENSEMBLE_SIZE survived every step", r.e.size==MDY_NP);
}
#endif
#ifdef TEST_GATHER_CONFORM_DV
// `packed || Zeros(width - array_size(packed))` -- the natural way to pad a
// masked (compacted) row out to a rectangle, which is the standard move for
// carrying a ragged structure as dense-plus-counts.
//
// It used to produce a MALFORMED result whenever the FIRST row needed no
// padding: dims came back 3 x 6 while size was 15 (3 rows of 5), so dims and
// size disagreed and every row after the first was read at the wrong stride.
// The cause was `||` itself, not the gather: appending an EMPTY array bumped
// dims[0] by a phantom row (the add_rows fallback reads b.dims[0] == 0 and
// substitutes 1) while size grew by nothing.  The gather faithfully copied the
// inconsistent descriptor it was handed.
//
// A gather is a STACK: one new leading axis, every element the same shape, as
// numpy's np.stack requires.  A non-conforming element is now a loud runtime
// error naming the shapes rather than being silently dropped -- not exercised
// here, since it aborts.
//
// Both orders are covered: FIRST row full (the case that broke) and LAST row
// full (which always worked), so a fix that merely moved the problem would
// show.
static void test_gather_conform_dv(void) {
  printf("\n=== Group: gather_conform_dv (|| padding; gather is a stack) ===\n");
  GC_results r = func_MAIN(5);
  // survivors 5,4,3 -> pads 0,1,2 -> rows all 5 long, FIRST needs no pad
  int want_first[3][5] = {{1,2,3,4,5},{1,2,3,4,0},{1,2,3,0,0}};
  // survivors 3,4,5 -> pads 2,1,0 -> rows all 5 long, LAST needs no pad
  int want_last[3][5]  = {{1,2,3,0,0},{1,2,3,4,0},{1,2,3,4,5}};
  check("padded rows are rank-2 with dims consistent with size",
        r.rows.rank == 2 && (int)r.rows.dims[0] == 3
        && (int)r.rows.dims[1] == 5
        && (int)r.rows.size == (int)r.rows.dims[0] * (int)r.rows.dims[1]);
  int oklen = (int)r.lens.size == 3;
  for (int i = 0; oklen && i < 3; i++)
    if (((int32_t*)r.lens.data)[i] != 5) oklen = 0;
  check("`a || Zeros(0)` reports length 5, not 6 (no phantom row)", oklen);
  int okf = (int)r.rows.dims[1] == 5;
  for (int p = 0; okf && p < 3; p++)
    for (int k = 0; k < 5; k++)
      if (((int32_t*)r.rows.data)[p*5+k] != want_first[p][k]) okf = 0;
  check("rows read at dims[1] are correct when the FIRST needs no pad", okf);
  int okl = r.last.rank == 2 && (int)r.last.dims[1] == 5;
  for (int p = 0; okl && p < 3; p++)
    for (int k = 0; k < 5; k++)
      if (((int32_t*)r.last.data)[p*5+k] != want_last[p][k]) okl = 0;
  check("rows are correct when the LAST needs no pad (always worked)", okl);
}
#endif
#ifdef TEST_FORINIT_CATENATE_DV
// `returns value of catenate` on a SEQUENTIAL loop, which was rejected
// outright.  Why it went unnoticed: across the whole e2e corpus there were 97
// uses of catenate and every one sat in a FORALL -- not one in a for-initial.
// The gap was never worked around, it was never asked for.  The only two
// programs in test/unit that ask (crossovers.sis, ssphot.sis) were both
// unported, ssphot for exactly this reason; both compile now.
//
// A forall catenate PREALLOCATES -- catenate_store wants the trip count to size
// the result and a counter to index it -- and a sequential loop has neither.
// sisal_array_catenate, the grow-by-appending form, wants neither either, so
// the sequential path uses that.  argmax/argmin stay rejected: they must report
// a loop INDEX, which genuinely is absent.
static void test_forinit_catenate_dv(void) {
  printf("\n=== Group: forinit_catenate_dv (catenate on a sequential loop) ===\n");
  FCAT_results r = func_MAIN();
  auto eq = [](sisal_array_t x, const int* w, int n) {
    if ((int)x.size != n) return 0;
    for (int i = 0; i < n; i++) if (((int32_t*)x.data)[i] != w[i]) return 0;
    return 1;
  };
  int wseq[10] = {11,21,22,31,32,33,41,42,43,44};
  int wzt[9]   = {91,92,93,94,95,96,97,98,99};
  int wmk[7]   = {31,32,33,41,42,43,44};
  check("sequential catenate over rows 1..4, seed's row included",
        eq(r.seq, wseq, 10));
  // the 1.2 history rule: the seed is body_0, so a zero-trip is NOT empty
  check("ZERO TRIP still yields the seed's row, not nothing", eq(r.zt, wzt, 9));
  check("masked keeps only the surviving rows", eq(r.mask, wmk, 7));
  check("the forall form gives the identical 10 elements", eq(r.fa, wseq, 10));
  check("both loop forms agree on length", r.n == 10);
}
#endif
#ifdef TEST_PSA_DV
// psa.sis entire: Parallel Scheduler v1.0 (1989), simulated annealing on the
// School TimeTable Problem.  Lessons are dealt into timeslot periods; two in
// the same period cost 1 for each of room, class and teacher they share; the
// annealer moves lessons between periods, accepting worsenings with
// probability e**(-delta/T) and cooling by 0.9.
//
// Init_Periods joins its two unequal groups of periods with `||` -- held padded
// they are blocks of one rectangle, so it is a vstack, rank-2 on rank-2.
// Get_Swap_Set is a four-output forall: two gathers (advanced seeds as rank-1
// rows stacked into a rank-2, and the proposed swaps as records) plus two sum
// reductions.
//
// WHAT IS EXACT AND WHAT IS NOT.  Everything deterministic is pinned to OSC
// 13.0.3: the partition, the initial cost, one full swap round.  The cooling
// run is deliberately NOT compared value-by-value -- it is a long trajectory
// whose every branch is a float comparison against exp(), so matching OSC step
// for step would demand bit-identical transcendentals rather than correct
// compilation.  It is checked by the invariants that hold however the dice
// fall.
static void test_psa_dv(void) {
  printf("\n=== Group: psa_dv (whole program: annealing a timetable) ===\n");
  auto eq = [](sisal_array_t x, const int* w, int n) {
    if ((int)x.size != n) return 0;
    for (int i = 0; i < n; i++) if (((int32_t*)x.data)[i] != w[i]) return 0;
    return 1;
  };
  // --- 7 lessons over 3 periods: uneven partition, one swap accepted ---
  PSA_results a = func_MAIN(7, 3, 12345, 40, 20, 5.0f);
  int a0[3] = {3,2,2}, af[3] = {1,4,6}, a1[3] = {4,1,2};
  check("7 over 3: Init_Periods deals [3 2 2] -- `||` joins the two groups",
        eq(a.sz0, a0, 3));
  check("periods start at lessons 1, 4, 6", eq(a.firsts, af, 3));
  check("that partition is already clash-free (cost 0)", a.cost0 == 0);
  check("one round proposes 3 moves and accepts 1", a.nsw == 3 && a.nsu == 1);
  check("leaving sizes [4 1 2]", eq(a.sz1, a1, 3));
  // --- 30 over 3: periods wide enough to clash, so it actually anneals ---
  PSA_results b = func_MAIN(30, 3, 12345, 40, 20, 5.0f);
  int b0[3] = {10,10,10}, bf[3] = {1,11,21};
  check("30 over 3: even partition [10 10 10]", eq(b.sz0, b0, 3));
  check("periods start at lessons 1, 11, 21", eq(b.firsts, bf, 3));
  check("initial cost 36", b.cost0 == 36);
  check("one round proposes 3 moves and accepts none", b.nsw == 3 && b.nsu == 0);
  check("so the sizes are unchanged", eq(b.sz1, b0, 3));
  // --- the cooling run, by invariant ---
  int lessons = 0, maxp = 0;
  for (uint64_t i = 0; i < b.szf.size; i++) {
    int v = ((int32_t*)b.szf.data)[i];
    lessons += v; if (v > maxp) maxp = v;
  }
  check("it terminates and records at least one temperature", b.Es.size >= 1);
  check("every lesson is still scheduled exactly once", lessons == 30);
  check("no period overflows the capacity", maxp <= 30);
  int neg = 0;
  for (uint64_t i = 0; i < b.Es.size; i++)
    if (((int32_t*)b.Es.data)[i] < 0) neg = 1;
  check("the energy never goes negative", !neg);
}
#endif
#ifdef TEST_PSA_UPDATE_DV
// Applying a swap -- the layer that exercises the padded schedule hardest,
// since this is what makes periods shrink and grow.
//
// The original removes with a HOLE-FILL, not an ordered delete: the last lesson
// is moved over the vacated slot and the period shortens by one.  Order within
// a period carries no meaning (the cost is symmetric over pairs), so it ports
// to the padded form exactly -- overwrite slot `index` with slot n, decrement
// PSIZE.  Nothing reallocates, and the stale copy left at slot n sits past the
// live length where it can never be read.  Both ends of a swap become O(1)
// index writes, where the original's array_remh/array_addh each copy a period.
//
// Reproduced rather than tidied: Update_State_P recomputes Er with NO `- 3`,
// while Get_Swap's Er subtracts 3 for the lesson's own self-match.  The
// parallel path really does price a move differently from the sequential one --
// the original comment concedes the energy "may be incorrect due to
// simultaneous swaps".  Inserting the -3 would disagree with OSC.
static void test_psa_update_dv(void) {
  printf("\n=== Group: psa_update_dv (hole-fill removal, insert, energy) ===\n");
  PSA_UPD_results r = func_MAIN(6);
  auto eq = [](sisal_array_t x, const int* w, int n) {
    if ((int)x.size != n) return 0;
    for (int i = 0; i < n; i++) if (((int32_t*)x.data)[i] != w[i]) return 0;
    return 1;
  };
  int w1[3] = {2,3,4}, wsub[2] = {1,3}, w2[3] = {3,4,2};
  check("one swap 1->3: sizes [2 3 4]", eq(r.sz1, w1, 3));
  check("energy 2", r.E1 == 2);
  // subject 3 was the last lesson; it filled the hole subject 2 left
  check("period 1 holds subjects [1 3] -- 3 filled 2's hole", eq(r.subj1, wsub, 2));
  check("global cost 5 over the live slots only", r.gc == 5);
  check("two simultaneous swaps: energy 3", r.E2 == 3);
  check("and sizes [3 4 2]", eq(r.sz2, w2, 3));
}
#endif
#ifdef TEST_PSA_SWAP_DV
// psa's move selection: draw a lesson and a destination period at random,
// price the move, and let the Boltzmann criterion accept or reject.
//
// This is where the for-initial loops with no derivable trip count live -- the
// ones that made psa uncompilable.  `while array_size(schedule[from]) = 0` and
// `while to = from` are REJECTION SAMPLING: the iteration count is not merely
// unknown, it is unbounded in principle.  Both are FinalValue loops, so they
// never needed a preallocated gather, but the trip-count derivation ran anyway
// and rejected the program.
//
// On the padded schedule, `array_size(schedule[from])` becomes PSize[from] --
// reading the row would give the CAPACITY, which for an empty period is not 0
// and would break the rejection loop's exit test.  Values are OSC 13.0.3's.
static void test_psa_swap_dv(void) {
  printf("\n=== Group: psa_swap_dv (rejection sampling + Boltzmann) ===\n");
  PSA_SWAP_results r = func_MAIN(12345, 1.0f);
  auto eq = [](sisal_array_t x, const int* w, int n) {
    if ((int)x.size != n) return 0;
    for (int i = 0; i < n; i++) if (((int32_t*)x.data)[i] != w[i]) return 0;
    return 1;
  };
  int wsw[6] = {1,3,2,2,0,2};        // From To Index Ea Er Subject
  int ws1[4] = {125,3914,1591,2084};
  int wz[6]  = {0,0,0,0,0,0};
  check("Get_Swap: from 1 to 3, slot 2, Ea 2 Er 0, moving Subject 2",
        eq(r.sw, wsw, 6));
  check("and the seed it leaves behind = [125 3914 1591 2084]", eq(r.s1, ws1, 4));
  check("Get_Swap_P rejects this move (success 0)", r.ok == 0);
  check("a rejected move returns the zero swap", eq(r.swp, wz, 6));
  check("Boltzmann accepts delta 2 at T 1", r.b);
}
#endif
#ifdef TEST_XFA_DEP_EXPR
// fec8715 made `for i in 1,n cross j in i,n` work by moving a dependent nested
// bound's COPY-INS out of the preheader.  The bound MATH stayed hoisted, which
// is only correct while the bound is a bare name.  `j in i + 1, n` -- the upper
// triangle, how psa writes Period_Cost -- computed i+1 once with i unset, so it
// returned all zeros; `j in i, n-1` came back empty.
static void test_xfa_dep_expr(void) {
  printf("\n=== Group: xfa_dep_expr (dependent cross, expression bounds) ===\n");
  XDE_results r = func_MAIN(3);
  auto eq = [](sisal_array_t x, const int* w, int n) {
    if ((int)x.size != n) return 0;
    for (int i = 0; i < n; i++) if (((int32_t*)x.data)[i] != w[i]) return 0;
    return 1;
  };
  int wb[6] = {11,12,13,22,23,33}, wp[3] = {12,13,23};
  int wl[6] = {11,21,22,31,32,33}, wu[3] = {11,12,22};
  check("j in i, n     -- bare lower (worked before)", eq(r.bare, wb, 6));
  check("j in i + 1, n -- EXPRESSION: upper triangle", eq(r.plus1, wp, 3));
  check("j in 1, i     -- bare upper", eq(r.lower, wl, 6));
  check("j in i, n - 1 -- dependent lower, expression upper", eq(r.upper, wu, 3));
  check("reduction over the same nest counts 3 pairs", r.pairs == 3);
}
#endif
#ifdef TEST_PSA_COST_DV
// psa's cost/energy layer, and the schedule representation the later layers
// need.  psa's schedule is array[array[Tuple]] whose period sizes CHANGE as the
// annealer moves lessons between periods -- so there is no rectangle.  It
// becomes a padded rank-2 array_dv (periods x capacity) plus a PSIZE vector,
// the dense-plus-counts treatment moldyn's neighbour lists got; slots past
// PSIZE[p] hold a zero tuple and must never be counted.  Values are OSC
// 13.0.3's.  Period_Cost is the upper-triangle dependent cross that
// xfa_dep_expr covers.
static void test_psa_cost_dv(void) {
  printf("\n=== Group: psa_cost_dv (energy over a padded schedule) ===\n");
  PSA_COST_results r = func_MAIN(3, 3);
  auto eq = [](sisal_array_t x, const int* w, int n) {
    if ((int)x.size != n) return 0;
    for (int i = 0; i < n; i++) if (((int32_t*)x.data)[i] != w[i]) return 0;
    return 1;
  };
  int w111[3] = {1,1,1}, wr[3] = {3,0,1}, wsz[3] = {4,2,3};
  check("equal 3x3 periods: costs [1 1 1]", eq(r.PC, w111, 3));
  check("global cost 3", r.GC == 3);
  check("Member finds a tuple that is present", r.m1);
  check("Member rejects one that is not", !r.m2);
  check("Period_Index locates it at slot 2", r.i1 == 2);
  check("Period_Index returns the length when absent", r.i2 == 3);
  // the padded case: capacity 4, live lengths 4/2/3 -- the pad must not count
  check("ragged 4,2,3 held padded: costs [3 0 1]", eq(r.RPC, wr, 3));
  check("its global cost 4 -- padding contributes nothing", r.RGC == 4);
  check("live lengths [4 2 3]", eq(r.RSZ, wsz, 3));
}
#endif
#ifdef TEST_PSA_RNG_DV
// The RNG layer of psa.sis (Parallel Scheduler v1.0, 1989: simulated annealing
// on the School TimeTable Problem).  psa could not be compiled AT ALL until the
// for-initial gather stopped requiring a derivable trip count.
//
// A 48-bit multiplicative congruential sequence carried in FOUR 12-bit limbs --
// a bignum in base 4096 built from nothing but integer * / and mod -- so it
// pins exact integer semantics end to end, with no clock or OS entropy.
//
// `fourplex` is 0-BASED; Seed_Type = array[fourplex] becomes a rank-2 array_dv
// (n x 4) whose rows are those 0-based limb vectors.  That combination found a
// real bug: sisal_copy_inner_dims copied dims but not lower_bound, so stacking
// 0-based rows produced a rank-2 that was 1-BASED on its inner axis, and a row
// taken back out read one limb off.  ranf then returned 1.796434e-07 instead of
// 4.385825e-11 -- which is exactly 12345/68719476736, i.e. seed[1] where
// seed[0] was meant.  Values below are OSC 13.0.3's.
static void test_psa_rng_dv(void) {
  printf("\n=== Group: psa_rng_dv (psa's 48-bit LCG in 12-bit limbs) ===\n");
  PSA_RNG_results r = func_MAIN(5, 12345);
  auto ints_eq = [](sisal_array_t x, const int* w, int n, int lb) {
    if (x.rank != 1 || (int)x.size != n || (int)x.lower_bound[0] != lb) return 0;
    for (int i = 0; i < n; i++) if (((int32_t*)x.data)[i] != w[i]) return 0;
    return 1;
  };
  int wK[4] = {3276, 3276, 3276, 204};
  check("ranf_k(5) = [3276 3276 3276 204], 0-based", ints_eq(r.K, wK, 4, 0));
  // 48 bits, least significant first; 1-based since ranf_a_to_k reads k[1..46]
  int wKB[48]; for (int i = 0; i < 48; i++) wKB[i] = ((i % 4) == 2 || (i % 4) == 3) ? 1 : 0;
  wKB[44] = 0; wKB[45] = 0; wKB[46] = 0; wKB[47] = 0;
  check("its 48-bit expansion, 1-based", ints_eq(r.KB, wKB, 48, 1));
  int wAK[4] = {401, 1026, 1384, 3243};
  check("a**k mod 2**48 = [401 1026 1384 3243]", ints_eq(r.AK, wAK, 4, 0));
  // the seed set: rows 1-based, limbs 0-based -- the lower_bound that was lost
  int wSS[20] = { 12345,0,0,0,  2377,2346,60,607,  2905,580,3633,1934,
                  1641,2130,2945,2989,  2681,2532,1992,2514 };
  int okss = r.SS.rank == 2 && (int)r.SS.dims[0] == 5 && (int)r.SS.dims[1] == 4
             && (int)r.SS.size == 20
             && (int)r.SS.lower_bound[0] == 1 && (int)r.SS.lower_bound[1] == 0;
  for (int i = 0; okss && i < 20; i++)
    if (((int32_t*)r.SS.data)[i] != wSS[i]) okss = 0;
  check("rans(5,12345): 5 x 4 seeds, rows 1-based and limbs 0-BASED", okss);
  // the value that exposed the lost bound
  check("ranf(SS[1,..]) = 4.385825e-11 (not 1.796434e-07)",
        fabs(r.r - 4.3858247e-11) < 1e-17);
  int ws2[4] = {781, 3527, 3254, 267};
  check("and the seed after it = [781 3527 3254 267]", ints_eq(r.s2, ws2, 4, 0));
}
#endif
#ifdef TEST_FORINIT_GATHER_GROWTH_DV
// A for-initial gather PREALLOCATES, sizing itself from a trip count read off
// the loop test -- which only works for `i <op> bound` with op in </<=/>/>=.
// Anything else was a hard compile failure ("loop test is not a </<=/>/>=
// comparison"), which rejected ordinary loops: psa.sis has `while to = from`
// and `while ~found & (i < array_size(period))`, inside.sis a compound test.
// Preallocation is now a fast path; with no derivable count the gather starts
// from a typed empty array_dv and appends.  Values are OSC 13.0.3's.
static void test_forinit_gather_growth_dv(void) {
  printf("\n=== Group: forinit_gather_growth_dv (gather w/o a trip count) ===\n");
  FGG_results r = func_MAIN();
  auto ints_eq = [](sisal_array_t x, const int* w, int n) {
    if (x.rank != 1 || (int)x.size != n || (int)x.dims[0] != n) return 0;
    for (int i = 0; i < n; i++) if (((int32_t*)x.data)[i] != w[i]) return 0;
    return 1;
  };
  int w15[5] = {1,2,3,4,5}, w14[4] = {1,2,3,4}, w36[4] = {3,4,5,6};
  check("`<` comparison still preallocates -> [1 2 3 4 5]", ints_eq(r.ok, w15, 5));
  check("`~=` has no derivable count, appends -> [1 2 3 4 5]", ints_eq(r.eq, w15, 5));
  check("`~F & (I < 5)` (psa's shape) -> [1 2 3 4]", ints_eq(r.cj, w14, 4));
  // appends only survivors, so there is nothing over-allocated to shrink
  check("masked append -> [3 4 5 6], no post-loop shrink", ints_eq(r.mk, w36, 4));
  // element size comes off the descriptor, not a hardcoded 4/8
  float wr[4] = {1.0f, 2.0f, 4.0f, 8.0f};
  int okr = r.rl.rank == 1 && (int)r.rl.size == 4;
  for (int i = 0; okr && i < 4; i++)
    if (fabsf(((float*)r.rl.data)[i] - wr[i]) > 1e-6f) okr = 0;
  check("real element appends at the right stride -> [1 2 4 8]", okr);
  // 1-byte bool: a 4-byte store would corrupt the neighbouring elements
  bool wb[5] = {false,false,true,true,true};
  int okb = r.bl.rank == 1 && (int)r.bl.size == 5;
  for (int i = 0; okb && i < 5; i++)
    if (((bool*)r.bl.data)[i] != wb[i]) okb = 0;
  check("boolean element appends 1 byte apart -> [F F T T T]", okb);
}
#endif
#ifdef TEST_ADDH_ROW_DV
// `||` is concatenation along the FIRST axis, rank polymorphic the way numpy's
// concatenate-along-axis-0 is: rank2||rank1 appends one row, rank2||rank2
// appends a stack, rank1||rank1 flattens.  addh_arr always picked the right
// add_rows for these; what it never did was check that the operands CONFORM,
// so a mismatch was silent and produced a descriptor whose dims disagreed with
// its own size (3x5 || a 3-wide row reported dims 4 x 5 = 20 slots while size
// stayed 18, and the last row read past the end of the buffer).  Every
// dimension except the extended one must now match, as numpy requires; a
// mismatch aborts naming both shapes, so it is not exercised here.
static void test_addh_row_dv(void) {
  printf("\n=== Group: addh_row_dv (|| appends a conforming row) ===\n");
  AR_results r = func_MAIN(5);
  // Row(P,5) is P*10+1 .. P*10+5, so row P reads 11..15, 21..25, ...
  auto rows_ok = [](sisal_array_t x, int nr) {
    if (x.rank != 2 || (int)x.dims[0] != nr || (int)x.dims[1] != 5) return 0;
    if ((int)x.size != nr * 5) return 0;              // dims must match size
    for (int p = 0; p < nr; p++)
      for (int k = 0; k < 5; k++)
        if (((int32_t*)x.data)[p*5+k] != (p+1)*10 + k+1) return 0;
    return 1;
  };
  check("3x5 || one row  -> 4x5 (np.vstack)", rows_ok(r.one, 4));
  check("3x5 || 2x5      -> 5x5 (np.concatenate axis 0)", rows_ok(r.blk, 5));
  check("rows appended in a loop from a 1xN seed -> 4x5", rows_ok(r.grown, 4));
  // rank1 || rank1 FLATTENS -- it does not build a 2x5, just as np.concatenate
  // on two 1-D arrays gives a 1-D result
  int okflat = r.flat.rank == 1 && (int)r.flat.size == 10 && (int)r.flat.dims[0] == 10;
  for (int i = 0; okflat && i < 10; i++)
    if (((int32_t*)r.flat.data)[i] != (i/5+1)*10 + i%5 + 1) okflat = 0;
  check("row || row -> flat 10, not 2x5", okflat);
  check("m || empty is the identity", rows_ok(r.ident, 3));
  // array_addh is the sharper tool: its second operand is ONE element by
  // definition, so a row is unambiguous and nothing has to be sniffed.  That
  // is what lets it work from an EMPTY accumulator, where a zero-trip gather's
  // rank-1 descriptor leaves `||` with nothing to infer from.
  check("array_addh(3x5, row) -> 4x5", rows_ok(r.ah_one, 4));
  check("array_addh(empty, row) -> 1x5, not rank 1",
        r.ah_empty.rank == 2 && (int)r.ah_empty.dims[0] == 1
        && (int)r.ah_empty.dims[1] == 5 && (int)r.ah_empty.size == 5);
  // the one that actually bites: this silently built a flat 15-vector
  check("rows added in a loop from an EMPTY seed -> 3x5, not flat 15",
        rows_ok(r.ah_accum, 3));
}
#endif
#ifdef TEST_MOLDYN_NEIGHBORS_DV
// moldyn's Get_Neighbor_Lists / Get_Neighbors / Separation -- what BUILDS the
// ragged neighbour structure moldyn_force_dv consumes.
//
// Get_Neighbors is kept as the original writes it: a masked gather on a SINGLE
// generator, which compacts correctly since a lone generator's survivors are
// counted once.  Get_Neighbor_Lists is what cannot survive -- it gathers those
// rows with `array of N_LIST`, and rows of differing length are ragged.  It
// becomes the padded rank-2 NEIGHBORS plus the NCOUNT extent vector the force
// core already expects.
//
// The padded row is built by an explicit scan rather than by appending zeros
// to the packed row.  `N_LIST || Zeros(MaxN - array_size(N_LIST))` hits a
// compiler bug: when the FIRST row's right operand is empty, the enclosing
// rank-2 gather reports dims[1] = true_length + 1 while size stays correct, so
// every later row is read at the wrong stride.  Case B below is exactly that
// shape -- every particle has the maximum neighbour count, so every pad is
// empty -- and it must come out rectangular and consistent.
//
// Counts are cross-checked two ways: NCOUNT comes from array_size of the
// ORIGINAL packed masked gather, while the rows come from the scan, so the two
// spellings of "who are my neighbours" have to agree with each other and with
// the mirror.
static int mn_case(const float* px, const float* py, const float* pz, const char* tag) {
  const int NP = 6, NT = 2, MaxN = NP - 1;
  int ty[NP] = { 1, 1, 2, 1, 2, 1 };
  float rc[NT * NT] = { 2.0f, 2.0f, 2.0f, 2.0f };
  auto sep = [&](int a, int b) {
    float dx = px[a] - px[b], dy = py[a] - py[b], dz = pz[a] - pz[b];
    return sqrtf(dx * dx + dy * dy + dz * dz);
  };
  std::vector<std::vector<int>> nb(NP);
  for (int p = 1; p <= NP; p++) for (int q = 1; q <= NP; q++)
    if (q != p && sep(p - 1, q - 1) <= rc[(ty[p - 1] - 1) * NT + (ty[q - 1] - 1)])
      nb[p - 1].push_back(q);

  auto mk1 = [&](const void* s2, size_t n, size_t esz) {
    sisal_array_t A = sisal_array_alloc_sized(1, 96, n, esz);
    A.lower_bound[0] = 1; A.stride[0] = 1; memcpy(A.data, s2, esz * n); return A;
  };
  auto mk2 = [&](const void* s2, int d0, int d1, size_t esz) {
    sisal_array_t A = sisal_array_alloc_sized(2, 96, (size_t)d0 * d1, esz);
    A.rank = 2; A.dims[0] = d0; A.dims[1] = d1;
    A.lower_bound[0] = 1; A.lower_bound[1] = 1; A.stride[0] = d1; A.stride[1] = 1;
    memcpy(A.data, s2, esz * (size_t)d0 * d1); return A;
  };
  mn_ens e; e.tout = 0; e.step = 0.01f; e.err = 0; e.size = NP;
  e.pos.X = mk1(px, NP, sizeof(float)); e.pos.Y = mk1(py, NP, sizeof(float));
  e.pos.Z = mk1(pz, NP, sizeof(float));
  float zv[NP] = { 0, 0, 0, 0, 0, 0 };
  e.vel.VX = mk1(zv, NP, sizeof(float)); e.vel.VY = mk1(zv, NP, sizeof(float));
  e.vel.VZ = mk1(zv, NP, sizeof(float));
  e.types = mk1(ty, NP, sizeof(int32_t));
  mn_pd pd; pd.nt = NT; float one[NT * NT] = { 1, 1, 1, 1 };
  pd.A1 = mk2(one, NT, NT, sizeof(float)); pd.B1 = mk2(one, NT, NT, sizeof(float));
  pd.Re = mk2(one, NT, NT, sizeof(float)); pd.Rc = mk2(rc, NT, NT, sizeof(float));
  pd.ALFA = mk2(one, NT, NT, sizeof(float)); pd.C0 = mk2(one, NT, NT, sizeof(float));
  float mass[NT] = { 1, 2 }; pd.MASS = mk1(mass, NT, sizeof(float));
  pd.dt = 0.01f; pd.endt = 1.0f; pd.tol = 1e-6f;
  MN_results r = func_MAIN(e, pd);

  char msg[160];
  snprintf(msg, sizeof msg, "%s: NEIGHBORS is rectangular rank-2 (NP x MaxN)", tag);
  check(msg, r.neighbors.rank == 2 && (int)r.neighbors.dims[0] == NP
         && (int)r.neighbors.dims[1] == MaxN
         && (int)r.neighbors.size == NP * MaxN);
  int okc = (int)r.ncount.size == NP, okr = 1;
  for (int p = 0; p < NP; p++) {
    if (((int32_t*)r.ncount.data)[p] != (int)nb[p].size()) okc = 0;
    for (int k = 0; k < MaxN; k++) {
      int want = k < (int)nb[p].size() ? nb[p][k] : 0;
      if (((int32_t*)r.neighbors.data)[p * MaxN + k] != want) okr = 0;
    }
  }
  snprintf(msg, sizeof msg, "%s: NCOUNT (from the packed masked gather) == mirror", tag);
  check(msg, okc);
  snprintf(msg, sizeof msg, "%s: padded rows == mirror, zero-filled past the count", tag);
  check(msg, okr);
  // The rows above are built the NATURAL way -- `N_LIST || Zeros(MaxN - size)`
  // -- which used to be unwritable here: an empty pad on the FIRST row left
  // the gather reporting dims[1] = true_length + 1, so every later row was
  // read at the wrong offset.  NEIGHBORS_SCAN builds the identical rectangle
  // by an independent search (Kth_Neighbor), so the two spellings have to
  // agree element for element -- a regression in either shows as a
  // disagreement rather than as a plausible wrong answer.
  int oks = r.scan.rank == 2 && (int)r.scan.dims[0] == NP
            && (int)r.scan.dims[1] == MaxN && (int)r.scan.size == NP * MaxN;
  for (int i = 0; oks && i < NP * MaxN; i++)
    if (((int32_t*)r.scan.data)[i] != ((int32_t*)r.neighbors.data)[i]) oks = 0;
  snprintf(msg, sizeof msg, "%s: `|| Zeros(..)` rows == independent scan", tag);
  check(msg, oks);
  return okc && okr && oks;
}
static void test_moldyn_neighbors_dv(void) {
  printf("\n=== Group: moldyn_neighbors_dv (building the ragged lists) ===\n");
  // A: spread along a line -> counts vary (2 3 3 2 0 0), two isolated particles
  float ax[6] = { 0.0f, 0.5f, 1.0f, 2.5f, 5.0f, 20.0f };
  float ay[6] = { 0, 0, 0, 0, 0, 0 }, az[6] = { 0, 0, 0, 0, 0, 0 };
  // B: one tight cluster -> EVERY particle has the maximum count, so every
  //    pad is empty including the first
  float bx[6] = { 0.0f, 0.1f, 0.2f, 0.3f, 0.4f, 0.5f };
  float by[6] = { 0, 0, 0, 0, 0, 0 }, bz[6] = { 0, 0, 0, 0, 0, 0 };
  mn_case(ax, ay, az, "varied counts");
  mn_case(bx, by, bz, "every particle maximal");
}
#endif
#ifdef TEST_MOLDYN_NBRLIST_DV
// The same neighbour structure as moldyn_neighbors_dv, but as a LIST OF
// array_dv -- which is what a ragged 2-D actually is.  The inner dimension is
// a genuine rank-1 dope of exactly the neighbour count (the ORIGINAL masked
// gather, untouched); the outer dimension is a cons list holding those dopes
// by reference.
//
// Nothing is padded and nothing is scanned.  moldyn_neighbors_dv has to spend
// NP x (NP-1) slots however sparse the graph is, and needs a per-slot search
// to fill them; here the outer loop is O(1) per particle because consing
// stores the handle.  The check below prints both figures: for the sparse
// case the flat data is 10 slots against the padded form's 30.
//
// The cross nest cannot express this.  `for P in 1,NP cross K in 1,MaxN` fixes
// dims[1] before the loops open and lands row P at P*width via a single flat
// write counter -- there is no width here.  So the nest comes apart: a
// let-bound inner forall per particle, and a for-initial over particles that
// conses.  Iteration runs DOWNWARD so consing yields ascending order with no
// reversal pass.
//
// Verified as a CSR pair -- Flatten gives every row end to end, Row_Lengths
// gives where each stops -- against a mirror that builds the ragged lists
// directly.
static int nl_case(const float* px, const float* py, const float* pz, const char* tag) {
  const int NP = 6, NT = 2;
  int ty[NP] = { 1, 1, 2, 1, 2, 1 };
  float rc[NT * NT] = { 2.0f, 2.0f, 2.0f, 2.0f };
  auto sep = [&](int a, int b) {
    float dx = px[a] - px[b], dy = py[a] - py[b], dz = pz[a] - pz[b];
    return sqrtf(dx * dx + dy * dy + dz * dz);
  };
  std::vector<std::vector<int>> nb(NP);
  for (int p = 1; p <= NP; p++) for (int q = 1; q <= NP; q++)
    if (q != p && sep(p - 1, q - 1) <= rc[(ty[p - 1] - 1) * NT + (ty[q - 1] - 1)])
      nb[p - 1].push_back(q);
  std::vector<int> mflat, mlens;
  for (int p = 0; p < NP; p++) {
    mlens.push_back((int)nb[p].size());
    for (int v : nb[p]) mflat.push_back(v);
  }
  auto mk1 = [&](const void* s2, size_t n, size_t esz) {
    sisal_array_t A = sisal_array_alloc_sized(1, 96, n, esz);
    A.lower_bound[0] = 1; A.stride[0] = 1; memcpy(A.data, s2, esz * n); return A;
  };
  auto mk2 = [&](const void* s2, int d0, int d1, size_t esz) {
    sisal_array_t A = sisal_array_alloc_sized(2, 96, (size_t)d0 * d1, esz);
    A.rank = 2; A.dims[0] = d0; A.dims[1] = d1;
    A.lower_bound[0] = 1; A.lower_bound[1] = 1; A.stride[0] = d1; A.stride[1] = 1;
    memcpy(A.data, s2, esz * (size_t)d0 * d1); return A;
  };
  nl_ens e; e.tout = 0; e.step = 0.01f; e.err = 0; e.size = NP;
  e.pos.X = mk1(px, NP, sizeof(float)); e.pos.Y = mk1(py, NP, sizeof(float));
  e.pos.Z = mk1(pz, NP, sizeof(float));
  float zv[NP] = { 0, 0, 0, 0, 0, 0 };
  e.vel.VX = mk1(zv, NP, sizeof(float)); e.vel.VY = mk1(zv, NP, sizeof(float));
  e.vel.VZ = mk1(zv, NP, sizeof(float));
  e.types = mk1(ty, NP, sizeof(int32_t));
  nl_pd pd; pd.nt = NT; float one[NT * NT] = { 1, 1, 1, 1 };
  pd.A1 = mk2(one, NT, NT, sizeof(float)); pd.B1 = mk2(one, NT, NT, sizeof(float));
  pd.Re = mk2(one, NT, NT, sizeof(float)); pd.Rc = mk2(rc, NT, NT, sizeof(float));
  pd.ALFA = mk2(one, NT, NT, sizeof(float)); pd.C0 = mk2(one, NT, NT, sizeof(float));
  float mass[NT] = { 1, 2 }; pd.MASS = mk1(mass, NT, sizeof(float));
  pd.dt = 0.01f; pd.endt = 1.0f; pd.tol = 1e-6f;

  char msg[160];
  // one call per particle: each hands back that row's OWN array_dv, at its
  // true length -- no padding to strip, no buffer to slice
  int okl = 1, okr = 1, okn = 1, total = 0;
  for (int p = 1; p <= NP; p++) {
    NL_results r = func_MAIN(e, pd, p);
    okn &= (r.nrows == NP) && ((int)r.lens.size == NP);
    for (int i = 0; i < NP && i < (int)r.lens.size; i++)
      if (((int32_t*)r.lens.data)[i] != (int)nb[i].size()) okl = 0;
    // the row itself: length is the neighbour count exactly
    if ((int)r.row.size != (int)nb[p - 1].size()) okr = 0;
    else for (int k = 0; k < (int)nb[p - 1].size(); k++)
      if (((int32_t*)r.row.data)[k] != nb[p - 1][k]) okr = 0;
    if (p == 1) for (int i = 0; i < NP; i++) total += (int)nb[i].size();
  }
  snprintf(msg, sizeof msg, "%s: one list node per particle", tag);
  check(msg, okn);
  snprintf(msg, sizeof msg, "%s: row lengths == ragged mirror", tag);
  check(msg, okl);
  snprintf(msg, sizeof msg, "%s: each row is its OWN array_dv at its true length", tag);
  check(msg, okr);
  printf("       rows hold %d elements total; the padded rank-2 form would hold %d\n",
         total, NP * (NP - 1));
  return okl && okr && okn;
}
static void test_moldyn_nbrlist_dv(void) {
  printf("\n=== Group: moldyn_nbrlist_dv (ragged 2-D as a list of array_dv) ===\n");
  float ax[6] = { 0.0f, 0.5f, 1.0f, 2.5f, 5.0f, 20.0f };
  float ay[6] = { 0, 0, 0, 0, 0, 0 }, az[6] = { 0, 0, 0, 0, 0, 0 };
  float bx[6] = { 0.0f, 0.1f, 0.2f, 0.3f, 0.4f, 0.5f };
  float by[6] = { 0, 0, 0, 0, 0, 0 }, bz[6] = { 0, 0, 0, 0, 0, 0 };
  nl_case(ax, ay, az, "sparse");
  nl_case(bx, by, bz, "dense");
}
#endif
#ifdef TEST_ZEROTRIP_EXPR_DV
// docs/loop_behavior_comparison.md Rule 1: the `initial` clause is body_0 of
// every returns sequence, so a zero-trip loop yields the SEED, not nothing.
// That held for a RETURNS whose payload is a bare CARRY -- a carry has a MERGE
// which INIT seeds -- but not for an EXPRESSION payload, which was lowered
// only into the BODY and so read a port the body never wrote, coming back as
// the type default (0 / empty / wrong element type).
//
// Expected values are OSC 13.0.3's, taken from ~/work/oldsisal, not our own.
// Bare and expression forms sit side by side because only the expression ones
// were ever wrong, and `live` pins that the zero-trip arm does NOT leak into
// the ordinary path (the loop runs; keep-last must be the final body value).
static void test_zerotrip_expr_dv(void) {
  printf("\n=== Group: zerotrip_expr_dv (Rule 1 for expression payloads) ===\n");
  ZT_results r = func_MAIN();
  check("value of I           == 10  (bare, already worked)", r.fvb == 10);
  check("value of I * 2       == 20  (OSC 13.0.3)", r.fve == 20);
  check("value of I * 3 + 1   == 31  (OSC 13.0.3)", r.fvn == 31);
  check("array_dv of I        == [10] (bare)",
        (int)r.gab.size == 1 && ((int32_t*)r.gab.data)[0] == 10);
  check("array_dv of I * 2    == [20], and as INTEGRAL not double",
        (int)r.gae.size == 1 && ((int32_t*)r.gae.data)[0] == 20);
  check("value of sum I       == 10  (bare)", r.rdb == 10);
  check("value of sum I * 2   == 20  (OSC 13.0.3)", r.rde == 20);
  check("non zero-trip keep-last still the last BODY value (8)", r.live == 8);
}
#endif
#ifdef TEST_FORINIT_MASK_DV
// `when`/`unless` on a for-initial RETURNS.  These were dropped entirely --
// masked gathers and masked reductions on a sequential loop admitted every
// element, silently, for loops that RUN.  The forall path was always right,
// which is why moldyn's Get_Neighbors (a forall) worked while the same shape
// as a for-initial did not.
//
// The seed carries the interesting case: a carry's history begins with body_0,
// so the seed must be masked too, using the mask applied to the SEED.  The
// BODY's copy computes it on the post-update value instead, so masks are
// specialised in INIT and selected by their own INIT|BODY mux.  Both zero-trip
// directions are pinned below precisely so neither can pass by accident --
// before the fix, mask-TRUE-at-seed was right only because the mask was
// ignored, and mask-FALSE-at-seed was wrong.
//
// All expectations are OSC 13.0.3's, from ~/work/oldsisal.
static void test_forinit_mask_dv(void) {
  printf("\n=== Group: forinit_mask_dv (when/unless on a sequential loop) ===\n");
  FM_results r = func_MAIN();
  auto same = [](sisal_array_t a, std::vector<int> w) {
    if ((int)a.size != (int)w.size()) return 0;
    for (int i = 0; i < (int)w.size(); i++)
      if (((int32_t*)a.data)[i] != w[i]) return 0;
    return 1;
  };
  check("forall masked gather == [3,4,5] (was already right)",
        same(r.fa, { 3, 4, 5 }));
  check("for-initial masked gather == [3,4,5]", same(r.fi, { 3, 4, 5 }));
  check("forall masked reduce == 12 (was already right)", r.ra == 12);
  check("for-initial masked reduce == 12", r.ri == 12);
  check("zero-trip, mask TRUE at the seed == [10]", same(r.zt, { 10 }));
  check("zero-trip, mask FALSE at the seed == [] (seed excluded)",
        (int)r.zf.size == 0);
  check("unmasked control still the whole history == [1,2,3,4,5]",
        same(r.un, { 1, 2, 3, 4, 5 }));
}
#endif
#ifdef TEST_ARRAY_EX_DV
// array_dv[real]: multi-element replace rh[1:rh[2];2:rh[3]] then `|| ph`.
// rh=[1.18,7.23,3.18,10.6] -> [7.23,3.18,3.18,10.6] ++ ph=[2.18,4.23,6.18,12.6].
static void test_array_ex_dv() {
  printf("\n=== Group: array_ex_dv (array_dv multi-replace + catenate) ===\n");
  sisal_array_t r = func_MAIN();
  float exp[] = {7.23f, 3.18f, 3.18f, 10.6f, 2.18f, 4.23f, 6.18f, 12.6f};
  check("size is 8", (int)r.size == 8);
  int ok = (int)r.size == 8;
  for (int i = 0; ok && i < 8; i++) ok = std::fabs(((float *)r.data)[i] - exp[i]) < 1e-4f;
  check("values [7.23,3.18,3.18,10.6,2.18,4.23,6.18,12.6]", ok);
}
#endif
#ifdef TEST_NICO_DV
// Sieve of Eratosthenes over odd integers (array_dv_fill boolean + sift +
// masked-gather convert): returns the odd primes in [3, 2N+1].  Exercises the
// boolean-fill fix.  Reference = a straight sieve over [3, 2N+1].
static void test_nico_dv() {
  printf("\n=== Group: nico_dv (odd-prime sieve; array_dv_fill bool + masked gather) ===\n");
  for (int N : {3, 5, 10, 20, 50}) {
    int hi = 2 * N + 1;
    std::vector<char> comp(hi + 1, 0);
    std::vector<int32_t> ref;
    for (int p = 2; p <= hi; p++)
      if (!comp[p]) {
        if (p >= 3) ref.push_back(p);              // odd primes only (2 excluded)
        for (int m = 2 * p; m <= hi; m += p) comp[m] = 1;
      }
    sisal_array_t r = func_MAIN(N);
    int ok = (int)r.size == (int)ref.size();
    for (size_t i = 0; ok && i < ref.size(); i++) ok = ((int32_t *)r.data)[i] == ref[i];
    char tag[48]; snprintf(tag, sizeof tag, "primes in [3,%d] (N=%d)", hi, N);
    check(tag, ok);
  }
}
#endif
#ifdef TEST_NICO2_DV
// Same odd-prime sieve as nico, but Sift marks composites via in-place boolean
// element REPLACE in a for-initial loop (`x := old x[j: false]`) -- exercises
// the boolean array_dv replace fix.  Reference = same sieve over [3, 2N+1].
static void test_nico2_dv() {
  printf("\n=== Group: nico2_dv (odd-prime sieve; boolean array_dv replace) ===\n");
  for (int N : {3, 5, 10, 20, 50}) {
    int hi = 2 * N + 1;
    std::vector<char> comp(hi + 1, 0);
    std::vector<int32_t> ref;
    for (int p = 2; p <= hi; p++)
      if (!comp[p]) {
        if (p >= 3) ref.push_back(p);
        for (int m = 2 * p; m <= hi; m += p) comp[m] = 1;
      }
    sisal_array_t r = func_MAIN(N);
    int ok = (int)r.size == (int)ref.size();
    for (size_t i = 0; ok && i < ref.size(); i++) ok = ((int32_t *)r.data)[i] == ref[i];
    char tag[48]; snprintf(tag, sizeof tag, "primes in [3,%d] (N=%d)", hi, N);
    check(tag, ok);
  }
}
#endif
#ifdef TEST_TEST_BIN_DV
// Nested-function scalar arithmetic: Main(level) = tempFun(a,b) = a*b where
// a = x*y + 6z, b = x*z + 6y, x=level-1, y=level+1, z=level-4.
static void test_test_bin_dv() {
  printf("\n=== Group: test_bin_dv (nested-fn scalar arithmetic) ===\n");
  for (int lv : {5, 10, 0, -3, 7, 100}) {
    int x = lv - 1, y = lv + 1, z = lv - 4;
    int ref = (x * y + 2 * 3 * z) * (x * z + 2 * 3 * y);
    char tag[32]; snprintf(tag, sizeof tag, "level=%d", lv);
    check(tag, func_MAIN(lv) == ref);
  }
}
#endif
#ifdef TEST_IF_COMPLEX_REVIEW_DV
// if/elseif returning a (int, array_dv[int], MyRec) tuple.  MyRec{a:int;b:double}.
// Exercises flat records + array_dv pass-through + multi-return through nested if
// (compiles thanks to the struct default-init fix).  Reference by construction.
static sisal_array_t ticr_mkarr(const int32_t *v, int n) {
  sisal_array_t a = sisal_array_alloc_empty(1, 6, n);
  a.lower_bound[0] = 1; a.dims[0] = n;
  for (int i = 0; i < n; i++) ((int32_t *)a.data)[i] = v[i];
  return a;
}
static void test_if_complex_review_dv() {
  printf("\n=== Group: test_if_complex_review_dv (if/elseif -> int,array_dv,record) ===\n");
  int32_t A[] = {10, 20, 30}, zero[] = {0};
  struct ticr_rec rec{7, 3.5};
  auto chk = [&](const char *t, struct FUNC_MAIN_results r, int e0,
                 const int32_t *ea, int en, int erA, double erB) {
    int ok = r.res_0 == e0 && (int)r.res_1.size == en && r.res_2.A == erA
             && std::fabs(r.res_2.B - erB) < 1e-9;
    for (int i = 0; ok && i < en; i++) ok = ((int32_t *)r.res_1.data)[i] == ea[i];
    check(t, ok);
  };
  chk("sel=1 flag=T", func_MAIN(1, true,  100, ticr_mkarr(A, 3), rec), 110, A, 3, 7, 3.5);
  chk("sel=1 flag=F", func_MAIN(1, false, 100, ticr_mkarr(A, 3), rec), 120, A, 3, 8, 3.5);
  chk("sel=2",        func_MAIN(2, true,  100, ticr_mkarr(A, 3), rec), 200, A, 3, 7, 3.5);
  chk("else (sel=9)", func_MAIN(9, true,  100, ticr_mkarr(A, 3), rec), 0, zero, 1, 0, 0.0);
}
#endif
#ifdef TEST_TAGCASE_II_DV
// tagcase over union[A:int; B:int; D:array_dv[int]] (non-recursive), built
// internally.  A -> I, B -> otherwise -> 4, D -> P[I] (=I*10 for [10,20,30,40]).
static void test_tagcase_ii_dv() {
  printf("\n=== Group: tagcase_ii_dv (tagcase over union w/ array payload) ===\n");
  for (int I : {1, 2, 3, 4}) {
    struct FUNC_MAIN_results r = func_MAIN(I, 0);
    char tag[24]; snprintf(tag, sizeof tag, "I=%d", I);
    check(tag, r.res_0 == I && r.res_1 == 4 && r.res_2 == I * 10);
  }
}
#endif
#ifdef TEST_NESTED_DV
// Minimal nested-function capture: Outer(I) { Inner(X) = X + I; Inner(I) } = 2I.
static void test_nested_dv() {
  printf("\n=== Group: nested_dv (minimal nested-fn capture) ===\n");
  for (int i : {5, 0, -3, 100, 7}) {
    char tag[24]; snprintf(tag, sizeof tag, "Outer(%d)", i);
    check(tag, func_OUTER(i) == 2 * i);
  }
}
#endif
#ifdef TEST_VECTEST_DV
// 18 vector kernels over internally-built arrays (i=1..n):
//   Tri(XIn,Z,Y): scan X=Z[k]*(Y[k]-X); Sum(YIn): partial sums; both gather the
//   seed then each body value (N elements).  min/amin/max/amax: index of first
//   (abs) min/max over WIn (=+-i).  D/R/I = double/float/int precision.
template <class T> static int vt_maxi(const T *w, int n) { int x=1; for (int k=2;k<=n;k++) if (w[k]>w[x]) x=k; return x; }
template <class T> static int vt_mini(const T *w, int n) { int x=1; for (int k=2;k<=n;k++) if (w[k]<w[x]) x=k; return x; }
template <class T> static int vt_amaxi(const T *w, int n) { int x=1; for (int k=2;k<=n;k++) if (std::abs(w[k])>std::abs(w[x])) x=k; return x; }
template <class T> static int vt_amini(const T *w, int n) { int x=1; for (int k=2;k<=n;k++) if (std::abs(w[k])<std::abs(w[x])) x=k; return x; }
template <class T> static void vt_tri(const T *xin, const T *z, const T *y, int n, T *o) { T x=xin[1]; o[0]=x; for (int k=2;k<=n;k++){ x=z[k]*(y[k]-x); o[k-1]=x; } }
template <class T> static void vt_psum(const T *yin, int n, T *o) { T x=yin[1]; o[0]=x; for (int k=2;k<=n;k++){ x=x+yin[k]; o[k-1]=x; } }
template <class T> static bool vt_eqarr(sisal_array_t a, const T *ref, int n, double tol) {
  if ((int)a.size != n) return false;
  for (int i = 0; i < n; i++) if (std::abs((double)((T *)a.data)[i] - (double)ref[i]) > tol) return false;
  return true;
}
static bool vectest_run(int n) {
  double XInD[70],ZD[70],YD[70],YInD[70],WInD[70];
  float  XInR[70],ZR[70],YR[70],YInR[70],WInR[70];
  int    XInI[70],ZI[70],YI[70],YInI[70],WInI[70];
  for (int i = 1; i <= n; i++) {
    XInD[i]=1.0/i; ZD[i]=1.0/(i+1); YD[i]=1.0/(i+2); YInD[i]=1.0/i;
    XInR[i]=1.0f/i; ZR[i]=1.0f/(i+1); YR[i]=1.0f/(i+2); YInR[i]=1.0f/i;
    XInI[i]=1; ZI[i]=2; YI[i]=3; YInI[i]=i;
    int w=(i%2==0)?-i:i; WInD[i]=w; WInR[i]=(float)w; WInI[i]=w;
  }
  double triD[70],sumD[70]; float triR[70],sumR[70]; int triI[70],sumI[70];
  vt_tri(XInD,ZD,YD,n,triD); vt_tri(XInR,ZR,YR,n,triR); vt_tri(XInI,ZI,YI,n,triI);
  vt_psum(YInD,n,sumD); vt_psum(YInR,n,sumR); vt_psum(YInI,n,sumI);
  struct FUNC_MAIN_results r = func_MAIN(n);
  return vt_eqarr(r.res_0,triD,n,1e-9) && vt_eqarr(r.res_1,triR,n,1e-4) && vt_eqarr(r.res_2,triI,n,0)
      && vt_eqarr(r.res_3,sumD,n,1e-9) && vt_eqarr(r.res_4,sumR,n,1e-4) && vt_eqarr(r.res_5,sumI,n,0)
      && r.res_6==vt_mini(WInD,n) && r.res_7==vt_mini(WInR,n) && r.res_8==vt_mini(WInI,n)
      && r.res_9==vt_amini(WInD,n) && r.res_10==vt_amini(WInR,n) && r.res_11==vt_amini(WInI,n)
      && r.res_12==vt_maxi(WInD,n) && r.res_13==vt_maxi(WInR,n) && r.res_14==vt_maxi(WInI,n)
      && r.res_15==vt_amaxi(WInD,n) && r.res_16==vt_amaxi(WInR,n) && r.res_17==vt_amaxi(WInI,n);
}
static void test_vectest_dv() {
  printf("\n=== Group: vectest_dv (18 vector kernels: Tri/Sum scans + min/max indices) ===\n");
  for (int n : {3, 5, 8, 12, 20}) {
    char tag[24]; snprintf(tag, sizeof tag, "n=%d (18 kernels)", n);
    check(tag, vectest_run(n));
  }
}
#endif
#ifdef TEST_LEGPOLY1_DV
// Legendre polynomial (1st kind), ir=2 branch (p2 := pp): the pp for-initial
// recurrence with an inner s1/s2 loop and array element replaces at n+1 /
// n+irmax2, over SIN/COS/SQRT.  Faithful C mirror of the algorithm (1-indexed).
static void legpoly1_ref(int ir, int irmax2, int jxxmx, double theta, double *out) {
  double p[320] = {0};   // 1-indexed; jxxmx bounded well under 320
  double sqr2 = sqrt(2.0), c1 = sqr2; p[1] = 1.0 / sqr2;
  int irpp = ir + 2, n_old = 1;
  while (n_old <= irpp) {
    double fn = (double)n_old, fn2 = 2.0 * fn, fn2sq = fn2 * fn2;
    c1 = c1 * sqrt(1.0 - 1.0 / fn2sq);
    double c3 = c1 / sqrt(fn * (fn + 1.0));
    int kk_old = 1; double ang = fn * theta; int n1 = n_old + 1;
    double ss1 = 0, ss2 = 0, c4 = 1.0, c5 = fn, a = -1.0, b = 0.0;
    while (kk_old <= n1) {
      int kk = kk_old + 2, k = kk_old - 1;
      double ss2n = ss2 + c5 * sin(ang) * c4;
      double c4t = (k == n_old) ? 0.5 * c4 : c4;
      double ss1n = ss1 + c4t * cos(ang);
      double an = a + 2.0, bn = b + 1.0, fk = (double)k;
      double angn = theta * (fn - fk - 2.0);
      double c4n = (an * (fn - bn + 1.0) / (bn * (fn2 - an))) * c4t;
      double c5n = c5 - 2.0;
      kk_old = kk; ss1 = ss1n; ss2 = ss2n; ang = angn; c4 = c4n; c5 = c5n; a = an; b = bn;
    }
    double s1 = ss1, s2 = ss2;
    if (n_old - irpp < 0) { p[n_old + 1] = s1 * c1; p[n_old + irmax2] = s2 * c3; }
    else if (n_old - irpp == 0) { p[n_old + irmax2] = s2 * c3; }
    n_old++;
  }
  for (int i = 0; i < jxxmx; i++) out[i] = p[i + 1];
}
static void test_legpoly1_dv() {
  printf("\n=== Group: legpoly1_dv (Legendre 1st kind, ir=2 recurrence) ===\n");
  struct { int irmax2, jxxmx; double ang; } cs[] = {
    {20, 60, 0.5}, {20, 60, 1.0}, {15, 50, 0.3}, {25, 80, 0.8},
  };
  for (auto &c : cs) {
    double ref[300];
    legpoly1_ref(2, c.irmax2, c.jxxmx, c.ang, ref);
    sisal_array_t r = func_LEGENDREPOLYOF1STKIND(2, c.irmax2, c.jxxmx,
        (float)cos(c.ang), (float)sin(c.ang), (float)c.ang);
    int ok = (int)r.size == c.jxxmx;
    for (int i = 0; ok && i < c.jxxmx; i++)
      ok = std::fabs(((double *)r.data)[i] - ref[i]) < 1e-4;
    char tag[48]; snprintf(tag, sizeof tag, "ir=2 irmax2=%d jxxmx=%d ang=%.1f", c.irmax2, c.jxxmx, c.ang);
    check(tag, ok);
  }
}
#endif
#ifdef TEST_INTRINSICS_TEST_DV
// AllIntrinsics(A,B,flag): C=A*B+(A-B)/2, D=max(A,B), E=(A==B)|flag (bool array).
static sisal_array_t it_mkf(const float *v, int n) {
  sisal_array_t a = sisal_array_alloc_empty(1, 6, n);
  a.lower_bound[0] = 1; a.dims[0] = n;
  for (int i = 0; i < n; i++) ((float *)a.data)[i] = v[i];
  return a;
}
static void test_intrinsics_test_dv() {
  printf("\n=== Group: intrinsics_test_dv (elementwise arith + select + bool array) ===\n");
  float A[] = {1, 5, 3, 2, 9, -4}, B[] = {4, 5, 1, 8, 9, -4};
  int n = 6;
  for (bool flag : {false, true}) {
    struct FUNC_ALLINTRINSICS_results r = func_ALLINTRINSICS(it_mkf(A, n), it_mkf(B, n), flag);
    int ok = (int)r.res_0.size == n && (int)r.res_1.size == n && (int)r.res_2.size == n;
    for (int i = 0; ok && i < n; i++) {
      float c = A[i] * B[i] + (A[i] - B[i]) / 2.0f;
      float d = A[i] > B[i] ? A[i] : B[i];
      bool e = (A[i] == B[i]) || flag;
      ok = std::fabs(((float *)r.res_0.data)[i] - c) < 1e-4f
        && std::fabs(((float *)r.res_1.data)[i] - d) < 1e-4f
        && (((bool *)r.res_2.data)[i] == e);
    }
    char tag[24]; snprintf(tag, sizeof tag, "flag=%d", flag);
    check(tag, ok);
  }
}
#endif
#ifdef TEST_TUPLE_HASH_TESTS_DV
// #() tuple destructuring: swap(a,b)=(b,a); typed(a,b)=(a+1,b+1);
// sum3(a,b,c) = let #(s,d)=#(a+b,a-b) in s+c = a+b+c.
static void test_tuple_hash_tests_dv() {
  printf("\n=== Group: tuple_hash_tests_dv (#() tuple destructuring) ===\n");
  int cs[][3] = {{3, 7, 2}, {10, -4, 5}, {0, 0, 0}, {-2, -8, 100}};
  for (auto &c : cs) {
    struct FUNC_TUPLE_SWAP_results s = func_TUPLE_SWAP(c[0], c[1]);
    struct FUNC_TUPLE_TYPED_results t = func_TUPLE_TYPED(c[0], c[1]);
    int u = func_TUPLE_SUM3(c[0], c[1], c[2]);
    char tag[48]; snprintf(tag, sizeof tag, "a=%d b=%d c=%d", c[0], c[1], c[2]);
    check(tag, s.res_0 == c[1] && s.res_1 == c[0]
            && t.res_0 == c[0] + 1 && t.res_1 == c[1] + 1
            && u == c[0] + c[1] + c[2]);
  }
}
#endif
#ifdef TEST_TUPLE_KW_TESTS_DV
// tuple() keyword variant: same three tests as tuple_hash via `tuple(x,y)`.
static void test_tuple_kw_tests_dv() {
  printf("\n=== Group: tuple_kw_tests_dv (tuple() keyword destructuring) ===\n");
  int cs[][3] = {{3, 7, 2}, {10, -4, 5}, {0, 0, 0}, {-2, -8, 100}};
  for (auto &c : cs) {
    struct FUNC_TUPLE_KW_SWAP_results s = func_TUPLE_KW_SWAP(c[0], c[1]);
    struct FUNC_TUPLE_KW_TYPED_results t = func_TUPLE_KW_TYPED(c[0], c[1]);
    int u = func_TUPLE_KW_CHAIN(c[0], c[1], c[2]);
    char tag[48]; snprintf(tag, sizeof tag, "a=%d b=%d c=%d", c[0], c[1], c[2]);
    check(tag, s.res_0 == c[1] && s.res_1 == c[0]
            && t.res_0 == c[0] + 1 && t.res_1 == c[1] + 1
            && u == c[0] + c[1] + c[2]);
  }
}
#endif
#ifdef TEST_BUILTIN_SCALAR_DV
// Scalar math intrinsics vs C references: abs, max, min, mod (=%), floor (->-inf),
// trunc (->0), exp (=pow, integer exponent), across int/real/double.
static void test_builtin_scalar_dv() {
  printf("\n=== Group: builtin_scalar_dv (scalar math intrinsics) ===\n");
  check("abs_int",    func_SCALAR_ABS_INT(-5)==5 && func_SCALAR_ABS_INT(7)==7);
  check("abs_real",   std::fabs(func_SCALAR_ABS_REAL(-2.5f)-2.5f)<1e-5);
  check("abs_double", std::fabs(func_SCALAR_ABS_DOUBLE(-3.5)-3.5)<1e-12);
  check("max_int",    func_SCALAR_MAX_INT(3,7)==7 && func_SCALAR_MAX_INT(-2,-9)==-2);
  check("min_int",    func_SCALAR_MIN_INT(3,7)==3 && func_SCALAR_MIN_INT(-2,-9)==-9);
  check("max_real",   std::fabs(func_SCALAR_MAX_REAL(2.5f,1.5f)-2.5f)<1e-5);
  check("min_real",   std::fabs(func_SCALAR_MIN_REAL(2.5f,1.5f)-1.5f)<1e-5);
  check("mod_int",    func_SCALAR_MOD_INT(17,5)==(17%5) && func_SCALAR_MOD_INT(-17,5)==(-17%5) && func_SCALAR_MOD_INT(17,-5)==(17%-5));
  check("floor_real", func_SCALAR_FLOOR_REAL(2.7f)==2 && func_SCALAR_FLOOR_REAL(-2.3f)==-3);
  check("floor_double", func_SCALAR_FLOOR_DOUBLE(3.9)==3 && func_SCALAR_FLOOR_DOUBLE(-3.1)==-4);
  check("trunc_real", func_SCALAR_TRUNC_REAL(2.7f)==2 && func_SCALAR_TRUNC_REAL(-2.7f)==-2);
  check("trunc_double", func_SCALAR_TRUNC_DOUBLE(3.9)==3 && func_SCALAR_TRUNC_DOUBLE(-3.9)==-3);
  check("exp_real",   std::fabs(func_SCALAR_EXP_REAL(2.0f,10)-1024.0f)<1e-2 && std::fabs(func_SCALAR_EXP_REAL(1.5f,3)-3.375f)<1e-4);
  check("exp_double", std::fabs(func_SCALAR_EXP_DOUBLE(3.0,4)-81.0)<1e-9);
}
#endif
#ifdef TEST_CPXCONV_DV
// Complex pack/unpack over array_dv of a flat record CplexReal{Repart,Impart}.
// Complexing: reals -> records (pairs); Decomplexing: records -> reals (interleave).
static sisal_array_t cc_mkreal(const float *v, int n) {
  sisal_array_t a = sisal_array_alloc_empty(1, 6, n); a.lower_bound[0]=1; a.dims[0]=n;
  for (int i = 0; i < n; i++) ((float *)a.data)[i] = v[i]; return a;
}
static sisal_array_t cc_mkrec(const cc_rec *v, int n) {
  sisal_array_t a = sisal_array_alloc_sized(1, 97, n, sizeof(cc_rec)); a.lower_bound[0]=1; a.dims[0]=n;
  for (int i = 0; i < n; i++) ((cc_rec *)a.data)[i] = v[i]; return a;
}
static void test_cpxconv_dv() {
  printf("\n=== Group: cpxconv_dv (array_dv of flat record; complex pack/unpack) ===\n");
  // Complexing jxmx=3: ct=[10..60] -> [{10,20},{30,40},{50,60}]; zt likewise.
  float ct[]={10,20,30,40,50,60}, e[]={1,2,3,4,5,6}, pt[]={-1,-2,-3,-4,-5,-6}, zt[]={7,8,9,10,11,12};
  struct FUNC_COMPLEXING_CT_E_PT_ZTSP_results c =
      func_COMPLEXING_CT_E_PT_ZTSP(3, cc_mkreal(ct,6), cc_mkreal(e,6), cc_mkreal(pt,6), cc_mkreal(zt,6));
  int cok = (int)c.res_0.size == 3;
  for (int i = 0; cok && i < 3; i++) {
    cc_rec r = ((cc_rec *)c.res_0.data)[i];
    cok = std::fabs(r.REPART-ct[2*i])<1e-4 && std::fabs(r.IMPART-ct[2*i+1])<1e-4;
  }
  cc_rec z2 = ((cc_rec *)c.res_3.data)[2];
  cok = cok && std::fabs(z2.REPART-zt[4])<1e-4 && std::fabs(z2.IMPART-zt[5])<1e-4;
  check("Complexing reals->records", cok);
  // Decomplexing jxmx=2,jxxmx=3: p=[{1,2},{3,4}]->[1,2,3,4]; u=[{7,8},{9,10},{11,12}]->[7..12]
  cc_rec p[]={{1,2},{3,4}}, zd[]={{5,6},{7,8}}, u[]={{7,8},{9,10},{11,12}}, v[]={{20,21},{22,23},{24,25}};
  struct FUNC_DECOMPLEXING_P_ZDIFF_U_V_results d =
      func_DECOMPLEXING_P_ZDIFF_U_V(2, 3, cc_mkrec(p,2), cc_mkrec(zd,2), cc_mkrec(u,3), cc_mkrec(v,3));
  float pexp[]={1,2,3,4}, uexp[]={7,8,9,10,11,12};
  int dok = (int)d.res_0.size == 4 && (int)d.res_2.size == 6;
  for (int i = 0; dok && i < 4; i++) dok = std::fabs(((float*)d.res_0.data)[i]-pexp[i])<1e-4;
  for (int i = 0; dok && i < 6; i++) dok = std::fabs(((float*)d.res_2.data)[i]-uexp[i])<1e-4;
  check("Decomplexing records->reals", dok);
}
#endif
#ifdef TEST_INTERPROC_PROVIDED_E2E
// DPS / provided-variant guard: an array-returning helper called every loop
// iteration as the carry, each step's output depending on the WHOLE previous
// array (Step(A)[i] = A[i] + sum(A)).  Value semantics are load-bearing — an
// in-place reuse of the carry buffer that overwrites while reading corrupts
// the compounding recurrence.  Reference = C mirror.
static void test_interproc_provided_e2e() {
  printf("\n=== Group: interproc_provided_e2e (DPS provided-variant recurrence) ===\n");
  auto run = [](int N, int Steps) {
    long V[64]; for (int i = 0; i < N; i++) V[i] = i + 1;
    for (int s = 0; s < Steps; s++) {
      long t = 0; for (int i = 0; i < N; i++) t += V[i];
      for (int i = 0; i < N; i++) V[i] += t;
    }
    sisal_array_t r = func_MAIN(N, Steps);
    int ok = (int)r.size == N;
    for (int i = 0; ok && i < N; i++) ok = ((int32_t*)r.data)[i] == (int32_t)V[i];
    return ok;
  };
  check("N=4 Steps=3 recurrence", run(4, 3));
  check("N=1 Steps=5 (single element)", run(1, 5));
  check("N=6 Steps=0 (seed only, INIT provided path)", run(6, 0));
  check("N=5 Steps=4 (compounded)", run(5, 4));
}
#endif
#ifdef TEST_STREAM_SIMPLE_DV
static void test_stream_simple_dv() {
  printf("\n=== Group: stream_simple_dv ===\n");
  std::vector<float> got;
  for (sisal_generator<float> r = func_MAIN(); !sisal_stream_empty_pred(r);
       r = sisal_stream_rest(r))
    got.push_back(sisal_stream_first<float>(r));
  check("size is 2", got.size() == 2);
  check("element 0 is 1.2", got.size() > 0 && fabs(got[0] - 1.2f) < 1e-5);
  check("element 1 is 3.2", got.size() > 1 && fabs(got[1] - 3.2f) < 1e-5);
}
#endif
#ifdef TEST_STREAM_LOOP_DV
static void test_stream_loop_dv() {
  printf("\n=== Group: stream_loop_dv ===\n");
  std::vector<int32_t> got;
  for (sisal_generator<int32_t> r = func_MAIN(5); !sisal_stream_empty_pred(r);
       r = sisal_stream_rest(r))
    got.push_back(sisal_stream_first<int32_t>(r));
  check("size is 5", (int)got.size() == 5);
  for (int i = 0; i < (int)got.size() && i < 5; i++) {
    char label[64];
    snprintf(label, sizeof(label), "element %d is %d", i, i + 1);
    check(label, got[i] == i + 1);
  }
}
#endif
#ifdef TEST_STREAM_SIEVE_DV
static void test_stream_sieve_dv() {
  printf("\n=== Group: stream_sieve_dv ===\n");
  std::vector<int32_t> got;
  for (sisal_generator<int32_t> r = func_MAIN(20); !sisal_stream_empty_pred(r);
       r = sisal_stream_rest(r))
    got.push_back(sisal_stream_first<int32_t>(r));
  check("size is 8", (int)got.size() == 8);
  int32_t expected[] = {2, 3, 5, 7, 11, 13, 17, 19};
  for (int i = 0; i < (int)got.size() && i < 8; i++) {
    char label[64];
    snprintf(label, sizeof(label), "prime %d is %d", i, expected[i]);
    check(label, got[i] == expected[i]);
  }
}
#endif
#ifdef TEST_STREAM_INTEGERS_DV
static void test_stream_integers_dv() {
  printf("\n=== Group: stream_integers_dv ===\n");
  // Reference model of Sisal `for initial ... returns stream of I`
  // (docs/loop_behavior_comparison.md): seed always gathered (Rule 1), then
  // each body-computed I gathered incl. the final out-of-bounds one (Rule 2).
  auto run = [](int32_t Limit) {
    int32_t ref[256];
    int n = 0;
    int32_t I = 3;
    ref[n++] = I;                 // Rule 1: initial seed
    while (I < Limit - 1) {
      I = I + 2;                  // body: old I + 2
      ref[n++] = I;               // Rule 2: gather body value (incl. out-of-bounds)
    }
    std::vector<int32_t> got;
    for (sisal_generator<int32_t> r = func_MAIN(Limit);
         !sisal_stream_empty_pred(r); r = sisal_stream_rest(r))
      got.push_back(sisal_stream_first<int32_t>(r));
    char label[96];
    snprintf(label, sizeof(label), "Limit=%d size is %d", Limit, n);
    check(label, (int)got.size() == n);
    for (int i = 0; i < n && i < (int)got.size(); i++) {
      snprintf(label, sizeof(label), "Limit=%d element %d is %d", Limit, i,
               ref[i]);
      check(label, got[i] == ref[i]);
    }
  };
  run(30);  // normal: 3 5 7 ... 27 29
  run(15);  // normal: 3 5 7 9 11 13 15
  run(4);   // zero-trip (I:=3, 3<3 false): just the seed [3]
}
#endif
#ifdef TEST_STREAM_SIEVE_V2_DV
static void test_stream_sieve_v2_dv() {
  printf("\n=== Group: stream_sieve_v2_dv ===\n");
  // Reference: the forall generator emits odd candidates 3,5,...,maxcand with
  // maxcand = 3 + 2*((Limit-3)/2) <= Limit, plus the seed 2.  Since every
  // composite candidate has a factor <= sqrt(Limit)=Maxt, the sieve is exact,
  // so the output is precisely the primes in [2, maxcand] (trial division).
  auto run = [](int32_t Limit) {
    int32_t maxcand = 3 + 2 * ((Limit - 3) / 2);
    int32_t ref[512];
    int n = 0;
    for (int32_t p = 2; p <= maxcand; p++) {
      bool prime = true;
      for (int32_t d = 2; (int64_t)d * d <= p; d++)
        if (p % d == 0) { prime = false; break; }
      if (prime) ref[n++] = p;
    }
    std::vector<int32_t> got;
    for (sisal_generator<int32_t> r = func_MAIN(Limit);
         !sisal_stream_empty_pred(r); r = sisal_stream_rest(r))
      got.push_back(sisal_stream_first<int32_t>(r));
    char label[96];
    snprintf(label, sizeof(label), "Limit=%d size is %d", Limit, n);
    check(label, (int)got.size() == n);
    for (int i = 0; i < n && i < (int)got.size(); i++) {
      snprintf(label, sizeof(label), "Limit=%d prime %d is %d", Limit, i,
               ref[i]);
      check(label, got[i] == ref[i]);
    }
  };
  run(10);  // 2 3 5 7
  run(30);  // 2 3 5 7 11 13 17 19 23 29
  run(50);  // 2 3 5 7 ... 43 47
}
#endif
#ifdef TEST_STREAM_UPRIME2_DV
static void test_stream_uprime2_dv() {
  printf("\n=== Group: stream_uprime2_dv ===\n");
  // Infinite-Integers sieve.  Reference = the ACTUAL sieve, not primality:
  // seed 2, then successive odd survivors while T < Limit, plus the first
  // survivor >= Limit (Rule 2 overshoot).  A survivor is an odd q with no
  // factor in [2, Maxt] below itself (Maxt = floor(sqrt(Limit))); that
  // overshoot survivor may be COMPOSITE (e.g. Limit=48 -> ...47 49).
  auto run = [](int32_t Limit) {
    int32_t Maxt = (int32_t)sqrt((double)Limit);
    int32_t ref[512];
    int n = 0;
    ref[n++] = 2;
    for (int32_t q = 3;; q += 2) {
      bool surv = true;
      for (int32_t d = 2; d <= Maxt && d < q; d++)
        if (q % d == 0) { surv = false; break; }
      if (surv) {
        ref[n++] = q;
        if (q >= Limit) break;
      }
    }
    std::vector<int32_t> got;
    for (sisal_generator<int32_t> r = func_MAIN(Limit);
         !sisal_stream_empty_pred(r); r = sisal_stream_rest(r))
      got.push_back(sisal_stream_first<int32_t>(r));
    char label[96];
    snprintf(label, sizeof(label), "Limit=%d size is %d", Limit, n);
    check(label, (int)got.size() == n);
    for (int i = 0; i < n && i < (int)got.size(); i++) {
      snprintf(label, sizeof(label), "Limit=%d element %d is %d", Limit, i,
               ref[i]);
      check(label, got[i] == ref[i]);
    }
  };
  run(20);  // 2 3 5 7 11 13 17 19 23
  run(30);  // 2 3 5 7 11 13 17 19 23 29 31
  run(48);  // 2 3 5 7 ... 47 49  (49 = 7*7 is a COMPOSITE overshoot)
}
#endif

#ifdef TEST_FORALL_INTERPROC_E2E
extern "C" sisal_array_t func_MAIN(int32_t N);
static void test_forall_interproc_e2e() {
  printf("\n=== Group: forall_interproc_e2e (Forall interprocedural DPS provided-variant) ===\n");
  auto run = [](int N) {
    sisal_array_t r = func_MAIN(N);
    int ok = (int)r.size == N;
    for (int i = 0; ok && i < N; i++) {
      double expected = (double)(i + 1) * (double)(N * (N + 1) / 2);
      double actual = ((double*)r.data)[i];
      ok = fabs(actual - expected) < 1e-6;
    }
    return ok;
  };
  check("N=4 forall interprocedural provided", run(4));
  check("N=10 forall interprocedural provided", run(10));
}
#endif

#ifdef TEST_FORALL_2D_INTERPROC_E2E
extern "C" sisal_array_t func_MAIN(int32_t Rows, int32_t Cols);
static void test_forall_2d_interproc_e2e() {
  printf("\n=== Group: forall_2d_interproc_e2e (2D Forall stencil row-builder provided-variant) ===\n");
  auto run = [](int Rows, int Cols) {
    sisal_array_t r = func_MAIN(Rows, Cols);
    int ok = (int)r.size == Rows;
    for (int i = 0; ok && i < Rows; i++) {
      float row_sum = 0.0f;
      for (int j = 1; j <= Cols; j++) row_sum += (float)((i + 1) * 10 + j);
      float actual = ((float*)r.data)[i];
      ok = fabsf(actual - row_sum) < 1e-5f;
    }
    return ok;
  };
  check("Rows=3 Cols=4 forall 2D provided", run(3, 4));
  check("Rows=5 Cols=5 forall 2D provided", run(5, 5));
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
#ifdef TEST_BASIC_DV
  test_basic_dv ();
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
#ifdef TEST_MULTIBIND_DV
  test_multibind_dv ();
#endif
#ifdef TEST_TAG_DISPATCH_DV
  test_tag_dispatch_dv ();
#endif
#ifdef TEST_SIMPSON
  test_simpson ();
#endif
#ifdef TEST_MINMAX_DV
  test_minmax_dv ();
#endif
#ifdef TEST_INSERTION1_DV
  test_insertion1_dv ();
#endif
#ifdef TEST_MESORT_DV
  test_mesort_dv ();
#endif
#ifdef TEST_FOR_ALL_ARGMAX
  test_for_all_argmax ();
#endif
#ifdef TEST_TUPLE_MIXED3
  test_tuple_mixed3 ();
#endif
#ifdef TEST_RECORD1
  test_record1 ();
#endif
#ifdef TEST_UNION1
  test_union1 ();
#endif
#ifdef TEST_TUPLE_MIXED2
  test_tuple_mixed2 ();
#endif
#ifdef TEST_UNION0
  test_union0 ();
#endif
#ifdef TEST_TUPLE_ADD_DV
  test_tuple_add_dv ();
#endif
#ifdef TEST_IDIV
  test_idiv ();
#endif
#ifdef TEST_FORALL_SIMPLE_DV
  test_forall_simple_dv ();
#endif
#ifdef TEST_FORALL_DOT_DV
  test_forall_dot_dv ();
#endif
#ifdef TEST_TUPLE_MIXED
  test_tuple_mixed ();
#endif
#ifdef TEST_RECORD2
  test_record2 ();
#endif
#ifdef TEST_RECORD1_REORDER
  test_record1_reorder ();
#endif
#ifdef TEST_RECORD_REPLACE_E2E
  test_record_replace_e2e ();
#endif
#ifdef TEST_PARPI1
  test_parpi1 ();
#endif
#ifdef TEST_FORALL_CROSS_DV
  test_forall_cross_dv ();
#endif
#ifdef TEST_FORALL_SHAPED_GATHER_DV
  test_forall_shaped_gather_dv ();
#endif
#ifdef TEST_FOR_INITIAL_SIMPLE
  test_for_initial_simple ();
#endif
#ifdef TEST_PARPI2
  test_parpi2 ();
#endif
#ifdef TEST_PARPI_BABB
  test_parpi_babb ();
#endif
#ifdef TEST_FOR_INITIAL_LOOPA
  test_for_initial_loopa ();
#endif
#ifdef TEST_LOOPAT2_DV
  test_loopat2_dv ();
#endif
#ifdef TEST_TST_LOOP2_DV
  test_tst_loop2_dv ();
#endif
#ifdef TEST_FOR_ALL_REDUCE
  test_for_all_reduce ();
#endif
#ifdef TEST_SIMPLEBATCHER_DV
  test_simplebatcher_dv ();
#endif
#ifdef TEST_SEQBATCHER_DV
  test_seqbatcher_dv ();
#endif
#ifdef TEST_BATCHER_DV
  test_batcher_dv ();
#endif
#ifdef TEST_ANGMOM_DV
  test_angmom_dv ();
#endif
#ifdef TEST_VSPHERE_DV
  test_vsphere_dv ();
#endif
#ifdef TEST_ENERGY_DV
  test_energy_dv ();
#endif
#ifdef TEST_SPECAM_DV
  test_specam_dv ();
#endif
#ifdef TEST_SAS_DV
  test_sas_dv ();
#endif
#ifdef TEST_LINEAR_DV
  test_linear_dv ();
#endif
#ifdef TEST_UVSPEC_DV
  test_uvspec_dv ();
#endif
#ifdef TEST_SPEC_DV
  test_spec_dv ();
#endif
#ifdef TEST_NOISE_DV
  test_noise_dv ();
#endif
#ifdef TEST_TST_LOOPX_DV
  test_tst_loopx_dv ();
#endif
#ifdef TEST_TST_LOOPX2_DV
  test_tst_loopx2_dv ();
#endif
#ifdef TEST_INSERTION2_DV
  test_insertion2_dv ();
#endif
#ifdef TEST_INSERT_DV
  test_insert_dv ();
#endif
#ifdef TEST_TST_LOOPAT1_DV
  test_tst_loopat1_dv ();
#endif
#ifdef TEST_TUPLE_DESTRUCTURE
  test_tuple_destructure ();
#endif
#ifdef TEST_SIFUNCS
  test_sifuncs ();
#endif
#ifdef TEST_ADA
  test_ada ();
#endif
#ifdef TEST_TSTEP_DV
  test_tstep_dv ();
#endif
#ifdef TEST_FREQ_DV
  test_freq_dv ();
#endif
#ifdef TEST_COMPLEX_TYPES_E2E
  test_complex_types_e2e ();
#endif
#ifdef TEST_VERIFY_NUMPY_BROADCAST
  test_verify_numpy_broadcast ();
#endif
#ifdef TEST_PINSERT_DV
  test_pinsert_dv ();
#endif
#ifdef TEST_ALPHABETA_DV
  test_alphabeta_dv ();
#endif
#ifdef TEST_LIFE2_DV
  test_life2_dv ();
#endif
#ifdef TEST_RICARD_DV
  test_ricard_dv ();
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
#ifdef TEST_ARRAY_ADD_DV
  test_array_add_dv ();
#endif
#ifdef TEST_PICK_DV
  test_pick_dv ();
#endif
#ifdef TEST_ZERO_ARRAYS
  test_zero_arrays ();
#endif
#ifdef TEST_CPXFUNCS_DV
  test_cpxfuncs_dv ();
#endif
#ifdef TEST_XFA_B4_REDUCE
  test_xfa_b4_reduce ();
#endif
#ifdef TEST_XFA_C4_DEP2
  test_xfa_c4_dep2 ();
#endif
#ifdef TEST_XFA_C5_DEP3
  test_xfa_c5_dep3 ();
#endif
#ifdef TEST_FORALL_GPU_DV
  test_forall_gpu ();
#endif
#ifdef TEST_MIX_ARRAY_DV_IF
  test_mix_array_dv_if ();
#endif
#ifdef TEST_QUEENS_DV
  test_8queens_dv ();
#endif
#ifdef TEST_GAUSSJ_PERM_DV
  test_gaussj_perm_dv ();
#endif
#ifdef TEST_FORINIT_HISTORY_DV
  test_forinit_history_dv ();
#endif
#ifdef TEST_MATMULT_DV
  test_matmult_dv ();
#endif
#ifdef TEST_MM_DV
  test_mm_dv ();
#endif
#ifdef TEST_TRANSPOSE_DV
  test_transpose_dv ();
#endif
#ifdef TEST_SP_DV
  test_sp_dv ();
#endif
#ifdef TEST_INVERSE_DV
  test_inverse_dv ();
#endif
#ifdef TEST_BADFFT_DV
  test_badfft_dv ();
#endif
#ifdef TEST_FLOAT_SCATTER_DV
  test_float_scatter_dv ();
#endif
#ifdef TEST_SUB_R3_PERM
  test_sub_r3_perm ();
#endif
#ifdef TEST_SUB_R4_PERM
  test_sub_r4_perm ();
#endif
#ifdef TEST_SUB_R5_PERM
  test_sub_r5_perm ();
#endif
#ifdef TEST_IF_ARRAY_DV
  test_if_array_dv ();
#endif
#ifdef TEST_MIX_SCALAR_ARRAY_DV
  test_mix_scalar_array_dv ();
#endif
#ifdef TEST_IF_MULTI_ARRAY_DV
  test_if_multi_array_dv ();
#endif
#ifdef TEST_MULTI_ARRAY_IF_DV
  test_multi_array_if_dv ();
#endif
#ifdef TEST_UNION_ARRAY_IF_DV
  test_union_array_if_dv ();
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
#ifdef TEST_BUBBLE_E2E
  test_bubble_e2e ();
#endif
#ifdef TEST_LEGPOLY_DV_E2E
  test_legpoly_dv_e2e ();
#endif
#ifdef TEST_NESTED_INIT_MERGE_DV
  test_nested_init_merge_dv ();
#endif
#ifdef TEST_MUTUAL_BUG_E2E
  test_mutual_bug_e2e ();
#endif
#ifdef TEST_LU_NPIV_DV
  test_lu_npiv_dv ();
#endif
#ifdef TEST_LU_PIV_DV
  test_lu_piv_dv ();
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
#ifdef TEST_KIN16_DV
  test_kin16_dv ();
#endif
#ifdef TEST_CFFT_DV
  test_cfft_dv ();
#endif
#ifdef TEST_HILBERT_DV
  test_hilbert_dv ();
#endif
#ifdef TEST_ARRAY_SWAP_E2E
  test_array_swap_e2e ();
#endif
#ifdef TEST_QUICKSORT_DV
  test_quicksort_dv ();
#endif
#ifdef TEST_HEAPSORT_DV
  test_heapsort_dv ();
#endif
#ifdef TEST_NESTED_CAPTURE_DV
  test_nested_capture_dv ();
#endif
#ifdef TEST_STREAM_GURD_DV
  test_stream_gurd_dv ();
#endif
#ifdef TEST_TEST_IF_NESTED_CAPTURE_DV
  test_test_if_nested_capture_dv ();
#endif
#ifdef TEST_TEST_IF_LET_CASCADE_DV
  test_test_if_let_cascade_dv ();
#endif
#ifdef TEST_TAGCASE_BARE_DV
  test_tagcase_bare_dv ();
#endif
#ifdef TEST_TAGCASE_BARE_MIXED_DV
  test_tagcase_bare_mixed_dv ();
#endif
#ifdef TEST_TAGCASE_BARE_NESTED_DV
  test_tagcase_bare_nested_dv ();
#endif
#ifdef TEST_CRYPTO_DV
  test_crypto_dv ();
#endif
#ifdef TEST_SQRT_DV
  test_sqrt_dv ();
#endif
#ifdef TEST_REC_FIELD_DV
  test_rec_field_dv ();
#endif
#ifdef TEST_REC_AOS_DV
  test_rec_aos_dv ();
#endif
#ifdef TEST_REC_SOA_DV
  test_rec_soa_dv ();
#endif
#ifdef TEST_RESHAPE_DV
  test_reshape_dv ();
#endif
#ifdef TEST_SOA_INIT_DV
  test_soa_init_dv ();
#endif
#ifdef TEST_NUCLEIC_SOA_DV
  test_nucleic_soa_dv ();
#endif
#ifdef TEST_NUCLEIC_MAKET_DV
  test_nucleic_maket_dv ();
#endif
#ifdef TEST_NUCLEIC_DGFBASE_DV
  test_nucleic_dgfbase_dv ();
#endif
#ifdef TEST_NUCLEIC_GETVAR_DV
  test_nucleic_getvar_dv ();
#endif
#ifdef TEST_MEMBER_DV
  test_member_dv ();
#endif
#ifdef TEST_ML_LIST_DV
  test_ml_list_dv ();
#endif
#ifdef TEST_NUCLEIC_SEARCH_DV
  test_nucleic_search_dv ();
#endif
#ifdef TEST_ML_LIST_REPLACE_DV
  test_ml_list_replace_dv ();
#endif
#ifdef TEST_NUCLEIC_KERNELS_DV
  test_nucleic_kernels_dv ();
#endif
#ifdef TEST_NUCLEIC_BUILDERS_DV
  test_nucleic_builders_dv ();
#endif
#ifdef TEST_NUCLEIC_BASES_DV
  test_nucleic_bases_dv ();
#endif
#ifdef TEST_NUCLEIC_DV
  test_nucleic_dv ();
#endif
#ifdef TEST_BINTREE_DV
  test_bintree_dv ();
#endif
#ifdef TEST_PARA_DEARRAY_DV
  test_para_dearray_dv ();
#endif
#ifdef TEST_LIST_ITER_DV
  test_list_iter_dv ();
#endif
#ifdef TEST_FORINIT_REDUCE_DV
  test_forinit_reduce_dv ();
#endif
#ifdef TEST_WORDCOUNT_DV
  test_wordcount_dv ();
#endif
#ifdef TEST_BACKTRACK_DV
  test_backtrack_dv ();
#endif
#ifdef TEST_SUCCESSOR_DV
  test_successor_dv ();
#endif
#ifdef TEST_GENLINKS_DV
  test_genlinks_dv ();
#endif
#ifdef TEST_GENARCS_DV
  test_genarcs_dv ();
#endif
#ifdef TEST_TRACEUTIL_DV
  test_traceutil_dv ();
#endif
#ifdef TEST_ARCGRID_DV
  test_arcgrid_dv ();
#endif
#ifdef TEST_TRACE_DV
  test_trace_dv ();
#endif
#ifdef TEST_JOB_DV
  test_job_dv ();
#endif
#ifdef TEST_MOLDYN_FORCE_DV
  test_moldyn_force_dv ();
#endif
#ifdef TEST_MOLDYN_DIFFUN_DV
  test_moldyn_diffun_dv ();
#endif
#ifdef TEST_MOLDYN_RK_DV
  test_moldyn_rk_dv ();
#endif
#ifdef TEST_MOLDYN_RKF45_DV
  test_moldyn_rkf45_dv ();
#endif
#ifdef TEST_MOLDYN_SOLVE_DV
  test_moldyn_solve_dv ();
#endif
#ifdef TEST_MOLDYN_DV
  test_moldyn_dv ();
#endif
#ifdef TEST_GATHER_CONFORM_DV
  test_gather_conform_dv ();
#endif
#ifdef TEST_ADDH_ROW_DV
  test_addh_row_dv ();
#endif
#ifdef TEST_FORINIT_GATHER_GROWTH_DV
  test_forinit_gather_growth_dv ();
#endif
#ifdef TEST_PSA_RNG_DV
  test_psa_rng_dv ();
#endif
#ifdef TEST_XFA_DEP_EXPR
  test_xfa_dep_expr ();
#endif
#ifdef TEST_PSA_SWAP_DV
  test_psa_swap_dv ();
#endif
#ifdef TEST_PSA_UPDATE_DV
  test_psa_update_dv ();
#endif
#ifdef TEST_PSA_DV
  test_psa_dv ();
#endif
#ifdef TEST_FORINIT_CATENATE_DV
  test_forinit_catenate_dv ();
#endif
#ifdef TEST_PSA_COST_DV
  test_psa_cost_dv ();
#endif
#ifdef TEST_MOLDYN_NEIGHBORS_DV
  test_moldyn_neighbors_dv ();
#endif
#ifdef TEST_MOLDYN_NBRLIST_DV
  test_moldyn_nbrlist_dv ();
#endif
#ifdef TEST_ZEROTRIP_EXPR_DV
  test_zerotrip_expr_dv ();
#endif
#ifdef TEST_FORINIT_MASK_DV
  test_forinit_mask_dv ();
#endif
#ifdef TEST_ARRAY_EX_DV
  test_array_ex_dv ();
#endif
#ifdef TEST_NICO_DV
  test_nico_dv ();
#endif
#ifdef TEST_NICO2_DV
  test_nico2_dv ();
#endif
#ifdef TEST_TEST_BIN_DV
  test_test_bin_dv ();
#endif
#ifdef TEST_IF_COMPLEX_REVIEW_DV
  test_if_complex_review_dv ();
#endif
#ifdef TEST_TAGCASE_II_DV
  test_tagcase_ii_dv ();
#endif
#ifdef TEST_NESTED_DV
  test_nested_dv ();
#endif
#ifdef TEST_VECTEST_DV
  test_vectest_dv ();
#endif
#ifdef TEST_LEGPOLY1_DV
  test_legpoly1_dv ();
#endif
#ifdef TEST_INTRINSICS_TEST_DV
  test_intrinsics_test_dv ();
#endif
#ifdef TEST_TUPLE_HASH_TESTS_DV
  test_tuple_hash_tests_dv ();
#endif
#ifdef TEST_TUPLE_KW_TESTS_DV
  test_tuple_kw_tests_dv ();
#endif
#ifdef TEST_BUILTIN_SCALAR_DV
  test_builtin_scalar_dv ();
#endif
#ifdef TEST_CPXCONV_DV
  test_cpxconv_dv ();
#endif
#ifdef TEST_INTERPROC_PROVIDED_E2E
  test_interproc_provided_e2e ();
#endif
#ifdef TEST_STREAM_SIMPLE_DV
  test_stream_simple_dv ();
#endif
#ifdef TEST_STREAM_LOOP_DV
  test_stream_loop_dv ();
#endif
#ifdef TEST_STREAM_SIEVE_DV
  test_stream_sieve_dv ();
#endif
#ifdef TEST_STREAM_INTEGERS_DV
  test_stream_integers_dv ();
#endif
#ifdef TEST_STREAM_SIEVE_V2_DV
  test_stream_sieve_v2_dv ();
#endif
#ifdef TEST_STREAM_UPRIME2_DV
  test_stream_uprime2_dv ();
#endif
#ifdef TEST_FORALL_INTERPROC_E2E
  test_forall_interproc_e2e ();
#endif
#ifdef TEST_FORALL_2D_INTERPROC_E2E
  test_forall_2d_interproc_e2e ();
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
    && !defined(TEST_RICARD_DV) && !defined(TEST_MULTIBIND_DV) && !defined(TEST_TAG_DISPATCH_DV) \
    && !defined(TEST_SIMPSON) && !defined(TEST_MINMAX_DV) && !defined(TEST_INSERTION1_DV) && !defined(TEST_MESORT_DV) && !defined(TEST_LIFE2_DV) \
    && !defined(TEST_FOR_ALL_ARGMAX) && !defined(TEST_TUPLE_MIXED3) && !defined(TEST_RECORD1) && !defined(TEST_UNION1) \
    && !defined(TEST_TUPLE_MIXED2) && !defined(TEST_UNION0) && !defined(TEST_TUPLE_ADD_DV) && !defined(TEST_IDIV) \
    && !defined(TEST_FORALL_SIMPLE_DV) && !defined(TEST_FORALL_DOT_DV) \
    && !defined(TEST_TUPLE_MIXED) && !defined(TEST_RECORD2) && !defined(TEST_RECORD1_REORDER) && !defined(TEST_RECORD_REPLACE_E2E) && !defined(TEST_PARPI1) && !defined(TEST_FORALL_CROSS_DV) && !defined(TEST_FORALL_SHAPED_GATHER_DV) && !defined(TEST_FOR_INITIAL_SIMPLE) \
    && !defined(TEST_PARPI2) && !defined(TEST_PARPI_BABB) && !defined(TEST_FOR_INITIAL_LOOPA) && !defined(TEST_LOOPAT2_DV) && !defined(TEST_TST_LOOP2_DV) && !defined(TEST_FOR_ALL_REDUCE) && !defined(TEST_SIMPLEBATCHER_DV) && !defined(TEST_SEQBATCHER_DV) && !defined(TEST_BATCHER_DV) && !defined(TEST_ANGMOM_DV) && !defined(TEST_VSPHERE_DV) && !defined(TEST_ENERGY_DV) && !defined(TEST_SPECAM_DV) && !defined(TEST_SAS_DV) && !defined(TEST_LINEAR_DV) && !defined(TEST_UVSPEC_DV) && !defined(TEST_SPEC_DV) && !defined(TEST_NOISE_DV) && !defined(TEST_TST_LOOPX_DV) && !defined(TEST_TST_LOOPX2_DV) && !defined(TEST_INSERTION2_DV) && !defined(TEST_INSERT_DV) && !defined(TEST_TST_LOOPAT1_DV) && !defined(TEST_TUPLE_DESTRUCTURE) && !defined(TEST_SIFUNCS) && !defined(TEST_ADA) && !defined(TEST_PINSERT_DV) && !defined(TEST_ALPHABETA_DV) && !defined(TEST_TSTEP_DV) && !defined(TEST_FREQ_DV) && !defined(TEST_COMPLEX_TYPES_E2E) && !defined(TEST_VERIFY_NUMPY_BROADCAST)                \
    && !defined(TEST_SHAPED_GATHER_DV) && !defined(TEST_FORINIT_MAT_GATHER_DV) \
    && !defined(TEST_SCATTER_AT_DV) && !defined(TEST_GROW_NEST_DV)            \
    && !defined(TEST_TRANSPOSE_AT_DV) && !defined(TEST_FORALL_ROWSCATTER_DV)  \
    && !defined(TEST_SMOOTH_DV) && !defined(TEST_DFT_DV)                      \
    && !defined(TEST_RECORD_OPS_DV) && !defined(TEST_ARRAY_ADD_DV)\
    && !defined(TEST_ZERO_ARRAYS) && !defined(TEST_CPXFUNCS_DV)\
    && !defined(TEST_XFA_B4_REDUCE)\
    && !defined(TEST_XFA_C4_DEP2) && !defined(TEST_XFA_C5_DEP3)\
    && !defined(TEST_FORALL_GPU_DV) && !defined(TEST_MIX_ARRAY_DV_IF)\
    && !defined(TEST_QUEENS_DV) && !defined(TEST_GAUSSJ_PERM_DV)\
    && !defined(TEST_FORINIT_HISTORY_DV)\
    && !defined(TEST_MATMULT_DV) && !defined(TEST_MM_DV)\
    && !defined(TEST_TRANSPOSE_DV) && !defined(TEST_SP_DV)\
    && !defined(TEST_INVERSE_DV) && !defined(TEST_BADFFT_DV)\
    && !defined(TEST_FLOAT_SCATTER_DV)\
    && !defined(TEST_SUB_R3_PERM) && !defined(TEST_SUB_R4_PERM)\
    && !defined(TEST_SUB_R5_PERM) && !defined(TEST_IF_ARRAY_DV)\
    && !defined(TEST_MIX_SCALAR_ARRAY_DV) && !defined(TEST_IF_MULTI_ARRAY_DV)\
    && !defined(TEST_MULTI_ARRAY_IF_DV) && !defined(TEST_UNION_ARRAY_IF_DV)\
    && !defined(TEST_PICK_DV)                                           \
    && !defined(TEST_RECORD_E2E)                                              \
    && !defined(TEST_TAGCASE_E2E)                                              \
    && !defined(TEST_COMPLEX_FEATURES_E2E)                                    \
    && !defined(TEST_COMPLEX_OPS_E2E)                                         \
    && !defined(TEST_BUBBLE_E2E)                                              \
    && !defined(TEST_LEGPOLY_DV_E2E)                                          \
    && !defined(TEST_NESTED_INIT_MERGE_DV)                                    \
    && !defined(TEST_MUTUAL_BUG_E2E)                                          \
    && !defined(TEST_LU_NPIV_DV)                                              \
    && !defined(TEST_LU_PIV_DV)                                               \
    && !defined(TEST_RANK8_SLICES)                                            \
    && !defined(TEST_NEWTON_RAPHSON)                                          \
    && !defined(TEST_FEO_FFT_PARTS1) && !defined(TEST_FEO_FFT_PARTS2)         \
    && !defined(TEST_FEO_FFT_PARTS3) && !defined(TEST_FEO_FFT_PARTS4)         \
    && !defined(TEST_FEO_FFT_DV) && !defined(TEST_FEO_FFT) && !defined(TEST_KIN16_DV) && !defined(TEST_BASIC_DV) && !defined(TEST_CFFT_DV) && !defined(TEST_HILBERT_DV) && !defined(TEST_ARRAY_SWAP_E2E) && !defined(TEST_QUICKSORT_DV) && !defined(TEST_HEAPSORT_DV) && !defined(TEST_NESTED_CAPTURE_DV) && !defined(TEST_INTERPROC_PROVIDED_E2E) && !defined(TEST_FORALL_INTERPROC_E2E) && !defined(TEST_FORALL_2D_INTERPROC_E2E) && !defined(TEST_STREAM_SIMPLE_DV) && !defined(TEST_STREAM_LOOP_DV) && !defined(TEST_STREAM_SIEVE_DV) && !defined(TEST_STREAM_INTEGERS_DV) && !defined(TEST_STREAM_SIEVE_V2_DV) && !defined(TEST_STREAM_UPRIME2_DV) && !defined(TEST_STREAM_GURD_DV) && !defined(TEST_TEST_IF_NESTED_CAPTURE_DV) && !defined(TEST_TEST_IF_LET_CASCADE_DV) && !defined(TEST_TAGCASE_BARE_DV) && !defined(TEST_TAGCASE_BARE_MIXED_DV) && !defined(TEST_TAGCASE_BARE_NESTED_DV) && !defined(TEST_CRYPTO_DV) && !defined(TEST_SQRT_DV) && !defined(TEST_ARRAY_EX_DV) && !defined(TEST_NICO_DV) && !defined(TEST_NICO2_DV) && !defined(TEST_TEST_BIN_DV) && !defined(TEST_IF_COMPLEX_REVIEW_DV) && !defined(TEST_TAGCASE_II_DV) && !defined(TEST_NESTED_DV) && !defined(TEST_VECTEST_DV) && !defined(TEST_LEGPOLY1_DV) && !defined(TEST_INTRINSICS_TEST_DV) && !defined(TEST_TUPLE_HASH_TESTS_DV) && !defined(TEST_TUPLE_KW_TESTS_DV) && !defined(TEST_BUILTIN_SCALAR_DV) && !defined(TEST_CPXCONV_DV) && !defined(TEST_REC_FIELD_DV) && !defined(TEST_REC_AOS_DV) && !defined(TEST_REC_SOA_DV) && !defined(TEST_RESHAPE_DV) && !defined(TEST_SOA_INIT_DV) && !defined(TEST_NUCLEIC_SOA_DV) && !defined(TEST_NUCLEIC_MAKET_DV) && !defined(TEST_NUCLEIC_DGFBASE_DV) && !defined(TEST_NUCLEIC_GETVAR_DV) && !defined(TEST_MEMBER_DV) && !defined(TEST_ML_LIST_DV) && !defined(TEST_NUCLEIC_SEARCH_DV) && !defined(TEST_ML_LIST_REPLACE_DV) && !defined(TEST_NUCLEIC_KERNELS_DV) && !defined(TEST_NUCLEIC_BUILDERS_DV) && !defined(TEST_NUCLEIC_BASES_DV) && !defined(TEST_NUCLEIC_DV) && !defined(TEST_BINTREE_DV) && !defined(TEST_PARA_DEARRAY_DV) && !defined(TEST_LIST_ITER_DV) && !defined(TEST_FORINIT_REDUCE_DV) && !defined(TEST_WORDCOUNT_DV) && !defined(TEST_BACKTRACK_DV) && !defined(TEST_SUCCESSOR_DV) && !defined(TEST_GENLINKS_DV) && !defined(TEST_GENARCS_DV) && !defined(TEST_TRACEUTIL_DV) && !defined(TEST_ARCGRID_DV) && !defined(TEST_TRACE_DV) && !defined(TEST_JOB_DV) && !defined(TEST_MOLDYN_FORCE_DV) && !defined(TEST_MOLDYN_DIFFUN_DV) && !defined(TEST_MOLDYN_RK_DV) && !defined(TEST_MOLDYN_RKF45_DV) && !defined(TEST_MOLDYN_SOLVE_DV) && !defined(TEST_MOLDYN_DV) && !defined(TEST_GATHER_CONFORM_DV) && !defined(TEST_MOLDYN_NEIGHBORS_DV) && !defined(TEST_MOLDYN_NBRLIST_DV) && !defined(TEST_ZEROTRIP_EXPR_DV) && !defined(TEST_FORINIT_MASK_DV) && !defined(TEST_ADDH_ROW_DV) && !defined(TEST_FORINIT_GATHER_GROWTH_DV) && !defined(TEST_PSA_RNG_DV) && !defined(TEST_XFA_DEP_EXPR) && !defined(TEST_PSA_SWAP_DV) && !defined(TEST_PSA_UPDATE_DV) && !defined(TEST_PSA_DV) && !defined(TEST_FORINIT_CATENATE_DV) && !defined(TEST_PSA_COST_DV)
  printf ("ERROR: No TEST_XXX macro defined.  Compile with e.g. "
          "-DTEST_ABS_DEMO\n");
  return 1;
#endif

  printf ("\n--- Summary: %d passed, %d failed ---\n", g_pass, g_fail);
  return (g_fail > 0) ? 1 : 0;
}
