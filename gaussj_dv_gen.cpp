#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <math.h>
#include <iostream>
#include <dispatch/dispatch.h>
#include <Accelerate/Accelerate.h>
#include <sisal_runtime.h>

struct struct_rec_111;
struct struct_rec_110;
struct struct_rec_109;
struct struct_rec_93;
struct struct_rec_92;
struct struct_rec_91;
struct struct_rec_90;
struct struct_rec_89;
struct struct_rec_88;
struct FUNC_COMPUTE_results {
  sisal_array_t res_0;
  sisal_array_t res_1;
};
struct FUNC_GETPIVOT_results {
  int32_t res_0;
  int32_t res_1;
};
extern "C" sisal_array_t func_MAIN(int32_t N, sisal_array_t AIN, sisal_array_t BIN);
extern "C" struct FUNC_COMPUTE_results func_COMPUTE(int32_t N, int32_t PVTROW, sisal_array_t AIN, sisal_array_t BIN);
extern "C" struct FUNC_GETPIVOT_results func_GETPIVOT(int32_t N, sisal_array_t A, sisal_array_t PIVR);
extern "C" int32_t func_IDFMAX(sisal_array_t A, int32_t N);
extern "C" int32_t func_IDFAMAX(sisal_array_t A, int32_t N);

extern "C" int32_t func_IDFAMAX(sisal_array_t A, int32_t N) {
  sisal_array_t v_g1_n__0_A = {0};
  int32_t v_g1_n__0_N = 0;
  (v_g1_n__0_A = SISAL_CAST(sisal_array_t, A));
  (v_g1_n__0_N = SISAL_CAST(int32_t, N));
  int32_t v_g1_n__0_p0_i = 0;
  int32_t v_g1_n__1_p0_o = 0;
  {
    int32_t v_FORALL_14048_n__0_N = 0;
    (v_FORALL_14048_n__0_N = SISAL_CAST(int32_t, v_g1_n__0_N));
    sisal_array_t v_FORALL_14048_n__0_A = {0};
    (v_FORALL_14048_n__0_A = SISAL_CAST(sisal_array_t, v_g1_n__0_A));
    int32_t v_GENERATOR_14050_n__2_I = 0;
    int32_t v_GENERATOR_14050_n__0_N = 0;
    (v_GENERATOR_14050_n__0_N = SISAL_CAST(int32_t, v_FORALL_14048_n__0_N));
    int32_t v_GENERATOR_14050_n__1_p0_o = 0;
    (v_GENERATOR_14050_n__1_p0_o = SISAL_CAST(int32_t, 1));
    (v_GENERATOR_14050_n__2_I = SISAL_CAST(int32_t, ((SISAL_CAST(int32_t, v_GENERATOR_14050_n__0_N) - SISAL_CAST(int32_t, v_GENERATOR_14050_n__1_p0_o)) + 1)));
    (v_g1_n__1_p0_o = SISAL_CAST(int32_t, 0));
    double __argm_val_FORALL_14048 = (-1e308);
    int32_t __argm_idx_FORALL_14048 = 0;
    for (int32_t __idx_FORALL_14048 = 0; (__idx_FORALL_14048 < v_GENERATOR_14050_n__2_I); (__idx_FORALL_14048 = (__idx_FORALL_14048 + 1))) {
      sisal_array_t v_BODY_14051_n__0_A = {0};
      int32_t v_BODY_14051_n__0_I = 0;
      int32_t v_BODY_14051_n__0_N = 0;
      (v_BODY_14051_n__0_N = SISAL_CAST(int32_t, v_FORALL_14048_n__0_N));
      (v_BODY_14051_n__0_A = SISAL_CAST(sisal_array_t, v_FORALL_14048_n__0_A));
      (v_BODY_14051_n__0_I = SISAL_CAST(int32_t, (v_GENERATOR_14050_n__1_p0_o + __idx_FORALL_14048)));
      float v_BODY_14051_n__1_p0_o = 0;
      (v_BODY_14051_n__1_p0_o = SISAL_CAST(float, ((float *)SISAL_CAST(sisal_array_t, v_BODY_14051_n__0_A).data)[(SISAL_CAST(int32_t, v_BODY_14051_n__0_I) - SISAL_CAST(sisal_array_t, v_BODY_14051_n__0_A).lower_bound)]));
      double v_BODY_14051_n__2_p0_o = 0;
      (v_BODY_14051_n__2_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_14051_n__0_A).data)[(SISAL_CAST(int32_t, v_BODY_14051_n__0_I) - SISAL_CAST(sisal_array_t, v_BODY_14051_n__0_A).lower_bound)]));
      double v_BODY_14051_n__3_p0_o = 0;
      (v_BODY_14051_n__3_p0_o = SISAL_CAST(double, func__SABS__D__D(SISAL_CAST(double, v_BODY_14051_n__2_p0_o))));
      if ((SISAL_CAST(double, v_BODY_14051_n__3_p0_o) > __argm_val_FORALL_14048)) {
        (__argm_val_FORALL_14048 = SISAL_CAST(double, v_BODY_14051_n__3_p0_o));
        (__argm_idx_FORALL_14048 = (__idx_FORALL_14048 + v_GENERATOR_14050_n__1_p0_o));
      }
    }
    (v_g1_n__1_p0_o = SISAL_CAST(int32_t, __argm_idx_FORALL_14048));
  }
  (v_g1_n__0_p0_i = SISAL_CAST(int32_t, v_g1_n__1_p0_o));
  return SISAL_CAST(int32_t, v_g1_n__0_p0_i);
}

extern "C" int32_t func_IDFMAX(sisal_array_t A, int32_t N) {
  sisal_array_t v_g2_n__0_A = {0};
  int32_t v_g2_n__0_N = 0;
  (v_g2_n__0_A = SISAL_CAST(sisal_array_t, A));
  (v_g2_n__0_N = SISAL_CAST(int32_t, N));
  int32_t v_g2_n__0_p0_i = 0;
  int32_t v_g2_n__1_p0_o = 0;
  {
    int32_t v_FORALL_13044_n__0_N = 0;
    (v_FORALL_13044_n__0_N = SISAL_CAST(int32_t, v_g2_n__0_N));
    sisal_array_t v_FORALL_13044_n__0_A = {0};
    (v_FORALL_13044_n__0_A = SISAL_CAST(sisal_array_t, v_g2_n__0_A));
    int32_t v_GENERATOR_13046_n__2_I = 0;
    int32_t v_GENERATOR_13046_n__0_N = 0;
    (v_GENERATOR_13046_n__0_N = SISAL_CAST(int32_t, v_FORALL_13044_n__0_N));
    int32_t v_GENERATOR_13046_n__1_p0_o = 0;
    (v_GENERATOR_13046_n__1_p0_o = SISAL_CAST(int32_t, 1));
    (v_GENERATOR_13046_n__2_I = SISAL_CAST(int32_t, ((SISAL_CAST(int32_t, v_GENERATOR_13046_n__0_N) - SISAL_CAST(int32_t, v_GENERATOR_13046_n__1_p0_o)) + 1)));
    (v_g2_n__1_p0_o = SISAL_CAST(int32_t, 0));
    double __argm_val_FORALL_13044 = (-1e308);
    int32_t __argm_idx_FORALL_13044 = 0;
    for (int32_t __idx_FORALL_13044 = 0; (__idx_FORALL_13044 < v_GENERATOR_13046_n__2_I); (__idx_FORALL_13044 = (__idx_FORALL_13044 + 1))) {
      sisal_array_t v_BODY_13047_n__0_A = {0};
      int32_t v_BODY_13047_n__0_I = 0;
      int32_t v_BODY_13047_n__0_N = 0;
      (v_BODY_13047_n__0_N = SISAL_CAST(int32_t, v_FORALL_13044_n__0_N));
      (v_BODY_13047_n__0_A = SISAL_CAST(sisal_array_t, v_FORALL_13044_n__0_A));
      (v_BODY_13047_n__0_I = SISAL_CAST(int32_t, (v_GENERATOR_13046_n__1_p0_o + __idx_FORALL_13044)));
      double v_BODY_13047_n__1_p0_o = 0;
      (v_BODY_13047_n__1_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_13047_n__0_A).data)[(SISAL_CAST(int32_t, v_BODY_13047_n__0_I) - SISAL_CAST(sisal_array_t, v_BODY_13047_n__0_A).lower_bound)]));
      if ((SISAL_CAST(double, v_BODY_13047_n__1_p0_o) > __argm_val_FORALL_13044)) {
        (__argm_val_FORALL_13044 = SISAL_CAST(double, v_BODY_13047_n__1_p0_o));
        (__argm_idx_FORALL_13044 = (__idx_FORALL_13044 + v_GENERATOR_13046_n__1_p0_o));
      }
    }
    (v_g2_n__1_p0_o = SISAL_CAST(int32_t, __argm_idx_FORALL_13044));
  }
  (v_g2_n__0_p0_i = SISAL_CAST(int32_t, v_g2_n__1_p0_o));
  return SISAL_CAST(int32_t, v_g2_n__0_p0_i);
}

extern "C" struct FUNC_GETPIVOT_results func_GETPIVOT(int32_t N, sisal_array_t A, sisal_array_t PIVR) {
  sisal_array_t v_g3_n__0_A = {0};
  int32_t v_g3_n__0_N = 0;
  sisal_array_t v_g3_n__0_PIVR = {0};
  (v_g3_n__0_N = SISAL_CAST(int32_t, N));
  (v_g3_n__0_A = SISAL_CAST(sisal_array_t, A));
  (v_g3_n__0_PIVR = SISAL_CAST(sisal_array_t, PIVR));
  int32_t v_g3_n__0_p0_i = 0;
  int32_t v_g3_n__0_p1_i = 0;
  int32_t v_g3_n__1_p0_o = 0;
  int32_t v_g3_n__1_p1_o = 0;
  {
    sisal_array_t v_LET_NON_REC_12033_n__0_A = {0};
    sisal_array_t v_LET_NON_REC_12033_n__2_COLS = {0};
    int32_t v_LET_NON_REC_12033_n__3_IROW = 0;
    sisal_array_t v_LET_NON_REC_12033_n__2_MAXS = {0};
    int32_t v_LET_NON_REC_12033_n__0_N = 0;
    sisal_array_t v_LET_NON_REC_12033_n__0_PIVR = {0};
    (v_LET_NON_REC_12033_n__0_N = SISAL_CAST(int32_t, v_g3_n__0_N));
    (v_LET_NON_REC_12033_n__0_PIVR = SISAL_CAST(sisal_array_t, v_g3_n__0_PIVR));
    (v_LET_NON_REC_12033_n__0_A = SISAL_CAST(sisal_array_t, v_g3_n__0_A));
    sisal_array_t v_LET_NON_REC_12033_n__1_p0_o = {0};
    sisal_array_t v_LET_NON_REC_12033_n__1_p1_o = {0};
    {
      int32_t v_FORALL_12034_n__0_N = 0;
      (v_FORALL_12034_n__0_N = SISAL_CAST(int32_t, v_LET_NON_REC_12033_n__0_N));
      sisal_array_t v_FORALL_12034_n__0_PIVR = {0};
      (v_FORALL_12034_n__0_PIVR = SISAL_CAST(sisal_array_t, v_LET_NON_REC_12033_n__0_PIVR));
      sisal_array_t v_FORALL_12034_n__0_A = {0};
      (v_FORALL_12034_n__0_A = SISAL_CAST(sisal_array_t, v_LET_NON_REC_12033_n__0_A));
      int32_t v_GENERATOR_12036_n__2_I = 0;
      int32_t v_GENERATOR_12036_n__0_N = 0;
      (v_GENERATOR_12036_n__0_N = SISAL_CAST(int32_t, v_FORALL_12034_n__0_N));
      int32_t v_GENERATOR_12036_n__1_p0_o = 0;
      (v_GENERATOR_12036_n__1_p0_o = SISAL_CAST(int32_t, 1));
      (v_GENERATOR_12036_n__2_I = SISAL_CAST(int32_t, ((SISAL_CAST(int32_t, v_GENERATOR_12036_n__0_N) - SISAL_CAST(int32_t, v_GENERATOR_12036_n__1_p0_o)) + 1)));
      (v_LET_NON_REC_12033_n__1_p0_o = SISAL_CAST(sisal_array_t, 0));
      (v_LET_NON_REC_12033_n__1_p0_o = sisal_array_alloc_empty(1, 6, ((uint64_t)v_GENERATOR_12036_n__2_I)));
      for (int32_t __idx_FORALL_12034 = 0; (__idx_FORALL_12034 < v_GENERATOR_12036_n__2_I); (__idx_FORALL_12034 = (__idx_FORALL_12034 + 1))) {
        sisal_array_t v_BODY_12037_n__0_A = {0};
        int32_t v_BODY_12037_n__1_COL = 0;
        int32_t v_BODY_12037_n__0_I = 0;
        double v_BODY_12037_n__1_MAX = 0;
        int32_t v_BODY_12037_n__0_N = 0;
        sisal_array_t v_BODY_12037_n__0_PIVR = {0};
        (v_BODY_12037_n__0_N = SISAL_CAST(int32_t, v_FORALL_12034_n__0_N));
        (v_BODY_12037_n__0_PIVR = SISAL_CAST(sisal_array_t, v_FORALL_12034_n__0_PIVR));
        (v_BODY_12037_n__0_I = SISAL_CAST(int32_t, (v_GENERATOR_12036_n__1_p0_o + __idx_FORALL_12034)));
        (v_BODY_12037_n__0_A = SISAL_CAST(sisal_array_t, v_FORALL_12034_n__0_A));
        float __idx_FORALL_12034 = 0;
        (__idx_FORALL_12034 = SISAL_CAST(float, v_LET_NON_REC_12033_n__2_COLS));
        sisal_array_t v_IF_DOUBLE__INTEGRAL___12038_n__0_PIVR = {0};
        (v_IF_DOUBLE__INTEGRAL___12038_n__0_PIVR = SISAL_CAST(sisal_array_t, v_BODY_12037_n__0_PIVR));
        int32_t v_IF_DOUBLE__INTEGRAL___12038_n__0_I = 0;
        (v_IF_DOUBLE__INTEGRAL___12038_n__0_I = SISAL_CAST(int32_t, v_BODY_12037_n__0_I));
        sisal_array_t v_IF_DOUBLE__INTEGRAL___12038_n__0_A = {0};
        (v_IF_DOUBLE__INTEGRAL___12038_n__0_A = SISAL_CAST(sisal_array_t, v_BODY_12037_n__0_A));
        int32_t v_IF_DOUBLE__INTEGRAL___12038_n__0_N = 0;
        (v_IF_DOUBLE__INTEGRAL___12038_n__0_N = SISAL_CAST(int32_t, v_BODY_12037_n__0_N));
        {
          int32_t v_PREDICATE_12039_n__0_I = 0;
          sisal_array_t v_PREDICATE_12039_n__0_PIVR = {0};
          (v_PREDICATE_12039_n__0_PIVR = SISAL_CAST(sisal_array_t, v_IF_DOUBLE__INTEGRAL___12038_n__0_PIVR));
          (v_PREDICATE_12039_n__0_I = SISAL_CAST(int32_t, v_IF_DOUBLE__INTEGRAL___12038_n__0_I));
          int32_t v_PREDICATE_12039_n__1_p0_o = 0;
          (v_PREDICATE_12039_n__1_p0_o = SISAL_CAST(int32_t, ((int32_t *)SISAL_CAST(sisal_array_t, v_PREDICATE_12039_n__0_PIVR).data)[(SISAL_CAST(int32_t, v_PREDICATE_12039_n__0_I) - SISAL_CAST(sisal_array_t, v_PREDICATE_12039_n__0_PIVR).lower_bound)]));
          int32_t v_PREDICATE_12039_n__2_p0_o = 0;
          (v_PREDICATE_12039_n__2_p0_o = SISAL_CAST(int32_t, 0));
          bool v_PREDICATE_12039_n__3_p0_o = 0;
          (v_PREDICATE_12039_n__3_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_PREDICATE_12039_n__1_p0_o) == SISAL_CAST(int32_t, v_PREDICATE_12039_n__2_p0_o))));
          if (v_PREDICATE_12039_n__3_p0_o) {
            sisal_array_t v_THEN_12041_n__0_A = {0};
            int32_t v_THEN_12041_n__0_I = 0;
            int32_t v_THEN_12041_n__0_N = 0;
            (v_THEN_12041_n__0_A = SISAL_CAST(sisal_array_t, v_IF_DOUBLE__INTEGRAL___12038_n__0_A));
            (v_THEN_12041_n__0_I = SISAL_CAST(int32_t, v_IF_DOUBLE__INTEGRAL___12038_n__0_I));
            (v_THEN_12041_n__0_N = SISAL_CAST(int32_t, v_IF_DOUBLE__INTEGRAL___12038_n__0_N));
            int32_t v_THEN_12041_n__1_p0_o = 0;
            double v_THEN_12041_n__1_p1_o = 0;
            {
              sisal_array_t v_LET_NON_REC_12042_n__0_A = {0};
              int32_t v_LET_NON_REC_12042_n__0_I = 0;
              int32_t v_LET_NON_REC_12042_n__3_IMAX = 0;
              int32_t v_LET_NON_REC_12042_n__0_N = 0;
              (v_LET_NON_REC_12042_n__0_A = SISAL_CAST(sisal_array_t, v_THEN_12041_n__0_A));
              (v_LET_NON_REC_12042_n__0_I = SISAL_CAST(int32_t, v_THEN_12041_n__0_I));
              (v_LET_NON_REC_12042_n__0_N = SISAL_CAST(int32_t, v_THEN_12041_n__0_N));
              sisal_array_t v_LET_NON_REC_12042_n__1_p0_o = {0};
              (v_LET_NON_REC_12042_n__1_p0_o = SISAL_CAST(sisal_array_t, sisal_dv_rank_reduce(SISAL_CAST(sisal_array_t, v_LET_NON_REC_12042_n__0_A), SISAL_CAST(int32_t, v_LET_NON_REC_12042_n__0_I))));
              sisal_array_t v_LET_NON_REC_12042_n__2_p0_o = {0};
              (v_LET_NON_REC_12042_n__2_p0_o = SISAL_CAST(sisal_array_t, sisal_dv_rank_reduce(SISAL_CAST(sisal_array_t, v_LET_NON_REC_12042_n__0_A), SISAL_CAST(int32_t, v_LET_NON_REC_12042_n__0_I))));
              (v_LET_NON_REC_12042_n__3_IMAX = SISAL_CAST(int32_t, func_IDFAMAX(SISAL_CAST(sisal_array_t, v_LET_NON_REC_12042_n__2_p0_o), SISAL_CAST(int32_t, v_LET_NON_REC_12042_n__0_N))));
              sisal_array_t v_LET_NON_REC_12042_n__4_p0_o = {0};
              (v_LET_NON_REC_12042_n__4_p0_o = SISAL_CAST(sisal_array_t, sisal_dv_rank_reduce(SISAL_CAST(sisal_array_t, v_LET_NON_REC_12042_n__0_A), SISAL_CAST(int32_t, v_LET_NON_REC_12042_n__0_I))));
              float v_LET_NON_REC_12042_n__5_p0_o = 0;
              (v_LET_NON_REC_12042_n__5_p0_o = SISAL_CAST(float, ((float *)SISAL_CAST(sisal_array_t, v_LET_NON_REC_12042_n__4_p0_o).data)[(SISAL_CAST(int32_t, v_LET_NON_REC_12042_n__3_IMAX) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_12042_n__4_p0_o).lower_bound)]));
              sisal_array_t v_LET_NON_REC_12042_n__6_p0_o = {0};
              (v_LET_NON_REC_12042_n__6_p0_o = SISAL_CAST(sisal_array_t, sisal_dv_rank_reduce(SISAL_CAST(sisal_array_t, v_LET_NON_REC_12042_n__0_A), SISAL_CAST(int32_t, v_LET_NON_REC_12042_n__0_I))));
              double v_LET_NON_REC_12042_n__7_p0_o = 0;
              (v_LET_NON_REC_12042_n__7_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_LET_NON_REC_12042_n__6_p0_o).data)[(SISAL_CAST(int32_t, v_LET_NON_REC_12042_n__3_IMAX) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_12042_n__6_p0_o).lower_bound)]));
              double v_LET_NON_REC_12042_n__8_p0_o = 0;
              (v_LET_NON_REC_12042_n__8_p0_o = SISAL_CAST(double, func__SABS__D__D(SISAL_CAST(double, v_LET_NON_REC_12042_n__7_p0_o))));
              (v_THEN_12041_n__1_p0_o = SISAL_CAST(int32_t, v_LET_NON_REC_12042_n__3_IMAX));
              (v_THEN_12041_n__1_p1_o = SISAL_CAST(double, v_LET_NON_REC_12042_n__8_p0_o));
            }
            (v_BODY_12037_n__1_COL = SISAL_CAST(int32_t, v_THEN_12041_n__1_p0_o));
            (v_BODY_12037_n__1_MAX = SISAL_CAST(double, v_THEN_12041_n__1_p1_o));
          }
          else {
            int32_t v_ELSE_12040_n__1_p0_o = 0;
            (v_ELSE_12040_n__1_p0_o = SISAL_CAST(int32_t, 0));
            double v_ELSE_12040_n__2_p0_o = 0;
            (v_ELSE_12040_n__2_p0_o = SISAL_CAST(double, 1.f));
            double v_ELSE_12040_n__3_p0_o = 0;
            (v_ELSE_12040_n__3_p0_o = SISAL_CAST(double, (-SISAL_CAST(double, v_ELSE_12040_n__2_p0_o))));
            (v_BODY_12037_n__1_COL = SISAL_CAST(int32_t, v_ELSE_12040_n__1_p0_o));
            (v_BODY_12037_n__1_MAX = SISAL_CAST(double, v_ELSE_12040_n__3_p0_o));
          }
        }
        (((double *)v_LET_NON_REC_12033_n__1_p0_o.data)[__idx_FORALL_12034] = SISAL_CAST(double, v_BODY_12037_n__1_MAX));
      }
    }
    (v_LET_NON_REC_12033_n__3_IROW = SISAL_CAST(int32_t, func_IDFMAX(SISAL_CAST(sisal_array_t, v_LET_NON_REC_12033_n__1_p1_o), SISAL_CAST(int32_t, v_LET_NON_REC_12033_n__0_N))));
    int32_t v_LET_NON_REC_12033_n__4_p0_o = 0;
    (v_LET_NON_REC_12033_n__4_p0_o = SISAL_CAST(int32_t, ((int32_t *)SISAL_CAST(sisal_array_t, v_LET_NON_REC_12033_n__1_p0_o).data)[(SISAL_CAST(int32_t, v_LET_NON_REC_12033_n__3_IROW) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_12033_n__1_p0_o).lower_bound)]));
    (v_g3_n__1_p0_o = SISAL_CAST(int32_t, v_LET_NON_REC_12033_n__4_p0_o));
    (v_g3_n__1_p1_o = SISAL_CAST(int32_t, v_LET_NON_REC_12033_n__3_IROW));
  }
  (v_g3_n__0_p0_i = SISAL_CAST(int32_t, v_g3_n__1_p0_o));
  (v_g3_n__0_p1_i = SISAL_CAST(int32_t, v_g3_n__1_p1_o));
  struct FUNC_GETPIVOT_results __res_obj;
  (__res_obj.res_0 = SISAL_CAST(int32_t, v_g3_n__0_p0_i));
  (__res_obj.res_1 = SISAL_CAST(int32_t, v_g3_n__0_p1_i));
  return __res_obj;
}

extern "C" struct FUNC_COMPUTE_results func_COMPUTE(int32_t N, int32_t PVTROW, sisal_array_t AIN, sisal_array_t BIN) {
  sisal_array_t v_g4_n__0_AIN = {0};
  sisal_array_t v_g4_n__0_BIN = {0};
  int32_t v_g4_n__0_N = 0;
  int32_t v_g4_n__0_PVTROW = 0;
  (v_g4_n__0_N = SISAL_CAST(int32_t, N));
  (v_g4_n__0_PVTROW = SISAL_CAST(int32_t, PVTROW));
  (v_g4_n__0_AIN = SISAL_CAST(sisal_array_t, AIN));
  (v_g4_n__0_BIN = SISAL_CAST(sisal_array_t, BIN));
  sisal_array_t v_g4_n__0_p0_i = {0};
  sisal_array_t v_g4_n__0_p1_i = {0};
  sisal_array_t v_g4_n__1_p0_o = {0};
  sisal_array_t v_g4_n__1_p1_o = {0};
  {
    int32_t v_FORALL_11015_n__0_N = 0;
    (v_FORALL_11015_n__0_N = SISAL_CAST(int32_t, v_g4_n__0_N));
    sisal_array_t v_FORALL_11015_n__0_AIN = {0};
    (v_FORALL_11015_n__0_AIN = SISAL_CAST(sisal_array_t, v_g4_n__0_AIN));
    int32_t v_FORALL_11015_n__0_PVTROW = 0;
    (v_FORALL_11015_n__0_PVTROW = SISAL_CAST(int32_t, v_g4_n__0_PVTROW));
    sisal_array_t v_FORALL_11015_n__0_BIN = {0};
    (v_FORALL_11015_n__0_BIN = SISAL_CAST(sisal_array_t, v_g4_n__0_BIN));
    int32_t v_GENERATOR_11017_n__2_I = 0;
    int32_t v_GENERATOR_11017_n__0_N = 0;
    (v_GENERATOR_11017_n__0_N = SISAL_CAST(int32_t, v_FORALL_11015_n__0_N));
    int32_t v_GENERATOR_11017_n__1_p0_o = 0;
    (v_GENERATOR_11017_n__1_p0_o = SISAL_CAST(int32_t, 1));
    (v_GENERATOR_11017_n__2_I = SISAL_CAST(int32_t, ((SISAL_CAST(int32_t, v_GENERATOR_11017_n__0_N) - SISAL_CAST(int32_t, v_GENERATOR_11017_n__1_p0_o)) + 1)));
    (v_g4_n__1_p0_o = SISAL_CAST(sisal_array_t, 0));
    (v_g4_n__1_p0_o = sisal_array_alloc_empty(1, 4, ((uint64_t)v_GENERATOR_11017_n__2_I)));
    for (int32_t __idx_FORALL_11015 = 0; (__idx_FORALL_11015 < v_GENERATOR_11017_n__2_I); (__idx_FORALL_11015 = (__idx_FORALL_11015 + 1))) {
      sisal_array_t v_BODY_11018_n__0_AIN = {0};
      sisal_array_t v_BODY_11018_n__3_AROW = {0};
      double v_BODY_11018_n__3_BELE = 0;
      sisal_array_t v_BODY_11018_n__0_BIN = {0};
      int32_t v_BODY_11018_n__0_I = 0;
      int32_t v_BODY_11018_n__0_N = 0;
      double v_BODY_11018_n__2_PVTELE = 0;
      int32_t v_BODY_11018_n__0_PVTROW = 0;
      (v_BODY_11018_n__0_N = SISAL_CAST(int32_t, v_FORALL_11015_n__0_N));
      (v_BODY_11018_n__0_AIN = SISAL_CAST(sisal_array_t, v_FORALL_11015_n__0_AIN));
      (v_BODY_11018_n__0_PVTROW = SISAL_CAST(int32_t, v_FORALL_11015_n__0_PVTROW));
      (v_BODY_11018_n__0_I = SISAL_CAST(int32_t, (v_GENERATOR_11017_n__1_p0_o + __idx_FORALL_11015)));
      (v_BODY_11018_n__0_BIN = SISAL_CAST(sisal_array_t, v_FORALL_11015_n__0_BIN));
      sisal_array_t v_BODY_11018_n__1_p0_o = {0};
      (v_BODY_11018_n__1_p0_o = SISAL_CAST(sisal_array_t, sisal_dv_rank_reduce(SISAL_CAST(sisal_array_t, v_BODY_11018_n__0_AIN), SISAL_CAST(int32_t, v_BODY_11018_n__0_PVTROW))));
      (v_BODY_11018_n__2_PVTELE = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_11018_n__1_p0_o).data)[(SISAL_CAST(int32_t, v_BODY_11018_n__0_PVTROW) - SISAL_CAST(sisal_array_t, v_BODY_11018_n__1_p0_o).lower_bound)]));
      int32_t v_IF_DOUBLE__array_dv_DOUBLE____11019_n__0_I = 0;
      (v_IF_DOUBLE__array_dv_DOUBLE____11019_n__0_I = SISAL_CAST(int32_t, v_BODY_11018_n__0_I));
      int32_t v_IF_DOUBLE__array_dv_DOUBLE____11019_n__0_PVTROW = 0;
      (v_IF_DOUBLE__array_dv_DOUBLE____11019_n__0_PVTROW = SISAL_CAST(int32_t, v_BODY_11018_n__0_PVTROW));
      sisal_array_t v_IF_DOUBLE__array_dv_DOUBLE____11019_n__0_AIN = {0};
      (v_IF_DOUBLE__array_dv_DOUBLE____11019_n__0_AIN = SISAL_CAST(sisal_array_t, v_BODY_11018_n__0_AIN));
      double v_IF_DOUBLE__array_dv_DOUBLE____11019_n__0_PVTELE = 0;
      (v_IF_DOUBLE__array_dv_DOUBLE____11019_n__0_PVTELE = SISAL_CAST(double, v_BODY_11018_n__2_PVTELE));
      int32_t v_IF_DOUBLE__array_dv_DOUBLE____11019_n__0_N = 0;
      (v_IF_DOUBLE__array_dv_DOUBLE____11019_n__0_N = SISAL_CAST(int32_t, v_BODY_11018_n__0_N));
      sisal_array_t v_IF_DOUBLE__array_dv_DOUBLE____11019_n__0_BIN = {0};
      (v_IF_DOUBLE__array_dv_DOUBLE____11019_n__0_BIN = SISAL_CAST(sisal_array_t, v_BODY_11018_n__0_BIN));
      {
        int32_t v_PREDICATE_11020_n__0_I = 0;
        int32_t v_PREDICATE_11020_n__0_PVTROW = 0;
        (v_PREDICATE_11020_n__0_I = SISAL_CAST(int32_t, v_IF_DOUBLE__array_dv_DOUBLE____11019_n__0_I));
        (v_PREDICATE_11020_n__0_PVTROW = SISAL_CAST(int32_t, v_IF_DOUBLE__array_dv_DOUBLE____11019_n__0_PVTROW));
        bool v_PREDICATE_11020_n__1_p0_o = 0;
        (v_PREDICATE_11020_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_PREDICATE_11020_n__0_I) == SISAL_CAST(int32_t, v_PREDICATE_11020_n__0_PVTROW))));
        if (v_PREDICATE_11020_n__1_p0_o) {
          sisal_array_t v_THEN_11027_n__0_AIN = {0};
          sisal_array_t v_THEN_11027_n__0_BIN = {0};
          int32_t v_THEN_11027_n__0_I = 0;
          int32_t v_THEN_11027_n__0_N = 0;
          double v_THEN_11027_n__0_PVTELE = 0;
          (v_THEN_11027_n__0_N = SISAL_CAST(int32_t, v_IF_DOUBLE__array_dv_DOUBLE____11019_n__0_N));
          (v_THEN_11027_n__0_AIN = SISAL_CAST(sisal_array_t, v_IF_DOUBLE__array_dv_DOUBLE____11019_n__0_AIN));
          (v_THEN_11027_n__0_I = SISAL_CAST(int32_t, v_IF_DOUBLE__array_dv_DOUBLE____11019_n__0_I));
          (v_THEN_11027_n__0_PVTELE = SISAL_CAST(double, v_IF_DOUBLE__array_dv_DOUBLE____11019_n__0_PVTELE));
          (v_THEN_11027_n__0_BIN = SISAL_CAST(sisal_array_t, v_IF_DOUBLE__array_dv_DOUBLE____11019_n__0_BIN));
          sisal_array_t v_THEN_11027_n__1_p0_o = {0};
          {
            int32_t v_FORALL_11028_n__0_N = 0;
            (v_FORALL_11028_n__0_N = SISAL_CAST(int32_t, v_THEN_11027_n__0_N));
            sisal_array_t v_FORALL_11028_n__0_AIN = {0};
            (v_FORALL_11028_n__0_AIN = SISAL_CAST(sisal_array_t, v_THEN_11027_n__0_AIN));
            int32_t v_FORALL_11028_n__0_I = 0;
            (v_FORALL_11028_n__0_I = SISAL_CAST(int32_t, v_THEN_11027_n__0_I));
            double v_FORALL_11028_n__0_PVTELE = 0;
            (v_FORALL_11028_n__0_PVTELE = SISAL_CAST(double, v_THEN_11027_n__0_PVTELE));
            int32_t v_GENERATOR_11030_n__2_J = 0;
            int32_t v_GENERATOR_11030_n__0_N = 0;
            (v_GENERATOR_11030_n__0_N = SISAL_CAST(int32_t, v_FORALL_11028_n__0_N));
            int32_t v_GENERATOR_11030_n__1_p0_o = 0;
            (v_GENERATOR_11030_n__1_p0_o = SISAL_CAST(int32_t, 1));
            (v_GENERATOR_11030_n__2_J = SISAL_CAST(int32_t, ((SISAL_CAST(int32_t, v_GENERATOR_11030_n__0_N) - SISAL_CAST(int32_t, v_GENERATOR_11030_n__1_p0_o)) + 1)));
            (v_THEN_11027_n__1_p0_o = SISAL_CAST(sisal_array_t, 0));
            (v_THEN_11027_n__1_p0_o = sisal_array_alloc_empty(1, 4, ((uint64_t)v_GENERATOR_11030_n__2_J)));
            for (int32_t __idx_FORALL_11028 = 0; (__idx_FORALL_11028 < v_GENERATOR_11030_n__2_J); (__idx_FORALL_11028 = (__idx_FORALL_11028 + 1))) {
              sisal_array_t v_BODY_11031_n__0_AIN = {0};
              int32_t v_BODY_11031_n__0_I = 0;
              int32_t v_BODY_11031_n__0_J = 0;
              int32_t v_BODY_11031_n__0_N = 0;
              double v_BODY_11031_n__0_PVTELE = 0;
              (v_BODY_11031_n__0_N = SISAL_CAST(int32_t, v_FORALL_11028_n__0_N));
              (v_BODY_11031_n__0_AIN = SISAL_CAST(sisal_array_t, v_FORALL_11028_n__0_AIN));
              (v_BODY_11031_n__0_I = SISAL_CAST(int32_t, v_FORALL_11028_n__0_I));
              (v_BODY_11031_n__0_J = SISAL_CAST(int32_t, (v_GENERATOR_11030_n__1_p0_o + __idx_FORALL_11028)));
              (v_BODY_11031_n__0_PVTELE = SISAL_CAST(double, v_FORALL_11028_n__0_PVTELE));
              float __idx_FORALL_11028 = 0;
              (__idx_FORALL_11028 = SISAL_CAST(float, v_BODY_11018_n__2_PVTELE));
              sisal_array_t v_BODY_11031_n__1_p0_o = {0};
              (v_BODY_11031_n__1_p0_o = SISAL_CAST(sisal_array_t, sisal_dv_rank_reduce(SISAL_CAST(sisal_array_t, v_BODY_11031_n__0_AIN), SISAL_CAST(int32_t, v_BODY_11031_n__0_I))));
              float v_BODY_11031_n__2_p0_o = 0;
              (v_BODY_11031_n__2_p0_o = SISAL_CAST(float, ((float *)SISAL_CAST(sisal_array_t, v_BODY_11031_n__1_p0_o).data)[(SISAL_CAST(int32_t, v_BODY_11031_n__0_J) - SISAL_CAST(sisal_array_t, v_BODY_11031_n__1_p0_o).lower_bound)]));
              sisal_array_t v_BODY_11031_n__3_p0_o = {0};
              (v_BODY_11031_n__3_p0_o = SISAL_CAST(sisal_array_t, sisal_dv_rank_reduce(SISAL_CAST(sisal_array_t, v_BODY_11031_n__0_AIN), SISAL_CAST(int32_t, v_BODY_11031_n__0_I))));
              double v_BODY_11031_n__4_p0_o = 0;
              (v_BODY_11031_n__4_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_11031_n__3_p0_o).data)[(SISAL_CAST(int32_t, v_BODY_11031_n__0_J) - SISAL_CAST(sisal_array_t, v_BODY_11031_n__3_p0_o).lower_bound)]));
              double v_BODY_11031_n__5_p0_o = 0;
              (v_BODY_11031_n__5_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_BODY_11031_n__4_p0_o) / SISAL_CAST(double, v_BODY_11031_n__0_PVTELE))));
              (((double *)v_THEN_11027_n__1_p0_o.data)[__idx_FORALL_11028] = SISAL_CAST(double, v_BODY_11031_n__5_p0_o));
            }
          }
          float v_THEN_11027_n__3_p0_o = 0;
          (v_THEN_11027_n__3_p0_o = SISAL_CAST(float, ((float *)SISAL_CAST(sisal_array_t, v_THEN_11027_n__0_BIN).data)[(SISAL_CAST(int32_t, v_THEN_11027_n__0_I) - SISAL_CAST(sisal_array_t, v_THEN_11027_n__0_BIN).lower_bound)]));
          double v_THEN_11027_n__4_p0_o = 0;
          (v_THEN_11027_n__4_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_THEN_11027_n__0_BIN).data)[(SISAL_CAST(int32_t, v_THEN_11027_n__0_I) - SISAL_CAST(sisal_array_t, v_THEN_11027_n__0_BIN).lower_bound)]));
          double v_THEN_11027_n__5_p0_o = 0;
          (v_THEN_11027_n__5_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_THEN_11027_n__4_p0_o) / SISAL_CAST(double, v_THEN_11027_n__0_PVTELE))));
          (v_BODY_11018_n__3_AROW = SISAL_CAST(sisal_array_t, v_THEN_11027_n__1_p0_o));
          (v_BODY_11018_n__3_BELE = SISAL_CAST(double, v_THEN_11027_n__5_p0_o));
        }
        else {
          sisal_array_t v_ELSE_11021_n__0_AIN = {0};
          sisal_array_t v_ELSE_11021_n__0_BIN = {0};
          int32_t v_ELSE_11021_n__0_I = 0;
          int32_t v_ELSE_11021_n__0_N = 0;
          double v_ELSE_11021_n__0_PVTELE = 0;
          int32_t v_ELSE_11021_n__0_PVTROW = 0;
          (v_ELSE_11021_n__0_AIN = SISAL_CAST(sisal_array_t, v_IF_DOUBLE__array_dv_DOUBLE____11019_n__0_AIN));
          (v_ELSE_11021_n__0_I = SISAL_CAST(int32_t, v_IF_DOUBLE__array_dv_DOUBLE____11019_n__0_I));
          (v_ELSE_11021_n__0_PVTROW = SISAL_CAST(int32_t, v_IF_DOUBLE__array_dv_DOUBLE____11019_n__0_PVTROW));
          (v_ELSE_11021_n__0_PVTELE = SISAL_CAST(double, v_IF_DOUBLE__array_dv_DOUBLE____11019_n__0_PVTELE));
          (v_ELSE_11021_n__0_N = SISAL_CAST(int32_t, v_IF_DOUBLE__array_dv_DOUBLE____11019_n__0_N));
          (v_ELSE_11021_n__0_BIN = SISAL_CAST(sisal_array_t, v_IF_DOUBLE__array_dv_DOUBLE____11019_n__0_BIN));
          sisal_array_t v_ELSE_11021_n__1_p0_o = {0};
          double v_ELSE_11021_n__1_p1_o = 0;
          {
            sisal_array_t v_LET_NON_REC_11022_n__0_AIN = {0};
            sisal_array_t v_LET_NON_REC_11022_n__0_BIN = {0};
            int32_t v_LET_NON_REC_11022_n__0_I = 0;
            double v_LET_NON_REC_11022_n__5_MULTIPLER = 0;
            int32_t v_LET_NON_REC_11022_n__0_N = 0;
            double v_LET_NON_REC_11022_n__0_PVTELE = 0;
            int32_t v_LET_NON_REC_11022_n__0_PVTROW = 0;
            (v_LET_NON_REC_11022_n__0_AIN = SISAL_CAST(sisal_array_t, v_ELSE_11021_n__0_AIN));
            (v_LET_NON_REC_11022_n__0_I = SISAL_CAST(int32_t, v_ELSE_11021_n__0_I));
            (v_LET_NON_REC_11022_n__0_PVTROW = SISAL_CAST(int32_t, v_ELSE_11021_n__0_PVTROW));
            (v_LET_NON_REC_11022_n__0_PVTELE = SISAL_CAST(double, v_ELSE_11021_n__0_PVTELE));
            (v_LET_NON_REC_11022_n__0_N = SISAL_CAST(int32_t, v_ELSE_11021_n__0_N));
            (v_LET_NON_REC_11022_n__0_BIN = SISAL_CAST(sisal_array_t, v_ELSE_11021_n__0_BIN));
            sisal_array_t v_LET_NON_REC_11022_n__1_p0_o = {0};
            (v_LET_NON_REC_11022_n__1_p0_o = SISAL_CAST(sisal_array_t, sisal_dv_rank_reduce(SISAL_CAST(sisal_array_t, v_LET_NON_REC_11022_n__0_AIN), SISAL_CAST(int32_t, v_LET_NON_REC_11022_n__0_I))));
            float v_LET_NON_REC_11022_n__2_p0_o = 0;
            (v_LET_NON_REC_11022_n__2_p0_o = SISAL_CAST(float, ((float *)SISAL_CAST(sisal_array_t, v_LET_NON_REC_11022_n__1_p0_o).data)[(SISAL_CAST(int32_t, v_LET_NON_REC_11022_n__0_PVTROW) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_11022_n__1_p0_o).lower_bound)]));
            sisal_array_t v_LET_NON_REC_11022_n__3_p0_o = {0};
            (v_LET_NON_REC_11022_n__3_p0_o = SISAL_CAST(sisal_array_t, sisal_dv_rank_reduce(SISAL_CAST(sisal_array_t, v_LET_NON_REC_11022_n__0_AIN), SISAL_CAST(int32_t, v_LET_NON_REC_11022_n__0_I))));
            double v_LET_NON_REC_11022_n__4_p0_o = 0;
            (v_LET_NON_REC_11022_n__4_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_LET_NON_REC_11022_n__3_p0_o).data)[(SISAL_CAST(int32_t, v_LET_NON_REC_11022_n__0_PVTROW) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_11022_n__3_p0_o).lower_bound)]));
            (v_LET_NON_REC_11022_n__5_MULTIPLER = SISAL_CAST(double, (SISAL_CAST(double, v_LET_NON_REC_11022_n__4_p0_o) / SISAL_CAST(double, v_LET_NON_REC_11022_n__0_PVTELE))));
            sisal_array_t v_LET_NON_REC_11022_n__6_p0_o = {0};
            {
              sisal_array_t v_FORALL_11023_n__0_AIN = {0};
              (v_FORALL_11023_n__0_AIN = SISAL_CAST(sisal_array_t, v_LET_NON_REC_11022_n__0_AIN));
              int32_t v_FORALL_11023_n__0_I = 0;
              (v_FORALL_11023_n__0_I = SISAL_CAST(int32_t, v_LET_NON_REC_11022_n__0_I));
              int32_t v_FORALL_11023_n__0_PVTROW = 0;
              (v_FORALL_11023_n__0_PVTROW = SISAL_CAST(int32_t, v_LET_NON_REC_11022_n__0_PVTROW));
              double v_FORALL_11023_n__0_PVTELE = 0;
              (v_FORALL_11023_n__0_PVTELE = SISAL_CAST(double, v_LET_NON_REC_11022_n__0_PVTELE));
              int32_t v_FORALL_11023_n__0_N = 0;
              (v_FORALL_11023_n__0_N = SISAL_CAST(int32_t, v_LET_NON_REC_11022_n__0_N));
              double v_FORALL_11023_n__0_MULTIPLER = 0;
              (v_FORALL_11023_n__0_MULTIPLER = SISAL_CAST(double, v_LET_NON_REC_11022_n__5_MULTIPLER));
              sisal_array_t v_GENERATOR_11025_n__0_AIN = {0};
              int32_t v_GENERATOR_11025_n__0_I = 0;
              int32_t v_GENERATOR_11025_n__2_J = 0;
              int32_t v_GENERATOR_11025_n__0_N = 0;
              double v_GENERATOR_11025_n__0_PVTELE = 0;
              int32_t v_GENERATOR_11025_n__0_PVTROW = 0;
              (v_GENERATOR_11025_n__0_AIN = SISAL_CAST(sisal_array_t, v_FORALL_11023_n__0_AIN));
              (v_GENERATOR_11025_n__0_I = SISAL_CAST(int32_t, v_FORALL_11023_n__0_I));
              (v_GENERATOR_11025_n__0_PVTROW = SISAL_CAST(int32_t, v_FORALL_11023_n__0_PVTROW));
              (v_GENERATOR_11025_n__0_PVTELE = SISAL_CAST(double, v_FORALL_11023_n__0_PVTELE));
              (v_GENERATOR_11025_n__0_N = SISAL_CAST(int32_t, v_FORALL_11023_n__0_N));
              int32_t v_GENERATOR_11025_n__1_p0_o = 0;
              (v_GENERATOR_11025_n__1_p0_o = SISAL_CAST(int32_t, 1));
              (v_GENERATOR_11025_n__2_J = SISAL_CAST(int32_t, ((SISAL_CAST(int32_t, v_GENERATOR_11025_n__0_N) - SISAL_CAST(int32_t, v_GENERATOR_11025_n__1_p0_o)) + 1)));
              (v_LET_NON_REC_11022_n__6_p0_o = SISAL_CAST(sisal_array_t, 0));
              (v_LET_NON_REC_11022_n__6_p0_o = sisal_array_alloc_empty(1, 4, ((uint64_t)v_GENERATOR_11025_n__2_J)));
              for (int32_t __idx_FORALL_11023 = 0; (__idx_FORALL_11023 < v_GENERATOR_11025_n__2_J); (__idx_FORALL_11023 = (__idx_FORALL_11023 + 1))) {
                sisal_array_t v_BODY_11026_n__0_AIN = {0};
                int32_t v_BODY_11026_n__0_I = 0;
                int32_t v_BODY_11026_n__0_J = 0;
                double v_BODY_11026_n__0_MULTIPLER = 0;
                int32_t v_BODY_11026_n__0_N = 0;
                double v_BODY_11026_n__0_PVTELE = 0;
                int32_t v_BODY_11026_n__0_PVTROW = 0;
                (v_BODY_11026_n__0_AIN = SISAL_CAST(sisal_array_t, v_FORALL_11023_n__0_AIN));
                (v_BODY_11026_n__0_I = SISAL_CAST(int32_t, v_FORALL_11023_n__0_I));
                (v_BODY_11026_n__0_PVTROW = SISAL_CAST(int32_t, v_FORALL_11023_n__0_PVTROW));
                (v_BODY_11026_n__0_PVTELE = SISAL_CAST(double, v_FORALL_11023_n__0_PVTELE));
                (v_BODY_11026_n__0_N = SISAL_CAST(int32_t, v_FORALL_11023_n__0_N));
                (v_BODY_11026_n__0_J = SISAL_CAST(int32_t, (v_GENERATOR_11025_n__1_p0_o + __idx_FORALL_11023)));
                (v_BODY_11026_n__0_MULTIPLER = SISAL_CAST(double, v_FORALL_11023_n__0_MULTIPLER));
                float __idx_FORALL_11023 = 0;
                (__idx_FORALL_11023 = SISAL_CAST(float, v_LET_NON_REC_11022_n__2_p0_o));
                sisal_array_t v_BODY_11026_n__1_p0_o = {0};
                (v_BODY_11026_n__1_p0_o = SISAL_CAST(sisal_array_t, sisal_dv_rank_reduce(SISAL_CAST(sisal_array_t, v_BODY_11026_n__0_AIN), SISAL_CAST(int32_t, v_BODY_11026_n__0_I))));
                double v_BODY_11026_n__2_p0_o = 0;
                (v_BODY_11026_n__2_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_11026_n__1_p0_o).data)[(SISAL_CAST(int32_t, v_BODY_11026_n__0_J) - SISAL_CAST(sisal_array_t, v_BODY_11026_n__1_p0_o).lower_bound)]));
                sisal_array_t v_BODY_11026_n__3_p0_o = {0};
                (v_BODY_11026_n__3_p0_o = SISAL_CAST(sisal_array_t, sisal_dv_rank_reduce(SISAL_CAST(sisal_array_t, v_BODY_11026_n__0_AIN), SISAL_CAST(int32_t, v_BODY_11026_n__0_PVTROW))));
                double v_BODY_11026_n__4_p0_o = 0;
                (v_BODY_11026_n__4_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_11026_n__3_p0_o).data)[(SISAL_CAST(int32_t, v_BODY_11026_n__0_J) - SISAL_CAST(sisal_array_t, v_BODY_11026_n__3_p0_o).lower_bound)]));
                double v_BODY_11026_n__5_p0_o = 0;
                (v_BODY_11026_n__5_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_BODY_11026_n__0_MULTIPLER) * SISAL_CAST(double, v_BODY_11026_n__4_p0_o))));
                double v_BODY_11026_n__6_p0_o = 0;
                (v_BODY_11026_n__6_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_BODY_11026_n__2_p0_o) - SISAL_CAST(double, v_BODY_11026_n__5_p0_o))));
                (((double *)v_LET_NON_REC_11022_n__6_p0_o.data)[__idx_FORALL_11023] = SISAL_CAST(double, v_BODY_11026_n__6_p0_o));
              }
            }
            double v_LET_NON_REC_11022_n__8_p0_o = 0;
            (v_LET_NON_REC_11022_n__8_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_LET_NON_REC_11022_n__0_BIN).data)[(SISAL_CAST(int32_t, v_LET_NON_REC_11022_n__0_I) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_11022_n__0_BIN).lower_bound)]));
            double v_LET_NON_REC_11022_n__9_p0_o = 0;
            (v_LET_NON_REC_11022_n__9_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_LET_NON_REC_11022_n__0_BIN).data)[(SISAL_CAST(int32_t, v_LET_NON_REC_11022_n__0_PVTROW) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_11022_n__0_BIN).lower_bound)]));
            double v_LET_NON_REC_11022_n__10_p0_o = 0;
            (v_LET_NON_REC_11022_n__10_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_LET_NON_REC_11022_n__5_MULTIPLER) * SISAL_CAST(double, v_LET_NON_REC_11022_n__9_p0_o))));
            double v_LET_NON_REC_11022_n__11_p0_o = 0;
            (v_LET_NON_REC_11022_n__11_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_LET_NON_REC_11022_n__8_p0_o) - SISAL_CAST(double, v_LET_NON_REC_11022_n__10_p0_o))));
            (v_ELSE_11021_n__1_p0_o = SISAL_CAST(sisal_array_t, v_LET_NON_REC_11022_n__6_p0_o));
            (v_ELSE_11021_n__1_p1_o = SISAL_CAST(double, v_LET_NON_REC_11022_n__11_p0_o));
          }
          (v_BODY_11018_n__3_AROW = SISAL_CAST(sisal_array_t, v_ELSE_11021_n__1_p0_o));
          (v_BODY_11018_n__3_BELE = SISAL_CAST(double, v_ELSE_11021_n__1_p1_o));
        }
      }
      (((double *)v_g4_n__1_p0_o.data)[__idx_FORALL_11015] = SISAL_CAST(double, v_BODY_11018_n__3_BELE));
    }
  }
  (v_g4_n__0_p0_i = SISAL_CAST(sisal_array_t, v_g4_n__1_p0_o));
  (v_g4_n__0_p1_i = SISAL_CAST(sisal_array_t, v_g4_n__1_p1_o));
  struct FUNC_COMPUTE_results __res_obj;
  (__res_obj.res_0 = SISAL_CAST(sisal_array_t, v_g4_n__0_p0_i));
  (__res_obj.res_1 = SISAL_CAST(sisal_array_t, v_g4_n__0_p1_i));
  return __res_obj;
}

extern "C" sisal_array_t func_MAIN(int32_t N, sisal_array_t AIN, sisal_array_t BIN) {
  sisal_array_t v_g5_n__0_AIN = {0};
  sisal_array_t v_g5_n__0_BIN = {0};
  int32_t v_g5_n__0_N = 0;
  (v_g5_n__0_N = SISAL_CAST(int32_t, N));
  (v_g5_n__0_AIN = SISAL_CAST(sisal_array_t, AIN));
  (v_g5_n__0_BIN = SISAL_CAST(sisal_array_t, BIN));
  sisal_array_t v_g5_n__0_p0_i = {0};
  sisal_array_t v_g5_n__1_p0_o = {0};
  {
    sisal_array_t v_LoopB_10001_n__0_AIN = {0};
    (v_LoopB_10001_n__0_AIN = SISAL_CAST(sisal_array_t, v_g5_n__0_AIN));
    sisal_array_t v_LoopB_10001_n__0_BIN = {0};
    (v_LoopB_10001_n__0_BIN = SISAL_CAST(sisal_array_t, v_g5_n__0_BIN));
    int32_t v_LoopB_10001_n__0_N = 0;
    (v_LoopB_10001_n__0_N = SISAL_CAST(int32_t, v_g5_n__0_N));
    sisal_array_t v_INIT_10010_n__0_A = {0};
    sisal_array_t v_INIT_10010_n__0_AIN = {0};
    sisal_array_t v_INIT_10010_n__0_B = {0};
    sisal_array_t v_INIT_10010_n__0_BIN = {0};
    int32_t v_INIT_10010_n__1_I = 0;
    int32_t v_INIT_10010_n__0_N = 0;
    sisal_array_t v_INIT_10010_n__2_PIVR = {0};
    (v_INIT_10010_n__0_AIN = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__0_AIN));
    (v_INIT_10010_n__0_BIN = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__0_BIN));
    (v_INIT_10010_n__0_N = SISAL_CAST(int32_t, v_LoopB_10001_n__0_N));
    (v_INIT_10010_n__1_I = SISAL_CAST(int32_t, 0));
    {
      sisal_array_t v_FORALL_10011_n__0_AIN = {0};
      (v_FORALL_10011_n__0_AIN = SISAL_CAST(sisal_array_t, v_INIT_10010_n__0_AIN));
      sisal_array_t v_FORALL_10011_n__0_BIN = {0};
      (v_FORALL_10011_n__0_BIN = SISAL_CAST(sisal_array_t, v_INIT_10010_n__0_BIN));
      int32_t v_FORALL_10011_n__0_N = 0;
      (v_FORALL_10011_n__0_N = SISAL_CAST(int32_t, v_INIT_10010_n__0_N));
      sisal_array_t v_GENERATOR_10013_n__0_AIN = {0};
      sisal_array_t v_GENERATOR_10013_n__0_BIN = {0};
      int32_t v_GENERATOR_10013_n__2_J = 0;
      int32_t v_GENERATOR_10013_n__0_N = 0;
      (v_GENERATOR_10013_n__0_AIN = SISAL_CAST(sisal_array_t, v_FORALL_10011_n__0_AIN));
      (v_GENERATOR_10013_n__0_BIN = SISAL_CAST(sisal_array_t, v_FORALL_10011_n__0_BIN));
      (v_GENERATOR_10013_n__0_N = SISAL_CAST(int32_t, v_FORALL_10011_n__0_N));
      int32_t v_GENERATOR_10013_n__1_p0_o = 0;
      (v_GENERATOR_10013_n__1_p0_o = SISAL_CAST(int32_t, 1));
      (v_GENERATOR_10013_n__2_J = SISAL_CAST(int32_t, ((SISAL_CAST(int32_t, v_GENERATOR_10013_n__0_N) - SISAL_CAST(int32_t, v_GENERATOR_10013_n__1_p0_o)) + 1)));
      (v_INIT_10010_n__2_PIVR = SISAL_CAST(sisal_array_t, 0));
      (v_INIT_10010_n__2_PIVR = sisal_array_alloc_empty(1, 6, ((uint64_t)v_GENERATOR_10013_n__2_J)));
      for (int32_t __idx_FORALL_10011 = 0; (__idx_FORALL_10011 < v_GENERATOR_10013_n__2_J); (__idx_FORALL_10011 = (__idx_FORALL_10011 + 1))) {
        sisal_array_t v_BODY_10014_n__0_AIN = {0};
        sisal_array_t v_BODY_10014_n__0_BIN = {0};
        int32_t v_BODY_10014_n__0_N = 0;
        (v_BODY_10014_n__0_AIN = SISAL_CAST(sisal_array_t, v_FORALL_10011_n__0_AIN));
        (v_BODY_10014_n__0_BIN = SISAL_CAST(sisal_array_t, v_FORALL_10011_n__0_BIN));
        (v_BODY_10014_n__0_N = SISAL_CAST(int32_t, v_FORALL_10011_n__0_N));
        float __idx_FORALL_10011 = 0;
        (__idx_FORALL_10011 = SISAL_CAST(float, v_INIT_10010_n__2_PIVR));
        int32_t v_BODY_10014_n__1_p0_o = 0;
        (v_BODY_10014_n__1_p0_o = SISAL_CAST(int32_t, 0));
        (((int32_t *)v_INIT_10010_n__2_PIVR.data)[__idx_FORALL_10011] = SISAL_CAST(int32_t, v_BODY_10014_n__1_p0_o));
      }
    }
    sisal_array_t v_LoopB_10001_n__0_A = {0};
    (v_LoopB_10001_n__0_A = SISAL_CAST(sisal_array_t, v_INIT_10010_n__0_AIN));
    sisal_array_t v_LoopB_10001_n__0_B = {0};
    (v_LoopB_10001_n__0_B = SISAL_CAST(sisal_array_t, v_INIT_10010_n__0_BIN));
    int32_t v_LoopB_10001_n__0_I = 0;
    (v_LoopB_10001_n__0_I = SISAL_CAST(int32_t, v_INIT_10010_n__1_I));
    sisal_array_t v_LoopB_10001_n__0_OLD_PIVR = {0};
    (v_LoopB_10001_n__0_OLD_PIVR = SISAL_CAST(sisal_array_t, v_INIT_10010_n__2_PIVR));
    sisal_array_t v_TEST_10009_n__0_AIN = {0};
    sisal_array_t v_TEST_10009_n__0_BIN = {0};
    int32_t v_TEST_10009_n__0_I = 0;
    int32_t v_TEST_10009_n__0_N = 0;
    sisal_array_t v_TEST_10009_n__0_OLD_A = {0};
    sisal_array_t v_TEST_10009_n__0_OLD_B = {0};
    int32_t v_TEST_10009_n__0_OLD_I = 0;
    sisal_array_t v_TEST_10009_n__2_OLD_PIVR = {0};
    (v_TEST_10009_n__0_OLD_A = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__0_AIN));
    (v_TEST_10009_n__0_OLD_B = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__0_BIN));
    (v_TEST_10009_n__0_N = SISAL_CAST(int32_t, v_LoopB_10001_n__0_N));
    (v_TEST_10009_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_10001_n__0_I));
    bool v_TEST_10009_n__1_p0_o = 0;
    (v_TEST_10009_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_TEST_10009_n__0_OLD_I) < SISAL_CAST(int32_t, v_TEST_10009_n__0_N))));
    while (v_TEST_10009_n__1_p0_o) {
      sisal_array_t v_BODY_10003_n__10_A = {0};
      sisal_array_t v_BODY_10003_n__5_A1 = {0};
      sisal_array_t v_BODY_10003_n__0_AIN = {0};
      sisal_array_t v_BODY_10003_n__10_B = {0};
      sisal_array_t v_BODY_10003_n__5_B1 = {0};
      sisal_array_t v_BODY_10003_n__0_BIN = {0};
      int32_t v_BODY_10003_n__2_I = 0;
      int32_t v_BODY_10003_n__3_ICOL = 0;
      int32_t v_BODY_10003_n__3_IROW = 0;
      int32_t v_BODY_10003_n__0_N = 0;
      sisal_array_t v_BODY_10003_n__0_OLD_A = {0};
      sisal_array_t v_BODY_10003_n__0_OLD_B = {0};
      int32_t v_BODY_10003_n__0_OLD_I = 0;
      sisal_array_t v_BODY_10003_n__0_OLD_PIVR = {0};
      sisal_array_t v_BODY_10003_n__9_PIVR = {0};
      (v_BODY_10003_n__0_AIN = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__0_AIN));
      (v_BODY_10003_n__0_BIN = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__0_BIN));
      (v_BODY_10003_n__0_N = SISAL_CAST(int32_t, v_LoopB_10001_n__0_N));
      (v_BODY_10003_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_10001_n__0_I));
      (v_BODY_10003_n__0_OLD_A = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__0_A));
      (v_BODY_10003_n__0_OLD_PIVR = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__0_OLD_PIVR));
      (v_BODY_10003_n__0_OLD_B = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__0_B));
      int32_t v_BODY_10003_n__1_p0_o = 0;
      (v_BODY_10003_n__1_p0_o = SISAL_CAST(int32_t, 1));
      (v_BODY_10003_n__2_I = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_10003_n__0_OLD_I) + SISAL_CAST(int32_t, v_BODY_10003_n__1_p0_o))));
      struct FUNC_GETPIVOT_results _mr_BODY_10003_3 = func_GETPIVOT(SISAL_CAST(int32_t, v_BODY_10003_n__0_N), SISAL_CAST(sisal_array_t, v_BODY_10003_n__0_OLD_A), SISAL_CAST(sisal_array_t, v_BODY_10003_n__0_OLD_PIVR));
      (v_BODY_10003_n__3_ICOL = SISAL_CAST(int32_t, _mr_BODY_10003_3.res_0));
      (v_BODY_10003_n__3_IROW = SISAL_CAST(int32_t, _mr_BODY_10003_3.res_1));
      int32_t v_IF_array_dv_DOUBLE___array_dv_DOUBLE____10004_n__0_ICOL = 0;
      (v_IF_array_dv_DOUBLE___array_dv_DOUBLE____10004_n__0_ICOL = SISAL_CAST(int32_t, v_BODY_10003_n__3_ICOL));
      int32_t v_IF_array_dv_DOUBLE___array_dv_DOUBLE____10004_n__0_IROW = 0;
      (v_IF_array_dv_DOUBLE___array_dv_DOUBLE____10004_n__0_IROW = SISAL_CAST(int32_t, v_BODY_10003_n__3_IROW));
      sisal_array_t v_IF_array_dv_DOUBLE___array_dv_DOUBLE____10004_n__0_OLD_A = {0};
      (v_IF_array_dv_DOUBLE___array_dv_DOUBLE____10004_n__0_OLD_A = SISAL_CAST(sisal_array_t, v_BODY_10003_n__0_OLD_A));
      sisal_array_t v_IF_array_dv_DOUBLE___array_dv_DOUBLE____10004_n__0_OLD_B = {0};
      (v_IF_array_dv_DOUBLE___array_dv_DOUBLE____10004_n__0_OLD_B = SISAL_CAST(sisal_array_t, v_BODY_10003_n__0_OLD_B));
      {
        int32_t v_PREDICATE_10005_n__0_ICOL = 0;
        int32_t v_PREDICATE_10005_n__0_IROW = 0;
        (v_PREDICATE_10005_n__0_ICOL = SISAL_CAST(int32_t, v_IF_array_dv_DOUBLE___array_dv_DOUBLE____10004_n__0_ICOL));
        (v_PREDICATE_10005_n__0_IROW = SISAL_CAST(int32_t, v_IF_array_dv_DOUBLE___array_dv_DOUBLE____10004_n__0_IROW));
        bool v_PREDICATE_10005_n__1_p0_o = 0;
        (v_PREDICATE_10005_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_PREDICATE_10005_n__0_ICOL) != SISAL_CAST(int32_t, v_PREDICATE_10005_n__0_IROW))));
        if (v_PREDICATE_10005_n__1_p0_o) {
          int32_t v_THEN_10007_n__0_ICOL = 0;
          int32_t v_THEN_10007_n__0_IROW = 0;
          sisal_array_t v_THEN_10007_n__0_OLD_A = {0};
          sisal_array_t v_THEN_10007_n__0_OLD_B = {0};
          (v_THEN_10007_n__0_OLD_A = SISAL_CAST(sisal_array_t, v_IF_array_dv_DOUBLE___array_dv_DOUBLE____10004_n__0_OLD_A));
          (v_THEN_10007_n__0_IROW = SISAL_CAST(int32_t, v_IF_array_dv_DOUBLE___array_dv_DOUBLE____10004_n__0_IROW));
          (v_THEN_10007_n__0_ICOL = SISAL_CAST(int32_t, v_IF_array_dv_DOUBLE___array_dv_DOUBLE____10004_n__0_ICOL));
          (v_THEN_10007_n__0_OLD_B = SISAL_CAST(sisal_array_t, v_IF_array_dv_DOUBLE___array_dv_DOUBLE____10004_n__0_OLD_B));
          sisal_array_t v_THEN_10007_n__1_p0_o = {0};
          (v_THEN_10007_n__1_p0_o = SISAL_CAST(sisal_array_t, sisal_dv_rank_reduce(SISAL_CAST(sisal_array_t, v_THEN_10007_n__0_OLD_A), SISAL_CAST(int32_t, v_THEN_10007_n__0_IROW))));
          sisal_array_t v_THEN_10007_n__3_p0_o = {0};
          (v_THEN_10007_n__3_p0_o = SISAL_CAST(sisal_array_t, sisal_array_replace_arr(SISAL_CAST(sisal_array_t, v_THEN_10007_n__0_OLD_A), ((int64_t)SISAL_CAST(int32_t, v_THEN_10007_n__0_ICOL)), SISAL_CAST(sisal_array_t, v_THEN_10007_n__1_p0_o))));
          sisal_array_t v_THEN_10007_n__4_p0_o = {0};
          (v_THEN_10007_n__4_p0_o = SISAL_CAST(sisal_array_t, sisal_dv_rank_reduce(SISAL_CAST(sisal_array_t, v_THEN_10007_n__0_OLD_A), SISAL_CAST(int32_t, v_THEN_10007_n__0_ICOL))));
          sisal_array_t v_THEN_10007_n__6_p0_o = {0};
          (v_THEN_10007_n__6_p0_o = SISAL_CAST(sisal_array_t, sisal_array_replace_arr(SISAL_CAST(sisal_array_t, v_THEN_10007_n__3_p0_o), ((int64_t)SISAL_CAST(int32_t, v_THEN_10007_n__0_IROW)), SISAL_CAST(sisal_array_t, v_THEN_10007_n__4_p0_o))));
          double v_THEN_10007_n__7_p0_o = 0;
          (v_THEN_10007_n__7_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_THEN_10007_n__0_OLD_B).data)[(SISAL_CAST(int32_t, v_THEN_10007_n__0_IROW) - SISAL_CAST(sisal_array_t, v_THEN_10007_n__0_OLD_B).lower_bound)]));
          sisal_array_t v_THEN_10007_n__9_p0_o = {0};
          (v_THEN_10007_n__9_p0_o = SISAL_CAST(sisal_array_t, sisal_array_replace_f64(SISAL_CAST(sisal_array_t, v_THEN_10007_n__0_OLD_B), ((int64_t)SISAL_CAST(int32_t, v_THEN_10007_n__0_ICOL)), SISAL_CAST(double, v_THEN_10007_n__7_p0_o))));
          double v_THEN_10007_n__10_p0_o = 0;
          (v_THEN_10007_n__10_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_THEN_10007_n__0_OLD_B).data)[(SISAL_CAST(int32_t, v_THEN_10007_n__0_ICOL) - SISAL_CAST(sisal_array_t, v_THEN_10007_n__0_OLD_B).lower_bound)]));
          sisal_array_t v_THEN_10007_n__12_p0_o = {0};
          (v_THEN_10007_n__12_p0_o = SISAL_CAST(sisal_array_t, sisal_array_replace_f64(SISAL_CAST(sisal_array_t, v_THEN_10007_n__9_p0_o), ((int64_t)SISAL_CAST(int32_t, v_THEN_10007_n__0_IROW)), SISAL_CAST(double, v_THEN_10007_n__10_p0_o))));
          (v_BODY_10003_n__5_A1 = SISAL_CAST(sisal_array_t, v_THEN_10007_n__6_p0_o));
          (v_BODY_10003_n__5_B1 = SISAL_CAST(sisal_array_t, v_THEN_10007_n__12_p0_o));
        }
        else {
          sisal_array_t v_ELSE_10006_n__0_OLD_A = {0};
          sisal_array_t v_ELSE_10006_n__0_OLD_B = {0};
          (v_ELSE_10006_n__0_OLD_A = SISAL_CAST(sisal_array_t, v_IF_array_dv_DOUBLE___array_dv_DOUBLE____10004_n__0_OLD_A));
          (v_ELSE_10006_n__0_OLD_B = SISAL_CAST(sisal_array_t, v_IF_array_dv_DOUBLE___array_dv_DOUBLE____10004_n__0_OLD_B));
          (v_BODY_10003_n__5_A1 = SISAL_CAST(sisal_array_t, v_ELSE_10006_n__0_OLD_A));
          (v_BODY_10003_n__5_B1 = SISAL_CAST(sisal_array_t, v_ELSE_10006_n__0_OLD_B));
        }
      }
      int32_t v_BODY_10003_n__7_p0_o = 0;
      (v_BODY_10003_n__7_p0_o = SISAL_CAST(int32_t, 1));
      (v_BODY_10003_n__9_PIVR = SISAL_CAST(sisal_array_t, sisal_array_replace_i32(SISAL_CAST(sisal_array_t, v_BODY_10003_n__0_OLD_PIVR), ((int64_t)SISAL_CAST(int32_t, v_BODY_10003_n__3_ICOL)), SISAL_CAST(int32_t, v_BODY_10003_n__7_p0_o))));
      struct FUNC_COMPUTE_results _mr_BODY_10003_10 = func_COMPUTE(SISAL_CAST(int32_t, v_BODY_10003_n__0_N), SISAL_CAST(int32_t, v_BODY_10003_n__3_ICOL), SISAL_CAST(sisal_array_t, v_BODY_10003_n__5_A1), SISAL_CAST(sisal_array_t, v_BODY_10003_n__5_B1));
      (v_BODY_10003_n__10_A = SISAL_CAST(sisal_array_t, _mr_BODY_10003_10.res_0));
      (v_BODY_10003_n__10_B = SISAL_CAST(sisal_array_t, _mr_BODY_10003_10.res_1));
      (v_LoopB_10001_n__0_A = SISAL_CAST(sisal_array_t, v_BODY_10003_n__10_A));
      (v_LoopB_10001_n__0_B = SISAL_CAST(sisal_array_t, v_BODY_10003_n__10_B));
      (v_LoopB_10001_n__0_I = SISAL_CAST(int32_t, v_BODY_10003_n__2_I));
      (v_LoopB_10001_n__0_OLD_PIVR = SISAL_CAST(sisal_array_t, v_BODY_10003_n__9_PIVR));
      (v_TEST_10009_n__0_OLD_A = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__0_AIN));
      (v_TEST_10009_n__0_OLD_B = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__0_BIN));
      (v_TEST_10009_n__0_N = SISAL_CAST(int32_t, v_LoopB_10001_n__0_N));
      (v_TEST_10009_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_10001_n__0_I));
      (v_TEST_10009_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_TEST_10009_n__0_OLD_I) < SISAL_CAST(int32_t, v_TEST_10009_n__0_N))));
    }
    sisal_array_t v_RETURNS_10002_n__0_p1_o = {0};
    (v_RETURNS_10002_n__0_p1_o = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__0_B));
    sisal_array_t v_RETURNS_10002_n__1_p0_o = {0};
    (v_RETURNS_10002_n__1_p0_o = SISAL_CAST(sisal_array_t, SISAL_CAST(sisal_array_t, v_RETURNS_10002_n__0_p1_o)));
    (v_g5_n__1_p0_o = SISAL_CAST(sisal_array_t, v_RETURNS_10002_n__1_p0_o));
  }
  (v_g5_n__0_p0_i = SISAL_CAST(sisal_array_t, v_g5_n__1_p0_o));
  return SISAL_CAST(sisal_array_t, v_g5_n__0_p0_i);
}
