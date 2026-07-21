#define SISAL_CUSTOM_ELEM_SIZE

#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <math.h>
#include <iostream>
#include <dispatch/dispatch.h>
#include <Accelerate/Accelerate.h>
#include <sisal_runtime.h>

struct struct_rec_103 {
  int32_t lo;
  int32_t stride;
  int32_t size;
};
struct struct_rec_102 {
  int32_t stride;
  int32_t size;
};
struct struct_rec_101 {
  int32_t size;
};
struct struct_rec_93 {
  double RE;
  double IM;
};
struct struct_rec_92 {
  double IM;
};
struct struct_rec_91 {
  float RE;
  float IM;
};
struct struct_rec_90 {
  float IM;
};
struct struct_rec_89 {
  float RE;
  float IM;
};
struct struct_rec_88 {
  float IM;
};
struct FUNC_REDUCE_AND_MAX_results {
  sisal_array_t res_0;
  sisal_array_t res_1;
  double res_2;
  sisal_array_t res_3;
};
struct FUNC_INDEX_OF_MAX_results {
  int32_t res_0;
  int32_t res_1;
};
struct FUNC_FINDMAX_results {
  double res_0;
  sisal_array_t res_1;
};
size_t sisal_elem_size(int32_t type_id) {
    switch (type_id) {
        case 83:
            return sizeof(void*);
        case 12:
            return sizeof(uint32_t);
        case 93:
            return sizeof(struct struct_rec_93);
        case 92:
            return sizeof(struct struct_rec_92);
        case 91:
            return sizeof(struct struct_rec_91);
        case 90:
            return sizeof(struct struct_rec_90);
        case 89:
            return sizeof(struct struct_rec_89);
        case 88:
            return sizeof(struct struct_rec_88);
        case 103:
        case 104:
            return sizeof(struct struct_rec_103);
        case 102:
            return sizeof(struct struct_rec_102);
        case 101:
            return sizeof(struct struct_rec_101);
        case 96:
        case 97:
        case 98:
        case 99:
        case 100:
        case 105:
        case 106:
        case 107:
        case 108:
        case 109:
        case 110:
        case 111:
        case 112:
        case 113:
        case 114:
        case 115:
        case 116:
        case 117:
        case 118:
        case 119:
        case 120:
        case 121:
        case 122:
        case 123:
        case 124:
            return sizeof(sisal_array_t);
        case 7:
        case 13:
            return sizeof(int64_t);
        case 2:
        case 6:
        case 10:
        case 94:
            return sizeof(int32_t);
        case 9:
        case 14:
            return sizeof(int16_t);
        case 5:
        case 8:
        case 15:
        case 16:
        case 17:
        case 18:
        case 19:
        case 20:
        case 21:
        case 22:
        case 23:
        case 24:
        case 25:
        case 26:
        case 27:
        case 28:
        case 29:
        case 30:
        case 31:
        case 32:
        case 33:
        case 34:
        case 35:
        case 36:
        case 37:
        case 38:
        case 39:
        case 40:
        case 41:
        case 42:
        case 43:
        case 44:
        case 45:
        case 46:
        case 47:
        case 48:
        case 49:
        case 50:
        case 51:
        case 52:
        case 53:
        case 54:
        case 55:
        case 56:
        case 57:
        case 58:
        case 59:
        case 60:
        case 61:
        case 62:
        case 63:
        case 64:
        case 65:
        case 66:
        case 67:
        case 68:
        case 69:
        case 70:
        case 71:
        case 72:
        case 73:
        case 74:
        case 75:
        case 76:
        case 77:
        case 78:
        case 79:
        case 80:
        case 81:
        case 82:
            return sizeof(float);
        case 4:
        case 95:
            return sizeof(double);
        case 3:
        case 11:
            return sizeof(char);
        case 1:
            return sizeof(bool);
        default:
            return sizeof(sisal_array_t);
    }
}

extern "C" sisal_array_t func_MAIN(int32_t N, sisal_array_t AIN, sisal_array_t BIN);
extern "C" struct FUNC_REDUCE_AND_MAX_results func_REDUCE_AND_MAX(sisal_array_t A, int32_t PIVOT, sisal_array_t PIVR, sisal_array_t B);
extern "C" struct FUNC_INDEX_OF_MAX_results func_INDEX_OF_MAX(double MAX, sisal_array_t MAXS, sisal_array_t A);
extern "C" struct FUNC_FINDMAX_results func_FINDMAX(sisal_array_t A);

extern "C" struct FUNC_FINDMAX_results func_FINDMAX(sisal_array_t A) {
  sisal_array_t v_g1_n__0_A = {0};
  (v_g1_n__0_A = SISAL_CAST(sisal_array_t, A));
  double v_g1_n__0_p0_i = 0;
  sisal_array_t v_g1_n__0_p1_i = {0};
  double v_g1_n__1_p0_o = 0;
  sisal_array_t v_g1_n__1_p1_o = {0};
  {
    sisal_array_t v_FORALL_13042_n__0_A = v_g1_n__0_A;
    sisal_array_t v_FORALL_13042_n__2_ROW;
    double v_FORALL_13042_n__3___forall_body_0;
    double v_FORALL_13042_n__3___forall_body_1;
    sisal_array_t v_GENERATOR_13044_n__0_A;
    sisal_array_t v_GENERATOR_13044_n__1_ROW;
    sisal_array_t v_BODY_13045_n__0_A;
    double v_BODY_13045_n__1_MAX;
    sisal_array_t v_BODY_13045_n__0_ROW;
    sisal_array_t v_FORALL_13046_n__0_A;
    sisal_array_t v_FORALL_13046_n__0_ROW;
    double v_FORALL_13046_n__2_X;
    double v_FORALL_13046_n__3___forall_body_0;
    sisal_array_t v_GENERATOR_13048_n__0_A;
    sisal_array_t v_GENERATOR_13048_n__0_ROW;
    double v_GENERATOR_13048_n__1_X;
    sisal_array_t v_BODY_13049_n__0_A;
    sisal_array_t v_BODY_13049_n__0_ROW;
    double v_BODY_13049_n__0_X;
    (v_GENERATOR_13044_n__0_A = v_FORALL_13042_n__0_A);
    (v_g1_n__1_p0_o = (-1e308));
    (v_g1_n__1_p1_o = sisal_array_alloc_empty(1, 4, ((uint64_t)(1 * ((int32_t)v_GENERATOR_13044_n__0_A.dims[0])))));
    (v_g1_n__1_p1_o.dims[0] = ((int32_t)v_GENERATOR_13044_n__0_A.dims[0]));
    (v_g1_n__1_p1_o.lower_bound[0] = 1);
    int32_t __g_13042 = 0;
    for (int32_t __k_13044 = 0; (__k_13044 < ((int32_t)v_GENERATOR_13044_n__0_A.dims[0])); (__k_13044++)) {
      (v_GENERATOR_13044_n__1_ROW = sisal_array_get_row(v_GENERATOR_13044_n__0_A, __k_13044));
      (v_BODY_13045_n__0_A = SISAL_CAST(sisal_array_t, v_FORALL_13042_n__0_A));
      (v_BODY_13045_n__0_ROW = SISAL_CAST(sisal_array_t, v_GENERATOR_13044_n__1_ROW));
      {
        sisal_array_t v_FORALL_13046_n__0_A = v_BODY_13045_n__0_A;
        sisal_array_t v_FORALL_13046_n__0_ROW = v_BODY_13045_n__0_ROW;
        double v_FORALL_13046_n__2_X;
        double v_FORALL_13046_n__3___forall_body_0;
        sisal_array_t v_GENERATOR_13048_n__0_A;
        sisal_array_t v_GENERATOR_13048_n__0_ROW;
        double v_GENERATOR_13048_n__1_X;
        sisal_array_t v_BODY_13049_n__0_A;
        sisal_array_t v_BODY_13049_n__0_ROW;
        double v_BODY_13049_n__0_X;
        (v_GENERATOR_13048_n__0_ROW = v_FORALL_13046_n__0_ROW);
        (v_BODY_13045_n__1_MAX = (-1e308));
        for (int32_t __k_13048 = 0; (__k_13048 < ((int32_t)v_GENERATOR_13048_n__0_ROW.size)); (__k_13048++)) {
          (v_GENERATOR_13048_n__1_X = ((double *)v_GENERATOR_13048_n__0_ROW.data)[__k_13048]);
          (v_BODY_13049_n__0_A = SISAL_CAST(sisal_array_t, v_FORALL_13046_n__0_A));
          (v_BODY_13049_n__0_ROW = SISAL_CAST(sisal_array_t, v_FORALL_13046_n__0_ROW));
          (v_BODY_13049_n__0_X = SISAL_CAST(double, v_GENERATOR_13048_n__1_X));
          double v_BODY_13049_n__1_p0_o = 0;
          (v_BODY_13049_n__1_p0_o = SISAL_CAST(double, func__SABS__D__D(SISAL_CAST(double, v_BODY_13049_n__0_X))));
          if ((SISAL_CAST(double, v_BODY_13049_n__1_p0_o) > v_BODY_13045_n__1_MAX)) {
            (v_BODY_13045_n__1_MAX = SISAL_CAST(double, v_BODY_13049_n__1_p0_o));
          }
        }
      }
      if ((SISAL_CAST(double, v_BODY_13045_n__1_MAX) > v_g1_n__1_p0_o)) {
        (v_g1_n__1_p0_o = SISAL_CAST(double, v_BODY_13045_n__1_MAX));
      }
      (((double *)v_g1_n__1_p1_o.data)[__g_13042] = SISAL_CAST(double, v_BODY_13045_n__1_MAX));
      (__g_13042++);
    }
  }
  (v_g1_n__0_p0_i = SISAL_CAST(double, v_g1_n__1_p0_o));
  (v_g1_n__0_p1_i = SISAL_CAST(sisal_array_t, v_g1_n__1_p1_o));
  struct FUNC_FINDMAX_results __res_obj;
  (__res_obj.res_0 = SISAL_CAST(double, v_g1_n__0_p0_i));
  (__res_obj.res_1 = SISAL_CAST(sisal_array_t, v_g1_n__0_p1_i));
  return __res_obj;
}

extern "C" struct FUNC_INDEX_OF_MAX_results func_INDEX_OF_MAX(double MAX, sisal_array_t MAXS, sisal_array_t A) {
  sisal_array_t v_g2_n__0_A = {0};
  double v_g2_n__0_MAX = 0;
  sisal_array_t v_g2_n__0_MAXS = {0};
  (v_g2_n__0_MAX = SISAL_CAST(double, MAX));
  (v_g2_n__0_MAXS = SISAL_CAST(sisal_array_t, MAXS));
  (v_g2_n__0_A = SISAL_CAST(sisal_array_t, A));
  int32_t v_g2_n__0_p0_i = 0;
  int32_t v_g2_n__0_p1_i = 0;
  int32_t v_g2_n__1_p0_o = 0;
  int32_t v_g2_n__1_p1_o = 0;
  {
    sisal_array_t v_LET_NON_REC_12033_n__0_A = {0};
    int32_t v_LET_NON_REC_12033_n__4_COL = 0;
    double v_LET_NON_REC_12033_n__0_MAX = 0;
    sisal_array_t v_LET_NON_REC_12033_n__0_MAXS = {0};
    int32_t v_LET_NON_REC_12033_n__2_ROW = 0;
    (v_LET_NON_REC_12033_n__0_A = SISAL_CAST(sisal_array_t, v_g2_n__0_A));
    (v_LET_NON_REC_12033_n__0_MAX = SISAL_CAST(double, v_g2_n__0_MAX));
    (v_LET_NON_REC_12033_n__0_MAXS = SISAL_CAST(sisal_array_t, v_g2_n__0_MAXS));
    int32_t v_LET_NON_REC_12033_n__1_p0_o = 0;
    {
      sisal_array_t v_FORALL_12034_n__0_A = v_LET_NON_REC_12033_n__0_A;
      int32_t v_FORALL_12034_n__2_I;
      double v_FORALL_12034_n__0_MAX = v_LET_NON_REC_12033_n__0_MAX;
      sisal_array_t v_FORALL_12034_n__0_MAXS = v_LET_NON_REC_12033_n__0_MAXS;
      double v_FORALL_12034_n__2_X;
      int32_t v_FORALL_12034_n__3___forall_body_0;
      bool v_FORALL_12034_n__3___forall_mask_0;
      sisal_array_t v_GENERATOR_12036_n__0_A;
      int32_t v_GENERATOR_12036_n__1_I;
      double v_GENERATOR_12036_n__0_MAX;
      sisal_array_t v_GENERATOR_12036_n__0_MAXS;
      double v_GENERATOR_12036_n__1_X;
      sisal_array_t v_BODY_12037_n__0_A;
      int32_t v_BODY_12037_n__0_I;
      double v_BODY_12037_n__0_MAX;
      sisal_array_t v_BODY_12037_n__0_MAXS;
      double v_BODY_12037_n__0_X;
      (v_GENERATOR_12036_n__0_MAXS = v_FORALL_12034_n__0_MAXS);
      (v_LET_NON_REC_12033_n__1_p0_o = 0x7fffffff);
      int32_t __g_12034 = 0;
      for (int32_t __k_12036 = 0; (__k_12036 < ((int32_t)v_GENERATOR_12036_n__0_MAXS.size)); (__k_12036++)) {
        (v_GENERATOR_12036_n__1_X = ((double *)v_GENERATOR_12036_n__0_MAXS.data)[__k_12036]);
        (v_GENERATOR_12036_n__1_I = (((int32_t)v_GENERATOR_12036_n__0_MAXS.lower_bound[0]) + __k_12036));
        (v_BODY_12037_n__0_A = SISAL_CAST(sisal_array_t, v_FORALL_12034_n__0_A));
        (v_BODY_12037_n__0_I = SISAL_CAST(int32_t, v_GENERATOR_12036_n__1_I));
        (v_BODY_12037_n__0_MAX = SISAL_CAST(double, v_FORALL_12034_n__0_MAX));
        (v_BODY_12037_n__0_MAXS = SISAL_CAST(sisal_array_t, v_FORALL_12034_n__0_MAXS));
        (v_BODY_12037_n__0_X = SISAL_CAST(double, v_GENERATOR_12036_n__1_X));
        bool v_BODY_12037_n__1_p0_o = 0;
        (v_BODY_12037_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(double, v_BODY_12037_n__0_X) == SISAL_CAST(double, v_BODY_12037_n__0_MAX))));
        if (v_BODY_12037_n__1_p0_o) {
          if ((SISAL_CAST(int32_t, v_BODY_12037_n__0_I) < v_LET_NON_REC_12033_n__1_p0_o)) {
            (v_LET_NON_REC_12033_n__1_p0_o = SISAL_CAST(int32_t, v_BODY_12037_n__0_I));
          }
        }
        (__g_12034++);
      }
    }
    int32_t v_LET_NON_REC_12033_n__3_p0_o = 0;
    {
      sisal_array_t v_FORALL_12038_n__0_A = v_LET_NON_REC_12033_n__0_A;
      int32_t v_FORALL_12038_n__2_J;
      double v_FORALL_12038_n__0_MAX = v_LET_NON_REC_12033_n__0_MAX;
      sisal_array_t v_FORALL_12038_n__0_MAXS = v_LET_NON_REC_12033_n__0_MAXS;
      int32_t v_FORALL_12038_n__0_ROW = v_LET_NON_REC_12033_n__1_p0_o;
      double v_FORALL_12038_n__2_X;
      int32_t v_FORALL_12038_n__3___forall_body_0;
      bool v_FORALL_12038_n__3___forall_mask_0;
      sisal_array_t v_GENERATOR_12040_n__0_A;
      int32_t v_GENERATOR_12040_n__2_J;
      double v_GENERATOR_12040_n__0_MAX;
      sisal_array_t v_GENERATOR_12040_n__0_MAXS;
      int32_t v_GENERATOR_12040_n__0_ROW;
      double v_GENERATOR_12040_n__2_X;
      sisal_array_t v_BODY_12041_n__0_A;
      int32_t v_BODY_12041_n__0_J;
      double v_BODY_12041_n__0_MAX;
      sisal_array_t v_BODY_12041_n__0_MAXS;
      int32_t v_BODY_12041_n__0_ROW;
      double v_BODY_12041_n__0_X;
      (v_GENERATOR_12040_n__0_A = v_FORALL_12038_n__0_A);
      (v_GENERATOR_12040_n__0_ROW = v_FORALL_12038_n__0_ROW);
      sisal_array_t v_GENERATOR_12040_n__1_p0_o = {0};
      (v_GENERATOR_12040_n__1_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_GENERATOR_12040_n__0_A), (SISAL_CAST(int32_t, v_GENERATOR_12040_n__0_ROW) - SISAL_CAST(sisal_array_t, v_GENERATOR_12040_n__0_A).lower_bound[0]))));
      (v_LET_NON_REC_12033_n__3_p0_o = 0x7fffffff);
      int32_t __g_12038 = 0;
      for (int32_t __k_12040 = 0; (__k_12040 < ((int32_t)v_GENERATOR_12040_n__1_p0_o.size)); (__k_12040++)) {
        (v_GENERATOR_12040_n__2_X = ((double *)v_GENERATOR_12040_n__1_p0_o.data)[__k_12040]);
        (v_GENERATOR_12040_n__2_J = (((int32_t)v_GENERATOR_12040_n__1_p0_o.lower_bound[0]) + __k_12040));
        (v_BODY_12041_n__0_A = SISAL_CAST(sisal_array_t, v_FORALL_12038_n__0_A));
        (v_BODY_12041_n__0_J = SISAL_CAST(int32_t, v_GENERATOR_12040_n__2_J));
        (v_BODY_12041_n__0_MAX = SISAL_CAST(double, v_FORALL_12038_n__0_MAX));
        (v_BODY_12041_n__0_MAXS = SISAL_CAST(sisal_array_t, v_FORALL_12038_n__0_MAXS));
        (v_BODY_12041_n__0_ROW = SISAL_CAST(int32_t, v_FORALL_12038_n__0_ROW));
        (v_BODY_12041_n__0_X = SISAL_CAST(double, v_GENERATOR_12040_n__2_X));
        double v_BODY_12041_n__1_p0_o = 0;
        (v_BODY_12041_n__1_p0_o = SISAL_CAST(double, func__SABS__D__D(SISAL_CAST(double, v_BODY_12041_n__0_X))));
        bool v_BODY_12041_n__2_p0_o = 0;
        (v_BODY_12041_n__2_p0_o = SISAL_CAST(bool, (SISAL_CAST(double, v_BODY_12041_n__1_p0_o) == SISAL_CAST(double, v_BODY_12041_n__0_MAX))));
        if (v_BODY_12041_n__2_p0_o) {
          if ((SISAL_CAST(int32_t, v_BODY_12041_n__0_J) < v_LET_NON_REC_12033_n__3_p0_o)) {
            (v_LET_NON_REC_12033_n__3_p0_o = SISAL_CAST(int32_t, v_BODY_12041_n__0_J));
          }
        }
        (__g_12038++);
      }
    }
    (v_g2_n__1_p0_o = SISAL_CAST(int32_t, v_LET_NON_REC_12033_n__1_p0_o));
    (v_g2_n__1_p1_o = SISAL_CAST(int32_t, v_LET_NON_REC_12033_n__3_p0_o));
  }
  (v_g2_n__0_p0_i = SISAL_CAST(int32_t, v_g2_n__1_p0_o));
  (v_g2_n__0_p1_i = SISAL_CAST(int32_t, v_g2_n__1_p1_o));
  struct FUNC_INDEX_OF_MAX_results __res_obj;
  (__res_obj.res_0 = SISAL_CAST(int32_t, v_g2_n__0_p0_i));
  (__res_obj.res_1 = SISAL_CAST(int32_t, v_g2_n__0_p1_i));
  return __res_obj;
}

extern "C" struct FUNC_REDUCE_AND_MAX_results func_REDUCE_AND_MAX(sisal_array_t A, int32_t PIVOT, sisal_array_t PIVR, sisal_array_t B) {
  sisal_array_t v_g3_n__0_A = {0};
  sisal_array_t v_g3_n__0_B = {0};
  int32_t v_g3_n__0_PIVOT = 0;
  sisal_array_t v_g3_n__0_PIVR = {0};
  (v_g3_n__0_A = SISAL_CAST(sisal_array_t, A));
  (v_g3_n__0_PIVOT = SISAL_CAST(int32_t, PIVOT));
  (v_g3_n__0_PIVR = SISAL_CAST(sisal_array_t, PIVR));
  (v_g3_n__0_B = SISAL_CAST(sisal_array_t, B));
  sisal_array_t v_g3_n__0_p0_i = {0};
  sisal_array_t v_g3_n__0_p1_i = {0};
  double v_g3_n__0_p2_i = 0;
  sisal_array_t v_g3_n__0_p3_i = {0};
  sisal_array_t v_g3_n__1_p0_o = {0};
  sisal_array_t v_g3_n__1_p1_o = {0};
  double v_g3_n__1_p2_o = 0;
  sisal_array_t v_g3_n__1_p3_o = {0};
  {
    sisal_array_t v_FORALL_11010_n__0_A = v_g3_n__0_A;
    sisal_array_t v_FORALL_11010_n__0_B = v_g3_n__0_B;
    int32_t v_FORALL_11010_n__2_I;
    int32_t v_FORALL_11010_n__0_PIVOT = v_g3_n__0_PIVOT;
    sisal_array_t v_FORALL_11010_n__0_PIVR = v_g3_n__0_PIVR;
    sisal_array_t v_FORALL_11010_n__2_ROW;
    sisal_array_t v_FORALL_11010_n__3___forall_body_0;
    double v_FORALL_11010_n__3___forall_body_1;
    double v_FORALL_11010_n__3___forall_body_2;
    double v_FORALL_11010_n__3___forall_body_3;
    sisal_array_t v_GENERATOR_11012_n__0_A;
    sisal_array_t v_GENERATOR_11012_n__0_B;
    int32_t v_GENERATOR_11012_n__1_I;
    int32_t v_GENERATOR_11012_n__0_PIVOT;
    sisal_array_t v_GENERATOR_11012_n__0_PIVR;
    sisal_array_t v_GENERATOR_11012_n__1_ROW;
    sisal_array_t v_BODY_11013_n__0_A;
    sisal_array_t v_BODY_11013_n__0_B;
    int32_t v_BODY_11013_n__0_I;
    double v_BODY_11013_n__8_MAX;
    double v_BODY_11013_n__7_MULT;
    int32_t v_BODY_11013_n__0_PIVOT;
    sisal_array_t v_BODY_11013_n__0_PIVR;
    double v_BODY_11013_n__8_RB;
    sisal_array_t v_BODY_11013_n__0_ROW;
    sisal_array_t v_BODY_11013_n__8_RROW;
    sisal_array_t v_IF_DOUBLE__DOUBLE__array_dv_DOUBLE____11014_n__0_A;
    sisal_array_t v_IF_DOUBLE__DOUBLE__array_dv_DOUBLE____11014_n__0_B;
    int32_t v_IF_DOUBLE__DOUBLE__array_dv_DOUBLE____11014_n__0_I;
    double v_IF_DOUBLE__DOUBLE__array_dv_DOUBLE____11014_n__0_MULT;
    int32_t v_IF_DOUBLE__DOUBLE__array_dv_DOUBLE____11014_n__0_PIVOT;
    sisal_array_t v_IF_DOUBLE__DOUBLE__array_dv_DOUBLE____11014_n__0_PIVR;
    sisal_array_t v_IF_DOUBLE__DOUBLE__array_dv_DOUBLE____11014_n__0_ROW;
    int32_t v_PREDICATE_11015_n__0_I;
    int32_t v_PREDICATE_11015_n__0_PIVOT;
    sisal_array_t v_ELSE_11016_n__0_A;
    sisal_array_t v_ELSE_11016_n__0_B;
    int32_t v_ELSE_11016_n__0_I;
    double v_ELSE_11016_n__0_MULT;
    int32_t v_ELSE_11016_n__0_PIVOT;
    sisal_array_t v_ELSE_11016_n__0_PIVR;
    sisal_array_t v_ELSE_11016_n__0_ROW;
    int32_t v_PREDICATE_11017_n__0_I;
    sisal_array_t v_PREDICATE_11017_n__0_PIVR;
    sisal_array_t v_ELSE_11018_n__0_A;
    sisal_array_t v_ELSE_11018_n__0_B;
    int32_t v_ELSE_11018_n__0_I;
    double v_ELSE_11018_n__0_MULT;
    int32_t v_ELSE_11018_n__0_PIVOT;
    sisal_array_t v_ELSE_11018_n__0_PIVR;
    sisal_array_t v_ELSE_11018_n__0_ROW;
    sisal_array_t v_FORALL_11019_n__0_A;
    sisal_array_t v_FORALL_11019_n__0_B;
    int32_t v_FORALL_11019_n__0_I;
    int32_t v_FORALL_11019_n__2_J;
    double v_FORALL_11019_n__0_MULT;
    int32_t v_FORALL_11019_n__0_PIVOT;
    sisal_array_t v_FORALL_11019_n__0_PIVR;
    sisal_array_t v_FORALL_11019_n__0_ROW;
    double v_FORALL_11019_n__2_X;
    double v_FORALL_11019_n__3___forall_body_0;
    double v_FORALL_11019_n__3___forall_body_1;
    sisal_array_t v_GENERATOR_11021_n__0_A;
    sisal_array_t v_GENERATOR_11021_n__0_B;
    int32_t v_GENERATOR_11021_n__0_I;
    int32_t v_GENERATOR_11021_n__1_J;
    double v_GENERATOR_11021_n__0_MULT;
    int32_t v_GENERATOR_11021_n__0_PIVOT;
    sisal_array_t v_GENERATOR_11021_n__0_PIVR;
    sisal_array_t v_GENERATOR_11021_n__0_ROW;
    double v_GENERATOR_11021_n__1_X;
    sisal_array_t v_BODY_11022_n__0_A;
    sisal_array_t v_BODY_11022_n__0_B;
    int32_t v_BODY_11022_n__0_I;
    int32_t v_BODY_11022_n__0_J;
    double v_BODY_11022_n__0_MULT;
    int32_t v_BODY_11022_n__0_PIVOT;
    sisal_array_t v_BODY_11022_n__0_PIVR;
    sisal_array_t v_BODY_11022_n__0_ROW;
    double v_BODY_11022_n__4_RX;
    double v_BODY_11022_n__0_X;
    sisal_array_t v_THEN_11023_n__0_A;
    sisal_array_t v_THEN_11023_n__0_B;
    int32_t v_THEN_11023_n__0_I;
    double v_THEN_11023_n__0_MULT;
    int32_t v_THEN_11023_n__0_PIVOT;
    sisal_array_t v_THEN_11023_n__0_PIVR;
    sisal_array_t v_THEN_11023_n__0_ROW;
    sisal_array_t v_FORALL_11024_n__0_A;
    sisal_array_t v_FORALL_11024_n__0_B;
    int32_t v_FORALL_11024_n__0_I;
    int32_t v_FORALL_11024_n__2_J;
    double v_FORALL_11024_n__0_MULT;
    int32_t v_FORALL_11024_n__0_PIVOT;
    sisal_array_t v_FORALL_11024_n__0_PIVR;
    sisal_array_t v_FORALL_11024_n__0_ROW;
    double v_FORALL_11024_n__2_X;
    double v_FORALL_11024_n__3___forall_body_0;
    double v_FORALL_11024_n__3___forall_body_1;
    sisal_array_t v_GENERATOR_11026_n__0_A;
    sisal_array_t v_GENERATOR_11026_n__0_B;
    int32_t v_GENERATOR_11026_n__0_I;
    int32_t v_GENERATOR_11026_n__1_J;
    double v_GENERATOR_11026_n__0_MULT;
    int32_t v_GENERATOR_11026_n__0_PIVOT;
    sisal_array_t v_GENERATOR_11026_n__0_PIVR;
    sisal_array_t v_GENERATOR_11026_n__0_ROW;
    double v_GENERATOR_11026_n__1_X;
    sisal_array_t v_BODY_11027_n__0_A;
    sisal_array_t v_BODY_11027_n__0_B;
    int32_t v_BODY_11027_n__0_I;
    int32_t v_BODY_11027_n__0_J;
    double v_BODY_11027_n__0_MULT;
    int32_t v_BODY_11027_n__0_PIVOT;
    sisal_array_t v_BODY_11027_n__0_PIVR;
    sisal_array_t v_BODY_11027_n__0_ROW;
    double v_BODY_11027_n__0_X;
    sisal_array_t v_THEN_11028_n__0_A;
    sisal_array_t v_THEN_11028_n__0_B;
    int32_t v_THEN_11028_n__0_I;
    double v_THEN_11028_n__0_MULT;
    int32_t v_THEN_11028_n__0_PIVOT;
    sisal_array_t v_THEN_11028_n__0_PIVR;
    sisal_array_t v_THEN_11028_n__0_ROW;
    sisal_array_t v_FORALL_11029_n__0_A;
    sisal_array_t v_FORALL_11029_n__0_B;
    int32_t v_FORALL_11029_n__0_I;
    double v_FORALL_11029_n__0_MULT;
    int32_t v_FORALL_11029_n__0_PIVOT;
    sisal_array_t v_FORALL_11029_n__0_PIVR;
    sisal_array_t v_FORALL_11029_n__0_ROW;
    double v_FORALL_11029_n__2_X;
    double v_FORALL_11029_n__3___forall_body_0;
    double v_FORALL_11029_n__3___forall_body_1;
    sisal_array_t v_GENERATOR_11031_n__0_A;
    sisal_array_t v_GENERATOR_11031_n__0_B;
    int32_t v_GENERATOR_11031_n__0_I;
    double v_GENERATOR_11031_n__0_MULT;
    int32_t v_GENERATOR_11031_n__0_PIVOT;
    sisal_array_t v_GENERATOR_11031_n__0_PIVR;
    sisal_array_t v_GENERATOR_11031_n__0_ROW;
    double v_GENERATOR_11031_n__1_X;
    sisal_array_t v_BODY_11032_n__0_A;
    sisal_array_t v_BODY_11032_n__0_B;
    int32_t v_BODY_11032_n__0_I;
    double v_BODY_11032_n__0_MULT;
    int32_t v_BODY_11032_n__0_PIVOT;
    sisal_array_t v_BODY_11032_n__0_PIVR;
    sisal_array_t v_BODY_11032_n__0_ROW;
    double v_BODY_11032_n__0_X;
    (v_GENERATOR_11012_n__0_A = v_FORALL_11010_n__0_A);
    (v_g3_n__1_p0_o = sisal_array_alloc_sized(1, 95, ((uint64_t)(1 * ((int32_t)v_GENERATOR_11012_n__0_A.dims[0]))), sizeof(sisal_array_t)));
    (v_g3_n__1_p0_o.dims[0] = ((int32_t)v_GENERATOR_11012_n__0_A.dims[0]));
    (v_g3_n__1_p0_o.lower_bound[0] = 1);
    (v_g3_n__1_p1_o = sisal_array_alloc_empty(1, 4, ((uint64_t)(1 * ((int32_t)v_GENERATOR_11012_n__0_A.dims[0])))));
    (v_g3_n__1_p1_o.dims[0] = ((int32_t)v_GENERATOR_11012_n__0_A.dims[0]));
    (v_g3_n__1_p1_o.lower_bound[0] = 1);
    (v_g3_n__1_p2_o = (-1e308));
    (v_g3_n__1_p3_o = sisal_array_alloc_empty(1, 4, ((uint64_t)(1 * ((int32_t)v_GENERATOR_11012_n__0_A.dims[0])))));
    (v_g3_n__1_p3_o.dims[0] = ((int32_t)v_GENERATOR_11012_n__0_A.dims[0]));
    (v_g3_n__1_p3_o.lower_bound[0] = 1);
    int32_t __g_11010 = 0;
    for (int32_t __k_11012 = 0; (__k_11012 < ((int32_t)v_GENERATOR_11012_n__0_A.dims[0])); (__k_11012++)) {
      (v_GENERATOR_11012_n__1_ROW = sisal_array_get_row(v_GENERATOR_11012_n__0_A, __k_11012));
      (v_GENERATOR_11012_n__1_I = (((int32_t)v_GENERATOR_11012_n__0_A.lower_bound[0]) + __k_11012));
      (v_BODY_11013_n__0_A = SISAL_CAST(sisal_array_t, v_FORALL_11010_n__0_A));
      (v_BODY_11013_n__0_B = SISAL_CAST(sisal_array_t, v_FORALL_11010_n__0_B));
      (v_BODY_11013_n__0_I = SISAL_CAST(int32_t, v_GENERATOR_11012_n__1_I));
      (v_BODY_11013_n__0_PIVOT = SISAL_CAST(int32_t, v_FORALL_11010_n__0_PIVOT));
      (v_BODY_11013_n__0_PIVR = SISAL_CAST(sisal_array_t, v_FORALL_11010_n__0_PIVR));
      (v_BODY_11013_n__0_ROW = SISAL_CAST(sisal_array_t, v_GENERATOR_11012_n__1_ROW));
      sisal_array_t v_BODY_11013_n__1_p0_o = {0};
      (v_BODY_11013_n__1_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_BODY_11013_n__0_A), (SISAL_CAST(int32_t, v_BODY_11013_n__0_I) - SISAL_CAST(sisal_array_t, v_BODY_11013_n__0_A).lower_bound[0]))));
      float v_BODY_11013_n__2_p0_o = 0;
      (v_BODY_11013_n__2_p0_o = SISAL_CAST(float, ((float *)SISAL_CAST(sisal_array_t, v_BODY_11013_n__1_p0_o).data)[(SISAL_CAST(int32_t, v_BODY_11013_n__0_PIVOT) - SISAL_CAST(sisal_array_t, v_BODY_11013_n__1_p0_o).lower_bound[0])]));
      sisal_array_t v_BODY_11013_n__3_p0_o = {0};
      (v_BODY_11013_n__3_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_BODY_11013_n__0_A), (SISAL_CAST(int32_t, v_BODY_11013_n__0_I) - SISAL_CAST(sisal_array_t, v_BODY_11013_n__0_A).lower_bound[0]))));
      double v_BODY_11013_n__4_p0_o = 0;
      (v_BODY_11013_n__4_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_11013_n__3_p0_o).data)[(SISAL_CAST(int32_t, v_BODY_11013_n__0_PIVOT) - SISAL_CAST(sisal_array_t, v_BODY_11013_n__3_p0_o).lower_bound[0])]));
      sisal_array_t v_BODY_11013_n__5_p0_o = {0};
      (v_BODY_11013_n__5_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_BODY_11013_n__0_A), (SISAL_CAST(int32_t, v_BODY_11013_n__0_PIVOT) - SISAL_CAST(sisal_array_t, v_BODY_11013_n__0_A).lower_bound[0]))));
      double v_BODY_11013_n__6_p0_o = 0;
      (v_BODY_11013_n__6_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_11013_n__5_p0_o).data)[(SISAL_CAST(int32_t, v_BODY_11013_n__0_PIVOT) - SISAL_CAST(sisal_array_t, v_BODY_11013_n__5_p0_o).lower_bound[0])]));
      (v_BODY_11013_n__7_MULT = SISAL_CAST(double, (SISAL_CAST(double, v_BODY_11013_n__4_p0_o) / SISAL_CAST(double, v_BODY_11013_n__6_p0_o))));
      (v_IF_DOUBLE__DOUBLE__array_dv_DOUBLE____11014_n__0_I = SISAL_CAST(int32_t, v_BODY_11013_n__0_I));
      (v_IF_DOUBLE__DOUBLE__array_dv_DOUBLE____11014_n__0_PIVOT = SISAL_CAST(int32_t, v_BODY_11013_n__0_PIVOT));
      (v_IF_DOUBLE__DOUBLE__array_dv_DOUBLE____11014_n__0_PIVR = SISAL_CAST(sisal_array_t, v_BODY_11013_n__0_PIVR));
      (v_IF_DOUBLE__DOUBLE__array_dv_DOUBLE____11014_n__0_A = SISAL_CAST(sisal_array_t, v_BODY_11013_n__0_A));
      (v_IF_DOUBLE__DOUBLE__array_dv_DOUBLE____11014_n__0_B = SISAL_CAST(sisal_array_t, v_BODY_11013_n__0_B));
      (v_IF_DOUBLE__DOUBLE__array_dv_DOUBLE____11014_n__0_MULT = SISAL_CAST(double, v_BODY_11013_n__7_MULT));
      (v_IF_DOUBLE__DOUBLE__array_dv_DOUBLE____11014_n__0_ROW = SISAL_CAST(sisal_array_t, v_BODY_11013_n__0_ROW));
      {
        (v_PREDICATE_11015_n__0_I = SISAL_CAST(int32_t, v_IF_DOUBLE__DOUBLE__array_dv_DOUBLE____11014_n__0_I));
        (v_PREDICATE_11015_n__0_PIVOT = SISAL_CAST(int32_t, v_IF_DOUBLE__DOUBLE__array_dv_DOUBLE____11014_n__0_PIVOT));
        bool v_PREDICATE_11015_n__1_p0_o = 0;
        (v_PREDICATE_11015_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_PREDICATE_11015_n__0_I) == SISAL_CAST(int32_t, v_PREDICATE_11015_n__0_PIVOT))));
        if (v_PREDICATE_11015_n__1_p0_o) {
          (v_THEN_11028_n__0_A = SISAL_CAST(sisal_array_t, v_IF_DOUBLE__DOUBLE__array_dv_DOUBLE____11014_n__0_A));
          (v_THEN_11028_n__0_B = SISAL_CAST(sisal_array_t, v_IF_DOUBLE__DOUBLE__array_dv_DOUBLE____11014_n__0_B));
          (v_THEN_11028_n__0_I = SISAL_CAST(int32_t, v_IF_DOUBLE__DOUBLE__array_dv_DOUBLE____11014_n__0_I));
          (v_THEN_11028_n__0_MULT = SISAL_CAST(double, v_IF_DOUBLE__DOUBLE__array_dv_DOUBLE____11014_n__0_MULT));
          (v_THEN_11028_n__0_PIVOT = SISAL_CAST(int32_t, v_IF_DOUBLE__DOUBLE__array_dv_DOUBLE____11014_n__0_PIVOT));
          (v_THEN_11028_n__0_PIVR = SISAL_CAST(sisal_array_t, v_IF_DOUBLE__DOUBLE__array_dv_DOUBLE____11014_n__0_PIVR));
          (v_THEN_11028_n__0_ROW = SISAL_CAST(sisal_array_t, v_IF_DOUBLE__DOUBLE__array_dv_DOUBLE____11014_n__0_ROW));
          sisal_array_t v_THEN_11028_n__1_p0_o = {0};
          double v_THEN_11028_n__1_p1_o = 0;
          {
            sisal_array_t v_FORALL_11029_n__0_A = v_THEN_11028_n__0_A;
            sisal_array_t v_FORALL_11029_n__0_B = v_THEN_11028_n__0_B;
            int32_t v_FORALL_11029_n__0_I = v_THEN_11028_n__0_I;
            double v_FORALL_11029_n__0_MULT = v_THEN_11028_n__0_MULT;
            int32_t v_FORALL_11029_n__0_PIVOT = v_THEN_11028_n__0_PIVOT;
            sisal_array_t v_FORALL_11029_n__0_PIVR = v_THEN_11028_n__0_PIVR;
            sisal_array_t v_FORALL_11029_n__0_ROW = v_THEN_11028_n__0_ROW;
            double v_FORALL_11029_n__2_X;
            double v_FORALL_11029_n__3___forall_body_0;
            double v_FORALL_11029_n__3___forall_body_1;
            sisal_array_t v_GENERATOR_11031_n__0_A;
            sisal_array_t v_GENERATOR_11031_n__0_B;
            int32_t v_GENERATOR_11031_n__0_I;
            double v_GENERATOR_11031_n__0_MULT;
            int32_t v_GENERATOR_11031_n__0_PIVOT;
            sisal_array_t v_GENERATOR_11031_n__0_PIVR;
            sisal_array_t v_GENERATOR_11031_n__0_ROW;
            double v_GENERATOR_11031_n__1_X;
            sisal_array_t v_BODY_11032_n__0_A;
            sisal_array_t v_BODY_11032_n__0_B;
            int32_t v_BODY_11032_n__0_I;
            double v_BODY_11032_n__0_MULT;
            int32_t v_BODY_11032_n__0_PIVOT;
            sisal_array_t v_BODY_11032_n__0_PIVR;
            sisal_array_t v_BODY_11032_n__0_ROW;
            double v_BODY_11032_n__0_X;
            (v_GENERATOR_11031_n__0_ROW = v_FORALL_11029_n__0_ROW);
            (v_THEN_11028_n__1_p0_o = sisal_array_alloc_empty(1, 4, ((uint64_t)(1 * ((int32_t)v_GENERATOR_11031_n__0_ROW.dims[0])))));
            (v_THEN_11028_n__1_p0_o.dims[0] = ((int32_t)v_GENERATOR_11031_n__0_ROW.dims[0]));
            (v_THEN_11028_n__1_p0_o.lower_bound[0] = 1);
            int32_t __g_11029 = 0;
            for (int32_t __k_11031 = 0; (__k_11031 < ((int32_t)v_GENERATOR_11031_n__0_ROW.size)); (__k_11031++)) {
              (v_GENERATOR_11031_n__1_X = ((double *)v_GENERATOR_11031_n__0_ROW.data)[__k_11031]);
              (v_BODY_11032_n__0_A = SISAL_CAST(sisal_array_t, v_FORALL_11029_n__0_A));
              (v_BODY_11032_n__0_B = SISAL_CAST(sisal_array_t, v_FORALL_11029_n__0_B));
              (v_BODY_11032_n__0_I = SISAL_CAST(int32_t, v_FORALL_11029_n__0_I));
              (v_BODY_11032_n__0_MULT = SISAL_CAST(double, v_FORALL_11029_n__0_MULT));
              (v_BODY_11032_n__0_PIVOT = SISAL_CAST(int32_t, v_FORALL_11029_n__0_PIVOT));
              (v_BODY_11032_n__0_PIVR = SISAL_CAST(sisal_array_t, v_FORALL_11029_n__0_PIVR));
              (v_BODY_11032_n__0_ROW = SISAL_CAST(sisal_array_t, v_FORALL_11029_n__0_ROW));
              (v_BODY_11032_n__0_X = SISAL_CAST(double, v_GENERATOR_11031_n__1_X));
              sisal_array_t v_BODY_11032_n__1_p0_o = {0};
              (v_BODY_11032_n__1_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_BODY_11032_n__0_A), (SISAL_CAST(int32_t, v_BODY_11032_n__0_PIVOT) - SISAL_CAST(sisal_array_t, v_BODY_11032_n__0_A).lower_bound[0]))));
              double v_BODY_11032_n__2_p0_o = 0;
              (v_BODY_11032_n__2_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_11032_n__1_p0_o).data)[(SISAL_CAST(int32_t, v_BODY_11032_n__0_PIVOT) - SISAL_CAST(sisal_array_t, v_BODY_11032_n__1_p0_o).lower_bound[0])]));
              double v_BODY_11032_n__3_p0_o = 0;
              (v_BODY_11032_n__3_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_BODY_11032_n__0_X) / SISAL_CAST(double, v_BODY_11032_n__2_p0_o))));
              double v_BODY_11032_n__4_p0_o = 0;
              (v_BODY_11032_n__4_p0_o = SISAL_CAST(double, 0.f));
              (((double *)v_THEN_11028_n__1_p0_o.data)[__g_11029] = SISAL_CAST(double, v_BODY_11032_n__3_p0_o));
              (v_THEN_11028_n__1_p1_o = SISAL_CAST(double, v_BODY_11032_n__4_p0_o));
              (__g_11029++);
            }
          }
          float v_THEN_11028_n__3_p0_o = 0;
          (v_THEN_11028_n__3_p0_o = SISAL_CAST(float, ((float *)SISAL_CAST(sisal_array_t, v_THEN_11028_n__0_B).data)[(SISAL_CAST(int32_t, v_THEN_11028_n__0_I) - SISAL_CAST(sisal_array_t, v_THEN_11028_n__0_B).lower_bound[0])]));
          double v_THEN_11028_n__4_p0_o = 0;
          (v_THEN_11028_n__4_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_THEN_11028_n__0_B).data)[(SISAL_CAST(int32_t, v_THEN_11028_n__0_I) - SISAL_CAST(sisal_array_t, v_THEN_11028_n__0_B).lower_bound[0])]));
          sisal_array_t v_THEN_11028_n__5_p0_o = {0};
          (v_THEN_11028_n__5_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_THEN_11028_n__0_A), (SISAL_CAST(int32_t, v_THEN_11028_n__0_PIVOT) - SISAL_CAST(sisal_array_t, v_THEN_11028_n__0_A).lower_bound[0]))));
          double v_THEN_11028_n__6_p0_o = 0;
          (v_THEN_11028_n__6_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_THEN_11028_n__5_p0_o).data)[(SISAL_CAST(int32_t, v_THEN_11028_n__0_PIVOT) - SISAL_CAST(sisal_array_t, v_THEN_11028_n__5_p0_o).lower_bound[0])]));
          double v_THEN_11028_n__7_p0_o = 0;
          (v_THEN_11028_n__7_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_THEN_11028_n__4_p0_o) / SISAL_CAST(double, v_THEN_11028_n__6_p0_o))));
          (v_BODY_11013_n__8_RROW = SISAL_CAST(sisal_array_t, v_THEN_11028_n__1_p0_o));
          (v_BODY_11013_n__8_MAX = SISAL_CAST(double, v_THEN_11028_n__1_p1_o));
          (v_BODY_11013_n__8_RB = SISAL_CAST(double, v_THEN_11028_n__7_p0_o));
        }
        else {
          (v_ELSE_11016_n__0_PIVR = SISAL_CAST(sisal_array_t, v_IF_DOUBLE__DOUBLE__array_dv_DOUBLE____11014_n__0_PIVR));
          (v_ELSE_11016_n__0_I = SISAL_CAST(int32_t, v_IF_DOUBLE__DOUBLE__array_dv_DOUBLE____11014_n__0_I));
          (v_ELSE_11016_n__0_A = SISAL_CAST(sisal_array_t, v_IF_DOUBLE__DOUBLE__array_dv_DOUBLE____11014_n__0_A));
          (v_ELSE_11016_n__0_B = SISAL_CAST(sisal_array_t, v_IF_DOUBLE__DOUBLE__array_dv_DOUBLE____11014_n__0_B));
          (v_ELSE_11016_n__0_MULT = SISAL_CAST(double, v_IF_DOUBLE__DOUBLE__array_dv_DOUBLE____11014_n__0_MULT));
          (v_ELSE_11016_n__0_PIVOT = SISAL_CAST(int32_t, v_IF_DOUBLE__DOUBLE__array_dv_DOUBLE____11014_n__0_PIVOT));
          (v_ELSE_11016_n__0_ROW = SISAL_CAST(sisal_array_t, v_IF_DOUBLE__DOUBLE__array_dv_DOUBLE____11014_n__0_ROW));
          {
            (v_PREDICATE_11017_n__0_PIVR = SISAL_CAST(sisal_array_t, v_ELSE_11016_n__0_PIVR));
            (v_PREDICATE_11017_n__0_I = SISAL_CAST(int32_t, v_ELSE_11016_n__0_I));
            int32_t v_PREDICATE_11017_n__1_p0_o = 0;
            (v_PREDICATE_11017_n__1_p0_o = SISAL_CAST(int32_t, ((int32_t *)SISAL_CAST(sisal_array_t, v_PREDICATE_11017_n__0_PIVR).data)[(SISAL_CAST(int32_t, v_PREDICATE_11017_n__0_I) - SISAL_CAST(sisal_array_t, v_PREDICATE_11017_n__0_PIVR).lower_bound[0])]));
            int32_t v_PREDICATE_11017_n__2_p0_o = 0;
            (v_PREDICATE_11017_n__2_p0_o = SISAL_CAST(int32_t, 1));
            bool v_PREDICATE_11017_n__3_p0_o = 0;
            (v_PREDICATE_11017_n__3_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_PREDICATE_11017_n__1_p0_o) == SISAL_CAST(int32_t, v_PREDICATE_11017_n__2_p0_o))));
            if (v_PREDICATE_11017_n__3_p0_o) {
              (v_THEN_11023_n__0_A = SISAL_CAST(sisal_array_t, v_ELSE_11016_n__0_A));
              (v_THEN_11023_n__0_B = SISAL_CAST(sisal_array_t, v_ELSE_11016_n__0_B));
              (v_THEN_11023_n__0_I = SISAL_CAST(int32_t, v_ELSE_11016_n__0_I));
              (v_THEN_11023_n__0_MULT = SISAL_CAST(double, v_ELSE_11016_n__0_MULT));
              (v_THEN_11023_n__0_PIVOT = SISAL_CAST(int32_t, v_ELSE_11016_n__0_PIVOT));
              (v_THEN_11023_n__0_PIVR = SISAL_CAST(sisal_array_t, v_ELSE_11016_n__0_PIVR));
              (v_THEN_11023_n__0_ROW = SISAL_CAST(sisal_array_t, v_ELSE_11016_n__0_ROW));
              sisal_array_t v_THEN_11023_n__1_p0_o = {0};
              double v_THEN_11023_n__1_p1_o = 0;
              {
                sisal_array_t v_FORALL_11024_n__0_A = v_THEN_11023_n__0_A;
                sisal_array_t v_FORALL_11024_n__0_B = v_THEN_11023_n__0_B;
                int32_t v_FORALL_11024_n__0_I = v_THEN_11023_n__0_I;
                int32_t v_FORALL_11024_n__2_J;
                double v_FORALL_11024_n__0_MULT = v_THEN_11023_n__0_MULT;
                int32_t v_FORALL_11024_n__0_PIVOT = v_THEN_11023_n__0_PIVOT;
                sisal_array_t v_FORALL_11024_n__0_PIVR = v_THEN_11023_n__0_PIVR;
                sisal_array_t v_FORALL_11024_n__0_ROW = v_THEN_11023_n__0_ROW;
                double v_FORALL_11024_n__2_X;
                double v_FORALL_11024_n__3___forall_body_0;
                double v_FORALL_11024_n__3___forall_body_1;
                sisal_array_t v_GENERATOR_11026_n__0_A;
                sisal_array_t v_GENERATOR_11026_n__0_B;
                int32_t v_GENERATOR_11026_n__0_I;
                int32_t v_GENERATOR_11026_n__1_J;
                double v_GENERATOR_11026_n__0_MULT;
                int32_t v_GENERATOR_11026_n__0_PIVOT;
                sisal_array_t v_GENERATOR_11026_n__0_PIVR;
                sisal_array_t v_GENERATOR_11026_n__0_ROW;
                double v_GENERATOR_11026_n__1_X;
                sisal_array_t v_BODY_11027_n__0_A;
                sisal_array_t v_BODY_11027_n__0_B;
                int32_t v_BODY_11027_n__0_I;
                int32_t v_BODY_11027_n__0_J;
                double v_BODY_11027_n__0_MULT;
                int32_t v_BODY_11027_n__0_PIVOT;
                sisal_array_t v_BODY_11027_n__0_PIVR;
                sisal_array_t v_BODY_11027_n__0_ROW;
                double v_BODY_11027_n__0_X;
                (v_GENERATOR_11026_n__0_ROW = v_FORALL_11024_n__0_ROW);
                (v_THEN_11023_n__1_p0_o = sisal_array_alloc_empty(1, 4, ((uint64_t)(1 * ((int32_t)v_GENERATOR_11026_n__0_ROW.dims[0])))));
                (v_THEN_11023_n__1_p0_o.dims[0] = ((int32_t)v_GENERATOR_11026_n__0_ROW.dims[0]));
                (v_THEN_11023_n__1_p0_o.lower_bound[0] = 1);
                int32_t __g_11024 = 0;
                for (int32_t __k_11026 = 0; (__k_11026 < ((int32_t)v_GENERATOR_11026_n__0_ROW.size)); (__k_11026++)) {
                  (v_GENERATOR_11026_n__1_X = ((double *)v_GENERATOR_11026_n__0_ROW.data)[__k_11026]);
                  (v_GENERATOR_11026_n__1_J = (((int32_t)v_GENERATOR_11026_n__0_ROW.lower_bound[0]) + __k_11026));
                  (v_BODY_11027_n__0_A = SISAL_CAST(sisal_array_t, v_FORALL_11024_n__0_A));
                  (v_BODY_11027_n__0_B = SISAL_CAST(sisal_array_t, v_FORALL_11024_n__0_B));
                  (v_BODY_11027_n__0_I = SISAL_CAST(int32_t, v_FORALL_11024_n__0_I));
                  (v_BODY_11027_n__0_J = SISAL_CAST(int32_t, v_GENERATOR_11026_n__1_J));
                  (v_BODY_11027_n__0_MULT = SISAL_CAST(double, v_FORALL_11024_n__0_MULT));
                  (v_BODY_11027_n__0_PIVOT = SISAL_CAST(int32_t, v_FORALL_11024_n__0_PIVOT));
                  (v_BODY_11027_n__0_PIVR = SISAL_CAST(sisal_array_t, v_FORALL_11024_n__0_PIVR));
                  (v_BODY_11027_n__0_ROW = SISAL_CAST(sisal_array_t, v_FORALL_11024_n__0_ROW));
                  (v_BODY_11027_n__0_X = SISAL_CAST(double, v_GENERATOR_11026_n__1_X));
                  sisal_array_t v_BODY_11027_n__1_p0_o = {0};
                  (v_BODY_11027_n__1_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_BODY_11027_n__0_A), (SISAL_CAST(int32_t, v_BODY_11027_n__0_PIVOT) - SISAL_CAST(sisal_array_t, v_BODY_11027_n__0_A).lower_bound[0]))));
                  double v_BODY_11027_n__2_p0_o = 0;
                  (v_BODY_11027_n__2_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_11027_n__1_p0_o).data)[(SISAL_CAST(int32_t, v_BODY_11027_n__0_J) - SISAL_CAST(sisal_array_t, v_BODY_11027_n__1_p0_o).lower_bound[0])]));
                  double v_BODY_11027_n__3_p0_o = 0;
                  (v_BODY_11027_n__3_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_BODY_11027_n__0_MULT) * SISAL_CAST(double, v_BODY_11027_n__2_p0_o))));
                  double v_BODY_11027_n__4_p0_o = 0;
                  (v_BODY_11027_n__4_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_BODY_11027_n__0_X) - SISAL_CAST(double, v_BODY_11027_n__3_p0_o))));
                  double v_BODY_11027_n__5_p0_o = 0;
                  (v_BODY_11027_n__5_p0_o = SISAL_CAST(double, 0.f));
                  (((double *)v_THEN_11023_n__1_p0_o.data)[__g_11024] = SISAL_CAST(double, v_BODY_11027_n__4_p0_o));
                  (v_THEN_11023_n__1_p1_o = SISAL_CAST(double, v_BODY_11027_n__5_p0_o));
                  (__g_11024++);
                }
              }
              double v_THEN_11023_n__3_p0_o = 0;
              (v_THEN_11023_n__3_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_THEN_11023_n__0_B).data)[(SISAL_CAST(int32_t, v_THEN_11023_n__0_I) - SISAL_CAST(sisal_array_t, v_THEN_11023_n__0_B).lower_bound[0])]));
              double v_THEN_11023_n__4_p0_o = 0;
              (v_THEN_11023_n__4_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_THEN_11023_n__0_B).data)[(SISAL_CAST(int32_t, v_THEN_11023_n__0_PIVOT) - SISAL_CAST(sisal_array_t, v_THEN_11023_n__0_B).lower_bound[0])]));
              double v_THEN_11023_n__5_p0_o = 0;
              (v_THEN_11023_n__5_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_THEN_11023_n__0_MULT) * SISAL_CAST(double, v_THEN_11023_n__4_p0_o))));
              double v_THEN_11023_n__6_p0_o = 0;
              (v_THEN_11023_n__6_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_THEN_11023_n__3_p0_o) - SISAL_CAST(double, v_THEN_11023_n__5_p0_o))));
              (v_BODY_11013_n__8_RROW = SISAL_CAST(sisal_array_t, v_THEN_11023_n__1_p0_o));
              (v_BODY_11013_n__8_MAX = SISAL_CAST(double, v_THEN_11023_n__1_p1_o));
              (v_BODY_11013_n__8_RB = SISAL_CAST(double, v_THEN_11023_n__6_p0_o));
            }
            else {
              (v_ELSE_11018_n__0_A = SISAL_CAST(sisal_array_t, v_ELSE_11016_n__0_A));
              (v_ELSE_11018_n__0_B = SISAL_CAST(sisal_array_t, v_ELSE_11016_n__0_B));
              (v_ELSE_11018_n__0_I = SISAL_CAST(int32_t, v_ELSE_11016_n__0_I));
              (v_ELSE_11018_n__0_MULT = SISAL_CAST(double, v_ELSE_11016_n__0_MULT));
              (v_ELSE_11018_n__0_PIVOT = SISAL_CAST(int32_t, v_ELSE_11016_n__0_PIVOT));
              (v_ELSE_11018_n__0_PIVR = SISAL_CAST(sisal_array_t, v_ELSE_11016_n__0_PIVR));
              (v_ELSE_11018_n__0_ROW = SISAL_CAST(sisal_array_t, v_ELSE_11016_n__0_ROW));
              sisal_array_t v_ELSE_11018_n__1_p0_o = {0};
              double v_ELSE_11018_n__1_p1_o = 0;
              {
                sisal_array_t v_FORALL_11019_n__0_A = v_ELSE_11018_n__0_A;
                sisal_array_t v_FORALL_11019_n__0_B = v_ELSE_11018_n__0_B;
                int32_t v_FORALL_11019_n__0_I = v_ELSE_11018_n__0_I;
                int32_t v_FORALL_11019_n__2_J;
                double v_FORALL_11019_n__0_MULT = v_ELSE_11018_n__0_MULT;
                int32_t v_FORALL_11019_n__0_PIVOT = v_ELSE_11018_n__0_PIVOT;
                sisal_array_t v_FORALL_11019_n__0_PIVR = v_ELSE_11018_n__0_PIVR;
                sisal_array_t v_FORALL_11019_n__0_ROW = v_ELSE_11018_n__0_ROW;
                double v_FORALL_11019_n__2_X;
                double v_FORALL_11019_n__3___forall_body_0;
                double v_FORALL_11019_n__3___forall_body_1;
                sisal_array_t v_GENERATOR_11021_n__0_A;
                sisal_array_t v_GENERATOR_11021_n__0_B;
                int32_t v_GENERATOR_11021_n__0_I;
                int32_t v_GENERATOR_11021_n__1_J;
                double v_GENERATOR_11021_n__0_MULT;
                int32_t v_GENERATOR_11021_n__0_PIVOT;
                sisal_array_t v_GENERATOR_11021_n__0_PIVR;
                sisal_array_t v_GENERATOR_11021_n__0_ROW;
                double v_GENERATOR_11021_n__1_X;
                sisal_array_t v_BODY_11022_n__0_A;
                sisal_array_t v_BODY_11022_n__0_B;
                int32_t v_BODY_11022_n__0_I;
                int32_t v_BODY_11022_n__0_J;
                double v_BODY_11022_n__0_MULT;
                int32_t v_BODY_11022_n__0_PIVOT;
                sisal_array_t v_BODY_11022_n__0_PIVR;
                sisal_array_t v_BODY_11022_n__0_ROW;
                double v_BODY_11022_n__4_RX;
                double v_BODY_11022_n__0_X;
                (v_GENERATOR_11021_n__0_ROW = v_FORALL_11019_n__0_ROW);
                (v_ELSE_11018_n__1_p0_o = sisal_array_alloc_empty(1, 4, ((uint64_t)(1 * ((int32_t)v_GENERATOR_11021_n__0_ROW.dims[0])))));
                (v_ELSE_11018_n__1_p0_o.dims[0] = ((int32_t)v_GENERATOR_11021_n__0_ROW.dims[0]));
                (v_ELSE_11018_n__1_p0_o.lower_bound[0] = 1);
                (v_ELSE_11018_n__1_p1_o = (-1e308));
                int32_t __g_11019 = 0;
                for (int32_t __k_11021 = 0; (__k_11021 < ((int32_t)v_GENERATOR_11021_n__0_ROW.size)); (__k_11021++)) {
                  (v_GENERATOR_11021_n__1_X = ((double *)v_GENERATOR_11021_n__0_ROW.data)[__k_11021]);
                  (v_GENERATOR_11021_n__1_J = (((int32_t)v_GENERATOR_11021_n__0_ROW.lower_bound[0]) + __k_11021));
                  (v_BODY_11022_n__0_A = SISAL_CAST(sisal_array_t, v_FORALL_11019_n__0_A));
                  (v_BODY_11022_n__0_B = SISAL_CAST(sisal_array_t, v_FORALL_11019_n__0_B));
                  (v_BODY_11022_n__0_I = SISAL_CAST(int32_t, v_FORALL_11019_n__0_I));
                  (v_BODY_11022_n__0_J = SISAL_CAST(int32_t, v_GENERATOR_11021_n__1_J));
                  (v_BODY_11022_n__0_MULT = SISAL_CAST(double, v_FORALL_11019_n__0_MULT));
                  (v_BODY_11022_n__0_PIVOT = SISAL_CAST(int32_t, v_FORALL_11019_n__0_PIVOT));
                  (v_BODY_11022_n__0_PIVR = SISAL_CAST(sisal_array_t, v_FORALL_11019_n__0_PIVR));
                  (v_BODY_11022_n__0_ROW = SISAL_CAST(sisal_array_t, v_FORALL_11019_n__0_ROW));
                  (v_BODY_11022_n__0_X = SISAL_CAST(double, v_GENERATOR_11021_n__1_X));
                  sisal_array_t v_BODY_11022_n__1_p0_o = {0};
                  (v_BODY_11022_n__1_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_BODY_11022_n__0_A), (SISAL_CAST(int32_t, v_BODY_11022_n__0_PIVOT) - SISAL_CAST(sisal_array_t, v_BODY_11022_n__0_A).lower_bound[0]))));
                  double v_BODY_11022_n__2_p0_o = 0;
                  (v_BODY_11022_n__2_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_11022_n__1_p0_o).data)[(SISAL_CAST(int32_t, v_BODY_11022_n__0_J) - SISAL_CAST(sisal_array_t, v_BODY_11022_n__1_p0_o).lower_bound[0])]));
                  double v_BODY_11022_n__3_p0_o = 0;
                  (v_BODY_11022_n__3_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_BODY_11022_n__0_MULT) * SISAL_CAST(double, v_BODY_11022_n__2_p0_o))));
                  (v_BODY_11022_n__4_RX = SISAL_CAST(double, (SISAL_CAST(double, v_BODY_11022_n__0_X) - SISAL_CAST(double, v_BODY_11022_n__3_p0_o))));
                  double v_BODY_11022_n__5_p0_o = 0;
                  (v_BODY_11022_n__5_p0_o = SISAL_CAST(double, func__SABS__D__D(SISAL_CAST(double, v_BODY_11022_n__4_RX))));
                  (((double *)v_ELSE_11018_n__1_p0_o.data)[__g_11019] = SISAL_CAST(double, v_BODY_11022_n__4_RX));
                  if ((SISAL_CAST(double, v_BODY_11022_n__5_p0_o) > v_ELSE_11018_n__1_p1_o)) {
                    (v_ELSE_11018_n__1_p1_o = SISAL_CAST(double, v_BODY_11022_n__5_p0_o));
                  }
                  (__g_11019++);
                }
              }
              double v_ELSE_11018_n__3_p0_o = 0;
              (v_ELSE_11018_n__3_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_ELSE_11018_n__0_B).data)[(SISAL_CAST(int32_t, v_ELSE_11018_n__0_I) - SISAL_CAST(sisal_array_t, v_ELSE_11018_n__0_B).lower_bound[0])]));
              double v_ELSE_11018_n__4_p0_o = 0;
              (v_ELSE_11018_n__4_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_ELSE_11018_n__0_B).data)[(SISAL_CAST(int32_t, v_ELSE_11018_n__0_PIVOT) - SISAL_CAST(sisal_array_t, v_ELSE_11018_n__0_B).lower_bound[0])]));
              double v_ELSE_11018_n__5_p0_o = 0;
              (v_ELSE_11018_n__5_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_ELSE_11018_n__0_MULT) * SISAL_CAST(double, v_ELSE_11018_n__4_p0_o))));
              double v_ELSE_11018_n__6_p0_o = 0;
              (v_ELSE_11018_n__6_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_ELSE_11018_n__3_p0_o) - SISAL_CAST(double, v_ELSE_11018_n__5_p0_o))));
              (v_BODY_11013_n__8_RROW = SISAL_CAST(sisal_array_t, v_ELSE_11018_n__1_p0_o));
              (v_BODY_11013_n__8_MAX = SISAL_CAST(double, v_ELSE_11018_n__1_p1_o));
              (v_BODY_11013_n__8_RB = SISAL_CAST(double, v_ELSE_11018_n__6_p0_o));
            }
          }
        }
      }
      (((sisal_array_t *)v_g3_n__1_p0_o.data)[__g_11010] = SISAL_CAST(sisal_array_t, v_BODY_11013_n__8_RROW));
      (((double *)v_g3_n__1_p1_o.data)[__g_11010] = SISAL_CAST(double, v_BODY_11013_n__8_RB));
      if ((SISAL_CAST(double, v_BODY_11013_n__8_MAX) > v_g3_n__1_p2_o)) {
        (v_g3_n__1_p2_o = SISAL_CAST(double, v_BODY_11013_n__8_MAX));
      }
      (((double *)v_g3_n__1_p3_o.data)[__g_11010] = SISAL_CAST(double, v_BODY_11013_n__8_MAX));
      (__g_11010++);
    }
    sisal_array_t __e0_v_g3_n__1_p0_o = ((sisal_array_t *)v_g3_n__1_p0_o.data)[0];
    sisal_array_t __flat_v_g3_n__1_p0_o = sisal_array_alloc_sized((1 + __e0_v_g3_n__1_p0_o.rank), __e0_v_g3_n__1_p0_o.type_id, ((uint64_t)(((uint64_t)(1 * ((int32_t)v_GENERATOR_11012_n__0_A.dims[0]))) * __e0_v_g3_n__1_p0_o.size)), sisal_esz(__e0_v_g3_n__1_p0_o));
    (__flat_v_g3_n__1_p0_o.dims[0] = ((int32_t)v_GENERATOR_11012_n__0_A.dims[0]));
    (__flat_v_g3_n__1_p0_o.lower_bound[0] = 1);
    for (int32_t __fk_v_g3_n__1_p0_o = 0; (__fk_v_g3_n__1_p0_o < __e0_v_g3_n__1_p0_o.rank); (__fk_v_g3_n__1_p0_o++)) {
      (__flat_v_g3_n__1_p0_o.dims[(1 + __fk_v_g3_n__1_p0_o)] = __e0_v_g3_n__1_p0_o.dims[__fk_v_g3_n__1_p0_o]);
      (__flat_v_g3_n__1_p0_o.lower_bound[(1 + __fk_v_g3_n__1_p0_o)] = __e0_v_g3_n__1_p0_o.lower_bound[__fk_v_g3_n__1_p0_o]);
    }
    for (int32_t __fi_v_g3_n__1_p0_o = 0; (__fi_v_g3_n__1_p0_o < ((int32_t)(1 * ((int32_t)v_GENERATOR_11012_n__0_A.dims[0])))); (__fi_v_g3_n__1_p0_o++)) {
      memcpy((((char *)__flat_v_g3_n__1_p0_o.data) + (((uint64_t)__fi_v_g3_n__1_p0_o) * (__e0_v_g3_n__1_p0_o.size * sisal_esz(__e0_v_g3_n__1_p0_o)))), ((sisal_array_t *)v_g3_n__1_p0_o.data)[__fi_v_g3_n__1_p0_o].data, (__e0_v_g3_n__1_p0_o.size * sisal_esz(__e0_v_g3_n__1_p0_o)));
    }
    (v_g3_n__1_p0_o = __flat_v_g3_n__1_p0_o);
  }
  int32_t v_g3_n__3_p0_o = 0;
  (v_g3_n__3_p0_o = SISAL_CAST(int32_t, ((int32_t)SISAL_CAST(sisal_array_t, v_g3_n__0_A).lower_bound[0])));
  sisal_array_t v_g3_n__4_p0_o = {0};
  (v_g3_n__4_p0_o = SISAL_CAST(sisal_array_t, sisal_array_setl(SISAL_CAST(sisal_array_t, v_g3_n__1_p0_o), ((int64_t)SISAL_CAST(int32_t, v_g3_n__3_p0_o)))));
  (v_g3_n__0_p0_i = SISAL_CAST(sisal_array_t, v_g3_n__4_p0_o));
  (v_g3_n__0_p1_i = SISAL_CAST(sisal_array_t, v_g3_n__1_p1_o));
  (v_g3_n__0_p2_i = SISAL_CAST(double, v_g3_n__1_p2_o));
  (v_g3_n__0_p3_i = SISAL_CAST(sisal_array_t, v_g3_n__1_p3_o));
  struct FUNC_REDUCE_AND_MAX_results __res_obj;
  (__res_obj.res_0 = SISAL_CAST(sisal_array_t, v_g3_n__0_p0_i));
  (__res_obj.res_1 = SISAL_CAST(sisal_array_t, v_g3_n__0_p1_i));
  (__res_obj.res_2 = SISAL_CAST(double, v_g3_n__0_p2_i));
  (__res_obj.res_3 = SISAL_CAST(sisal_array_t, v_g3_n__0_p3_i));
  return __res_obj;
}

extern "C" sisal_array_t func_MAIN(int32_t N, sisal_array_t AIN, sisal_array_t BIN) {
  sisal_array_t v_g4_n__0_AIN = {0};
  sisal_array_t v_g4_n__0_BIN = {0};
  int32_t v_g4_n__0_N = 0;
  (v_g4_n__0_N = SISAL_CAST(int32_t, N));
  (v_g4_n__0_AIN = SISAL_CAST(sisal_array_t, AIN));
  (v_g4_n__0_BIN = SISAL_CAST(sisal_array_t, BIN));
  sisal_array_t v_g4_n__0_p0_i = {0};
  sisal_array_t v_g4_n__1_p0_o = {0};
  {
    sisal_array_t v_LoopB_10001_n__5_MERGE_A = {0};
    sisal_array_t v_LoopB_10001_n__6_MERGE_B = {0};
    int32_t v_LoopB_10001_n__7_MERGE_COL = 0;
    int32_t v_LoopB_10001_n__8_MERGE_I = 0;
    double v_LoopB_10001_n__9_MERGE_MAX = 0;
    sisal_array_t v_LoopB_10001_n__10_MERGE_MAXS = {0};
    sisal_array_t v_LoopB_10001_n__11_MERGE_PIVR = {0};
    int32_t v_LoopB_10001_n__12_MERGE_ROW = 0;
    sisal_array_t v_LoopB_10001_n__13_MERGE_OLD_A = {0};
    sisal_array_t v_LoopB_10001_n__14_MERGE_OLD_B = {0};
    int32_t v_LoopB_10001_n__15_MERGE_OLD_COL = 0;
    int32_t v_LoopB_10001_n__16_MERGE_OLD_I = 0;
    double v_LoopB_10001_n__17_MERGE_OLD_MAX = 0;
    sisal_array_t v_LoopB_10001_n__18_MERGE_OLD_MAXS = {0};
    sisal_array_t v_LoopB_10001_n__19_MERGE_OLD_PIVR = {0};
    int32_t v_LoopB_10001_n__20_MERGE_OLD_ROW = 0;
    bool v_LoopB_10001_n__21_MERGE_first = 0;
    int32_t v_LoopB_10001_bodycap_n2_p0 = 0;
    sisal_array_t v_LoopB_10001_bodycap_n12_p0 = {0};
    sisal_array_t v_LoopB_10001_bodycap_n13_p0 = {0};
    sisal_array_t v_LoopB_10001_bodycap_n13_p1 = {0};
    double v_LoopB_10001_bodycap_n13_p2 = 0;
    sisal_array_t v_LoopB_10001_bodycap_n13_p3 = {0};
    int32_t v_LoopB_10001_bodycap_n15_p0 = 0;
    int32_t v_LoopB_10001_bodycap_n15_p1 = 0;
    bool v_LoopB_10001_bodycap_n17_p0 = 0;
    sisal_array_t v_LoopB_10001_n__0_AIN = {0};
    (v_LoopB_10001_n__0_AIN = SISAL_CAST(sisal_array_t, v_g4_n__0_AIN));
    sisal_array_t v_LoopB_10001_n__0_BIN = {0};
    (v_LoopB_10001_n__0_BIN = SISAL_CAST(sisal_array_t, v_g4_n__0_BIN));
    int32_t v_LoopB_10001_n__0_N = 0;
    (v_LoopB_10001_n__0_N = SISAL_CAST(int32_t, v_g4_n__0_N));
    sisal_array_t v_INIT_10005_n__0_A = {0};
    sisal_array_t v_INIT_10005_n__0_AIN = {0};
    sisal_array_t v_INIT_10005_n__0_B = {0};
    sisal_array_t v_INIT_10005_n__0_BIN = {0};
    int32_t v_INIT_10005_n__6_COL = 0;
    int32_t v_INIT_10005_n__1_I = 0;
    double v_INIT_10005_n__4_MAX = 0;
    sisal_array_t v_INIT_10005_n__4_MAXS = {0};
    int32_t v_INIT_10005_n__0_N = 0;
    sisal_array_t v_INIT_10005_n__0_OLD_A = {0};
    sisal_array_t v_INIT_10005_n__0_OLD_B = {0};
    int32_t v_INIT_10005_n__6_OLD_COL = 0;
    int32_t v_INIT_10005_n__1_OLD_I = 0;
    double v_INIT_10005_n__4_OLD_MAX = 0;
    sisal_array_t v_INIT_10005_n__4_OLD_MAXS = {0};
    sisal_array_t v_INIT_10005_n__2_OLD_PIVR = {0};
    int32_t v_INIT_10005_n__6_OLD_ROW = 0;
    sisal_array_t v_INIT_10005_n__2_PIVR = {0};
    int32_t v_INIT_10005_n__6_ROW = 0;
    (v_INIT_10005_n__0_OLD_A = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__0_AIN));
    (v_INIT_10005_n__0_OLD_B = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__0_BIN));
    (v_INIT_10005_n__0_N = SISAL_CAST(int32_t, v_LoopB_10001_n__0_N));
    (v_INIT_10005_n__1_OLD_I = SISAL_CAST(int32_t, 0));
    {
      sisal_array_t v_FORALL_10006_n__0_A = v_INIT_10005_n__0_OLD_A;
      sisal_array_t v_FORALL_10006_n__0_AIN = v_INIT_10005_n__0_OLD_A;
      sisal_array_t v_FORALL_10006_n__0_B = v_INIT_10005_n__0_OLD_B;
      sisal_array_t v_FORALL_10006_n__0_BIN = v_INIT_10005_n__0_OLD_B;
      int32_t v_FORALL_10006_n__0_I = v_INIT_10005_n__1_OLD_I;
      int32_t v_FORALL_10006_n__2_J;
      int32_t v_FORALL_10006_n__0_N = v_INIT_10005_n__0_N;
      int32_t v_FORALL_10006_n__3___forall_body_0;
      int32_t v_FORALL_10006_n__2___forall_lb_2_0;
      int32_t v_FORALL_10006_n__2___forall_ub_2_0;
      sisal_array_t v_GENERATOR_10008_n__0_A;
      sisal_array_t v_GENERATOR_10008_n__0_AIN;
      sisal_array_t v_GENERATOR_10008_n__0_B;
      sisal_array_t v_GENERATOR_10008_n__0_BIN;
      int32_t v_GENERATOR_10008_n__0_I;
      int32_t v_GENERATOR_10008_n__2_J;
      int32_t v_GENERATOR_10008_n__0_N;
      int32_t v_GENERATOR_10008_n__2___forall_lb_2_0;
      int32_t v_GENERATOR_10008_n__2___forall_ub_2_0;
      sisal_array_t v_BODY_10009_n__0_A;
      sisal_array_t v_BODY_10009_n__0_AIN;
      sisal_array_t v_BODY_10009_n__0_B;
      sisal_array_t v_BODY_10009_n__0_BIN;
      int32_t v_BODY_10009_n__0_I;
      int32_t v_BODY_10009_n__0_J;
      int32_t v_BODY_10009_n__0_N;
      int32_t v_BODY_10009_n__0___forall_lb_2_0;
      int32_t v_BODY_10009_n__0___forall_ub_2_0;
      (v_GENERATOR_10008_n__0_N = v_FORALL_10006_n__0_N);
      (v_GENERATOR_10008_n__2___forall_lb_2_0 = 1);
      (v_GENERATOR_10008_n__2___forall_ub_2_0 = v_GENERATOR_10008_n__0_N);
      (v_INIT_10005_n__2_OLD_PIVR = sisal_array_alloc_empty(1, 6, ((uint64_t)(1 * ((v_GENERATOR_10008_n__0_N - 1) + 1)))));
      (v_INIT_10005_n__2_OLD_PIVR.dims[0] = ((v_GENERATOR_10008_n__0_N - 1) + 1));
      (v_INIT_10005_n__2_OLD_PIVR.lower_bound[0] = 1);
      int32_t __g_10006 = 0;
      for ((v_GENERATOR_10008_n__2_J = 1); (v_GENERATOR_10008_n__2_J <= v_GENERATOR_10008_n__0_N); (v_GENERATOR_10008_n__2_J++)) {
        (v_BODY_10009_n__0_A = SISAL_CAST(sisal_array_t, v_FORALL_10006_n__0_A));
        (v_BODY_10009_n__0_AIN = SISAL_CAST(sisal_array_t, v_FORALL_10006_n__0_AIN));
        (v_BODY_10009_n__0_B = SISAL_CAST(sisal_array_t, v_FORALL_10006_n__0_B));
        (v_BODY_10009_n__0_BIN = SISAL_CAST(sisal_array_t, v_FORALL_10006_n__0_BIN));
        (v_BODY_10009_n__0_I = SISAL_CAST(int32_t, v_FORALL_10006_n__0_I));
        (v_BODY_10009_n__0_J = SISAL_CAST(int32_t, v_GENERATOR_10008_n__2_J));
        (v_BODY_10009_n__0_N = SISAL_CAST(int32_t, v_FORALL_10006_n__0_N));
        (v_BODY_10009_n__0___forall_lb_2_0 = SISAL_CAST(int32_t, v_GENERATOR_10008_n__2___forall_lb_2_0));
        (v_BODY_10009_n__0___forall_ub_2_0 = SISAL_CAST(int32_t, v_GENERATOR_10008_n__2___forall_ub_2_0));
        int32_t v_BODY_10009_n__1_p0_o = 0;
        (v_BODY_10009_n__1_p0_o = SISAL_CAST(int32_t, 0));
        (((int32_t *)v_INIT_10005_n__2_OLD_PIVR.data)[__g_10006] = SISAL_CAST(int32_t, v_BODY_10009_n__1_p0_o));
        (__g_10006++);
      }
    }
    struct FUNC_FINDMAX_results _mr_INIT_10005_4 = func_FINDMAX(SISAL_CAST(sisal_array_t, v_INIT_10005_n__0_OLD_A));
    (v_INIT_10005_n__4_OLD_MAX = SISAL_CAST(double, _mr_INIT_10005_4.res_0));
    (v_INIT_10005_n__4_OLD_MAXS = SISAL_CAST(sisal_array_t, _mr_INIT_10005_4.res_1));
    struct FUNC_INDEX_OF_MAX_results _mr_INIT_10005_6 = func_INDEX_OF_MAX(SISAL_CAST(double, v_INIT_10005_n__4_OLD_MAX), SISAL_CAST(sisal_array_t, v_INIT_10005_n__4_OLD_MAXS), SISAL_CAST(sisal_array_t, v_INIT_10005_n__0_OLD_A));
    (v_INIT_10005_n__6_ROW = SISAL_CAST(int32_t, _mr_INIT_10005_6.res_0));
    (v_INIT_10005_n__6_OLD_COL = SISAL_CAST(int32_t, _mr_INIT_10005_6.res_1));
    bool v_INIT_10005_n__8_p0_o = 0;
    (v_INIT_10005_n__8_p0_o = SISAL_CAST(bool, true));
    (v_LoopB_10001_n__5_MERGE_A = v_INIT_10005_n__0_OLD_A);
    (v_LoopB_10001_n__6_MERGE_B = v_INIT_10005_n__0_OLD_B);
    (v_LoopB_10001_n__7_MERGE_COL = v_INIT_10005_n__6_OLD_COL);
    (v_LoopB_10001_n__8_MERGE_I = v_INIT_10005_n__1_OLD_I);
    (v_LoopB_10001_n__9_MERGE_MAX = v_INIT_10005_n__4_OLD_MAX);
    (v_LoopB_10001_n__10_MERGE_MAXS = v_INIT_10005_n__4_OLD_MAXS);
    (v_LoopB_10001_n__11_MERGE_PIVR = v_INIT_10005_n__2_OLD_PIVR);
    (v_LoopB_10001_n__12_MERGE_ROW = v_INIT_10005_n__6_ROW);
    (v_LoopB_10001_n__13_MERGE_OLD_A = v_INIT_10005_n__0_OLD_A);
    (v_LoopB_10001_n__14_MERGE_OLD_B = v_INIT_10005_n__0_OLD_B);
    (v_LoopB_10001_n__15_MERGE_OLD_COL = v_INIT_10005_n__6_OLD_COL);
    (v_LoopB_10001_n__16_MERGE_OLD_I = v_INIT_10005_n__1_OLD_I);
    (v_LoopB_10001_n__17_MERGE_OLD_MAX = v_INIT_10005_n__4_OLD_MAX);
    (v_LoopB_10001_n__18_MERGE_OLD_MAXS = v_INIT_10005_n__4_OLD_MAXS);
    (v_LoopB_10001_n__19_MERGE_OLD_PIVR = v_INIT_10005_n__2_OLD_PIVR);
    (v_LoopB_10001_n__20_MERGE_OLD_ROW = v_INIT_10005_n__6_ROW);
    (v_LoopB_10001_n__21_MERGE_first = v_INIT_10005_n__8_p0_o);
    sisal_array_t v_TEST_10004_n__0_A = {0};
    sisal_array_t v_TEST_10004_n__0_AIN = {0};
    sisal_array_t v_TEST_10004_n__0_B = {0};
    sisal_array_t v_TEST_10004_n__0_BIN = {0};
    int32_t v_TEST_10004_n__0_COL = 0;
    int32_t v_TEST_10004_n__0_I = 0;
    double v_TEST_10004_n__0_MAX = 0;
    sisal_array_t v_TEST_10004_n__0_MAXS = {0};
    int32_t v_TEST_10004_n__0_N = 0;
    sisal_array_t v_TEST_10004_n__0_OLD_A = {0};
    sisal_array_t v_TEST_10004_n__0_OLD_B = {0};
    int32_t v_TEST_10004_n__0_OLD_COL = 0;
    int32_t v_TEST_10004_n__0_OLD_I = 0;
    double v_TEST_10004_n__0_OLD_MAX = 0;
    sisal_array_t v_TEST_10004_n__0_OLD_MAXS = {0};
    sisal_array_t v_TEST_10004_n__0_OLD_PIVR = {0};
    int32_t v_TEST_10004_n__0_OLD_ROW = 0;
    sisal_array_t v_TEST_10004_n__0_PIVR = {0};
    int32_t v_TEST_10004_n__0_ROW = 0;
    (v_TEST_10004_n__0_A = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__5_MERGE_A));
    (v_TEST_10004_n__0_AIN = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__0_AIN));
    (v_TEST_10004_n__0_B = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__6_MERGE_B));
    (v_TEST_10004_n__0_BIN = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__0_BIN));
    (v_TEST_10004_n__0_COL = SISAL_CAST(int32_t, v_LoopB_10001_n__7_MERGE_COL));
    (v_TEST_10004_n__0_I = SISAL_CAST(int32_t, v_LoopB_10001_n__8_MERGE_I));
    (v_TEST_10004_n__0_MAX = SISAL_CAST(double, v_LoopB_10001_n__9_MERGE_MAX));
    (v_TEST_10004_n__0_MAXS = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__10_MERGE_MAXS));
    (v_TEST_10004_n__0_N = SISAL_CAST(int32_t, v_LoopB_10001_n__0_N));
    (v_TEST_10004_n__0_OLD_A = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__13_MERGE_OLD_A));
    (v_TEST_10004_n__0_OLD_B = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__14_MERGE_OLD_B));
    (v_TEST_10004_n__0_OLD_COL = SISAL_CAST(int32_t, v_LoopB_10001_n__15_MERGE_OLD_COL));
    (v_TEST_10004_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_10001_n__16_MERGE_OLD_I));
    (v_TEST_10004_n__0_OLD_MAX = SISAL_CAST(double, v_LoopB_10001_n__17_MERGE_OLD_MAX));
    (v_TEST_10004_n__0_OLD_MAXS = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__18_MERGE_OLD_MAXS));
    (v_TEST_10004_n__0_OLD_PIVR = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__19_MERGE_OLD_PIVR));
    (v_TEST_10004_n__0_OLD_ROW = SISAL_CAST(int32_t, v_LoopB_10001_n__20_MERGE_OLD_ROW));
    (v_TEST_10004_n__0_PIVR = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__11_MERGE_PIVR));
    (v_TEST_10004_n__0_ROW = SISAL_CAST(int32_t, v_LoopB_10001_n__12_MERGE_ROW));
    bool v_TEST_10004_n__1_p0_o = 0;
    (v_TEST_10004_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_TEST_10004_n__0_I) < SISAL_CAST(int32_t, v_TEST_10004_n__0_N))));
    while (v_TEST_10004_n__1_p0_o) {
      sisal_array_t v_BODY_10002_n__13_A = {0};
      sisal_array_t v_BODY_10002_n__6_A1 = {0};
      sisal_array_t v_BODY_10002_n__0_AIN = {0};
      sisal_array_t v_BODY_10002_n__13_B = {0};
      sisal_array_t v_BODY_10002_n__10_B1 = {0};
      sisal_array_t v_BODY_10002_n__0_BIN = {0};
      int32_t v_BODY_10002_n__15_COL = 0;
      int32_t v_BODY_10002_n__2_I = 0;
      double v_BODY_10002_n__13_MAX = 0;
      sisal_array_t v_BODY_10002_n__13_MAXS = {0};
      int32_t v_BODY_10002_n__0_N = 0;
      sisal_array_t v_BODY_10002_n__0_OLD_A = {0};
      sisal_array_t v_BODY_10002_n__0_OLD_B = {0};
      int32_t v_BODY_10002_n__0_OLD_COL = 0;
      int32_t v_BODY_10002_n__0_OLD_I = 0;
      double v_BODY_10002_n__0_OLD_MAX = 0;
      sisal_array_t v_BODY_10002_n__0_OLD_MAXS = {0};
      sisal_array_t v_BODY_10002_n__0_OLD_PIVR = {0};
      int32_t v_BODY_10002_n__0_OLD_ROW = 0;
      sisal_array_t v_BODY_10002_n__12_PIVR = {0};
      int32_t v_BODY_10002_n__15_ROW = 0;
      sisal_array_t v_BODY_10002_n__0_p0_o = {0};
      (v_BODY_10002_n__0_p0_o = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__5_MERGE_A));
      (v_BODY_10002_n__0_AIN = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__0_AIN));
      sisal_array_t v_BODY_10002_n__0_p2_o = {0};
      (v_BODY_10002_n__0_p2_o = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__6_MERGE_B));
      (v_BODY_10002_n__0_BIN = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__0_BIN));
      int32_t v_BODY_10002_n__0_p4_o = 0;
      (v_BODY_10002_n__0_p4_o = SISAL_CAST(int32_t, v_LoopB_10001_n__7_MERGE_COL));
      int32_t v_BODY_10002_n__0_p5_o = 0;
      (v_BODY_10002_n__0_p5_o = SISAL_CAST(int32_t, v_LoopB_10001_n__8_MERGE_I));
      double v_BODY_10002_n__0_p6_o = 0;
      (v_BODY_10002_n__0_p6_o = SISAL_CAST(double, v_LoopB_10001_n__9_MERGE_MAX));
      sisal_array_t v_BODY_10002_n__0_p7_o = {0};
      (v_BODY_10002_n__0_p7_o = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__10_MERGE_MAXS));
      (v_BODY_10002_n__0_N = SISAL_CAST(int32_t, v_LoopB_10001_n__0_N));
      (v_BODY_10002_n__0_OLD_A = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__13_MERGE_OLD_A));
      (v_BODY_10002_n__0_OLD_B = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__14_MERGE_OLD_B));
      (v_BODY_10002_n__0_OLD_COL = SISAL_CAST(int32_t, v_LoopB_10001_n__15_MERGE_OLD_COL));
      (v_BODY_10002_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_10001_n__16_MERGE_OLD_I));
      (v_BODY_10002_n__0_OLD_MAX = SISAL_CAST(double, v_LoopB_10001_n__17_MERGE_OLD_MAX));
      (v_BODY_10002_n__0_OLD_MAXS = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__18_MERGE_OLD_MAXS));
      (v_BODY_10002_n__0_OLD_PIVR = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__19_MERGE_OLD_PIVR));
      (v_BODY_10002_n__0_OLD_ROW = SISAL_CAST(int32_t, v_LoopB_10001_n__20_MERGE_OLD_ROW));
      sisal_array_t v_BODY_10002_n__0_p17_o = {0};
      (v_BODY_10002_n__0_p17_o = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__11_MERGE_PIVR));
      int32_t v_BODY_10002_n__0_p18_o = 0;
      (v_BODY_10002_n__0_p18_o = SISAL_CAST(int32_t, v_LoopB_10001_n__12_MERGE_ROW));
      int32_t v_BODY_10002_n__1_p0_o = 0;
      (v_BODY_10002_n__1_p0_o = SISAL_CAST(int32_t, 1));
      (v_BODY_10002_n__2_I = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_10002_n__0_OLD_I) + SISAL_CAST(int32_t, v_BODY_10002_n__1_p0_o))));
      sisal_array_t v_BODY_10002_n__3_p0_o = {0};
      (v_BODY_10002_n__3_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_BODY_10002_n__0_OLD_A), (SISAL_CAST(int32_t, v_BODY_10002_n__0_OLD_ROW) - SISAL_CAST(sisal_array_t, v_BODY_10002_n__0_OLD_A).lower_bound[0]))));
      sisal_array_t v_BODY_10002_n__4_p0_o = {0};
      (v_BODY_10002_n__4_p0_o = SISAL_CAST(sisal_array_t, sisal_dv_replace_slice(SISAL_CAST(sisal_array_t, v_BODY_10002_n__0_OLD_A), ((int64_t)SISAL_CAST(int32_t, v_BODY_10002_n__0_OLD_COL)), SISAL_CAST(sisal_array_t, v_BODY_10002_n__3_p0_o))));
      sisal_array_t v_BODY_10002_n__5_p0_o = {0};
      (v_BODY_10002_n__5_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_BODY_10002_n__0_OLD_A), (SISAL_CAST(int32_t, v_BODY_10002_n__0_OLD_COL) - SISAL_CAST(sisal_array_t, v_BODY_10002_n__0_OLD_A).lower_bound[0]))));
      (v_BODY_10002_n__6_A1 = SISAL_CAST(sisal_array_t, sisal_dv_replace_slice(SISAL_CAST(sisal_array_t, v_BODY_10002_n__4_p0_o), ((int64_t)SISAL_CAST(int32_t, v_BODY_10002_n__0_OLD_ROW)), SISAL_CAST(sisal_array_t, v_BODY_10002_n__5_p0_o))));
      double v_BODY_10002_n__7_p0_o = 0;
      (v_BODY_10002_n__7_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_10002_n__0_OLD_B).data)[(SISAL_CAST(int32_t, v_BODY_10002_n__0_OLD_ROW) - SISAL_CAST(sisal_array_t, v_BODY_10002_n__0_OLD_B).lower_bound[0])]));
      sisal_array_t v_BODY_10002_n__8_p0_o = {0};
      (v_BODY_10002_n__8_p0_o = SISAL_CAST(sisal_array_t, sisal_array_replace_f64(SISAL_CAST(sisal_array_t, v_BODY_10002_n__0_OLD_B), ((int64_t)SISAL_CAST(int32_t, v_BODY_10002_n__0_OLD_COL)), SISAL_CAST(double, v_BODY_10002_n__7_p0_o))));
      double v_BODY_10002_n__9_p0_o = 0;
      (v_BODY_10002_n__9_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_10002_n__0_OLD_B).data)[(SISAL_CAST(int32_t, v_BODY_10002_n__0_OLD_COL) - SISAL_CAST(sisal_array_t, v_BODY_10002_n__0_OLD_B).lower_bound[0])]));
      (v_BODY_10002_n__10_B1 = SISAL_CAST(sisal_array_t, sisal_array_replace_f64(SISAL_CAST(sisal_array_t, v_BODY_10002_n__8_p0_o), ((int64_t)SISAL_CAST(int32_t, v_BODY_10002_n__0_OLD_ROW)), SISAL_CAST(double, v_BODY_10002_n__9_p0_o))));
      int32_t v_BODY_10002_n__11_p0_o = 0;
      (v_BODY_10002_n__11_p0_o = SISAL_CAST(int32_t, 1));
      (v_BODY_10002_n__12_PIVR = SISAL_CAST(sisal_array_t, sisal_array_replace_i32(SISAL_CAST(sisal_array_t, v_BODY_10002_n__0_OLD_PIVR), ((int64_t)SISAL_CAST(int32_t, v_BODY_10002_n__0_OLD_COL)), SISAL_CAST(int32_t, v_BODY_10002_n__11_p0_o))));
      struct FUNC_REDUCE_AND_MAX_results _mr_BODY_10002_13 = func_REDUCE_AND_MAX(SISAL_CAST(sisal_array_t, v_BODY_10002_n__6_A1), SISAL_CAST(int32_t, v_BODY_10002_n__0_OLD_COL), SISAL_CAST(sisal_array_t, v_BODY_10002_n__12_PIVR), SISAL_CAST(sisal_array_t, v_BODY_10002_n__10_B1));
      (v_BODY_10002_n__13_A = SISAL_CAST(sisal_array_t, _mr_BODY_10002_13.res_0));
      (v_BODY_10002_n__13_B = SISAL_CAST(sisal_array_t, _mr_BODY_10002_13.res_1));
      (v_BODY_10002_n__13_MAX = SISAL_CAST(double, _mr_BODY_10002_13.res_2));
      (v_BODY_10002_n__13_MAXS = SISAL_CAST(sisal_array_t, _mr_BODY_10002_13.res_3));
      struct FUNC_INDEX_OF_MAX_results _mr_BODY_10002_15 = func_INDEX_OF_MAX(SISAL_CAST(double, v_BODY_10002_n__13_MAX), SISAL_CAST(sisal_array_t, v_BODY_10002_n__13_MAXS), SISAL_CAST(sisal_array_t, v_BODY_10002_n__13_A));
      (v_BODY_10002_n__15_ROW = SISAL_CAST(int32_t, _mr_BODY_10002_15.res_0));
      (v_BODY_10002_n__15_COL = SISAL_CAST(int32_t, _mr_BODY_10002_15.res_1));
      bool v_BODY_10002_n__17_p0_o = 0;
      (v_BODY_10002_n__17_p0_o = SISAL_CAST(bool, false));
      (v_LoopB_10001_bodycap_n2_p0 = v_BODY_10002_n__2_I);
      (v_LoopB_10001_bodycap_n12_p0 = v_BODY_10002_n__12_PIVR);
      (v_LoopB_10001_bodycap_n13_p0 = v_BODY_10002_n__13_A);
      (v_LoopB_10001_bodycap_n13_p1 = v_BODY_10002_n__13_B);
      (v_LoopB_10001_bodycap_n13_p2 = v_BODY_10002_n__13_MAX);
      (v_LoopB_10001_bodycap_n13_p3 = v_BODY_10002_n__13_MAXS);
      (v_LoopB_10001_bodycap_n15_p0 = v_BODY_10002_n__15_ROW);
      (v_LoopB_10001_bodycap_n15_p1 = v_BODY_10002_n__15_COL);
      (v_LoopB_10001_bodycap_n17_p0 = v_BODY_10002_n__17_p0_o);
      (v_LoopB_10001_n__5_MERGE_A = v_LoopB_10001_bodycap_n13_p0);
      (v_LoopB_10001_n__6_MERGE_B = v_LoopB_10001_bodycap_n13_p1);
      (v_LoopB_10001_n__7_MERGE_COL = v_LoopB_10001_bodycap_n15_p1);
      (v_LoopB_10001_n__8_MERGE_I = v_LoopB_10001_bodycap_n2_p0);
      (v_LoopB_10001_n__9_MERGE_MAX = v_LoopB_10001_bodycap_n13_p2);
      (v_LoopB_10001_n__10_MERGE_MAXS = v_LoopB_10001_bodycap_n13_p3);
      (v_LoopB_10001_n__11_MERGE_PIVR = v_LoopB_10001_bodycap_n12_p0);
      (v_LoopB_10001_n__12_MERGE_ROW = v_LoopB_10001_bodycap_n15_p0);
      (v_LoopB_10001_n__13_MERGE_OLD_A = v_LoopB_10001_bodycap_n13_p0);
      (v_LoopB_10001_n__14_MERGE_OLD_B = v_LoopB_10001_bodycap_n13_p1);
      (v_LoopB_10001_n__15_MERGE_OLD_COL = v_LoopB_10001_bodycap_n15_p1);
      (v_LoopB_10001_n__16_MERGE_OLD_I = v_LoopB_10001_bodycap_n2_p0);
      (v_LoopB_10001_n__17_MERGE_OLD_MAX = v_LoopB_10001_bodycap_n13_p2);
      (v_LoopB_10001_n__18_MERGE_OLD_MAXS = v_LoopB_10001_bodycap_n13_p3);
      (v_LoopB_10001_n__19_MERGE_OLD_PIVR = v_LoopB_10001_bodycap_n12_p0);
      (v_LoopB_10001_n__20_MERGE_OLD_ROW = v_LoopB_10001_bodycap_n15_p0);
      (v_LoopB_10001_n__21_MERGE_first = v_LoopB_10001_bodycap_n17_p0);
      (v_TEST_10004_n__0_A = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__5_MERGE_A));
      (v_TEST_10004_n__0_AIN = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__0_AIN));
      (v_TEST_10004_n__0_B = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__6_MERGE_B));
      (v_TEST_10004_n__0_BIN = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__0_BIN));
      (v_TEST_10004_n__0_COL = SISAL_CAST(int32_t, v_LoopB_10001_n__7_MERGE_COL));
      (v_TEST_10004_n__0_I = SISAL_CAST(int32_t, v_LoopB_10001_n__8_MERGE_I));
      (v_TEST_10004_n__0_MAX = SISAL_CAST(double, v_LoopB_10001_n__9_MERGE_MAX));
      (v_TEST_10004_n__0_MAXS = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__10_MERGE_MAXS));
      (v_TEST_10004_n__0_N = SISAL_CAST(int32_t, v_LoopB_10001_n__0_N));
      (v_TEST_10004_n__0_OLD_A = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__13_MERGE_OLD_A));
      (v_TEST_10004_n__0_OLD_B = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__14_MERGE_OLD_B));
      (v_TEST_10004_n__0_OLD_COL = SISAL_CAST(int32_t, v_LoopB_10001_n__15_MERGE_OLD_COL));
      (v_TEST_10004_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_10001_n__16_MERGE_OLD_I));
      (v_TEST_10004_n__0_OLD_MAX = SISAL_CAST(double, v_LoopB_10001_n__17_MERGE_OLD_MAX));
      (v_TEST_10004_n__0_OLD_MAXS = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__18_MERGE_OLD_MAXS));
      (v_TEST_10004_n__0_OLD_PIVR = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__19_MERGE_OLD_PIVR));
      (v_TEST_10004_n__0_OLD_ROW = SISAL_CAST(int32_t, v_LoopB_10001_n__20_MERGE_OLD_ROW));
      (v_TEST_10004_n__0_PIVR = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__11_MERGE_PIVR));
      (v_TEST_10004_n__0_ROW = SISAL_CAST(int32_t, v_LoopB_10001_n__12_MERGE_ROW));
      (v_TEST_10004_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_TEST_10004_n__0_I) < SISAL_CAST(int32_t, v_TEST_10004_n__0_N))));
    }
    sisal_array_t v_RETURNS_10003_n__0_p0_o = {0};
    (v_RETURNS_10003_n__0_p0_o = SISAL_CAST(sisal_array_t, v_LoopB_10001_bodycap_n13_p1));
    sisal_array_t v_RETURNS_10003_n__1_p0_o = {0};
    (v_RETURNS_10003_n__1_p0_o = SISAL_CAST(sisal_array_t, SISAL_CAST(sisal_array_t, v_RETURNS_10003_n__0_p0_o)));
    (v_g4_n__1_p0_o = SISAL_CAST(sisal_array_t, v_RETURNS_10003_n__1_p0_o));
  }
  (v_g4_n__0_p0_i = SISAL_CAST(sisal_array_t, v_g4_n__1_p0_o));
  return SISAL_CAST(sisal_array_t, v_g4_n__0_p0_i);
}
