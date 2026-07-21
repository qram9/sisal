#define SISAL_CUSTOM_ELEM_SIZE

#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <math.h>
#include <iostream>
#include <dispatch/dispatch.h>
#include <Accelerate/Accelerate.h>
#include <sisal_runtime.h>

struct struct_rec_105 {
  int32_t lo;
  int32_t stride;
  int32_t size;
};
struct struct_rec_104 {
  int32_t stride;
  int32_t size;
};
struct struct_rec_103 {
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
struct FUNC_REDUCE_results {
  sisal_array_t res_0;
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
        case 105:
        case 106:
            return sizeof(struct struct_rec_105);
        case 104:
            return sizeof(struct struct_rec_104);
        case 103:
            return sizeof(struct struct_rec_103);
        case 96:
        case 97:
        case 98:
        case 99:
        case 100:
        case 101:
        case 102:
        case 107:
        case 108:
        case 109:
        case 110:
        case 111:
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
extern "C" struct FUNC_REDUCE_results func_REDUCE(sisal_array_t A, int32_t PIVOT, sisal_array_t B);

extern "C" struct FUNC_REDUCE_results func_REDUCE(sisal_array_t A, int32_t PIVOT, sisal_array_t B) {
  sisal_array_t v_g1_n__0_A = {0};
  sisal_array_t v_g1_n__0_B = {0};
  int32_t v_g1_n__0_PIVOT = 0;
  (v_g1_n__0_A = SISAL_CAST(sisal_array_t, A));
  (v_g1_n__0_PIVOT = SISAL_CAST(int32_t, PIVOT));
  (v_g1_n__0_B = SISAL_CAST(sisal_array_t, B));
  sisal_array_t v_g1_n__0_p0_i = {0};
  sisal_array_t v_g1_n__0_p1_i = {0};
  sisal_array_t v_g1_n__1_p0_o = {0};
  sisal_array_t v_g1_n__1_p1_o = {0};
  {
    sisal_array_t v_FORALL_11006_n__0_A = v_g1_n__0_A;
    sisal_array_t v_FORALL_11006_n__0_B = v_g1_n__0_B;
    int32_t v_FORALL_11006_n__2_I;
    int32_t v_FORALL_11006_n__0_PIVOT = v_g1_n__0_PIVOT;
    sisal_array_t v_FORALL_11006_n__2_ROW;
    sisal_array_t v_FORALL_11006_n__3___forall_body_0;
    double v_FORALL_11006_n__3___forall_body_1;
    sisal_array_t v_GENERATOR_11008_n__0_A;
    sisal_array_t v_GENERATOR_11008_n__0_B;
    int32_t v_GENERATOR_11008_n__1_I;
    int32_t v_GENERATOR_11008_n__0_PIVOT;
    sisal_array_t v_GENERATOR_11008_n__1_ROW;
    sisal_array_t v_BODY_11009_n__0_A;
    sisal_array_t v_BODY_11009_n__0_B;
    int32_t v_BODY_11009_n__0_I;
    double v_BODY_11009_n__7_MULT;
    int32_t v_BODY_11009_n__0_PIVOT;
    double v_BODY_11009_n__8_RB;
    sisal_array_t v_BODY_11009_n__0_ROW;
    sisal_array_t v_BODY_11009_n__8_RROW;
    sisal_array_t v_IF_DOUBLE__array_dv_DOUBLE____11010_n__0_A;
    sisal_array_t v_IF_DOUBLE__array_dv_DOUBLE____11010_n__0_B;
    int32_t v_IF_DOUBLE__array_dv_DOUBLE____11010_n__0_I;
    double v_IF_DOUBLE__array_dv_DOUBLE____11010_n__0_MULT;
    int32_t v_IF_DOUBLE__array_dv_DOUBLE____11010_n__0_PIVOT;
    sisal_array_t v_IF_DOUBLE__array_dv_DOUBLE____11010_n__0_ROW;
    int32_t v_PREDICATE_11011_n__0_I;
    int32_t v_PREDICATE_11011_n__0_PIVOT;
    sisal_array_t v_ELSE_11012_n__0_A;
    sisal_array_t v_ELSE_11012_n__0_B;
    int32_t v_ELSE_11012_n__0_I;
    double v_ELSE_11012_n__0_MULT;
    int32_t v_ELSE_11012_n__0_PIVOT;
    sisal_array_t v_ELSE_11012_n__0_ROW;
    sisal_array_t v_FORALL_11013_n__0_A;
    sisal_array_t v_FORALL_11013_n__0_B;
    int32_t v_FORALL_11013_n__0_I;
    int32_t v_FORALL_11013_n__2_J;
    double v_FORALL_11013_n__0_MULT;
    int32_t v_FORALL_11013_n__0_PIVOT;
    sisal_array_t v_FORALL_11013_n__0_ROW;
    double v_FORALL_11013_n__2_X;
    double v_FORALL_11013_n__3___forall_body_0;
    sisal_array_t v_GENERATOR_11015_n__0_A;
    sisal_array_t v_GENERATOR_11015_n__0_B;
    int32_t v_GENERATOR_11015_n__0_I;
    int32_t v_GENERATOR_11015_n__1_J;
    double v_GENERATOR_11015_n__0_MULT;
    int32_t v_GENERATOR_11015_n__0_PIVOT;
    sisal_array_t v_GENERATOR_11015_n__0_ROW;
    double v_GENERATOR_11015_n__1_X;
    sisal_array_t v_BODY_11016_n__0_A;
    sisal_array_t v_BODY_11016_n__0_B;
    int32_t v_BODY_11016_n__0_I;
    int32_t v_BODY_11016_n__0_J;
    double v_BODY_11016_n__0_MULT;
    int32_t v_BODY_11016_n__0_PIVOT;
    sisal_array_t v_BODY_11016_n__0_ROW;
    double v_BODY_11016_n__0_X;
    sisal_array_t v_THEN_11017_n__0_A;
    sisal_array_t v_THEN_11017_n__0_B;
    int32_t v_THEN_11017_n__0_I;
    double v_THEN_11017_n__0_MULT;
    int32_t v_THEN_11017_n__0_PIVOT;
    sisal_array_t v_THEN_11017_n__0_ROW;
    sisal_array_t v_FORALL_11018_n__0_A;
    sisal_array_t v_FORALL_11018_n__0_B;
    int32_t v_FORALL_11018_n__0_I;
    double v_FORALL_11018_n__0_MULT;
    int32_t v_FORALL_11018_n__0_PIVOT;
    sisal_array_t v_FORALL_11018_n__0_ROW;
    double v_FORALL_11018_n__2_X;
    double v_FORALL_11018_n__3___forall_body_0;
    sisal_array_t v_GENERATOR_11020_n__0_A;
    sisal_array_t v_GENERATOR_11020_n__0_B;
    int32_t v_GENERATOR_11020_n__0_I;
    double v_GENERATOR_11020_n__0_MULT;
    int32_t v_GENERATOR_11020_n__0_PIVOT;
    sisal_array_t v_GENERATOR_11020_n__0_ROW;
    double v_GENERATOR_11020_n__1_X;
    sisal_array_t v_BODY_11021_n__0_A;
    sisal_array_t v_BODY_11021_n__0_B;
    int32_t v_BODY_11021_n__0_I;
    double v_BODY_11021_n__0_MULT;
    int32_t v_BODY_11021_n__0_PIVOT;
    sisal_array_t v_BODY_11021_n__0_ROW;
    double v_BODY_11021_n__0_X;
    (v_GENERATOR_11008_n__0_A = v_FORALL_11006_n__0_A);
    (v_g1_n__1_p0_o = sisal_array_alloc_sized(1, 95, ((uint64_t)(1 * ((int32_t)v_GENERATOR_11008_n__0_A.dims[0]))), sizeof(sisal_array_t)));
    (v_g1_n__1_p0_o.dims[0] = ((int32_t)v_GENERATOR_11008_n__0_A.dims[0]));
    (v_g1_n__1_p0_o.lower_bound[0] = 1);
    (v_g1_n__1_p1_o = sisal_array_alloc_empty(1, 4, ((uint64_t)(1 * ((int32_t)v_GENERATOR_11008_n__0_A.dims[0])))));
    (v_g1_n__1_p1_o.dims[0] = ((int32_t)v_GENERATOR_11008_n__0_A.dims[0]));
    (v_g1_n__1_p1_o.lower_bound[0] = 1);
    int32_t __g_11006 = 0;
    for (int32_t __k_11008 = 0; (__k_11008 < ((int32_t)v_GENERATOR_11008_n__0_A.dims[0])); (__k_11008++)) {
      (v_GENERATOR_11008_n__1_ROW = sisal_array_get_row(v_GENERATOR_11008_n__0_A, __k_11008));
      (v_GENERATOR_11008_n__1_I = (((int32_t)v_GENERATOR_11008_n__0_A.lower_bound[0]) + __k_11008));
      (v_BODY_11009_n__0_A = SISAL_CAST(sisal_array_t, v_FORALL_11006_n__0_A));
      (v_BODY_11009_n__0_B = SISAL_CAST(sisal_array_t, v_FORALL_11006_n__0_B));
      (v_BODY_11009_n__0_I = SISAL_CAST(int32_t, v_GENERATOR_11008_n__1_I));
      (v_BODY_11009_n__0_PIVOT = SISAL_CAST(int32_t, v_FORALL_11006_n__0_PIVOT));
      (v_BODY_11009_n__0_ROW = SISAL_CAST(sisal_array_t, v_GENERATOR_11008_n__1_ROW));
      sisal_array_t v_BODY_11009_n__1_p0_o = {0};
      (v_BODY_11009_n__1_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_BODY_11009_n__0_A), (SISAL_CAST(int32_t, v_BODY_11009_n__0_I) - SISAL_CAST(sisal_array_t, v_BODY_11009_n__0_A).lower_bound[0]))));
      float v_BODY_11009_n__2_p0_o = 0;
      (v_BODY_11009_n__2_p0_o = SISAL_CAST(float, ((float *)SISAL_CAST(sisal_array_t, v_BODY_11009_n__1_p0_o).data)[(SISAL_CAST(int32_t, v_BODY_11009_n__0_PIVOT) - SISAL_CAST(sisal_array_t, v_BODY_11009_n__1_p0_o).lower_bound[0])]));
      sisal_array_t v_BODY_11009_n__3_p0_o = {0};
      (v_BODY_11009_n__3_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_BODY_11009_n__0_A), (SISAL_CAST(int32_t, v_BODY_11009_n__0_I) - SISAL_CAST(sisal_array_t, v_BODY_11009_n__0_A).lower_bound[0]))));
      double v_BODY_11009_n__4_p0_o = 0;
      (v_BODY_11009_n__4_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_11009_n__3_p0_o).data)[(SISAL_CAST(int32_t, v_BODY_11009_n__0_PIVOT) - SISAL_CAST(sisal_array_t, v_BODY_11009_n__3_p0_o).lower_bound[0])]));
      sisal_array_t v_BODY_11009_n__5_p0_o = {0};
      (v_BODY_11009_n__5_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_BODY_11009_n__0_A), (SISAL_CAST(int32_t, v_BODY_11009_n__0_PIVOT) - SISAL_CAST(sisal_array_t, v_BODY_11009_n__0_A).lower_bound[0]))));
      double v_BODY_11009_n__6_p0_o = 0;
      (v_BODY_11009_n__6_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_11009_n__5_p0_o).data)[(SISAL_CAST(int32_t, v_BODY_11009_n__0_PIVOT) - SISAL_CAST(sisal_array_t, v_BODY_11009_n__5_p0_o).lower_bound[0])]));
      (v_BODY_11009_n__7_MULT = SISAL_CAST(double, (SISAL_CAST(double, v_BODY_11009_n__4_p0_o) / SISAL_CAST(double, v_BODY_11009_n__6_p0_o))));
      (v_IF_DOUBLE__array_dv_DOUBLE____11010_n__0_I = SISAL_CAST(int32_t, v_BODY_11009_n__0_I));
      (v_IF_DOUBLE__array_dv_DOUBLE____11010_n__0_PIVOT = SISAL_CAST(int32_t, v_BODY_11009_n__0_PIVOT));
      (v_IF_DOUBLE__array_dv_DOUBLE____11010_n__0_A = SISAL_CAST(sisal_array_t, v_BODY_11009_n__0_A));
      (v_IF_DOUBLE__array_dv_DOUBLE____11010_n__0_B = SISAL_CAST(sisal_array_t, v_BODY_11009_n__0_B));
      (v_IF_DOUBLE__array_dv_DOUBLE____11010_n__0_MULT = SISAL_CAST(double, v_BODY_11009_n__7_MULT));
      (v_IF_DOUBLE__array_dv_DOUBLE____11010_n__0_ROW = SISAL_CAST(sisal_array_t, v_BODY_11009_n__0_ROW));
      {
        (v_PREDICATE_11011_n__0_I = SISAL_CAST(int32_t, v_IF_DOUBLE__array_dv_DOUBLE____11010_n__0_I));
        (v_PREDICATE_11011_n__0_PIVOT = SISAL_CAST(int32_t, v_IF_DOUBLE__array_dv_DOUBLE____11010_n__0_PIVOT));
        bool v_PREDICATE_11011_n__1_p0_o = 0;
        (v_PREDICATE_11011_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_PREDICATE_11011_n__0_I) == SISAL_CAST(int32_t, v_PREDICATE_11011_n__0_PIVOT))));
        if (v_PREDICATE_11011_n__1_p0_o) {
          (v_THEN_11017_n__0_A = SISAL_CAST(sisal_array_t, v_IF_DOUBLE__array_dv_DOUBLE____11010_n__0_A));
          (v_THEN_11017_n__0_B = SISAL_CAST(sisal_array_t, v_IF_DOUBLE__array_dv_DOUBLE____11010_n__0_B));
          (v_THEN_11017_n__0_I = SISAL_CAST(int32_t, v_IF_DOUBLE__array_dv_DOUBLE____11010_n__0_I));
          (v_THEN_11017_n__0_MULT = SISAL_CAST(double, v_IF_DOUBLE__array_dv_DOUBLE____11010_n__0_MULT));
          (v_THEN_11017_n__0_PIVOT = SISAL_CAST(int32_t, v_IF_DOUBLE__array_dv_DOUBLE____11010_n__0_PIVOT));
          (v_THEN_11017_n__0_ROW = SISAL_CAST(sisal_array_t, v_IF_DOUBLE__array_dv_DOUBLE____11010_n__0_ROW));
          sisal_array_t v_THEN_11017_n__1_p0_o = {0};
          {
            sisal_array_t v_FORALL_11018_n__0_A = v_THEN_11017_n__0_A;
            sisal_array_t v_FORALL_11018_n__0_B = v_THEN_11017_n__0_B;
            int32_t v_FORALL_11018_n__0_I = v_THEN_11017_n__0_I;
            double v_FORALL_11018_n__0_MULT = v_THEN_11017_n__0_MULT;
            int32_t v_FORALL_11018_n__0_PIVOT = v_THEN_11017_n__0_PIVOT;
            sisal_array_t v_FORALL_11018_n__0_ROW = v_THEN_11017_n__0_ROW;
            double v_FORALL_11018_n__2_X;
            double v_FORALL_11018_n__3___forall_body_0;
            sisal_array_t v_GENERATOR_11020_n__0_A;
            sisal_array_t v_GENERATOR_11020_n__0_B;
            int32_t v_GENERATOR_11020_n__0_I;
            double v_GENERATOR_11020_n__0_MULT;
            int32_t v_GENERATOR_11020_n__0_PIVOT;
            sisal_array_t v_GENERATOR_11020_n__0_ROW;
            double v_GENERATOR_11020_n__1_X;
            sisal_array_t v_BODY_11021_n__0_A;
            sisal_array_t v_BODY_11021_n__0_B;
            int32_t v_BODY_11021_n__0_I;
            double v_BODY_11021_n__0_MULT;
            int32_t v_BODY_11021_n__0_PIVOT;
            sisal_array_t v_BODY_11021_n__0_ROW;
            double v_BODY_11021_n__0_X;
            (v_GENERATOR_11020_n__0_ROW = v_FORALL_11018_n__0_ROW);
            (v_THEN_11017_n__1_p0_o = sisal_array_alloc_empty(1, 4, ((uint64_t)(1 * ((int32_t)v_GENERATOR_11020_n__0_ROW.dims[0])))));
            (v_THEN_11017_n__1_p0_o.dims[0] = ((int32_t)v_GENERATOR_11020_n__0_ROW.dims[0]));
            (v_THEN_11017_n__1_p0_o.lower_bound[0] = 1);
            int32_t __g_11018 = 0;
            for (int32_t __k_11020 = 0; (__k_11020 < ((int32_t)v_GENERATOR_11020_n__0_ROW.size)); (__k_11020++)) {
              (v_GENERATOR_11020_n__1_X = ((double *)v_GENERATOR_11020_n__0_ROW.data)[__k_11020]);
              (v_BODY_11021_n__0_A = SISAL_CAST(sisal_array_t, v_FORALL_11018_n__0_A));
              (v_BODY_11021_n__0_B = SISAL_CAST(sisal_array_t, v_FORALL_11018_n__0_B));
              (v_BODY_11021_n__0_I = SISAL_CAST(int32_t, v_FORALL_11018_n__0_I));
              (v_BODY_11021_n__0_MULT = SISAL_CAST(double, v_FORALL_11018_n__0_MULT));
              (v_BODY_11021_n__0_PIVOT = SISAL_CAST(int32_t, v_FORALL_11018_n__0_PIVOT));
              (v_BODY_11021_n__0_ROW = SISAL_CAST(sisal_array_t, v_FORALL_11018_n__0_ROW));
              (v_BODY_11021_n__0_X = SISAL_CAST(double, v_GENERATOR_11020_n__1_X));
              sisal_array_t v_BODY_11021_n__1_p0_o = {0};
              (v_BODY_11021_n__1_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_BODY_11021_n__0_A), (SISAL_CAST(int32_t, v_BODY_11021_n__0_PIVOT) - SISAL_CAST(sisal_array_t, v_BODY_11021_n__0_A).lower_bound[0]))));
              double v_BODY_11021_n__2_p0_o = 0;
              (v_BODY_11021_n__2_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_11021_n__1_p0_o).data)[(SISAL_CAST(int32_t, v_BODY_11021_n__0_PIVOT) - SISAL_CAST(sisal_array_t, v_BODY_11021_n__1_p0_o).lower_bound[0])]));
              double v_BODY_11021_n__3_p0_o = 0;
              (v_BODY_11021_n__3_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_BODY_11021_n__0_X) / SISAL_CAST(double, v_BODY_11021_n__2_p0_o))));
              (((double *)v_THEN_11017_n__1_p0_o.data)[__g_11018] = SISAL_CAST(double, v_BODY_11021_n__3_p0_o));
              (__g_11018++);
            }
          }
          float v_THEN_11017_n__3_p0_o = 0;
          (v_THEN_11017_n__3_p0_o = SISAL_CAST(float, ((float *)SISAL_CAST(sisal_array_t, v_THEN_11017_n__0_B).data)[(SISAL_CAST(int32_t, v_THEN_11017_n__0_I) - SISAL_CAST(sisal_array_t, v_THEN_11017_n__0_B).lower_bound[0])]));
          double v_THEN_11017_n__4_p0_o = 0;
          (v_THEN_11017_n__4_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_THEN_11017_n__0_B).data)[(SISAL_CAST(int32_t, v_THEN_11017_n__0_I) - SISAL_CAST(sisal_array_t, v_THEN_11017_n__0_B).lower_bound[0])]));
          sisal_array_t v_THEN_11017_n__5_p0_o = {0};
          (v_THEN_11017_n__5_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_THEN_11017_n__0_A), (SISAL_CAST(int32_t, v_THEN_11017_n__0_PIVOT) - SISAL_CAST(sisal_array_t, v_THEN_11017_n__0_A).lower_bound[0]))));
          double v_THEN_11017_n__6_p0_o = 0;
          (v_THEN_11017_n__6_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_THEN_11017_n__5_p0_o).data)[(SISAL_CAST(int32_t, v_THEN_11017_n__0_PIVOT) - SISAL_CAST(sisal_array_t, v_THEN_11017_n__5_p0_o).lower_bound[0])]));
          double v_THEN_11017_n__7_p0_o = 0;
          (v_THEN_11017_n__7_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_THEN_11017_n__4_p0_o) / SISAL_CAST(double, v_THEN_11017_n__6_p0_o))));
          (v_BODY_11009_n__8_RROW = SISAL_CAST(sisal_array_t, v_THEN_11017_n__1_p0_o));
          (v_BODY_11009_n__8_RB = SISAL_CAST(double, v_THEN_11017_n__7_p0_o));
        }
        else {
          (v_ELSE_11012_n__0_A = SISAL_CAST(sisal_array_t, v_IF_DOUBLE__array_dv_DOUBLE____11010_n__0_A));
          (v_ELSE_11012_n__0_B = SISAL_CAST(sisal_array_t, v_IF_DOUBLE__array_dv_DOUBLE____11010_n__0_B));
          (v_ELSE_11012_n__0_I = SISAL_CAST(int32_t, v_IF_DOUBLE__array_dv_DOUBLE____11010_n__0_I));
          (v_ELSE_11012_n__0_MULT = SISAL_CAST(double, v_IF_DOUBLE__array_dv_DOUBLE____11010_n__0_MULT));
          (v_ELSE_11012_n__0_PIVOT = SISAL_CAST(int32_t, v_IF_DOUBLE__array_dv_DOUBLE____11010_n__0_PIVOT));
          (v_ELSE_11012_n__0_ROW = SISAL_CAST(sisal_array_t, v_IF_DOUBLE__array_dv_DOUBLE____11010_n__0_ROW));
          sisal_array_t v_ELSE_11012_n__1_p0_o = {0};
          {
            sisal_array_t v_FORALL_11013_n__0_A = v_ELSE_11012_n__0_A;
            sisal_array_t v_FORALL_11013_n__0_B = v_ELSE_11012_n__0_B;
            int32_t v_FORALL_11013_n__0_I = v_ELSE_11012_n__0_I;
            int32_t v_FORALL_11013_n__2_J;
            double v_FORALL_11013_n__0_MULT = v_ELSE_11012_n__0_MULT;
            int32_t v_FORALL_11013_n__0_PIVOT = v_ELSE_11012_n__0_PIVOT;
            sisal_array_t v_FORALL_11013_n__0_ROW = v_ELSE_11012_n__0_ROW;
            double v_FORALL_11013_n__2_X;
            double v_FORALL_11013_n__3___forall_body_0;
            sisal_array_t v_GENERATOR_11015_n__0_A;
            sisal_array_t v_GENERATOR_11015_n__0_B;
            int32_t v_GENERATOR_11015_n__0_I;
            int32_t v_GENERATOR_11015_n__1_J;
            double v_GENERATOR_11015_n__0_MULT;
            int32_t v_GENERATOR_11015_n__0_PIVOT;
            sisal_array_t v_GENERATOR_11015_n__0_ROW;
            double v_GENERATOR_11015_n__1_X;
            sisal_array_t v_BODY_11016_n__0_A;
            sisal_array_t v_BODY_11016_n__0_B;
            int32_t v_BODY_11016_n__0_I;
            int32_t v_BODY_11016_n__0_J;
            double v_BODY_11016_n__0_MULT;
            int32_t v_BODY_11016_n__0_PIVOT;
            sisal_array_t v_BODY_11016_n__0_ROW;
            double v_BODY_11016_n__0_X;
            (v_GENERATOR_11015_n__0_ROW = v_FORALL_11013_n__0_ROW);
            (v_ELSE_11012_n__1_p0_o = sisal_array_alloc_empty(1, 4, ((uint64_t)(1 * ((int32_t)v_GENERATOR_11015_n__0_ROW.dims[0])))));
            (v_ELSE_11012_n__1_p0_o.dims[0] = ((int32_t)v_GENERATOR_11015_n__0_ROW.dims[0]));
            (v_ELSE_11012_n__1_p0_o.lower_bound[0] = 1);
            int32_t __g_11013 = 0;
            for (int32_t __k_11015 = 0; (__k_11015 < ((int32_t)v_GENERATOR_11015_n__0_ROW.size)); (__k_11015++)) {
              (v_GENERATOR_11015_n__1_X = ((double *)v_GENERATOR_11015_n__0_ROW.data)[__k_11015]);
              (v_GENERATOR_11015_n__1_J = (((int32_t)v_GENERATOR_11015_n__0_ROW.lower_bound[0]) + __k_11015));
              (v_BODY_11016_n__0_A = SISAL_CAST(sisal_array_t, v_FORALL_11013_n__0_A));
              (v_BODY_11016_n__0_B = SISAL_CAST(sisal_array_t, v_FORALL_11013_n__0_B));
              (v_BODY_11016_n__0_I = SISAL_CAST(int32_t, v_FORALL_11013_n__0_I));
              (v_BODY_11016_n__0_J = SISAL_CAST(int32_t, v_GENERATOR_11015_n__1_J));
              (v_BODY_11016_n__0_MULT = SISAL_CAST(double, v_FORALL_11013_n__0_MULT));
              (v_BODY_11016_n__0_PIVOT = SISAL_CAST(int32_t, v_FORALL_11013_n__0_PIVOT));
              (v_BODY_11016_n__0_ROW = SISAL_CAST(sisal_array_t, v_FORALL_11013_n__0_ROW));
              (v_BODY_11016_n__0_X = SISAL_CAST(double, v_GENERATOR_11015_n__1_X));
              sisal_array_t v_BODY_11016_n__1_p0_o = {0};
              (v_BODY_11016_n__1_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_BODY_11016_n__0_A), (SISAL_CAST(int32_t, v_BODY_11016_n__0_PIVOT) - SISAL_CAST(sisal_array_t, v_BODY_11016_n__0_A).lower_bound[0]))));
              double v_BODY_11016_n__2_p0_o = 0;
              (v_BODY_11016_n__2_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_11016_n__1_p0_o).data)[(SISAL_CAST(int32_t, v_BODY_11016_n__0_J) - SISAL_CAST(sisal_array_t, v_BODY_11016_n__1_p0_o).lower_bound[0])]));
              double v_BODY_11016_n__3_p0_o = 0;
              (v_BODY_11016_n__3_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_BODY_11016_n__0_MULT) * SISAL_CAST(double, v_BODY_11016_n__2_p0_o))));
              double v_BODY_11016_n__4_p0_o = 0;
              (v_BODY_11016_n__4_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_BODY_11016_n__0_X) - SISAL_CAST(double, v_BODY_11016_n__3_p0_o))));
              (((double *)v_ELSE_11012_n__1_p0_o.data)[__g_11013] = SISAL_CAST(double, v_BODY_11016_n__4_p0_o));
              (__g_11013++);
            }
          }
          double v_ELSE_11012_n__3_p0_o = 0;
          (v_ELSE_11012_n__3_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_ELSE_11012_n__0_B).data)[(SISAL_CAST(int32_t, v_ELSE_11012_n__0_I) - SISAL_CAST(sisal_array_t, v_ELSE_11012_n__0_B).lower_bound[0])]));
          double v_ELSE_11012_n__4_p0_o = 0;
          (v_ELSE_11012_n__4_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_ELSE_11012_n__0_B).data)[(SISAL_CAST(int32_t, v_ELSE_11012_n__0_PIVOT) - SISAL_CAST(sisal_array_t, v_ELSE_11012_n__0_B).lower_bound[0])]));
          double v_ELSE_11012_n__5_p0_o = 0;
          (v_ELSE_11012_n__5_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_ELSE_11012_n__0_MULT) * SISAL_CAST(double, v_ELSE_11012_n__4_p0_o))));
          double v_ELSE_11012_n__6_p0_o = 0;
          (v_ELSE_11012_n__6_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_ELSE_11012_n__3_p0_o) - SISAL_CAST(double, v_ELSE_11012_n__5_p0_o))));
          (v_BODY_11009_n__8_RROW = SISAL_CAST(sisal_array_t, v_ELSE_11012_n__1_p0_o));
          (v_BODY_11009_n__8_RB = SISAL_CAST(double, v_ELSE_11012_n__6_p0_o));
        }
      }
      (((sisal_array_t *)v_g1_n__1_p0_o.data)[__g_11006] = SISAL_CAST(sisal_array_t, v_BODY_11009_n__8_RROW));
      (((double *)v_g1_n__1_p1_o.data)[__g_11006] = SISAL_CAST(double, v_BODY_11009_n__8_RB));
      (__g_11006++);
    }
    sisal_array_t __e0_v_g1_n__1_p0_o = ((sisal_array_t *)v_g1_n__1_p0_o.data)[0];
    sisal_array_t __flat_v_g1_n__1_p0_o = sisal_array_alloc_sized((1 + __e0_v_g1_n__1_p0_o.rank), __e0_v_g1_n__1_p0_o.type_id, ((uint64_t)(((uint64_t)(1 * ((int32_t)v_GENERATOR_11008_n__0_A.dims[0]))) * __e0_v_g1_n__1_p0_o.size)), sisal_esz(__e0_v_g1_n__1_p0_o));
    (__flat_v_g1_n__1_p0_o.dims[0] = ((int32_t)v_GENERATOR_11008_n__0_A.dims[0]));
    (__flat_v_g1_n__1_p0_o.lower_bound[0] = 1);
    for (int32_t __fk_v_g1_n__1_p0_o = 0; (__fk_v_g1_n__1_p0_o < __e0_v_g1_n__1_p0_o.rank); (__fk_v_g1_n__1_p0_o++)) {
      (__flat_v_g1_n__1_p0_o.dims[(1 + __fk_v_g1_n__1_p0_o)] = __e0_v_g1_n__1_p0_o.dims[__fk_v_g1_n__1_p0_o]);
      (__flat_v_g1_n__1_p0_o.lower_bound[(1 + __fk_v_g1_n__1_p0_o)] = __e0_v_g1_n__1_p0_o.lower_bound[__fk_v_g1_n__1_p0_o]);
    }
    for (int32_t __fi_v_g1_n__1_p0_o = 0; (__fi_v_g1_n__1_p0_o < ((int32_t)(1 * ((int32_t)v_GENERATOR_11008_n__0_A.dims[0])))); (__fi_v_g1_n__1_p0_o++)) {
      memcpy((((char *)__flat_v_g1_n__1_p0_o.data) + (((uint64_t)__fi_v_g1_n__1_p0_o) * (__e0_v_g1_n__1_p0_o.size * sisal_esz(__e0_v_g1_n__1_p0_o)))), ((sisal_array_t *)v_g1_n__1_p0_o.data)[__fi_v_g1_n__1_p0_o].data, (__e0_v_g1_n__1_p0_o.size * sisal_esz(__e0_v_g1_n__1_p0_o)));
    }
    (v_g1_n__1_p0_o = __flat_v_g1_n__1_p0_o);
  }
  int32_t v_g1_n__3_p0_o = 0;
  (v_g1_n__3_p0_o = SISAL_CAST(int32_t, ((int32_t)SISAL_CAST(sisal_array_t, v_g1_n__0_A).lower_bound[0])));
  sisal_array_t v_g1_n__4_p0_o = {0};
  (v_g1_n__4_p0_o = SISAL_CAST(sisal_array_t, sisal_array_setl(SISAL_CAST(sisal_array_t, v_g1_n__1_p0_o), ((int64_t)SISAL_CAST(int32_t, v_g1_n__3_p0_o)))));
  (v_g1_n__0_p0_i = SISAL_CAST(sisal_array_t, v_g1_n__4_p0_o));
  (v_g1_n__0_p1_i = SISAL_CAST(sisal_array_t, v_g1_n__1_p1_o));
  struct FUNC_REDUCE_results __res_obj;
  (__res_obj.res_0 = SISAL_CAST(sisal_array_t, v_g1_n__0_p0_i));
  (__res_obj.res_1 = SISAL_CAST(sisal_array_t, v_g1_n__0_p1_i));
  return __res_obj;
}

extern "C" sisal_array_t func_MAIN(int32_t N, sisal_array_t AIN, sisal_array_t BIN) {
  sisal_array_t v_g2_n__0_AIN = {0};
  sisal_array_t v_g2_n__0_BIN = {0};
  int32_t v_g2_n__0_N = 0;
  (v_g2_n__0_N = SISAL_CAST(int32_t, N));
  (v_g2_n__0_AIN = SISAL_CAST(sisal_array_t, AIN));
  (v_g2_n__0_BIN = SISAL_CAST(sisal_array_t, BIN));
  sisal_array_t v_g2_n__0_p0_i = {0};
  sisal_array_t v_g2_n__1_p0_o = {0};
  {
    sisal_array_t v_LoopB_10001_n__5_MERGE_A = {0};
    sisal_array_t v_LoopB_10001_n__6_MERGE_B = {0};
    int32_t v_LoopB_10001_n__7_MERGE_I = 0;
    sisal_array_t v_LoopB_10001_n__8_MERGE_OLD_A = {0};
    sisal_array_t v_LoopB_10001_n__9_MERGE_OLD_B = {0};
    int32_t v_LoopB_10001_n__10_MERGE_OLD_I = 0;
    bool v_LoopB_10001_n__11_MERGE_first = 0;
    int32_t v_LoopB_10001_bodycap_n2_p0 = 0;
    sisal_array_t v_LoopB_10001_bodycap_n3_p0 = {0};
    sisal_array_t v_LoopB_10001_bodycap_n3_p1 = {0};
    bool v_LoopB_10001_bodycap_n5_p0 = 0;
    sisal_array_t v_LoopB_10001_n__0_AIN = {0};
    (v_LoopB_10001_n__0_AIN = SISAL_CAST(sisal_array_t, v_g2_n__0_AIN));
    sisal_array_t v_LoopB_10001_n__0_BIN = {0};
    (v_LoopB_10001_n__0_BIN = SISAL_CAST(sisal_array_t, v_g2_n__0_BIN));
    int32_t v_LoopB_10001_n__0_N = 0;
    (v_LoopB_10001_n__0_N = SISAL_CAST(int32_t, v_g2_n__0_N));
    sisal_array_t v_INIT_10005_n__0_A = {0};
    sisal_array_t v_INIT_10005_n__0_AIN = {0};
    sisal_array_t v_INIT_10005_n__0_B = {0};
    sisal_array_t v_INIT_10005_n__0_BIN = {0};
    int32_t v_INIT_10005_n__1_I = 0;
    int32_t v_INIT_10005_n__0_N = 0;
    sisal_array_t v_INIT_10005_n__0_OLD_A = {0};
    sisal_array_t v_INIT_10005_n__0_OLD_B = {0};
    int32_t v_INIT_10005_n__1_OLD_I = 0;
    (v_INIT_10005_n__0_OLD_A = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__0_AIN));
    (v_INIT_10005_n__0_OLD_B = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__0_BIN));
    (v_INIT_10005_n__0_N = SISAL_CAST(int32_t, v_LoopB_10001_n__0_N));
    (v_INIT_10005_n__1_OLD_I = SISAL_CAST(int32_t, 0));
    bool v_INIT_10005_n__2_p0_o = 0;
    (v_INIT_10005_n__2_p0_o = SISAL_CAST(bool, true));
    (v_LoopB_10001_n__5_MERGE_A = v_INIT_10005_n__0_OLD_A);
    (v_LoopB_10001_n__6_MERGE_B = v_INIT_10005_n__0_OLD_B);
    (v_LoopB_10001_n__7_MERGE_I = v_INIT_10005_n__1_OLD_I);
    (v_LoopB_10001_n__8_MERGE_OLD_A = v_INIT_10005_n__0_OLD_A);
    (v_LoopB_10001_n__9_MERGE_OLD_B = v_INIT_10005_n__0_OLD_B);
    (v_LoopB_10001_n__10_MERGE_OLD_I = v_INIT_10005_n__1_OLD_I);
    (v_LoopB_10001_n__11_MERGE_first = v_INIT_10005_n__2_p0_o);
    sisal_array_t v_TEST_10004_n__0_A = {0};
    sisal_array_t v_TEST_10004_n__0_AIN = {0};
    sisal_array_t v_TEST_10004_n__0_B = {0};
    sisal_array_t v_TEST_10004_n__0_BIN = {0};
    int32_t v_TEST_10004_n__0_I = 0;
    int32_t v_TEST_10004_n__0_N = 0;
    sisal_array_t v_TEST_10004_n__0_OLD_A = {0};
    sisal_array_t v_TEST_10004_n__0_OLD_B = {0};
    int32_t v_TEST_10004_n__0_OLD_I = 0;
    (v_TEST_10004_n__0_A = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__5_MERGE_A));
    (v_TEST_10004_n__0_AIN = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__0_AIN));
    (v_TEST_10004_n__0_B = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__6_MERGE_B));
    (v_TEST_10004_n__0_BIN = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__0_BIN));
    (v_TEST_10004_n__0_I = SISAL_CAST(int32_t, v_LoopB_10001_n__7_MERGE_I));
    (v_TEST_10004_n__0_N = SISAL_CAST(int32_t, v_LoopB_10001_n__0_N));
    (v_TEST_10004_n__0_OLD_A = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__8_MERGE_OLD_A));
    (v_TEST_10004_n__0_OLD_B = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__9_MERGE_OLD_B));
    (v_TEST_10004_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_10001_n__10_MERGE_OLD_I));
    bool v_TEST_10004_n__1_p0_o = 0;
    (v_TEST_10004_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_TEST_10004_n__0_I) < SISAL_CAST(int32_t, v_TEST_10004_n__0_N))));
    while (v_TEST_10004_n__1_p0_o) {
      sisal_array_t v_BODY_10002_n__3_A = {0};
      sisal_array_t v_BODY_10002_n__0_AIN = {0};
      sisal_array_t v_BODY_10002_n__3_B = {0};
      sisal_array_t v_BODY_10002_n__0_BIN = {0};
      int32_t v_BODY_10002_n__2_I = 0;
      int32_t v_BODY_10002_n__0_N = 0;
      sisal_array_t v_BODY_10002_n__0_OLD_A = {0};
      sisal_array_t v_BODY_10002_n__0_OLD_B = {0};
      int32_t v_BODY_10002_n__0_OLD_I = 0;
      sisal_array_t v_BODY_10002_n__0_p0_o = {0};
      (v_BODY_10002_n__0_p0_o = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__5_MERGE_A));
      (v_BODY_10002_n__0_AIN = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__0_AIN));
      sisal_array_t v_BODY_10002_n__0_p2_o = {0};
      (v_BODY_10002_n__0_p2_o = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__6_MERGE_B));
      (v_BODY_10002_n__0_BIN = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__0_BIN));
      int32_t v_BODY_10002_n__0_p4_o = 0;
      (v_BODY_10002_n__0_p4_o = SISAL_CAST(int32_t, v_LoopB_10001_n__7_MERGE_I));
      (v_BODY_10002_n__0_N = SISAL_CAST(int32_t, v_LoopB_10001_n__0_N));
      (v_BODY_10002_n__0_OLD_A = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__8_MERGE_OLD_A));
      (v_BODY_10002_n__0_OLD_B = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__9_MERGE_OLD_B));
      (v_BODY_10002_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_10001_n__10_MERGE_OLD_I));
      int32_t v_BODY_10002_n__1_p0_o = 0;
      (v_BODY_10002_n__1_p0_o = SISAL_CAST(int32_t, 1));
      (v_BODY_10002_n__2_I = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_10002_n__0_OLD_I) + SISAL_CAST(int32_t, v_BODY_10002_n__1_p0_o))));
      struct FUNC_REDUCE_results _mr_BODY_10002_3 = func_REDUCE(SISAL_CAST(sisal_array_t, v_BODY_10002_n__0_OLD_A), SISAL_CAST(int32_t, v_BODY_10002_n__2_I), SISAL_CAST(sisal_array_t, v_BODY_10002_n__0_OLD_B));
      (v_BODY_10002_n__3_A = SISAL_CAST(sisal_array_t, _mr_BODY_10002_3.res_0));
      (v_BODY_10002_n__3_B = SISAL_CAST(sisal_array_t, _mr_BODY_10002_3.res_1));
      bool v_BODY_10002_n__5_p0_o = 0;
      (v_BODY_10002_n__5_p0_o = SISAL_CAST(bool, false));
      (v_LoopB_10001_bodycap_n2_p0 = v_BODY_10002_n__2_I);
      (v_LoopB_10001_bodycap_n3_p0 = v_BODY_10002_n__3_A);
      (v_LoopB_10001_bodycap_n3_p1 = v_BODY_10002_n__3_B);
      (v_LoopB_10001_bodycap_n5_p0 = v_BODY_10002_n__5_p0_o);
      (v_LoopB_10001_n__5_MERGE_A = v_LoopB_10001_bodycap_n3_p0);
      (v_LoopB_10001_n__6_MERGE_B = v_LoopB_10001_bodycap_n3_p1);
      (v_LoopB_10001_n__7_MERGE_I = v_LoopB_10001_bodycap_n2_p0);
      (v_LoopB_10001_n__8_MERGE_OLD_A = v_LoopB_10001_bodycap_n3_p0);
      (v_LoopB_10001_n__9_MERGE_OLD_B = v_LoopB_10001_bodycap_n3_p1);
      (v_LoopB_10001_n__10_MERGE_OLD_I = v_LoopB_10001_bodycap_n2_p0);
      (v_LoopB_10001_n__11_MERGE_first = v_LoopB_10001_bodycap_n5_p0);
      (v_TEST_10004_n__0_A = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__5_MERGE_A));
      (v_TEST_10004_n__0_AIN = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__0_AIN));
      (v_TEST_10004_n__0_B = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__6_MERGE_B));
      (v_TEST_10004_n__0_BIN = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__0_BIN));
      (v_TEST_10004_n__0_I = SISAL_CAST(int32_t, v_LoopB_10001_n__7_MERGE_I));
      (v_TEST_10004_n__0_N = SISAL_CAST(int32_t, v_LoopB_10001_n__0_N));
      (v_TEST_10004_n__0_OLD_A = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__8_MERGE_OLD_A));
      (v_TEST_10004_n__0_OLD_B = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__9_MERGE_OLD_B));
      (v_TEST_10004_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_10001_n__10_MERGE_OLD_I));
      (v_TEST_10004_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_TEST_10004_n__0_I) < SISAL_CAST(int32_t, v_TEST_10004_n__0_N))));
    }
    sisal_array_t v_RETURNS_10003_n__0_p0_o = {0};
    (v_RETURNS_10003_n__0_p0_o = SISAL_CAST(sisal_array_t, v_LoopB_10001_bodycap_n3_p1));
    sisal_array_t v_RETURNS_10003_n__1_p0_o = {0};
    (v_RETURNS_10003_n__1_p0_o = SISAL_CAST(sisal_array_t, SISAL_CAST(sisal_array_t, v_RETURNS_10003_n__0_p0_o)));
    (v_g2_n__1_p0_o = SISAL_CAST(sisal_array_t, v_RETURNS_10003_n__1_p0_o));
  }
  (v_g2_n__0_p0_i = SISAL_CAST(sisal_array_t, v_g2_n__1_p0_o));
  return SISAL_CAST(sisal_array_t, v_g2_n__0_p0_i);
}
