#define SISAL_CUSTOM_ELEM_SIZE

#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <math.h>
#include <iostream>
#include <dispatch/dispatch.h>
#include <Accelerate/Accelerate.h>
#include <sisal_runtime.h>

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
        case 95:
        case 96:
        case 97:
        case 98:
        case 99:
        case 100:
        case 101:
        case 102:
        case 103:
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

extern "C" sisal_array_t func_MAIN(int32_t LEVEL);
extern "C" bool func_IN_CHECK(int32_t R, int32_t C, sisal_array_t QUEENS);

extern "C" bool func_IN_CHECK(int32_t R, int32_t C, sisal_array_t QUEENS) {
  int32_t v_g1_n__0_C = 0;
  sisal_array_t v_g1_n__0_QUEENS = {0};
  int32_t v_g1_n__0_R = 0;
  (v_g1_n__0_R = SISAL_CAST(int32_t, R));
  (v_g1_n__0_C = SISAL_CAST(int32_t, C));
  (v_g1_n__0_QUEENS = SISAL_CAST(sisal_array_t, QUEENS));
  bool v_g1_n__0_p0_i = 0;
  bool v_g1_n__1_p0_o = 0;
  {
    int32_t v_FORALL_11021_n__0_C = v_g1_n__0_C;
    int32_t v_FORALL_11021_n__2_COLUMN;
    sisal_array_t v_FORALL_11021_n__0_QUEENS = v_g1_n__0_QUEENS;
    int32_t v_FORALL_11021_n__0_R = v_g1_n__0_R;
    int32_t v_FORALL_11021_n__2_ROW;
    bool v_FORALL_11021_n__3___forall_body_0;
    int32_t v_GENERATOR_11023_n__0_C;
    int32_t v_GENERATOR_11023_n__1_COLUMN;
    sisal_array_t v_GENERATOR_11023_n__0_QUEENS;
    int32_t v_GENERATOR_11023_n__0_R;
    int32_t v_GENERATOR_11023_n__1_ROW;
    int32_t v_BODY_11024_n__0_C;
    int32_t v_BODY_11024_n__0_COLUMN;
    sisal_array_t v_BODY_11024_n__0_QUEENS;
    int32_t v_BODY_11024_n__0_R;
    int32_t v_BODY_11024_n__0_ROW;
    (v_GENERATOR_11023_n__0_QUEENS = v_FORALL_11021_n__0_QUEENS);
    (v_g1_n__1_p0_o = 0);
    for (int32_t __k_11023 = 0; (__k_11023 < ((int32_t)v_GENERATOR_11023_n__0_QUEENS.size)); (__k_11023++)) {
      (v_GENERATOR_11023_n__1_ROW = ((int32_t *)v_GENERATOR_11023_n__0_QUEENS.data)[__k_11023]);
      (v_GENERATOR_11023_n__1_COLUMN = (((int32_t)v_GENERATOR_11023_n__0_QUEENS.lower_bound[0]) + __k_11023));
      (v_BODY_11024_n__0_C = SISAL_CAST(int32_t, v_FORALL_11021_n__0_C));
      (v_BODY_11024_n__0_COLUMN = SISAL_CAST(int32_t, v_GENERATOR_11023_n__1_COLUMN));
      (v_BODY_11024_n__0_QUEENS = SISAL_CAST(sisal_array_t, v_FORALL_11021_n__0_QUEENS));
      (v_BODY_11024_n__0_R = SISAL_CAST(int32_t, v_FORALL_11021_n__0_R));
      (v_BODY_11024_n__0_ROW = SISAL_CAST(int32_t, v_GENERATOR_11023_n__1_ROW));
      bool v_BODY_11024_n__1_p0_o = 0;
      (v_BODY_11024_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_BODY_11024_n__0_R) == SISAL_CAST(int32_t, v_BODY_11024_n__0_ROW))));
      int32_t v_BODY_11024_n__3_p0_o = 0;
      (v_BODY_11024_n__3_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_11024_n__0_ROW) + SISAL_CAST(int32_t, v_BODY_11024_n__0_COLUMN))));
      int32_t v_BODY_11024_n__5_p0_o = 0;
      (v_BODY_11024_n__5_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_11024_n__0_R) + SISAL_CAST(int32_t, v_BODY_11024_n__0_C))));
      bool v_BODY_11024_n__7_p0_o = 0;
      (v_BODY_11024_n__7_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_BODY_11024_n__3_p0_o) == SISAL_CAST(int32_t, v_BODY_11024_n__5_p0_o))));
      bool v_BODY_11024_n__9_p0_o = 0;
      (v_BODY_11024_n__9_p0_o = SISAL_CAST(bool, (SISAL_CAST(bool, v_BODY_11024_n__1_p0_o) || SISAL_CAST(bool, v_BODY_11024_n__7_p0_o))));
      int32_t v_BODY_11024_n__10_p0_o = 0;
      (v_BODY_11024_n__10_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_11024_n__0_ROW) - SISAL_CAST(int32_t, v_BODY_11024_n__0_COLUMN))));
      int32_t v_BODY_11024_n__12_p0_o = 0;
      (v_BODY_11024_n__12_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_11024_n__0_R) - SISAL_CAST(int32_t, v_BODY_11024_n__0_C))));
      bool v_BODY_11024_n__14_p0_o = 0;
      (v_BODY_11024_n__14_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_BODY_11024_n__10_p0_o) == SISAL_CAST(int32_t, v_BODY_11024_n__12_p0_o))));
      bool v_BODY_11024_n__16_p0_o = 0;
      (v_BODY_11024_n__16_p0_o = SISAL_CAST(bool, (SISAL_CAST(bool, v_BODY_11024_n__9_p0_o) || SISAL_CAST(bool, v_BODY_11024_n__14_p0_o))));
      (v_g1_n__1_p0_o = (v_g1_n__1_p0_o || SISAL_CAST(bool, v_BODY_11024_n__16_p0_o)));
    }
  }
  (v_g1_n__0_p0_i = SISAL_CAST(bool, v_g1_n__1_p0_o));
  return SISAL_CAST(bool, v_g1_n__0_p0_i);
}

extern "C" sisal_array_t func_MAIN(int32_t LEVEL) {
  int32_t v_g2_n__0_LEVEL = 0;
  (v_g2_n__0_LEVEL = SISAL_CAST(int32_t, LEVEL));
  sisal_array_t v_g2_n__0_p0_i = {0};
  sisal_array_t v_g2_n__1_p0_o = {0};
  int32_t v_IF_array_array_INTEGRAL_____10001_n__0_LEVEL = 0;
  (v_IF_array_array_INTEGRAL_____10001_n__0_LEVEL = SISAL_CAST(int32_t, v_g2_n__0_LEVEL));
  {
    int32_t v_PREDICATE_10002_n__0_LEVEL = 0;
    (v_PREDICATE_10002_n__0_LEVEL = SISAL_CAST(int32_t, v_IF_array_array_INTEGRAL_____10001_n__0_LEVEL));
    int32_t v_PREDICATE_10002_n__1_p0_o = 0;
    (v_PREDICATE_10002_n__1_p0_o = SISAL_CAST(int32_t, 1));
    bool v_PREDICATE_10002_n__2_p0_o = 0;
    (v_PREDICATE_10002_n__2_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_PREDICATE_10002_n__0_LEVEL) == SISAL_CAST(int32_t, v_PREDICATE_10002_n__1_p0_o))));
    if (v_PREDICATE_10002_n__2_p0_o) {
      int32_t v_THEN_10016_n__0_LEVEL = 0;
      (v_THEN_10016_n__0_LEVEL = SISAL_CAST(int32_t, v_IF_array_array_INTEGRAL_____10001_n__0_LEVEL));
      sisal_array_t v_THEN_10016_n__1_p0_o = {0};
      {
        int32_t v_FORALL_10017_n__0_LEVEL = v_THEN_10016_n__0_LEVEL;
        int32_t v_FORALL_10017_n__2_ROW;
        sisal_array_t v_FORALL_10017_n__3___forall_body_0;
        int32_t v_FORALL_10017_n__2___forall_lb_3_0;
        int32_t v_FORALL_10017_n__2___forall_ub_3_0;
        int32_t v_GENERATOR_10019_n__0_LEVEL;
        int32_t v_GENERATOR_10019_n__3_ROW;
        int32_t v_GENERATOR_10019_n__3___forall_lb_3_0;
        int32_t v_GENERATOR_10019_n__3___forall_ub_3_0;
        sisal_array_t v_BODY_10020_n__3_ASSIGNMENT;
        int32_t v_BODY_10020_n__0_LEVEL;
        int32_t v_BODY_10020_n__0_ROW;
        int32_t v_BODY_10020_n__0___forall_lb_3_0;
        int32_t v_BODY_10020_n__0___forall_ub_3_0;
        (v_GENERATOR_10019_n__3___forall_lb_3_0 = 1);
        (v_GENERATOR_10019_n__3___forall_ub_3_0 = 4);
        (v_THEN_10016_n__1_p0_o = sisal_array_alloc_sized(1, 94, ((uint64_t)(1 * ((4 - 1) + 1))), sizeof(sisal_array_t)));
        (v_THEN_10016_n__1_p0_o.dims[0] = ((4 - 1) + 1));
        (v_THEN_10016_n__1_p0_o.lower_bound[0] = 1);
        int32_t __g_10017 = 0;
        for ((v_GENERATOR_10019_n__3_ROW = 1); (v_GENERATOR_10019_n__3_ROW <= 4); (v_GENERATOR_10019_n__3_ROW++)) {
          (v_BODY_10020_n__0_LEVEL = SISAL_CAST(int32_t, v_FORALL_10017_n__0_LEVEL));
          (v_BODY_10020_n__0_ROW = SISAL_CAST(int32_t, v_GENERATOR_10019_n__3_ROW));
          (v_BODY_10020_n__0___forall_lb_3_0 = SISAL_CAST(int32_t, v_GENERATOR_10019_n__3___forall_lb_3_0));
          (v_BODY_10020_n__0___forall_ub_3_0 = SISAL_CAST(int32_t, v_GENERATOR_10019_n__3___forall_ub_3_0));
          int32_t v_BODY_10020_n__1_p0_o = 0;
          (v_BODY_10020_n__1_p0_o = SISAL_CAST(int32_t, 1));
          (v_BODY_10020_n__3_ASSIGNMENT = SISAL_CAST(sisal_array_t, ([&]() -> sisal_array_t { const int32_t __arr[] = {v_BODY_10020_n__0_ROW}; return sisal_array_build_i32(v_BODY_10020_n__1_p0_o, 1, __arr); })()));
          (((sisal_array_t *)v_THEN_10016_n__1_p0_o.data)[__g_10017] = SISAL_CAST(sisal_array_t, v_BODY_10020_n__3_ASSIGNMENT));
          (__g_10017++);
        }
        sisal_array_t __e0_v_THEN_10016_n__1_p0_o = ((sisal_array_t *)v_THEN_10016_n__1_p0_o.data)[0];
        sisal_array_t __flat_v_THEN_10016_n__1_p0_o = sisal_array_alloc_sized((1 + __e0_v_THEN_10016_n__1_p0_o.rank), __e0_v_THEN_10016_n__1_p0_o.type_id, ((uint64_t)(((uint64_t)(1 * ((4 - 1) + 1))) * __e0_v_THEN_10016_n__1_p0_o.size)), sisal_esz(__e0_v_THEN_10016_n__1_p0_o));
        (__flat_v_THEN_10016_n__1_p0_o.dims[0] = ((4 - 1) + 1));
        (__flat_v_THEN_10016_n__1_p0_o.lower_bound[0] = 1);
        for (int32_t __fk_v_THEN_10016_n__1_p0_o = 0; (__fk_v_THEN_10016_n__1_p0_o < __e0_v_THEN_10016_n__1_p0_o.rank); (__fk_v_THEN_10016_n__1_p0_o++)) {
          (__flat_v_THEN_10016_n__1_p0_o.dims[(1 + __fk_v_THEN_10016_n__1_p0_o)] = __e0_v_THEN_10016_n__1_p0_o.dims[__fk_v_THEN_10016_n__1_p0_o]);
          (__flat_v_THEN_10016_n__1_p0_o.lower_bound[(1 + __fk_v_THEN_10016_n__1_p0_o)] = __e0_v_THEN_10016_n__1_p0_o.lower_bound[__fk_v_THEN_10016_n__1_p0_o]);
        }
        for (int32_t __fi_v_THEN_10016_n__1_p0_o = 0; (__fi_v_THEN_10016_n__1_p0_o < ((int32_t)(1 * ((4 - 1) + 1)))); (__fi_v_THEN_10016_n__1_p0_o++)) {
          memcpy((((char *)__flat_v_THEN_10016_n__1_p0_o.data) + (((uint64_t)__fi_v_THEN_10016_n__1_p0_o) * (__e0_v_THEN_10016_n__1_p0_o.size * sisal_esz(__e0_v_THEN_10016_n__1_p0_o)))), ((sisal_array_t *)v_THEN_10016_n__1_p0_o.data)[__fi_v_THEN_10016_n__1_p0_o].data, (__e0_v_THEN_10016_n__1_p0_o.size * sisal_esz(__e0_v_THEN_10016_n__1_p0_o)));
        }
        (v_THEN_10016_n__1_p0_o = __flat_v_THEN_10016_n__1_p0_o);
      }
      int32_t v_THEN_10016_n__3_p0_o = 0;
      (v_THEN_10016_n__3_p0_o = SISAL_CAST(int32_t, 1));
      sisal_array_t v_THEN_10016_n__4_p0_o = {0};
      (v_THEN_10016_n__4_p0_o = SISAL_CAST(sisal_array_t, sisal_array_setl(SISAL_CAST(sisal_array_t, v_THEN_10016_n__1_p0_o), ((int64_t)SISAL_CAST(int32_t, v_THEN_10016_n__3_p0_o)))));
      (v_g2_n__1_p0_o = SISAL_CAST(sisal_array_t, v_THEN_10016_n__4_p0_o));
    }
    else {
      int32_t v_ELSE_10003_n__0_LEVEL = 0;
      (v_ELSE_10003_n__0_LEVEL = SISAL_CAST(int32_t, v_IF_array_array_INTEGRAL_____10001_n__0_LEVEL));
      sisal_array_t v_ELSE_10003_n__1_p0_o = {0};
      {
        int32_t v_FORALL_10004_n__0_LEVEL = v_ELSE_10003_n__0_LEVEL;
        sisal_array_t v_FORALL_10004_n__2_PARTIAL_ASSIGNMENT;
        sisal_array_t v_FORALL_10004_n__3___forall_body_0;
        int32_t v_GENERATOR_10006_n__0_LEVEL;
        sisal_array_t v_GENERATOR_10006_n__6_PARTIAL_ASSIGNMENT;
        int32_t v_BODY_10007_n__3_COLUMN;
        int32_t v_BODY_10007_n__0_LEVEL;
        sisal_array_t v_BODY_10007_n__7_NEW_ASSIGNMENT;
        sisal_array_t v_BODY_10007_n__0_PARTIAL_ASSIGNMENT;
        int32_t v_FORALL_10008_n__0_COLUMN;
        int32_t v_FORALL_10008_n__0_LEVEL;
        sisal_array_t v_FORALL_10008_n__0_PARTIAL_ASSIGNMENT;
        int32_t v_FORALL_10008_n__2_ROW;
        sisal_array_t v_FORALL_10008_n__3___forall_body_0;
        int32_t v_FORALL_10008_n__2___forall_lb_3_0;
        int32_t v_FORALL_10008_n__2___forall_ub_3_0;
        int32_t v_GENERATOR_10010_n__0_COLUMN;
        int32_t v_GENERATOR_10010_n__0_LEVEL;
        sisal_array_t v_GENERATOR_10010_n__0_PARTIAL_ASSIGNMENT;
        int32_t v_GENERATOR_10010_n__3_ROW;
        int32_t v_GENERATOR_10010_n__3___forall_lb_3_0;
        int32_t v_GENERATOR_10010_n__3___forall_ub_3_0;
        sisal_array_t v_BODY_10011_n__2_ASSIGNMENT;
        int32_t v_BODY_10011_n__0_COLUMN;
        bool v_BODY_10011_n__1_ISCHECK;
        int32_t v_BODY_10011_n__0_LEVEL;
        sisal_array_t v_BODY_10011_n__0_PARTIAL_ASSIGNMENT;
        int32_t v_BODY_10011_n__0_ROW;
        int32_t v_BODY_10011_n__0___forall_lb_3_0;
        int32_t v_BODY_10011_n__0___forall_ub_3_0;
        bool v_IF_array_INTEGRAL____10012_n__0_ISCHECK;
        sisal_array_t v_IF_array_INTEGRAL____10012_n__0_PARTIAL_ASSIGNMENT;
        int32_t v_IF_array_INTEGRAL____10012_n__0_ROW;
        bool v_PREDICATE_10013_n__0_ISCHECK;
        sisal_array_t v_ELSE_10014_n__0_PARTIAL_ASSIGNMENT;
        int32_t v_ELSE_10014_n__0_ROW;
        (v_GENERATOR_10006_n__0_LEVEL = v_FORALL_10004_n__0_LEVEL);
        float v_GENERATOR_10006_n__2_p0_o = 0;
        (v_GENERATOR_10006_n__2_p0_o = SISAL_CAST(float, (SISAL_CAST(int32_t, v_GENERATOR_10006_n__0_LEVEL) - SISAL_CAST(int32_t, 1))));
        int32_t v_GENERATOR_10006_n__4_p0_o = 0;
        (v_GENERATOR_10006_n__4_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_GENERATOR_10006_n__0_LEVEL) - SISAL_CAST(int32_t, 1))));
        sisal_array_t v_GENERATOR_10006_n__5_p0_o = {0};
        (v_GENERATOR_10006_n__5_p0_o = SISAL_CAST(sisal_array_t, func_MAIN(SISAL_CAST(int32_t, v_GENERATOR_10006_n__4_p0_o))));
        (v_ELSE_10003_n__1_p0_o = sisal_array_empty());
        for (int32_t __k_10006 = 0; (__k_10006 < ((int32_t)v_GENERATOR_10006_n__5_p0_o.size)); (__k_10006++)) {
          (v_GENERATOR_10006_n__6_PARTIAL_ASSIGNMENT = ((sisal_array_t *)v_GENERATOR_10006_n__5_p0_o.data)[__k_10006]);
          (v_BODY_10007_n__0_LEVEL = SISAL_CAST(int32_t, v_FORALL_10004_n__0_LEVEL));
          (v_BODY_10007_n__0_PARTIAL_ASSIGNMENT = SISAL_CAST(sisal_array_t, v_GENERATOR_10006_n__6_PARTIAL_ASSIGNMENT));
          int32_t v_BODY_10007_n__1_p0_o = 0;
          (v_BODY_10007_n__1_p0_o = SISAL_CAST(int32_t, 1));
          int32_t v_BODY_10007_n__2_p0_o = 0;
          (v_BODY_10007_n__2_p0_o = SISAL_CAST(int32_t, ((int32_t)((SISAL_CAST(sisal_array_t, v_BODY_10007_n__0_PARTIAL_ASSIGNMENT).dims[0] > 0) ? SISAL_CAST(sisal_array_t, v_BODY_10007_n__0_PARTIAL_ASSIGNMENT).dims[0] : ((int64_t)SISAL_CAST(sisal_array_t, v_BODY_10007_n__0_PARTIAL_ASSIGNMENT).size)))));
          (v_BODY_10007_n__3_COLUMN = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_10007_n__1_p0_o) + SISAL_CAST(int32_t, v_BODY_10007_n__2_p0_o))));
          sisal_array_t v_BODY_10007_n__4_p0_o = {0};
          {
            int32_t v_FORALL_10008_n__0_COLUMN = v_BODY_10007_n__3_COLUMN;
            int32_t v_FORALL_10008_n__0_LEVEL = v_BODY_10007_n__0_LEVEL;
            sisal_array_t v_FORALL_10008_n__0_PARTIAL_ASSIGNMENT = v_BODY_10007_n__0_PARTIAL_ASSIGNMENT;
            int32_t v_FORALL_10008_n__2_ROW;
            sisal_array_t v_FORALL_10008_n__3___forall_body_0;
            int32_t v_FORALL_10008_n__2___forall_lb_3_0;
            int32_t v_FORALL_10008_n__2___forall_ub_3_0;
            int32_t v_GENERATOR_10010_n__0_COLUMN;
            int32_t v_GENERATOR_10010_n__0_LEVEL;
            sisal_array_t v_GENERATOR_10010_n__0_PARTIAL_ASSIGNMENT;
            int32_t v_GENERATOR_10010_n__3_ROW;
            int32_t v_GENERATOR_10010_n__3___forall_lb_3_0;
            int32_t v_GENERATOR_10010_n__3___forall_ub_3_0;
            sisal_array_t v_BODY_10011_n__2_ASSIGNMENT;
            int32_t v_BODY_10011_n__0_COLUMN;
            bool v_BODY_10011_n__1_ISCHECK;
            int32_t v_BODY_10011_n__0_LEVEL;
            sisal_array_t v_BODY_10011_n__0_PARTIAL_ASSIGNMENT;
            int32_t v_BODY_10011_n__0_ROW;
            int32_t v_BODY_10011_n__0___forall_lb_3_0;
            int32_t v_BODY_10011_n__0___forall_ub_3_0;
            bool v_IF_array_INTEGRAL____10012_n__0_ISCHECK;
            sisal_array_t v_IF_array_INTEGRAL____10012_n__0_PARTIAL_ASSIGNMENT;
            int32_t v_IF_array_INTEGRAL____10012_n__0_ROW;
            bool v_PREDICATE_10013_n__0_ISCHECK;
            sisal_array_t v_ELSE_10014_n__0_PARTIAL_ASSIGNMENT;
            int32_t v_ELSE_10014_n__0_ROW;
            (v_GENERATOR_10010_n__3___forall_lb_3_0 = 1);
            (v_GENERATOR_10010_n__3___forall_ub_3_0 = 8);
            (v_BODY_10007_n__4_p0_o = sisal_array_alloc_sized(1, 94, ((uint64_t)(1 * ((8 - 1) + 1))), sizeof(sisal_array_t)));
            (v_BODY_10007_n__4_p0_o.dims[0] = ((8 - 1) + 1));
            (v_BODY_10007_n__4_p0_o.lower_bound[0] = 1);
            int32_t __g_10008 = 0;
            for ((v_GENERATOR_10010_n__3_ROW = 1); (v_GENERATOR_10010_n__3_ROW <= 8); (v_GENERATOR_10010_n__3_ROW++)) {
              (v_BODY_10011_n__0_COLUMN = SISAL_CAST(int32_t, v_FORALL_10008_n__0_COLUMN));
              (v_BODY_10011_n__0_LEVEL = SISAL_CAST(int32_t, v_FORALL_10008_n__0_LEVEL));
              (v_BODY_10011_n__0_PARTIAL_ASSIGNMENT = SISAL_CAST(sisal_array_t, v_FORALL_10008_n__0_PARTIAL_ASSIGNMENT));
              (v_BODY_10011_n__0_ROW = SISAL_CAST(int32_t, v_GENERATOR_10010_n__3_ROW));
              (v_BODY_10011_n__0___forall_lb_3_0 = SISAL_CAST(int32_t, v_GENERATOR_10010_n__3___forall_lb_3_0));
              (v_BODY_10011_n__0___forall_ub_3_0 = SISAL_CAST(int32_t, v_GENERATOR_10010_n__3___forall_ub_3_0));
              (v_BODY_10011_n__1_ISCHECK = SISAL_CAST(bool, func_IN_CHECK(SISAL_CAST(int32_t, v_BODY_10011_n__0_ROW), SISAL_CAST(int32_t, v_BODY_10011_n__0_COLUMN), SISAL_CAST(sisal_array_t, v_BODY_10011_n__0_PARTIAL_ASSIGNMENT))));
              (v_IF_array_INTEGRAL____10012_n__0_ISCHECK = SISAL_CAST(bool, v_BODY_10011_n__1_ISCHECK));
              (v_IF_array_INTEGRAL____10012_n__0_PARTIAL_ASSIGNMENT = SISAL_CAST(sisal_array_t, v_BODY_10011_n__0_PARTIAL_ASSIGNMENT));
              (v_IF_array_INTEGRAL____10012_n__0_ROW = SISAL_CAST(int32_t, v_BODY_10011_n__0_ROW));
              {
                (v_PREDICATE_10013_n__0_ISCHECK = SISAL_CAST(bool, v_IF_array_INTEGRAL____10012_n__0_ISCHECK));
                if (v_PREDICATE_10013_n__0_ISCHECK) {
                  sisal_array_t v_THEN_10015_n__1_p0_o = {0};
                  (v_THEN_10015_n__1_p0_o = SISAL_CAST(sisal_array_t, sisal_array_alloc_empty(1, 6, ((uint64_t)0))));
                  (v_BODY_10011_n__2_ASSIGNMENT = SISAL_CAST(sisal_array_t, v_THEN_10015_n__1_p0_o));
                }
                else {
                  (v_ELSE_10014_n__0_PARTIAL_ASSIGNMENT = SISAL_CAST(sisal_array_t, v_IF_array_INTEGRAL____10012_n__0_PARTIAL_ASSIGNMENT));
                  (v_ELSE_10014_n__0_ROW = SISAL_CAST(int32_t, v_IF_array_INTEGRAL____10012_n__0_ROW));
                  sisal_array_t v_ELSE_10014_n__1_p0_o = {0};
                  (v_ELSE_10014_n__1_p0_o = SISAL_CAST(sisal_array_t, sisal_array_addh_i32(SISAL_CAST(sisal_array_t, v_ELSE_10014_n__0_PARTIAL_ASSIGNMENT), SISAL_CAST(int32_t, v_ELSE_10014_n__0_ROW))));
                  (v_BODY_10011_n__2_ASSIGNMENT = SISAL_CAST(sisal_array_t, v_ELSE_10014_n__1_p0_o));
                }
              }
              bool v_BODY_10011_n__4_p0_o = 0;
              (v_BODY_10011_n__4_p0_o = SISAL_CAST(bool, (!SISAL_CAST(bool, v_BODY_10011_n__1_ISCHECK))));
              (((sisal_array_t *)v_BODY_10007_n__4_p0_o.data)[__g_10008] = SISAL_CAST(sisal_array_t, v_BODY_10011_n__2_ASSIGNMENT));
              (__g_10008++);
            }
            sisal_array_t __e0_v_BODY_10007_n__4_p0_o = ((sisal_array_t *)v_BODY_10007_n__4_p0_o.data)[0];
            sisal_array_t __flat_v_BODY_10007_n__4_p0_o = sisal_array_alloc_sized((1 + __e0_v_BODY_10007_n__4_p0_o.rank), __e0_v_BODY_10007_n__4_p0_o.type_id, ((uint64_t)(((uint64_t)(1 * ((8 - 1) + 1))) * __e0_v_BODY_10007_n__4_p0_o.size)), sisal_esz(__e0_v_BODY_10007_n__4_p0_o));
            (__flat_v_BODY_10007_n__4_p0_o.dims[0] = ((8 - 1) + 1));
            (__flat_v_BODY_10007_n__4_p0_o.lower_bound[0] = 1);
            for (int32_t __fk_v_BODY_10007_n__4_p0_o = 0; (__fk_v_BODY_10007_n__4_p0_o < __e0_v_BODY_10007_n__4_p0_o.rank); (__fk_v_BODY_10007_n__4_p0_o++)) {
              (__flat_v_BODY_10007_n__4_p0_o.dims[(1 + __fk_v_BODY_10007_n__4_p0_o)] = __e0_v_BODY_10007_n__4_p0_o.dims[__fk_v_BODY_10007_n__4_p0_o]);
              (__flat_v_BODY_10007_n__4_p0_o.lower_bound[(1 + __fk_v_BODY_10007_n__4_p0_o)] = __e0_v_BODY_10007_n__4_p0_o.lower_bound[__fk_v_BODY_10007_n__4_p0_o]);
            }
            for (int32_t __fi_v_BODY_10007_n__4_p0_o = 0; (__fi_v_BODY_10007_n__4_p0_o < ((int32_t)(1 * ((8 - 1) + 1)))); (__fi_v_BODY_10007_n__4_p0_o++)) {
              memcpy((((char *)__flat_v_BODY_10007_n__4_p0_o.data) + (((uint64_t)__fi_v_BODY_10007_n__4_p0_o) * (__e0_v_BODY_10007_n__4_p0_o.size * sisal_esz(__e0_v_BODY_10007_n__4_p0_o)))), ((sisal_array_t *)v_BODY_10007_n__4_p0_o.data)[__fi_v_BODY_10007_n__4_p0_o].data, (__e0_v_BODY_10007_n__4_p0_o.size * sisal_esz(__e0_v_BODY_10007_n__4_p0_o)));
            }
            (v_BODY_10007_n__4_p0_o = __flat_v_BODY_10007_n__4_p0_o);
          }
          int32_t v_BODY_10007_n__6_p0_o = 0;
          (v_BODY_10007_n__6_p0_o = SISAL_CAST(int32_t, 1));
          (v_BODY_10007_n__7_NEW_ASSIGNMENT = SISAL_CAST(sisal_array_t, sisal_array_setl(SISAL_CAST(sisal_array_t, v_BODY_10007_n__4_p0_o), ((int64_t)SISAL_CAST(int32_t, v_BODY_10007_n__6_p0_o)))));
          (v_ELSE_10003_n__1_p0_o = sisal_array_catenate(v_ELSE_10003_n__1_p0_o, v_BODY_10007_n__7_NEW_ASSIGNMENT));
        }
      }
      (v_g2_n__1_p0_o = SISAL_CAST(sisal_array_t, v_ELSE_10003_n__1_p0_o));
    }
  }
  (v_g2_n__0_p0_i = SISAL_CAST(sisal_array_t, v_g2_n__1_p0_o));
  return SISAL_CAST(sisal_array_t, v_g2_n__0_p0_i);
}
