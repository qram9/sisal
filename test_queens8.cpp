#define SISAL_CUSTOM_ELEM_SIZE

#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <math.h>
#include <iostream>
#include <dispatch/dispatch.h>
#include <Accelerate/Accelerate.h>
#include <sisal_runtime.h>

struct struct_rec_113 {
  int32_t lo;
  int32_t stride;
  int32_t size;
};
struct struct_rec_112 {
  int32_t stride;
  int32_t size;
};
struct struct_rec_111 {
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
        case 113:
        case 114:
            return sizeof(struct struct_rec_113);
        case 112:
            return sizeof(struct struct_rec_112);
        case 111:
            return sizeof(struct struct_rec_111);
        case 95:
        case 96:
        case 97:
        case 98:
        case 99:
        case 100:
        case 101:
        case 102:
        case 103:
        case 104:
        case 105:
        case 107:
        case 108:
        case 109:
        case 110:
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
        case 106:
            return sizeof(bool);
        default:
            return sizeof(sisal_array_t);
    }
}

extern "C" sisal_array_t func_MAIN(int32_t LEVEL);
extern "C" sisal_array_t func_PLACE(int32_t N, int32_t COL, sisal_array_t QUEENS);
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
    int32_t v_FORALL_12019_n__0_C = v_g1_n__0_C;
    int32_t v_FORALL_12019_n__2_COL;
    sisal_array_t v_FORALL_12019_n__0_QUEENS = v_g1_n__0_QUEENS;
    int32_t v_FORALL_12019_n__0_R = v_g1_n__0_R;
    bool v_FORALL_12019_n__3___forall_body_0;
    int32_t v_FORALL_12019_n__2___forall_lb_4_0;
    int32_t v_FORALL_12019_n__2___forall_ub_4_0;
    int32_t v_GENERATOR_12021_n__0_C;
    int32_t v_GENERATOR_12021_n__4_COL;
    sisal_array_t v_GENERATOR_12021_n__0_QUEENS;
    int32_t v_GENERATOR_12021_n__0_R;
    int32_t v_GENERATOR_12021_n__4___forall_lb_4_0;
    int32_t v_GENERATOR_12021_n__4___forall_ub_4_0;
    int32_t v_BODY_12022_n__0_C;
    int32_t v_BODY_12022_n__0_COL;
    sisal_array_t v_BODY_12022_n__0_QUEENS;
    int32_t v_BODY_12022_n__0_R;
    int32_t v_BODY_12022_n__1_ROW_COL;
    int32_t v_BODY_12022_n__0___forall_lb_4_0;
    int32_t v_BODY_12022_n__0___forall_ub_4_0;
    (v_GENERATOR_12021_n__0_C = v_FORALL_12019_n__0_C);
    int32_t v_GENERATOR_12021_n__3_p0_o = 0;
    (v_GENERATOR_12021_n__3_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_GENERATOR_12021_n__0_C) - SISAL_CAST(int32_t, 1))));
    (v_GENERATOR_12021_n__4___forall_lb_4_0 = 1);
    (v_GENERATOR_12021_n__4___forall_ub_4_0 = v_GENERATOR_12021_n__3_p0_o);
    (v_g1_n__1_p0_o = 0);
    for ((v_GENERATOR_12021_n__4_COL = 1); (v_GENERATOR_12021_n__4_COL <= v_GENERATOR_12021_n__3_p0_o); (v_GENERATOR_12021_n__4_COL++)) {
      (v_BODY_12022_n__0_C = SISAL_CAST(int32_t, v_FORALL_12019_n__0_C));
      (v_BODY_12022_n__0_COL = SISAL_CAST(int32_t, v_GENERATOR_12021_n__4_COL));
      (v_BODY_12022_n__0_QUEENS = SISAL_CAST(sisal_array_t, v_FORALL_12019_n__0_QUEENS));
      (v_BODY_12022_n__0_R = SISAL_CAST(int32_t, v_FORALL_12019_n__0_R));
      (v_BODY_12022_n__0___forall_lb_4_0 = SISAL_CAST(int32_t, v_GENERATOR_12021_n__4___forall_lb_4_0));
      (v_BODY_12022_n__0___forall_ub_4_0 = SISAL_CAST(int32_t, v_GENERATOR_12021_n__4___forall_ub_4_0));
      (v_BODY_12022_n__1_ROW_COL = SISAL_CAST(int32_t, ((int32_t *)SISAL_CAST(sisal_array_t, v_BODY_12022_n__0_QUEENS).data)[(SISAL_CAST(int32_t, v_BODY_12022_n__0_COL) - SISAL_CAST(sisal_array_t, v_BODY_12022_n__0_QUEENS).lower_bound[0])]));
      bool v_BODY_12022_n__2_p0_o = 0;
      (v_BODY_12022_n__2_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_BODY_12022_n__0_R) == SISAL_CAST(int32_t, v_BODY_12022_n__1_ROW_COL))));
      int32_t v_BODY_12022_n__4_p0_o = 0;
      (v_BODY_12022_n__4_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_12022_n__1_ROW_COL) + SISAL_CAST(int32_t, v_BODY_12022_n__0_COL))));
      int32_t v_BODY_12022_n__6_p0_o = 0;
      (v_BODY_12022_n__6_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_12022_n__0_R) + SISAL_CAST(int32_t, v_BODY_12022_n__0_C))));
      bool v_BODY_12022_n__8_p0_o = 0;
      (v_BODY_12022_n__8_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_BODY_12022_n__4_p0_o) == SISAL_CAST(int32_t, v_BODY_12022_n__6_p0_o))));
      bool v_BODY_12022_n__10_p0_o = 0;
      (v_BODY_12022_n__10_p0_o = SISAL_CAST(bool, (SISAL_CAST(bool, v_BODY_12022_n__2_p0_o) || SISAL_CAST(bool, v_BODY_12022_n__8_p0_o))));
      int32_t v_BODY_12022_n__11_p0_o = 0;
      (v_BODY_12022_n__11_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_12022_n__1_ROW_COL) - SISAL_CAST(int32_t, v_BODY_12022_n__0_COL))));
      int32_t v_BODY_12022_n__13_p0_o = 0;
      (v_BODY_12022_n__13_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_12022_n__0_R) - SISAL_CAST(int32_t, v_BODY_12022_n__0_C))));
      bool v_BODY_12022_n__15_p0_o = 0;
      (v_BODY_12022_n__15_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_BODY_12022_n__11_p0_o) == SISAL_CAST(int32_t, v_BODY_12022_n__13_p0_o))));
      bool v_BODY_12022_n__17_p0_o = 0;
      (v_BODY_12022_n__17_p0_o = SISAL_CAST(bool, (SISAL_CAST(bool, v_BODY_12022_n__10_p0_o) || SISAL_CAST(bool, v_BODY_12022_n__15_p0_o))));
      (v_g1_n__1_p0_o = (v_g1_n__1_p0_o || SISAL_CAST(bool, v_BODY_12022_n__17_p0_o)));
    }
  }
  (v_g1_n__0_p0_i = SISAL_CAST(bool, v_g1_n__1_p0_o));
  return SISAL_CAST(bool, v_g1_n__0_p0_i);
}

extern "C" sisal_array_t func_PLACE(int32_t N, int32_t COL, sisal_array_t QUEENS) {
  int32_t v_g2_n__0_COL = 0;
  int32_t v_g2_n__0_N = 0;
  sisal_array_t v_g2_n__0_QUEENS = {0};
  (v_g2_n__0_N = SISAL_CAST(int32_t, N));
  (v_g2_n__0_COL = SISAL_CAST(int32_t, COL));
  (v_g2_n__0_QUEENS = SISAL_CAST(sisal_array_t, QUEENS));
  sisal_array_t v_g2_n__0_p0_i = {0};
  sisal_array_t v_g2_n__1_p0_o = {0};
  int32_t v_IF_array_array_dv_INTEGRAL_____11006_n__0_COL = 0;
  (v_IF_array_array_dv_INTEGRAL_____11006_n__0_COL = SISAL_CAST(int32_t, v_g2_n__0_COL));
  int32_t v_IF_array_array_dv_INTEGRAL_____11006_n__0_N = 0;
  (v_IF_array_array_dv_INTEGRAL_____11006_n__0_N = SISAL_CAST(int32_t, v_g2_n__0_N));
  sisal_array_t v_IF_array_array_dv_INTEGRAL_____11006_n__0_QUEENS = {0};
  (v_IF_array_array_dv_INTEGRAL_____11006_n__0_QUEENS = SISAL_CAST(sisal_array_t, v_g2_n__0_QUEENS));
  {
    int32_t v_PREDICATE_11007_n__0_COL = 0;
    int32_t v_PREDICATE_11007_n__0_N = 0;
    (v_PREDICATE_11007_n__0_COL = SISAL_CAST(int32_t, v_IF_array_array_dv_INTEGRAL_____11006_n__0_COL));
    (v_PREDICATE_11007_n__0_N = SISAL_CAST(int32_t, v_IF_array_array_dv_INTEGRAL_____11006_n__0_N));
    bool v_PREDICATE_11007_n__1_p0_o = 0;
    (v_PREDICATE_11007_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_PREDICATE_11007_n__0_COL) > SISAL_CAST(int32_t, v_PREDICATE_11007_n__0_N))));
    if (v_PREDICATE_11007_n__1_p0_o) {
      sisal_array_t v_THEN_11018_n__0_QUEENS = {0};
      (v_THEN_11018_n__0_QUEENS = SISAL_CAST(sisal_array_t, v_IF_array_array_dv_INTEGRAL_____11006_n__0_QUEENS));
      int32_t v_THEN_11018_n__1_p0_o = 0;
      (v_THEN_11018_n__1_p0_o = SISAL_CAST(int32_t, 1));
      sisal_array_t v_THEN_11018_n__3_p0_o = {0};
      (v_THEN_11018_n__3_p0_o = SISAL_CAST(sisal_array_t, ([&]() -> sisal_array_t { const sisal_array_t __arr[] = {v_THEN_11018_n__0_QUEENS}; return sisal_array_build_arr(v_THEN_11018_n__1_p0_o, 1, __arr); })()));
      (v_g2_n__1_p0_o = SISAL_CAST(sisal_array_t, v_THEN_11018_n__3_p0_o));
    }
    else {
      int32_t v_ELSE_11008_n__0_COL = 0;
      int32_t v_ELSE_11008_n__0_N = 0;
      sisal_array_t v_ELSE_11008_n__0_QUEENS = {0};
      (v_ELSE_11008_n__0_COL = SISAL_CAST(int32_t, v_IF_array_array_dv_INTEGRAL_____11006_n__0_COL));
      (v_ELSE_11008_n__0_N = SISAL_CAST(int32_t, v_IF_array_array_dv_INTEGRAL_____11006_n__0_N));
      (v_ELSE_11008_n__0_QUEENS = SISAL_CAST(sisal_array_t, v_IF_array_array_dv_INTEGRAL_____11006_n__0_QUEENS));
      sisal_array_t v_ELSE_11008_n__1_p0_o = {0};
      {
        sisal_array_t v_LET_NON_REC_11009_n__2_ALL_EXT = {0};
        int32_t v_LET_NON_REC_11009_n__0_COL = 0;
        int32_t v_LET_NON_REC_11009_n__0_N = 0;
        sisal_array_t v_LET_NON_REC_11009_n__2_OK = {0};
        sisal_array_t v_LET_NON_REC_11009_n__0_QUEENS = {0};
        sisal_array_t v_LET_NON_REC_11009_n__7_VALID_EXT = {0};
        (v_LET_NON_REC_11009_n__0_COL = SISAL_CAST(int32_t, v_ELSE_11008_n__0_COL));
        (v_LET_NON_REC_11009_n__0_N = SISAL_CAST(int32_t, v_ELSE_11008_n__0_N));
        (v_LET_NON_REC_11009_n__0_QUEENS = SISAL_CAST(sisal_array_t, v_ELSE_11008_n__0_QUEENS));
        sisal_array_t v_LET_NON_REC_11009_n__1_p0_o = {0};
        sisal_array_t v_LET_NON_REC_11009_n__1_p1_o = {0};
        {
          int32_t v_FORALL_11010_n__0_COL = v_LET_NON_REC_11009_n__0_COL;
          int32_t v_FORALL_11010_n__0_N = v_LET_NON_REC_11009_n__0_N;
          sisal_array_t v_FORALL_11010_n__0_QUEENS = v_LET_NON_REC_11009_n__0_QUEENS;
          int32_t v_FORALL_11010_n__2_ROW;
          sisal_array_t v_FORALL_11010_n__3___forall_body_0;
          bool v_FORALL_11010_n__3___forall_body_1;
          int32_t v_FORALL_11010_n__2___forall_lb_2_0;
          int32_t v_FORALL_11010_n__2___forall_ub_2_0;
          int32_t v_GENERATOR_11012_n__0_COL;
          int32_t v_GENERATOR_11012_n__0_N;
          sisal_array_t v_GENERATOR_11012_n__0_QUEENS;
          int32_t v_GENERATOR_11012_n__2_ROW;
          int32_t v_GENERATOR_11012_n__2___forall_lb_2_0;
          int32_t v_GENERATOR_11012_n__2___forall_ub_2_0;
          int32_t v_BODY_11013_n__0_COL;
          int32_t v_BODY_11013_n__0_N;
          sisal_array_t v_BODY_11013_n__0_QUEENS;
          int32_t v_BODY_11013_n__0_ROW;
          int32_t v_BODY_11013_n__0___forall_lb_2_0;
          int32_t v_BODY_11013_n__0___forall_ub_2_0;
          (v_GENERATOR_11012_n__0_N = v_FORALL_11010_n__0_N);
          (v_GENERATOR_11012_n__2___forall_lb_2_0 = 1);
          (v_GENERATOR_11012_n__2___forall_ub_2_0 = v_GENERATOR_11012_n__0_N);
          (v_LET_NON_REC_11009_n__1_p0_o = sisal_array_alloc_sized(1, 94, ((uint64_t)(1 * ((v_GENERATOR_11012_n__0_N - 1) + 1))), sizeof(sisal_array_t)));
          (v_LET_NON_REC_11009_n__1_p0_o.dims[0] = ((v_GENERATOR_11012_n__0_N - 1) + 1));
          (v_LET_NON_REC_11009_n__1_p0_o.lower_bound[0] = 1);
          (v_LET_NON_REC_11009_n__1_p1_o = sisal_array_alloc_empty(1, 1, ((uint64_t)(1 * ((v_GENERATOR_11012_n__0_N - 1) + 1)))));
          (v_LET_NON_REC_11009_n__1_p1_o.dims[0] = ((v_GENERATOR_11012_n__0_N - 1) + 1));
          (v_LET_NON_REC_11009_n__1_p1_o.lower_bound[0] = 1);
          int32_t __g_11010 = 0;
          for ((v_GENERATOR_11012_n__2_ROW = 1); (v_GENERATOR_11012_n__2_ROW <= v_GENERATOR_11012_n__0_N); (v_GENERATOR_11012_n__2_ROW++)) {
            (v_BODY_11013_n__0_COL = SISAL_CAST(int32_t, v_FORALL_11010_n__0_COL));
            (v_BODY_11013_n__0_N = SISAL_CAST(int32_t, v_FORALL_11010_n__0_N));
            (v_BODY_11013_n__0_QUEENS = SISAL_CAST(sisal_array_t, v_FORALL_11010_n__0_QUEENS));
            (v_BODY_11013_n__0_ROW = SISAL_CAST(int32_t, v_GENERATOR_11012_n__2_ROW));
            (v_BODY_11013_n__0___forall_lb_2_0 = SISAL_CAST(int32_t, v_GENERATOR_11012_n__2___forall_lb_2_0));
            (v_BODY_11013_n__0___forall_ub_2_0 = SISAL_CAST(int32_t, v_GENERATOR_11012_n__2___forall_ub_2_0));
            sisal_array_t v_BODY_11013_n__1_p0_o = {0};
            (v_BODY_11013_n__1_p0_o = SISAL_CAST(sisal_array_t, sisal_array_replace_i32(SISAL_CAST(sisal_array_t, v_BODY_11013_n__0_QUEENS), ((int64_t)SISAL_CAST(int32_t, v_BODY_11013_n__0_COL)), SISAL_CAST(int32_t, v_BODY_11013_n__0_ROW))));
            bool v_BODY_11013_n__2_p0_o = 0;
            (v_BODY_11013_n__2_p0_o = SISAL_CAST(bool, func_IN_CHECK(SISAL_CAST(int32_t, v_BODY_11013_n__0_ROW), SISAL_CAST(int32_t, v_BODY_11013_n__0_COL), SISAL_CAST(sisal_array_t, v_BODY_11013_n__0_QUEENS))));
            bool v_BODY_11013_n__3_p0_o = 0;
            (v_BODY_11013_n__3_p0_o = SISAL_CAST(bool, (!SISAL_CAST(bool, v_BODY_11013_n__2_p0_o))));
            (((sisal_array_t *)v_LET_NON_REC_11009_n__1_p0_o.data)[__g_11010] = SISAL_CAST(sisal_array_t, v_BODY_11013_n__1_p0_o));
            (((bool *)v_LET_NON_REC_11009_n__1_p1_o.data)[__g_11010] = SISAL_CAST(bool, v_BODY_11013_n__3_p0_o));
            (__g_11010++);
          }
          sisal_array_t __e0_v_LET_NON_REC_11009_n__1_p0_o = ((sisal_array_t *)v_LET_NON_REC_11009_n__1_p0_o.data)[0];
          sisal_array_t __flat_v_LET_NON_REC_11009_n__1_p0_o = sisal_array_alloc_sized((1 + __e0_v_LET_NON_REC_11009_n__1_p0_o.rank), __e0_v_LET_NON_REC_11009_n__1_p0_o.type_id, ((uint64_t)(((uint64_t)(1 * ((v_GENERATOR_11012_n__0_N - 1) + 1))) * __e0_v_LET_NON_REC_11009_n__1_p0_o.size)), sisal_esz(__e0_v_LET_NON_REC_11009_n__1_p0_o));
          (__flat_v_LET_NON_REC_11009_n__1_p0_o.dims[0] = ((v_GENERATOR_11012_n__0_N - 1) + 1));
          (__flat_v_LET_NON_REC_11009_n__1_p0_o.lower_bound[0] = 1);
          for (int32_t __fk_v_LET_NON_REC_11009_n__1_p0_o = 0; (__fk_v_LET_NON_REC_11009_n__1_p0_o < __e0_v_LET_NON_REC_11009_n__1_p0_o.rank); (__fk_v_LET_NON_REC_11009_n__1_p0_o++)) {
            (__flat_v_LET_NON_REC_11009_n__1_p0_o.dims[(1 + __fk_v_LET_NON_REC_11009_n__1_p0_o)] = __e0_v_LET_NON_REC_11009_n__1_p0_o.dims[__fk_v_LET_NON_REC_11009_n__1_p0_o]);
            (__flat_v_LET_NON_REC_11009_n__1_p0_o.lower_bound[(1 + __fk_v_LET_NON_REC_11009_n__1_p0_o)] = __e0_v_LET_NON_REC_11009_n__1_p0_o.lower_bound[__fk_v_LET_NON_REC_11009_n__1_p0_o]);
          }
          for (int32_t __fi_v_LET_NON_REC_11009_n__1_p0_o = 0; (__fi_v_LET_NON_REC_11009_n__1_p0_o < ((int32_t)(1 * ((v_GENERATOR_11012_n__0_N - 1) + 1)))); (__fi_v_LET_NON_REC_11009_n__1_p0_o++)) {
            memcpy((((char *)__flat_v_LET_NON_REC_11009_n__1_p0_o.data) + (((uint64_t)__fi_v_LET_NON_REC_11009_n__1_p0_o) * (__e0_v_LET_NON_REC_11009_n__1_p0_o.size * sisal_esz(__e0_v_LET_NON_REC_11009_n__1_p0_o)))), ((sisal_array_t *)v_LET_NON_REC_11009_n__1_p0_o.data)[__fi_v_LET_NON_REC_11009_n__1_p0_o].data, (__e0_v_LET_NON_REC_11009_n__1_p0_o.size * sisal_esz(__e0_v_LET_NON_REC_11009_n__1_p0_o)));
          }
          (v_LET_NON_REC_11009_n__1_p0_o = __flat_v_LET_NON_REC_11009_n__1_p0_o);
        }
        int32_t v_LET_NON_REC_11009_n__3_p0_o = 0;
        (v_LET_NON_REC_11009_n__3_p0_o = SISAL_CAST(int32_t, 1));
        sisal_array_t v_LET_NON_REC_11009_n__4_p0_o = {0};
        (v_LET_NON_REC_11009_n__4_p0_o = SISAL_CAST(sisal_array_t, sisal_array_setl(SISAL_CAST(sisal_array_t, v_LET_NON_REC_11009_n__1_p0_o), ((int64_t)SISAL_CAST(int32_t, v_LET_NON_REC_11009_n__3_p0_o)))));
        int32_t v_LET_NON_REC_11009_n__5_p0_o = 0;
        (v_LET_NON_REC_11009_n__5_p0_o = SISAL_CAST(int32_t, 1));
        sisal_array_t v_LET_NON_REC_11009_n__6_p0_o = {0};
        (v_LET_NON_REC_11009_n__6_p0_o = SISAL_CAST(sisal_array_t, sisal_array_setl(SISAL_CAST(sisal_array_t, v_LET_NON_REC_11009_n__1_p1_o), ((int64_t)SISAL_CAST(int32_t, v_LET_NON_REC_11009_n__5_p0_o)))));
        (v_LET_NON_REC_11009_n__7_VALID_EXT = SISAL_CAST(sisal_array_t, sisal_array_compress(SISAL_CAST(sisal_array_t, v_LET_NON_REC_11009_n__6_p0_o), SISAL_CAST(sisal_array_t, v_LET_NON_REC_11009_n__4_p0_o))));
        sisal_array_t v_LET_NON_REC_11009_n__8_p0_o = {0};
        {
          sisal_array_t v_FORALL_11014_n__0_ALL_EXT = v_LET_NON_REC_11009_n__4_p0_o;
          int32_t v_FORALL_11014_n__0_COL = v_LET_NON_REC_11009_n__0_COL;
          int32_t v_FORALL_11014_n__0_N = v_LET_NON_REC_11009_n__0_N;
          sisal_array_t v_FORALL_11014_n__0_OK = v_LET_NON_REC_11009_n__6_p0_o;
          sisal_array_t v_FORALL_11014_n__2_PARTIAL;
          sisal_array_t v_FORALL_11014_n__0_QUEENS = v_LET_NON_REC_11009_n__0_QUEENS;
          sisal_array_t v_FORALL_11014_n__0_VALID_EXT = v_LET_NON_REC_11009_n__7_VALID_EXT;
          sisal_array_t v_FORALL_11014_n__3___forall_body_0;
          sisal_array_t v_GENERATOR_11016_n__0_ALL_EXT;
          int32_t v_GENERATOR_11016_n__0_COL;
          int32_t v_GENERATOR_11016_n__0_N;
          sisal_array_t v_GENERATOR_11016_n__0_OK;
          sisal_array_t v_GENERATOR_11016_n__1_PARTIAL;
          sisal_array_t v_GENERATOR_11016_n__0_QUEENS;
          sisal_array_t v_GENERATOR_11016_n__0_VALID_EXT;
          sisal_array_t v_BODY_11017_n__0_ALL_EXT;
          int32_t v_BODY_11017_n__0_COL;
          int32_t v_BODY_11017_n__0_N;
          sisal_array_t v_BODY_11017_n__0_OK;
          sisal_array_t v_BODY_11017_n__0_PARTIAL;
          sisal_array_t v_BODY_11017_n__0_QUEENS;
          sisal_array_t v_BODY_11017_n__5_SUBS;
          sisal_array_t v_BODY_11017_n__0_VALID_EXT;
          (v_GENERATOR_11016_n__0_VALID_EXT = v_FORALL_11014_n__0_VALID_EXT);
          (v_LET_NON_REC_11009_n__8_p0_o = sisal_array_empty());
          for (int32_t __k_11016 = 0; (__k_11016 < ((int32_t)v_GENERATOR_11016_n__0_VALID_EXT.size)); (__k_11016++)) {
            (v_GENERATOR_11016_n__1_PARTIAL = ((sisal_array_t *)v_GENERATOR_11016_n__0_VALID_EXT.data)[__k_11016]);
            (v_BODY_11017_n__0_ALL_EXT = SISAL_CAST(sisal_array_t, v_FORALL_11014_n__0_ALL_EXT));
            (v_BODY_11017_n__0_COL = SISAL_CAST(int32_t, v_FORALL_11014_n__0_COL));
            (v_BODY_11017_n__0_N = SISAL_CAST(int32_t, v_FORALL_11014_n__0_N));
            (v_BODY_11017_n__0_OK = SISAL_CAST(sisal_array_t, v_FORALL_11014_n__0_OK));
            (v_BODY_11017_n__0_PARTIAL = SISAL_CAST(sisal_array_t, v_GENERATOR_11016_n__1_PARTIAL));
            (v_BODY_11017_n__0_QUEENS = SISAL_CAST(sisal_array_t, v_FORALL_11014_n__0_QUEENS));
            (v_BODY_11017_n__0_VALID_EXT = SISAL_CAST(sisal_array_t, v_FORALL_11014_n__0_VALID_EXT));
            int32_t v_BODY_11017_n__1_p0_o = 0;
            (v_BODY_11017_n__1_p0_o = SISAL_CAST(int32_t, 1));
            float v_BODY_11017_n__2_p0_o = 0;
            (v_BODY_11017_n__2_p0_o = SISAL_CAST(float, (SISAL_CAST(int32_t, v_BODY_11017_n__0_COL) + SISAL_CAST(int32_t, v_BODY_11017_n__1_p0_o))));
            int32_t v_BODY_11017_n__3_p0_o = 0;
            (v_BODY_11017_n__3_p0_o = SISAL_CAST(int32_t, 1));
            int32_t v_BODY_11017_n__4_p0_o = 0;
            (v_BODY_11017_n__4_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_11017_n__0_COL) + SISAL_CAST(int32_t, v_BODY_11017_n__3_p0_o))));
            (v_BODY_11017_n__5_SUBS = SISAL_CAST(sisal_array_t, func_PLACE(SISAL_CAST(int32_t, v_BODY_11017_n__0_N), SISAL_CAST(int32_t, v_BODY_11017_n__4_p0_o), SISAL_CAST(sisal_array_t, v_BODY_11017_n__0_PARTIAL))));
            (v_LET_NON_REC_11009_n__8_p0_o = sisal_array_catenate(v_LET_NON_REC_11009_n__8_p0_o, v_BODY_11017_n__5_SUBS));
          }
        }
        (v_ELSE_11008_n__1_p0_o = SISAL_CAST(sisal_array_t, v_LET_NON_REC_11009_n__8_p0_o));
      }
      (v_g2_n__1_p0_o = SISAL_CAST(sisal_array_t, v_ELSE_11008_n__1_p0_o));
    }
  }
  (v_g2_n__0_p0_i = SISAL_CAST(sisal_array_t, v_g2_n__1_p0_o));
  return SISAL_CAST(sisal_array_t, v_g2_n__0_p0_i);
}

extern "C" sisal_array_t func_MAIN(int32_t LEVEL) {
  int32_t v_g3_n__0_LEVEL = 0;
  (v_g3_n__0_LEVEL = SISAL_CAST(int32_t, LEVEL));
  sisal_array_t v_g3_n__0_p0_i = {0};
  sisal_array_t v_g3_n__1_p0_o = {0};
  {
    sisal_array_t v_LET_NON_REC_10001_n__2_EMPTY = {0};
    int32_t v_LET_NON_REC_10001_n__0_LEVEL = 0;
    (v_LET_NON_REC_10001_n__0_LEVEL = SISAL_CAST(int32_t, v_g3_n__0_LEVEL));
    sisal_array_t v_LET_NON_REC_10001_n__1_p0_o = {0};
    {
      int32_t v_FORALL_10002_n__2_J;
      int32_t v_FORALL_10002_n__0_LEVEL = v_LET_NON_REC_10001_n__0_LEVEL;
      int32_t v_FORALL_10002_n__3___forall_body_0;
      int32_t v_FORALL_10002_n__2___forall_lb_2_0;
      int32_t v_FORALL_10002_n__2___forall_ub_2_0;
      int32_t v_GENERATOR_10004_n__2_J;
      int32_t v_GENERATOR_10004_n__0_LEVEL;
      int32_t v_GENERATOR_10004_n__2___forall_lb_2_0;
      int32_t v_GENERATOR_10004_n__2___forall_ub_2_0;
      int32_t v_BODY_10005_n__0_J;
      int32_t v_BODY_10005_n__0_LEVEL;
      int32_t v_BODY_10005_n__0___forall_lb_2_0;
      int32_t v_BODY_10005_n__0___forall_ub_2_0;
      (v_GENERATOR_10004_n__0_LEVEL = v_FORALL_10002_n__0_LEVEL);
      (v_GENERATOR_10004_n__2___forall_lb_2_0 = 1);
      (v_GENERATOR_10004_n__2___forall_ub_2_0 = v_GENERATOR_10004_n__0_LEVEL);
      (v_LET_NON_REC_10001_n__1_p0_o = sisal_array_alloc_empty(1, 6, ((uint64_t)(1 * ((v_GENERATOR_10004_n__0_LEVEL - 1) + 1)))));
      (v_LET_NON_REC_10001_n__1_p0_o.dims[0] = ((v_GENERATOR_10004_n__0_LEVEL - 1) + 1));
      (v_LET_NON_REC_10001_n__1_p0_o.lower_bound[0] = 1);
      int32_t __g_10002 = 0;
      for ((v_GENERATOR_10004_n__2_J = 1); (v_GENERATOR_10004_n__2_J <= v_GENERATOR_10004_n__0_LEVEL); (v_GENERATOR_10004_n__2_J++)) {
        (v_BODY_10005_n__0_J = SISAL_CAST(int32_t, v_GENERATOR_10004_n__2_J));
        (v_BODY_10005_n__0_LEVEL = SISAL_CAST(int32_t, v_FORALL_10002_n__0_LEVEL));
        (v_BODY_10005_n__0___forall_lb_2_0 = SISAL_CAST(int32_t, v_GENERATOR_10004_n__2___forall_lb_2_0));
        (v_BODY_10005_n__0___forall_ub_2_0 = SISAL_CAST(int32_t, v_GENERATOR_10004_n__2___forall_ub_2_0));
        int32_t v_BODY_10005_n__1_p0_o = 0;
        (v_BODY_10005_n__1_p0_o = SISAL_CAST(int32_t, 0));
        (((int32_t *)v_LET_NON_REC_10001_n__1_p0_o.data)[__g_10002] = SISAL_CAST(int32_t, v_BODY_10005_n__1_p0_o));
        (__g_10002++);
      }
    }
    int32_t v_LET_NON_REC_10001_n__3_p0_o = 0;
    (v_LET_NON_REC_10001_n__3_p0_o = SISAL_CAST(int32_t, 1));
    int32_t v_LET_NON_REC_10001_n__4_p0_o = 0;
    (v_LET_NON_REC_10001_n__4_p0_o = SISAL_CAST(int32_t, 1));
    sisal_array_t v_LET_NON_REC_10001_n__5_p0_o = {0};
    (v_LET_NON_REC_10001_n__5_p0_o = SISAL_CAST(sisal_array_t, func_PLACE(SISAL_CAST(int32_t, v_LET_NON_REC_10001_n__0_LEVEL), SISAL_CAST(int32_t, v_LET_NON_REC_10001_n__4_p0_o), SISAL_CAST(sisal_array_t, v_LET_NON_REC_10001_n__1_p0_o))));
    (v_g3_n__1_p0_o = SISAL_CAST(sisal_array_t, v_LET_NON_REC_10001_n__5_p0_o));
  }
  (v_g3_n__0_p0_i = SISAL_CAST(sisal_array_t, v_g3_n__1_p0_o));
  return SISAL_CAST(sisal_array_t, v_g3_n__0_p0_i);
}
