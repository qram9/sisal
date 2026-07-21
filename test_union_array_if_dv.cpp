#define SISAL_CUSTOM_ELEM_SIZE

#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <math.h>
#include <iostream>
#include <dispatch/dispatch.h>
#include <Accelerate/Accelerate.h>
#include <sisal_runtime.h>

enum union_tag_96 {
  union_96_I = 95,
  union_96_D = 94
};
struct union_un_96 {
  int32_t tag;
  union union_val_96 {
  int32_t I;
  double D;
} val;
};
inline struct union_un_96 make_union_96_I(int32_t val) {
  struct union_un_96 tmp = {};
  tmp.tag = 95;
  tmp.val.I = val;
  return tmp;
}
inline struct union_un_96 make_union_96_D(double val) {
  struct union_un_96 tmp = {};
  tmp.tag = 94;
  tmp.val.D = val;
  return tmp;
}
enum union_tag_95 {
  union_95_I = 95,
  union_95_D = 94
};
struct union_un_95 {
  int32_t tag;
  union union_val_95 {
  int32_t I;
  double D;
} val;
};
inline struct union_un_95 make_union_95_I(int32_t val) {
  struct union_un_95 tmp = {};
  tmp.tag = 95;
  tmp.val.I = val;
  return tmp;
}
inline struct union_un_95 make_union_95_D(double val) {
  struct union_un_95 tmp = {};
  tmp.tag = 94;
  tmp.val.D = val;
  return tmp;
}
enum union_tag_94 {
  union_94_D = 94
};
struct union_un_94 {
  int32_t tag;
  union union_val_94 {
  double D;
} val;
};
inline struct union_un_94 make_union_94_D(double val) {
  struct union_un_94 tmp = {};
  tmp.tag = 94;
  tmp.val.D = val;
  return tmp;
}
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
struct FUNC_MAIN_results {
  sisal_array_t res_0;
  sisal_array_t res_1;
};
size_t sisal_elem_size(int32_t type_id) {
    switch (type_id) {
        case 83:
            return sizeof(void*);
        case 12:
            return sizeof(uint32_t);
        case 96:
        case 98:
        case 104:
            return sizeof(struct union_un_96);
        case 95:
            return sizeof(struct union_un_95);
        case 94:
            return sizeof(struct union_un_94);
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
        case 99:
        case 100:
        case 101:
        case 102:
            return sizeof(sisal_array_t);
        case 7:
        case 13:
            return sizeof(int64_t);
        case 2:
        case 6:
        case 10:
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
        case 97:
        case 103:
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

extern "C" struct FUNC_MAIN_results func_MAIN(int32_t N);

extern "C" struct FUNC_MAIN_results func_MAIN(int32_t N) {
  int32_t v_g1_n__0_N = 0;
  (v_g1_n__0_N = SISAL_CAST(int32_t, N));
  sisal_array_t v_g1_n__0_p0_i = {0};
  sisal_array_t v_g1_n__0_p1_i = {0};
  sisal_array_t v_g1_n__1_p0_o = {0};
  sisal_array_t v_g1_n__1_p1_o = {0};
  {
    int32_t v_FORALL_10001_n__2_I;
    int32_t v_FORALL_10001_n__0_N = v_g1_n__0_N;
    double v_FORALL_10001_n__3___forall_body_0;
    struct union_un_96 v_FORALL_10001_n__3___forall_body_1;
    int32_t v_FORALL_10001_n__2___forall_lb_2_0;
    int32_t v_FORALL_10001_n__2___forall_ub_2_0;
    int32_t v_GENERATOR_10003_n__2_I;
    int32_t v_GENERATOR_10003_n__0_N;
    int32_t v_GENERATOR_10003_n__2___forall_lb_2_0;
    int32_t v_GENERATOR_10003_n__2___forall_ub_2_0;
    int32_t v_BODY_10004_n__0_I;
    int32_t v_BODY_10004_n__0_N;
    int32_t v_BODY_10004_n__0___forall_lb_2_0;
    int32_t v_BODY_10004_n__0___forall_ub_2_0;
    int32_t v_IF_DOUBLE___10005_n__0_I;
    int32_t v_PREDICATE_10006_n__0_I;
    int32_t v_ELSE_10007_n__0_I;
    int32_t v_THEN_10008_n__0_I;
    int32_t v_IF_union_MISSING_ID_0____10009_n__0_I;
    int32_t v_PREDICATE_10010_n__0_I;
    int32_t v_ELSE_10011_n__0_I;
    int32_t v_THEN_10012_n__0_I;
    (v_GENERATOR_10003_n__0_N = v_FORALL_10001_n__0_N);
    (v_GENERATOR_10003_n__2___forall_lb_2_0 = 1);
    (v_GENERATOR_10003_n__2___forall_ub_2_0 = v_GENERATOR_10003_n__0_N);
    (v_g1_n__1_p0_o = sisal_array_alloc_empty(1, 4, ((uint64_t)(1 * ((v_GENERATOR_10003_n__0_N - 1) + 1)))));
    (v_g1_n__1_p0_o.dims[0] = ((v_GENERATOR_10003_n__0_N - 1) + 1));
    (v_g1_n__1_p0_o.lower_bound[0] = 1);
    (v_g1_n__1_p1_o = sisal_array_alloc_sized(1, 96, ((uint64_t)(1 * ((v_GENERATOR_10003_n__0_N - 1) + 1))), sizeof(struct union_un_96)));
    (v_g1_n__1_p1_o.dims[0] = ((v_GENERATOR_10003_n__0_N - 1) + 1));
    (v_g1_n__1_p1_o.lower_bound[0] = 1);
    int32_t __g_10001 = 0;
    for ((v_GENERATOR_10003_n__2_I = 1); (v_GENERATOR_10003_n__2_I <= v_GENERATOR_10003_n__0_N); (v_GENERATOR_10003_n__2_I++)) {
      (v_BODY_10004_n__0_I = SISAL_CAST(int32_t, v_GENERATOR_10003_n__2_I));
      (v_BODY_10004_n__0_N = SISAL_CAST(int32_t, v_FORALL_10001_n__0_N));
      (v_BODY_10004_n__0___forall_lb_2_0 = SISAL_CAST(int32_t, v_GENERATOR_10003_n__2___forall_lb_2_0));
      (v_BODY_10004_n__0___forall_ub_2_0 = SISAL_CAST(int32_t, v_GENERATOR_10003_n__2___forall_ub_2_0));
      double v_BODY_10004_n__1_p0_o = 0;
      (v_IF_DOUBLE___10005_n__0_I = SISAL_CAST(int32_t, v_BODY_10004_n__0_I));
      {
        (v_PREDICATE_10006_n__0_I = SISAL_CAST(int32_t, v_IF_DOUBLE___10005_n__0_I));
        int32_t v_PREDICATE_10006_n__1_p0_o = 0;
        (v_PREDICATE_10006_n__1_p0_o = SISAL_CAST(int32_t, 2));
        int32_t v_PREDICATE_10006_n__2_p0_o = 0;
        (v_PREDICATE_10006_n__2_p0_o = SISAL_CAST(int32_t, 2));
        int32_t v_PREDICATE_10006_n__3_p0_o = 0;
        (v_PREDICATE_10006_n__3_p0_o = SISAL_CAST(int32_t, func__SMOD__II__I(SISAL_CAST(int32_t, v_PREDICATE_10006_n__0_I), SISAL_CAST(int32_t, v_PREDICATE_10006_n__2_p0_o))));
        int32_t v_PREDICATE_10006_n__4_p0_o = 0;
        (v_PREDICATE_10006_n__4_p0_o = SISAL_CAST(int32_t, 0));
        bool v_PREDICATE_10006_n__5_p0_o = 0;
        (v_PREDICATE_10006_n__5_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_PREDICATE_10006_n__3_p0_o) == SISAL_CAST(int32_t, v_PREDICATE_10006_n__4_p0_o))));
        if (v_PREDICATE_10006_n__5_p0_o) {
          (v_THEN_10008_n__0_I = SISAL_CAST(int32_t, v_IF_DOUBLE___10005_n__0_I));
          double v_THEN_10008_n__2_p0_o = 0;
          (v_THEN_10008_n__2_p0_o = SISAL_CAST(double, SISAL_CAST(int32_t, v_THEN_10008_n__0_I)));
          double v_THEN_10008_n__3_p0_o = 0;
          (v_THEN_10008_n__3_p0_o = SISAL_CAST(double, 1.5f));
          double v_THEN_10008_n__4_p0_o = 0;
          (v_THEN_10008_n__4_p0_o = SISAL_CAST(double, SISAL_CAST(double, v_THEN_10008_n__3_p0_o)));
          double v_THEN_10008_n__5_p0_o = 0;
          (v_THEN_10008_n__5_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_THEN_10008_n__2_p0_o) * SISAL_CAST(double, v_THEN_10008_n__4_p0_o))));
          (v_BODY_10004_n__1_p0_o = SISAL_CAST(double, v_THEN_10008_n__5_p0_o));
        }
        else {
          (v_ELSE_10007_n__0_I = SISAL_CAST(int32_t, v_IF_DOUBLE___10005_n__0_I));
          double v_ELSE_10007_n__2_p0_o = 0;
          (v_ELSE_10007_n__2_p0_o = SISAL_CAST(double, SISAL_CAST(int32_t, v_ELSE_10007_n__0_I)));
          double v_ELSE_10007_n__3_p0_o = 0;
          (v_ELSE_10007_n__3_p0_o = SISAL_CAST(double, 0.5f));
          double v_ELSE_10007_n__4_p0_o = 0;
          (v_ELSE_10007_n__4_p0_o = SISAL_CAST(double, SISAL_CAST(double, v_ELSE_10007_n__3_p0_o)));
          double v_ELSE_10007_n__5_p0_o = 0;
          (v_ELSE_10007_n__5_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_ELSE_10007_n__2_p0_o) * SISAL_CAST(double, v_ELSE_10007_n__4_p0_o))));
          (v_BODY_10004_n__1_p0_o = SISAL_CAST(double, v_ELSE_10007_n__5_p0_o));
        }
      }
      struct union_un_96 v_BODY_10004_n__3_p0_o = {};
      (v_IF_union_MISSING_ID_0____10009_n__0_I = SISAL_CAST(int32_t, v_BODY_10004_n__0_I));
      {
        (v_PREDICATE_10010_n__0_I = SISAL_CAST(int32_t, v_IF_union_MISSING_ID_0____10009_n__0_I));
        int32_t v_PREDICATE_10010_n__1_p0_o = 0;
        (v_PREDICATE_10010_n__1_p0_o = SISAL_CAST(int32_t, 2));
        int32_t v_PREDICATE_10010_n__2_p0_o = 0;
        (v_PREDICATE_10010_n__2_p0_o = SISAL_CAST(int32_t, 2));
        int32_t v_PREDICATE_10010_n__3_p0_o = 0;
        (v_PREDICATE_10010_n__3_p0_o = SISAL_CAST(int32_t, func__SMOD__II__I(SISAL_CAST(int32_t, v_PREDICATE_10010_n__0_I), SISAL_CAST(int32_t, v_PREDICATE_10010_n__2_p0_o))));
        int32_t v_PREDICATE_10010_n__4_p0_o = 0;
        (v_PREDICATE_10010_n__4_p0_o = SISAL_CAST(int32_t, 0));
        bool v_PREDICATE_10010_n__5_p0_o = 0;
        (v_PREDICATE_10010_n__5_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_PREDICATE_10010_n__3_p0_o) == SISAL_CAST(int32_t, v_PREDICATE_10010_n__4_p0_o))));
        if (v_PREDICATE_10010_n__5_p0_o) {
          (v_THEN_10012_n__0_I = SISAL_CAST(int32_t, v_IF_union_MISSING_ID_0____10009_n__0_I));
          struct union_un_96 v_THEN_10012_n__1_p0_o = {};
          (v_THEN_10012_n__1_p0_o = SISAL_CAST(struct union_un_96, make_union_96_I(v_THEN_10012_n__0_I)));
          (v_BODY_10004_n__3_p0_o = SISAL_CAST(struct union_un_96, v_THEN_10012_n__1_p0_o));
        }
        else {
          (v_ELSE_10011_n__0_I = SISAL_CAST(int32_t, v_IF_union_MISSING_ID_0____10009_n__0_I));
          double v_ELSE_10011_n__2_p0_o = 0;
          (v_ELSE_10011_n__2_p0_o = SISAL_CAST(double, SISAL_CAST(int32_t, v_ELSE_10011_n__0_I)));
          struct union_un_96 v_ELSE_10011_n__3_p0_o = {};
          (v_ELSE_10011_n__3_p0_o = SISAL_CAST(struct union_un_96, make_union_96_D(v_ELSE_10011_n__2_p0_o)));
          (v_BODY_10004_n__3_p0_o = SISAL_CAST(struct union_un_96, v_ELSE_10011_n__3_p0_o));
        }
      }
      (((double *)v_g1_n__1_p0_o.data)[__g_10001] = SISAL_CAST(double, v_BODY_10004_n__1_p0_o));
      (((struct union_un_96 *)v_g1_n__1_p1_o.data)[__g_10001] = SISAL_CAST(struct union_un_96, v_BODY_10004_n__3_p0_o));
      (__g_10001++);
    }
  }
  int32_t v_g1_n__3_p0_o = 0;
  (v_g1_n__3_p0_o = SISAL_CAST(int32_t, 1));
  sisal_array_t v_g1_n__4_p0_o = {0};
  (v_g1_n__4_p0_o = SISAL_CAST(sisal_array_t, sisal_array_setl(SISAL_CAST(sisal_array_t, v_g1_n__1_p0_o), ((int64_t)SISAL_CAST(int32_t, v_g1_n__3_p0_o)))));
  int32_t v_g1_n__5_p0_o = 0;
  (v_g1_n__5_p0_o = SISAL_CAST(int32_t, 1));
  sisal_array_t v_g1_n__6_p0_o = {0};
  (v_g1_n__6_p0_o = SISAL_CAST(sisal_array_t, sisal_array_setl(SISAL_CAST(sisal_array_t, v_g1_n__1_p1_o), ((int64_t)SISAL_CAST(int32_t, v_g1_n__5_p0_o)))));
  (v_g1_n__0_p0_i = SISAL_CAST(sisal_array_t, v_g1_n__4_p0_o));
  (v_g1_n__0_p1_i = SISAL_CAST(sisal_array_t, v_g1_n__6_p0_o));
  struct FUNC_MAIN_results __res_obj;
  (__res_obj.res_0 = SISAL_CAST(sisal_array_t, v_g1_n__0_p0_i));
  (__res_obj.res_1 = SISAL_CAST(sisal_array_t, v_g1_n__0_p1_i));
  return __res_obj;
}
