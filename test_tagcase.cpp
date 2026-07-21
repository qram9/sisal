#define SISAL_CUSTOM_ELEM_SIZE

#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <math.h>
#include <iostream>
#include <dispatch/dispatch.h>
#include <Accelerate/Accelerate.h>
#include <sisal_runtime.h>

enum union_tag_98 {
  union_98_A = 97,
  union_98_B = 96,
  union_98_D = 95
};
struct union_un_98 {
  int32_t tag;
  union union_val_98 {
  int32_t A;
  float B;
  sisal_array_t D;
} val;
};
inline struct union_un_98 make_union_98_A(int32_t val) {
  struct union_un_98 tmp = {};
  tmp.tag = 97;
  tmp.val.A = val;
  return tmp;
}
inline struct union_un_98 make_union_98_B(float val) {
  struct union_un_98 tmp = {};
  tmp.tag = 96;
  tmp.val.B = val;
  return tmp;
}
inline struct union_un_98 make_union_98_D(sisal_array_t val) {
  struct union_un_98 tmp = {};
  tmp.tag = 95;
  tmp.val.D = val;
  return tmp;
}
enum union_tag_97 {
  union_97_A = 97,
  union_97_B = 96,
  union_97_D = 95
};
struct union_un_97 {
  int32_t tag;
  union union_val_97 {
  int32_t A;
  float B;
  sisal_array_t D;
} val;
};
inline struct union_un_97 make_union_97_A(int32_t val) {
  struct union_un_97 tmp = {};
  tmp.tag = 97;
  tmp.val.A = val;
  return tmp;
}
inline struct union_un_97 make_union_97_B(float val) {
  struct union_un_97 tmp = {};
  tmp.tag = 96;
  tmp.val.B = val;
  return tmp;
}
inline struct union_un_97 make_union_97_D(sisal_array_t val) {
  struct union_un_97 tmp = {};
  tmp.tag = 95;
  tmp.val.D = val;
  return tmp;
}
enum union_tag_96 {
  union_96_B = 96,
  union_96_D = 95
};
struct union_un_96 {
  int32_t tag;
  union union_val_96 {
  float B;
  sisal_array_t D;
} val;
};
inline struct union_un_96 make_union_96_B(float val) {
  struct union_un_96 tmp = {};
  tmp.tag = 96;
  tmp.val.B = val;
  return tmp;
}
inline struct union_un_96 make_union_96_D(sisal_array_t val) {
  struct union_un_96 tmp = {};
  tmp.tag = 95;
  tmp.val.D = val;
  return tmp;
}
enum union_tag_95 {
  union_95_D = 95
};
struct union_un_95 {
  int32_t tag;
  union union_val_95 {
  sisal_array_t D;
} val;
};
inline struct union_un_95 make_union_95_D(sisal_array_t val) {
  struct union_un_95 tmp = {};
  tmp.tag = 95;
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
  float res_0;
  float res_1;
};
struct FUNC_TESTUNION_results {
  float res_0;
  float res_1;
};
size_t sisal_elem_size(int32_t type_id) {
    switch (type_id) {
        case 83:
            return sizeof(void*);
        case 12:
            return sizeof(uint32_t);
        case 98:
            return sizeof(struct union_un_98);
        case 97:
            return sizeof(struct union_un_97);
        case 96:
            return sizeof(struct union_un_96);
        case 95:
            return sizeof(struct union_un_95);
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
        case 103:
        case 104:
        case 105:
        case 106:
        case 107:
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

extern "C" struct FUNC_MAIN_results func_MAIN(int32_t SEL, float VAL);
extern "C" struct FUNC_TESTUNION_results func_TESTUNION(struct union_un_98 X);

extern "C" struct FUNC_TESTUNION_results func_TESTUNION(struct union_un_98 X) {
  struct union_un_98 v_g1_n__0_X = {};
  (v_g1_n__0_X = SISAL_CAST(struct union_un_98, X));
  float v_g1_n__0_p0_i = 0;
  float v_g1_n__0_p1_i = 0;
  float v_g1_n__1_p0_o = 0;
  float v_g1_n__1_p1_o = 0;
  switch (v_g1_n__0_X.tag) {
  case union_98_D: {
    {
      sisal_array_t v_D_11012_n__0_P = {0};
      sisal_array_t v_D_11012_n__0_p0_i = v_g1_n__0_X.val.D;
      float v_D_11012_n__1_p0_o = 0;
      (v_D_11012_n__1_p0_o = SISAL_CAST(float, 3.f));
      float v_D_11012_n__2_p0_o = 0;
      (v_D_11012_n__2_p0_o = SISAL_CAST(float, 5.f));
      (v_g1_n__1_p0_o = SISAL_CAST(float, v_D_11012_n__2_p0_o));
      (v_g1_n__1_p1_o = SISAL_CAST(float, v_D_11012_n__1_p0_o));
      break;
    }
}
  case union_98_B: {
    {
      float v_B_11011_n__0_P = 0;
      float v_B_11011_n__0_p0_i = v_g1_n__0_X.val.B;
      (v_g1_n__1_p0_o = SISAL_CAST(float, v_B_11011_n__0_p0_i));
      (v_g1_n__1_p1_o = SISAL_CAST(float, v_B_11011_n__0_p0_i));
      break;
    }
}
  case union_98_A: {
    {
      int32_t v_OTHERWISE_11013_n__0_p0_i = v_g1_n__0_X.val.A;
      float v_OTHERWISE_11013_n__1_p0_o = 0;
      (v_OTHERWISE_11013_n__1_p0_o = SISAL_CAST(float, 4.f));
      float v_OTHERWISE_11013_n__2_p0_o = 0;
      (v_OTHERWISE_11013_n__2_p0_o = SISAL_CAST(float, 2.f));
      (v_g1_n__1_p0_o = SISAL_CAST(float, v_OTHERWISE_11013_n__2_p0_o));
      (v_g1_n__1_p1_o = SISAL_CAST(float, v_OTHERWISE_11013_n__1_p0_o));
      break;
    }
}
}
  (v_g1_n__0_p0_i = SISAL_CAST(float, v_g1_n__1_p0_o));
  (v_g1_n__0_p1_i = SISAL_CAST(float, v_g1_n__1_p1_o));
  struct FUNC_TESTUNION_results __res_obj;
  (__res_obj.res_0 = SISAL_CAST(float, v_g1_n__0_p0_i));
  (__res_obj.res_1 = SISAL_CAST(float, v_g1_n__0_p1_i));
  return __res_obj;
}

extern "C" struct FUNC_MAIN_results func_MAIN(int32_t SEL, float VAL) {
  int32_t v_g2_n__0_SEL = 0;
  float v_g2_n__0_VAL = 0;
  (v_g2_n__0_SEL = SISAL_CAST(int32_t, SEL));
  (v_g2_n__0_VAL = SISAL_CAST(float, VAL));
  float v_g2_n__0_p0_i = 0;
  float v_g2_n__0_p1_i = 0;
  float v_g2_n__1_p0_o = 0;
  float v_g2_n__1_p1_o = 0;
  {
    int32_t v_LET_NON_REC_10001_n__0_SEL = 0;
    struct union_un_98 v_LET_NON_REC_10001_n__2_U_A = {};
    struct union_un_98 v_LET_NON_REC_10001_n__3_U_B = {};
    struct union_un_98 v_LET_NON_REC_10001_n__8_U_D = {};
    float v_LET_NON_REC_10001_n__0_VAL = 0;
    (v_LET_NON_REC_10001_n__0_SEL = SISAL_CAST(int32_t, v_g2_n__0_SEL));
    (v_LET_NON_REC_10001_n__0_VAL = SISAL_CAST(float, v_g2_n__0_VAL));
    int32_t v_LET_NON_REC_10001_n__1_p0_o = 0;
    (v_LET_NON_REC_10001_n__1_p0_o = SISAL_CAST(int32_t, 42));
    (v_LET_NON_REC_10001_n__2_U_A = SISAL_CAST(struct union_un_98, make_union_98_A(v_LET_NON_REC_10001_n__1_p0_o)));
    (v_LET_NON_REC_10001_n__3_U_B = SISAL_CAST(struct union_un_98, make_union_98_B(v_LET_NON_REC_10001_n__0_VAL)));
    int32_t v_LET_NON_REC_10001_n__5_p0_o = 0;
    (v_LET_NON_REC_10001_n__5_p0_o = SISAL_CAST(int32_t, 1));
    int32_t v_LET_NON_REC_10001_n__6_p0_o = 0;
    (v_LET_NON_REC_10001_n__6_p0_o = SISAL_CAST(int32_t, 3));
    int32_t v_LET_NON_REC_10001_n__7_p0_o = 0;
    (v_LET_NON_REC_10001_n__7_p0_o = SISAL_CAST(int32_t, 10));
    sisal_array_t v_LET_NON_REC_10001_n__4_p0_o = {0};
    (v_LET_NON_REC_10001_n__4_p0_o = SISAL_CAST(sisal_array_t, sisal_array_fill_i32(((int64_t)SISAL_CAST(int32_t, v_LET_NON_REC_10001_n__5_p0_o)), ((int64_t)SISAL_CAST(int32_t, v_LET_NON_REC_10001_n__6_p0_o)), SISAL_CAST(int32_t, v_LET_NON_REC_10001_n__7_p0_o))));
    (v_LET_NON_REC_10001_n__8_U_D = SISAL_CAST(struct union_un_98, make_union_98_D(v_LET_NON_REC_10001_n__4_p0_o)));
    float v_LET_NON_REC_10001_n__9_p0_o = 0;
    float v_LET_NON_REC_10001_n__9_p1_o = 0;
    int32_t v_IF_REAL__REAL___10002_n__0_SEL = 0;
    (v_IF_REAL__REAL___10002_n__0_SEL = SISAL_CAST(int32_t, v_LET_NON_REC_10001_n__0_SEL));
    struct union_un_98 v_IF_REAL__REAL___10002_n__0_U_D = {};
    (v_IF_REAL__REAL___10002_n__0_U_D = SISAL_CAST(struct union_un_98, v_LET_NON_REC_10001_n__8_U_D));
    struct union_un_98 v_IF_REAL__REAL___10002_n__0_U_B = {};
    (v_IF_REAL__REAL___10002_n__0_U_B = SISAL_CAST(struct union_un_98, v_LET_NON_REC_10001_n__3_U_B));
    struct union_un_98 v_IF_REAL__REAL___10002_n__0_U_A = {};
    (v_IF_REAL__REAL___10002_n__0_U_A = SISAL_CAST(struct union_un_98, v_LET_NON_REC_10001_n__2_U_A));
    {
      int32_t v_PREDICATE_10003_n__0_SEL = 0;
      (v_PREDICATE_10003_n__0_SEL = SISAL_CAST(int32_t, v_IF_REAL__REAL___10002_n__0_SEL));
      int32_t v_PREDICATE_10003_n__1_p0_o = 0;
      (v_PREDICATE_10003_n__1_p0_o = SISAL_CAST(int32_t, 1));
      bool v_PREDICATE_10003_n__2_p0_o = 0;
      (v_PREDICATE_10003_n__2_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_PREDICATE_10003_n__0_SEL) == SISAL_CAST(int32_t, v_PREDICATE_10003_n__1_p0_o))));
      if (v_PREDICATE_10003_n__2_p0_o) {
        struct union_un_98 v_THEN_10009_n__0_U_A = {};
        (v_THEN_10009_n__0_U_A = SISAL_CAST(struct union_un_98, v_IF_REAL__REAL___10002_n__0_U_A));
        struct FUNC_TESTUNION_results _mr_THEN_10009_1 = func_TESTUNION(SISAL_CAST(struct union_un_98, v_THEN_10009_n__0_U_A));
        float v_THEN_10009_n__1_p0_o = 0;
        (v_THEN_10009_n__1_p0_o = SISAL_CAST(float, _mr_THEN_10009_1.res_0));
        float v_THEN_10009_n__1_p1_o = 0;
        (v_THEN_10009_n__1_p1_o = SISAL_CAST(float, _mr_THEN_10009_1.res_1));
        (v_LET_NON_REC_10001_n__9_p0_o = SISAL_CAST(float, v_THEN_10009_n__1_p0_o));
        (v_LET_NON_REC_10001_n__9_p1_o = SISAL_CAST(float, v_THEN_10009_n__1_p1_o));
      }
      else {
        int32_t v_ELSE_10004_n__0_SEL = 0;
        struct union_un_98 v_ELSE_10004_n__0_U_B = {};
        struct union_un_98 v_ELSE_10004_n__0_U_D = {};
        (v_ELSE_10004_n__0_SEL = SISAL_CAST(int32_t, v_IF_REAL__REAL___10002_n__0_SEL));
        (v_ELSE_10004_n__0_U_D = SISAL_CAST(struct union_un_98, v_IF_REAL__REAL___10002_n__0_U_D));
        (v_ELSE_10004_n__0_U_B = SISAL_CAST(struct union_un_98, v_IF_REAL__REAL___10002_n__0_U_B));
        float v_ELSE_10004_n__1_p0_o = 0;
        float v_ELSE_10004_n__1_p1_o = 0;
        int32_t v_IF_REAL__REAL___10005_n__0_SEL = 0;
        (v_IF_REAL__REAL___10005_n__0_SEL = SISAL_CAST(int32_t, v_ELSE_10004_n__0_SEL));
        struct union_un_98 v_IF_REAL__REAL___10005_n__0_U_D = {};
        (v_IF_REAL__REAL___10005_n__0_U_D = SISAL_CAST(struct union_un_98, v_ELSE_10004_n__0_U_D));
        struct union_un_98 v_IF_REAL__REAL___10005_n__0_U_B = {};
        (v_IF_REAL__REAL___10005_n__0_U_B = SISAL_CAST(struct union_un_98, v_ELSE_10004_n__0_U_B));
        {
          int32_t v_PREDICATE_10006_n__0_SEL = 0;
          (v_PREDICATE_10006_n__0_SEL = SISAL_CAST(int32_t, v_IF_REAL__REAL___10005_n__0_SEL));
          int32_t v_PREDICATE_10006_n__1_p0_o = 0;
          (v_PREDICATE_10006_n__1_p0_o = SISAL_CAST(int32_t, 2));
          bool v_PREDICATE_10006_n__2_p0_o = 0;
          (v_PREDICATE_10006_n__2_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_PREDICATE_10006_n__0_SEL) == SISAL_CAST(int32_t, v_PREDICATE_10006_n__1_p0_o))));
          if (v_PREDICATE_10006_n__2_p0_o) {
            struct union_un_98 v_THEN_10008_n__0_U_B = {};
            (v_THEN_10008_n__0_U_B = SISAL_CAST(struct union_un_98, v_IF_REAL__REAL___10005_n__0_U_B));
            struct FUNC_TESTUNION_results _mr_THEN_10008_1 = func_TESTUNION(SISAL_CAST(struct union_un_98, v_THEN_10008_n__0_U_B));
            float v_THEN_10008_n__1_p0_o = 0;
            (v_THEN_10008_n__1_p0_o = SISAL_CAST(float, _mr_THEN_10008_1.res_0));
            float v_THEN_10008_n__1_p1_o = 0;
            (v_THEN_10008_n__1_p1_o = SISAL_CAST(float, _mr_THEN_10008_1.res_1));
            (v_ELSE_10004_n__1_p0_o = SISAL_CAST(float, v_THEN_10008_n__1_p0_o));
            (v_ELSE_10004_n__1_p1_o = SISAL_CAST(float, v_THEN_10008_n__1_p1_o));
          }
          else {
            struct union_un_98 v_ELSE_10007_n__0_U_D = {};
            (v_ELSE_10007_n__0_U_D = SISAL_CAST(struct union_un_98, v_IF_REAL__REAL___10005_n__0_U_D));
            struct FUNC_TESTUNION_results _mr_ELSE_10007_1 = func_TESTUNION(SISAL_CAST(struct union_un_98, v_ELSE_10007_n__0_U_D));
            float v_ELSE_10007_n__1_p0_o = 0;
            (v_ELSE_10007_n__1_p0_o = SISAL_CAST(float, _mr_ELSE_10007_1.res_0));
            float v_ELSE_10007_n__1_p1_o = 0;
            (v_ELSE_10007_n__1_p1_o = SISAL_CAST(float, _mr_ELSE_10007_1.res_1));
            (v_ELSE_10004_n__1_p0_o = SISAL_CAST(float, v_ELSE_10007_n__1_p0_o));
            (v_ELSE_10004_n__1_p1_o = SISAL_CAST(float, v_ELSE_10007_n__1_p1_o));
          }
        }
        (v_LET_NON_REC_10001_n__9_p0_o = SISAL_CAST(float, v_ELSE_10004_n__1_p0_o));
        (v_LET_NON_REC_10001_n__9_p1_o = SISAL_CAST(float, v_ELSE_10004_n__1_p1_o));
      }
    }
    (v_g2_n__1_p0_o = SISAL_CAST(float, v_LET_NON_REC_10001_n__9_p0_o));
    (v_g2_n__1_p1_o = SISAL_CAST(float, v_LET_NON_REC_10001_n__9_p1_o));
  }
  (v_g2_n__0_p0_i = SISAL_CAST(float, v_g2_n__1_p0_o));
  (v_g2_n__0_p1_i = SISAL_CAST(float, v_g2_n__1_p1_o));
  struct FUNC_MAIN_results __res_obj;
  (__res_obj.res_0 = SISAL_CAST(float, v_g2_n__0_p0_i));
  (__res_obj.res_1 = SISAL_CAST(float, v_g2_n__0_p1_i));
  return __res_obj;
}
