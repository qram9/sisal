#define SISAL_CUSTOM_ELEM_SIZE

#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <math.h>
#include <iostream>
#include <dispatch/dispatch.h>
#include <Accelerate/Accelerate.h>
#include <sisal_runtime.h>

struct struct_rec_94 {
  float RE;
  float IM;
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
struct FUNC_MAIN_results {
  float res_0;
  float res_1;
  float res_2;
  float res_3;
  float res_4;
  float res_5;
};
size_t sisal_elem_size(int32_t type_id) {
    switch (type_id) {
        case 83:
            return sizeof(void*);
        case 12:
            return sizeof(uint32_t);
        case 94:
        case 95:
            return sizeof(struct struct_rec_94);
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

extern "C" struct FUNC_MAIN_results func_MAIN(float RE1, float IM1, float RE2, float IM2);
extern "C" struct struct_rec_94 func_COMPLEXSUM(sisal_array_t ARR);
extern "C" struct struct_rec_94 func_COMPLEXMUL(struct struct_rec_94 A, struct struct_rec_94 B);
extern "C" struct struct_rec_94 func_COMPLEXADD(struct struct_rec_94 A, struct struct_rec_94 B);

extern "C" struct struct_rec_94 func_COMPLEXADD(struct struct_rec_94 A, struct struct_rec_94 B) {
  struct struct_rec_94 v_g1_n__0_A = {};
  struct struct_rec_94 v_g1_n__0_B = {};
  (v_g1_n__0_A = SISAL_CAST(struct struct_rec_94, A));
  (v_g1_n__0_B = SISAL_CAST(struct struct_rec_94, B));
  struct struct_rec_94 v_g1_n__0_p0_i = {};
  float v_g1_n__1_p0_o = 0;
  (v_g1_n__1_p0_o = SISAL_CAST(float, v_g1_n__0_A.RE));
  float v_g1_n__2_p0_o = 0;
  (v_g1_n__2_p0_o = SISAL_CAST(float, v_g1_n__0_B.RE));
  float v_g1_n__3_p0_o = 0;
  (v_g1_n__3_p0_o = SISAL_CAST(float, (SISAL_CAST(float, v_g1_n__1_p0_o) + SISAL_CAST(float, v_g1_n__2_p0_o))));
  float v_g1_n__4_p0_o = 0;
  (v_g1_n__4_p0_o = SISAL_CAST(float, v_g1_n__0_A.IM));
  float v_g1_n__5_p0_o = 0;
  (v_g1_n__5_p0_o = SISAL_CAST(float, v_g1_n__0_B.IM));
  float v_g1_n__6_p0_o = 0;
  (v_g1_n__6_p0_o = SISAL_CAST(float, (SISAL_CAST(float, v_g1_n__4_p0_o) + SISAL_CAST(float, v_g1_n__5_p0_o))));
  struct struct_rec_94 v_g1_n__7_p0_o = {};
  (v_g1_n__7_p0_o = SISAL_CAST(struct struct_rec_94, (struct_rec_94{((float)v_g1_n__3_p0_o), ((float)v_g1_n__6_p0_o)})));
  (v_g1_n__0_p0_i = SISAL_CAST(struct struct_rec_94, v_g1_n__7_p0_o));
  return SISAL_CAST(struct struct_rec_94, v_g1_n__0_p0_i);
}

extern "C" struct struct_rec_94 func_COMPLEXMUL(struct struct_rec_94 A, struct struct_rec_94 B) {
  struct struct_rec_94 v_g2_n__0_A = {};
  struct struct_rec_94 v_g2_n__0_B = {};
  (v_g2_n__0_A = SISAL_CAST(struct struct_rec_94, A));
  (v_g2_n__0_B = SISAL_CAST(struct struct_rec_94, B));
  struct struct_rec_94 v_g2_n__0_p0_i = {};
  float v_g2_n__1_p0_o = 0;
  (v_g2_n__1_p0_o = SISAL_CAST(float, v_g2_n__0_A.RE));
  float v_g2_n__2_p0_o = 0;
  (v_g2_n__2_p0_o = SISAL_CAST(float, v_g2_n__0_B.RE));
  float v_g2_n__3_p0_o = 0;
  (v_g2_n__3_p0_o = SISAL_CAST(float, (SISAL_CAST(float, v_g2_n__1_p0_o) * SISAL_CAST(float, v_g2_n__2_p0_o))));
  float v_g2_n__4_p0_o = 0;
  (v_g2_n__4_p0_o = SISAL_CAST(float, v_g2_n__0_A.IM));
  float v_g2_n__5_p0_o = 0;
  (v_g2_n__5_p0_o = SISAL_CAST(float, v_g2_n__0_B.IM));
  float v_g2_n__6_p0_o = 0;
  (v_g2_n__6_p0_o = SISAL_CAST(float, (SISAL_CAST(float, v_g2_n__4_p0_o) * SISAL_CAST(float, v_g2_n__5_p0_o))));
  float v_g2_n__7_p0_o = 0;
  (v_g2_n__7_p0_o = SISAL_CAST(float, (SISAL_CAST(float, v_g2_n__3_p0_o) - SISAL_CAST(float, v_g2_n__6_p0_o))));
  float v_g2_n__8_p0_o = 0;
  (v_g2_n__8_p0_o = SISAL_CAST(float, v_g2_n__0_A.RE));
  float v_g2_n__9_p0_o = 0;
  (v_g2_n__9_p0_o = SISAL_CAST(float, v_g2_n__0_B.IM));
  float v_g2_n__10_p0_o = 0;
  (v_g2_n__10_p0_o = SISAL_CAST(float, (SISAL_CAST(float, v_g2_n__8_p0_o) * SISAL_CAST(float, v_g2_n__9_p0_o))));
  float v_g2_n__11_p0_o = 0;
  (v_g2_n__11_p0_o = SISAL_CAST(float, v_g2_n__0_A.IM));
  float v_g2_n__12_p0_o = 0;
  (v_g2_n__12_p0_o = SISAL_CAST(float, v_g2_n__0_B.RE));
  float v_g2_n__13_p0_o = 0;
  (v_g2_n__13_p0_o = SISAL_CAST(float, (SISAL_CAST(float, v_g2_n__11_p0_o) * SISAL_CAST(float, v_g2_n__12_p0_o))));
  float v_g2_n__14_p0_o = 0;
  (v_g2_n__14_p0_o = SISAL_CAST(float, (SISAL_CAST(float, v_g2_n__10_p0_o) + SISAL_CAST(float, v_g2_n__13_p0_o))));
  struct struct_rec_94 v_g2_n__15_p0_o = {};
  (v_g2_n__15_p0_o = SISAL_CAST(struct struct_rec_94, (struct_rec_94{((float)v_g2_n__7_p0_o), ((float)v_g2_n__14_p0_o)})));
  (v_g2_n__0_p0_i = SISAL_CAST(struct struct_rec_94, v_g2_n__15_p0_o));
  return SISAL_CAST(struct struct_rec_94, v_g2_n__0_p0_i);
}

extern "C" struct struct_rec_94 func_COMPLEXSUM(sisal_array_t ARR) {
  sisal_array_t v_g3_n__0_ARR = {0};
  (v_g3_n__0_ARR = SISAL_CAST(sisal_array_t, ARR));
  struct struct_rec_94 v_g3_n__0_p0_i = {};
  struct struct_rec_94 v_g3_n__1_p0_o = {};
  {
    sisal_array_t v_LET_NON_REC_11002_n__0_ARR = {0};
    float v_LET_NON_REC_11002_n__2_SUM_IM = 0;
    float v_LET_NON_REC_11002_n__2_SUM_RE = 0;
    (v_LET_NON_REC_11002_n__0_ARR = SISAL_CAST(sisal_array_t, v_g3_n__0_ARR));
    float v_LET_NON_REC_11002_n__1_p0_o = 0;
    float v_LET_NON_REC_11002_n__1_p1_o = 0;
    {
      sisal_array_t v_FORALL_11003_n__0_ARR = v_LET_NON_REC_11002_n__0_ARR;
      struct struct_rec_94 v_FORALL_11003_n__2_ELEM;
      float v_FORALL_11003_n__3___forall_body_0;
      float v_FORALL_11003_n__3___forall_body_1;
      sisal_array_t v_GENERATOR_11005_n__0_ARR;
      struct struct_rec_94 v_GENERATOR_11005_n__1_ELEM;
      sisal_array_t v_BODY_11006_n__0_ARR;
      struct struct_rec_94 v_BODY_11006_n__0_ELEM;
      (v_GENERATOR_11005_n__0_ARR = v_FORALL_11003_n__0_ARR);
      (v_LET_NON_REC_11002_n__1_p0_o = 0);
      (v_LET_NON_REC_11002_n__1_p1_o = 0);
      for (int32_t __k_11005 = 0; (__k_11005 < ((int32_t)v_GENERATOR_11005_n__0_ARR.size)); (__k_11005++)) {
        (v_GENERATOR_11005_n__1_ELEM = ((struct struct_rec_94 *)v_GENERATOR_11005_n__0_ARR.data)[__k_11005]);
        (v_BODY_11006_n__0_ARR = SISAL_CAST(sisal_array_t, v_FORALL_11003_n__0_ARR));
        (v_BODY_11006_n__0_ELEM = SISAL_CAST(struct struct_rec_94, v_GENERATOR_11005_n__1_ELEM));
        float v_BODY_11006_n__1_p0_o = 0;
        (v_BODY_11006_n__1_p0_o = SISAL_CAST(float, v_BODY_11006_n__0_ELEM.RE));
        float v_BODY_11006_n__2_p0_o = 0;
        (v_BODY_11006_n__2_p0_o = SISAL_CAST(float, v_BODY_11006_n__0_ELEM.IM));
        (v_LET_NON_REC_11002_n__1_p0_o = (v_LET_NON_REC_11002_n__1_p0_o + SISAL_CAST(float, v_BODY_11006_n__1_p0_o)));
        (v_LET_NON_REC_11002_n__1_p1_o = (v_LET_NON_REC_11002_n__1_p1_o + SISAL_CAST(float, v_BODY_11006_n__2_p0_o)));
      }
    }
    struct struct_rec_94 v_LET_NON_REC_11002_n__3_p0_o = {};
    (v_LET_NON_REC_11002_n__3_p0_o = SISAL_CAST(struct struct_rec_94, (struct_rec_94{((float)v_LET_NON_REC_11002_n__1_p0_o), ((float)v_LET_NON_REC_11002_n__1_p1_o)})));
    (v_g3_n__1_p0_o = SISAL_CAST(struct struct_rec_94, v_LET_NON_REC_11002_n__3_p0_o));
  }
  (v_g3_n__0_p0_i = SISAL_CAST(struct struct_rec_94, v_g3_n__1_p0_o));
  return SISAL_CAST(struct struct_rec_94, v_g3_n__0_p0_i);
}

extern "C" struct FUNC_MAIN_results func_MAIN(float RE1, float IM1, float RE2, float IM2) {
  float v_g4_n__0_IM1 = 0;
  float v_g4_n__0_IM2 = 0;
  float v_g4_n__0_RE1 = 0;
  float v_g4_n__0_RE2 = 0;
  (v_g4_n__0_RE1 = SISAL_CAST(float, RE1));
  (v_g4_n__0_IM1 = SISAL_CAST(float, IM1));
  (v_g4_n__0_RE2 = SISAL_CAST(float, RE2));
  (v_g4_n__0_IM2 = SISAL_CAST(float, IM2));
  float v_g4_n__0_p0_i = 0;
  float v_g4_n__0_p1_i = 0;
  float v_g4_n__0_p2_i = 0;
  float v_g4_n__0_p3_i = 0;
  float v_g4_n__0_p4_i = 0;
  float v_g4_n__0_p5_i = 0;
  float v_g4_n__1_p0_o = 0;
  float v_g4_n__1_p1_o = 0;
  float v_g4_n__1_p2_o = 0;
  float v_g4_n__1_p3_o = 0;
  float v_g4_n__1_p4_o = 0;
  float v_g4_n__1_p5_o = 0;
  {
    struct struct_rec_94 v_LET_NON_REC_10001_n__1_A = {};
    sisal_array_t v_LET_NON_REC_10001_n__5_ARR = {0};
    struct struct_rec_94 v_LET_NON_REC_10001_n__2_B = {};
    struct struct_rec_94 v_LET_NON_REC_10001_n__3_C = {};
    struct struct_rec_94 v_LET_NON_REC_10001_n__4_D = {};
    float v_LET_NON_REC_10001_n__0_IM1 = 0;
    float v_LET_NON_REC_10001_n__0_IM2 = 0;
    float v_LET_NON_REC_10001_n__0_RE1 = 0;
    float v_LET_NON_REC_10001_n__0_RE2 = 0;
    struct struct_rec_94 v_LET_NON_REC_10001_n__8_SUM_RES = {};
    (v_LET_NON_REC_10001_n__0_IM1 = SISAL_CAST(float, v_g4_n__0_IM1));
    (v_LET_NON_REC_10001_n__0_IM2 = SISAL_CAST(float, v_g4_n__0_IM2));
    (v_LET_NON_REC_10001_n__0_RE1 = SISAL_CAST(float, v_g4_n__0_RE1));
    (v_LET_NON_REC_10001_n__0_RE2 = SISAL_CAST(float, v_g4_n__0_RE2));
    (v_LET_NON_REC_10001_n__1_A = SISAL_CAST(struct struct_rec_94, (struct_rec_94{((float)v_LET_NON_REC_10001_n__0_RE1), ((float)v_LET_NON_REC_10001_n__0_IM1)})));
    (v_LET_NON_REC_10001_n__2_B = SISAL_CAST(struct struct_rec_94, (struct_rec_94{((float)v_LET_NON_REC_10001_n__0_RE2), ((float)v_LET_NON_REC_10001_n__0_IM2)})));
    (v_LET_NON_REC_10001_n__3_C = SISAL_CAST(struct struct_rec_94, func_COMPLEXADD(SISAL_CAST(struct struct_rec_94, v_LET_NON_REC_10001_n__1_A), SISAL_CAST(struct struct_rec_94, v_LET_NON_REC_10001_n__2_B))));
    (v_LET_NON_REC_10001_n__4_D = SISAL_CAST(struct struct_rec_94, func_COMPLEXMUL(SISAL_CAST(struct struct_rec_94, v_LET_NON_REC_10001_n__1_A), SISAL_CAST(struct struct_rec_94, v_LET_NON_REC_10001_n__2_B))));
    int32_t v_LET_NON_REC_10001_n__6_p0_o = 0;
    (v_LET_NON_REC_10001_n__6_p0_o = SISAL_CAST(int32_t, 1));
    int32_t v_LET_NON_REC_10001_n__7_p0_o = 0;
    (v_LET_NON_REC_10001_n__7_p0_o = SISAL_CAST(int32_t, 4));
    (v_LET_NON_REC_10001_n__5_ARR = SISAL_CAST(sisal_array_t, sisal_array_fill_rec(((int64_t)SISAL_CAST(int32_t, v_LET_NON_REC_10001_n__6_p0_o)), ((int64_t)SISAL_CAST(int32_t, v_LET_NON_REC_10001_n__7_p0_o)), SISAL_CAST(struct struct_rec_94, v_LET_NON_REC_10001_n__1_A), 95)));
    (v_LET_NON_REC_10001_n__8_SUM_RES = SISAL_CAST(struct struct_rec_94, func_COMPLEXSUM(SISAL_CAST(sisal_array_t, v_LET_NON_REC_10001_n__5_ARR))));
    float v_LET_NON_REC_10001_n__9_p0_o = 0;
    (v_LET_NON_REC_10001_n__9_p0_o = SISAL_CAST(float, v_LET_NON_REC_10001_n__3_C.RE));
    float v_LET_NON_REC_10001_n__10_p0_o = 0;
    (v_LET_NON_REC_10001_n__10_p0_o = SISAL_CAST(float, v_LET_NON_REC_10001_n__3_C.IM));
    float v_LET_NON_REC_10001_n__11_p0_o = 0;
    (v_LET_NON_REC_10001_n__11_p0_o = SISAL_CAST(float, v_LET_NON_REC_10001_n__4_D.RE));
    float v_LET_NON_REC_10001_n__12_p0_o = 0;
    (v_LET_NON_REC_10001_n__12_p0_o = SISAL_CAST(float, v_LET_NON_REC_10001_n__4_D.IM));
    float v_LET_NON_REC_10001_n__13_p0_o = 0;
    (v_LET_NON_REC_10001_n__13_p0_o = SISAL_CAST(float, v_LET_NON_REC_10001_n__8_SUM_RES.RE));
    float v_LET_NON_REC_10001_n__14_p0_o = 0;
    (v_LET_NON_REC_10001_n__14_p0_o = SISAL_CAST(float, v_LET_NON_REC_10001_n__8_SUM_RES.IM));
    (v_g4_n__1_p0_o = SISAL_CAST(float, v_LET_NON_REC_10001_n__9_p0_o));
    (v_g4_n__1_p1_o = SISAL_CAST(float, v_LET_NON_REC_10001_n__10_p0_o));
    (v_g4_n__1_p2_o = SISAL_CAST(float, v_LET_NON_REC_10001_n__11_p0_o));
    (v_g4_n__1_p3_o = SISAL_CAST(float, v_LET_NON_REC_10001_n__12_p0_o));
    (v_g4_n__1_p4_o = SISAL_CAST(float, v_LET_NON_REC_10001_n__13_p0_o));
    (v_g4_n__1_p5_o = SISAL_CAST(float, v_LET_NON_REC_10001_n__14_p0_o));
  }
  (v_g4_n__0_p0_i = SISAL_CAST(float, v_g4_n__1_p0_o));
  (v_g4_n__0_p1_i = SISAL_CAST(float, v_g4_n__1_p1_o));
  (v_g4_n__0_p2_i = SISAL_CAST(float, v_g4_n__1_p2_o));
  (v_g4_n__0_p3_i = SISAL_CAST(float, v_g4_n__1_p3_o));
  (v_g4_n__0_p4_i = SISAL_CAST(float, v_g4_n__1_p4_o));
  (v_g4_n__0_p5_i = SISAL_CAST(float, v_g4_n__1_p5_o));
  struct FUNC_MAIN_results __res_obj;
  (__res_obj.res_0 = SISAL_CAST(float, v_g4_n__0_p0_i));
  (__res_obj.res_1 = SISAL_CAST(float, v_g4_n__0_p1_i));
  (__res_obj.res_2 = SISAL_CAST(float, v_g4_n__0_p2_i));
  (__res_obj.res_3 = SISAL_CAST(float, v_g4_n__0_p3_i));
  (__res_obj.res_4 = SISAL_CAST(float, v_g4_n__0_p4_i));
  (__res_obj.res_5 = SISAL_CAST(float, v_g4_n__0_p5_i));
  return __res_obj;
}
