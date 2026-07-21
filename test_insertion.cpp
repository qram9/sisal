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
        case 94:
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

extern "C" sisal_array_t func_MAIN(sisal_array_t INPUT);

extern "C" sisal_array_t func_MAIN(sisal_array_t INPUT) {
  sisal_array_t v_g1_n__0_INPUT = {0};
  (v_g1_n__0_INPUT = SISAL_CAST(sisal_array_t, INPUT));
  sisal_array_t v_g1_n__0_p0_i = {0};
  sisal_array_t v_g1_n__1_p0_o = {0};
  {
    sisal_array_t v_LoopB_10001_n__5_MERGE_A = {0};
    int32_t v_LoopB_10001_n__6_MERGE_I = 0;
    sisal_array_t v_LoopB_10001_n__7_MERGE_OLD_A = {0};
    int32_t v_LoopB_10001_n__8_MERGE_OLD_I = 0;
    bool v_LoopB_10001_n__9_MERGE_first = 0;
    int32_t v_LoopB_10001_bodycap_n2_p0 = 0;
    sisal_array_t v_LoopB_10001_bodycap_n3_p0 = {0};
    bool v_LoopB_10001_bodycap_n5_p0 = 0;
    sisal_array_t v_LoopB_10001_n__0_INPUT = {0};
    (v_LoopB_10001_n__0_INPUT = SISAL_CAST(sisal_array_t, v_g1_n__0_INPUT));
    sisal_array_t v_INIT_10010_n__0_A = {0};
    int32_t v_INIT_10010_n__1_I = 0;
    sisal_array_t v_INIT_10010_n__0_INPUT = {0};
    sisal_array_t v_INIT_10010_n__0_OLD_A = {0};
    int32_t v_INIT_10010_n__1_OLD_I = 0;
    (v_INIT_10010_n__0_OLD_A = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__0_INPUT));
    (v_INIT_10010_n__1_OLD_I = SISAL_CAST(int32_t, ((int32_t)SISAL_CAST(sisal_array_t, v_INIT_10010_n__0_OLD_A).lower_bound[0])));
    bool v_INIT_10010_n__2_p0_o = 0;
    (v_INIT_10010_n__2_p0_o = SISAL_CAST(bool, true));
    (v_LoopB_10001_n__5_MERGE_A = v_INIT_10010_n__0_OLD_A);
    (v_LoopB_10001_n__6_MERGE_I = v_INIT_10010_n__1_OLD_I);
    (v_LoopB_10001_n__7_MERGE_OLD_A = v_INIT_10010_n__0_OLD_A);
    (v_LoopB_10001_n__8_MERGE_OLD_I = v_INIT_10010_n__1_OLD_I);
    (v_LoopB_10001_n__9_MERGE_first = v_INIT_10010_n__2_p0_o);
    sisal_array_t v_TEST_10009_n__0_A = {0};
    int32_t v_TEST_10009_n__0_I = 0;
    sisal_array_t v_TEST_10009_n__0_INPUT = {0};
    sisal_array_t v_TEST_10009_n__0_OLD_A = {0};
    int32_t v_TEST_10009_n__0_OLD_I = 0;
    (v_TEST_10009_n__0_A = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__5_MERGE_A));
    (v_TEST_10009_n__0_I = SISAL_CAST(int32_t, v_LoopB_10001_n__6_MERGE_I));
    (v_TEST_10009_n__0_INPUT = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__0_INPUT));
    (v_TEST_10009_n__0_OLD_A = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__7_MERGE_OLD_A));
    (v_TEST_10009_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_10001_n__8_MERGE_OLD_I));
    int32_t v_TEST_10009_n__1_p0_o = 0;
    (v_TEST_10009_n__1_p0_o = SISAL_CAST(int32_t, ((int32_t)((SISAL_CAST(sisal_array_t, v_TEST_10009_n__0_INPUT).lower_bound[0] + ((SISAL_CAST(sisal_array_t, v_TEST_10009_n__0_INPUT).dims[0] > 0) ? SISAL_CAST(sisal_array_t, v_TEST_10009_n__0_INPUT).dims[0] : ((int64_t)SISAL_CAST(sisal_array_t, v_TEST_10009_n__0_INPUT).size))) - 1))));
    bool v_TEST_10009_n__2_p0_o = 0;
    (v_TEST_10009_n__2_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_TEST_10009_n__0_I) < SISAL_CAST(int32_t, v_TEST_10009_n__1_p0_o))));
    while (v_TEST_10009_n__2_p0_o) {
      sisal_array_t v_BODY_10002_n__3_A = {0};
      int32_t v_BODY_10002_n__2_I = 0;
      sisal_array_t v_BODY_10002_n__0_INPUT = {0};
      sisal_array_t v_BODY_10002_n__0_OLD_A = {0};
      int32_t v_BODY_10002_n__0_OLD_I = 0;
      sisal_array_t v_BODY_10002_n__0_p0_o = {0};
      (v_BODY_10002_n__0_p0_o = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__5_MERGE_A));
      int32_t v_BODY_10002_n__0_p1_o = 0;
      (v_BODY_10002_n__0_p1_o = SISAL_CAST(int32_t, v_LoopB_10001_n__6_MERGE_I));
      (v_BODY_10002_n__0_INPUT = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__0_INPUT));
      (v_BODY_10002_n__0_OLD_A = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__7_MERGE_OLD_A));
      (v_BODY_10002_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_10001_n__8_MERGE_OLD_I));
      int32_t v_BODY_10002_n__1_p0_o = 0;
      (v_BODY_10002_n__1_p0_o = SISAL_CAST(int32_t, 1));
      (v_BODY_10002_n__2_I = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_10002_n__0_OLD_I) + SISAL_CAST(int32_t, v_BODY_10002_n__1_p0_o))));
      {
        sisal_array_t v_LoopB_10003_n__5_MERGE_B = {0};
        int32_t v_LoopB_10003_n__6_MERGE_J = 0;
        sisal_array_t v_LoopB_10003_n__7_MERGE_OLD_B = {0};
        int32_t v_LoopB_10003_n__8_MERGE_OLD_J = 0;
        bool v_LoopB_10003_n__9_MERGE_first = 0;
        int32_t v_LoopB_10003_bodycap_n2_p0 = 0;
        sisal_array_t v_LoopB_10003_bodycap_n5_p0 = {0};
        bool v_LoopB_10003_bodycap_n6_p0 = 0;
        sisal_array_t v_LoopB_10003_n__0_A = {0};
        (v_LoopB_10003_n__0_A = SISAL_CAST(sisal_array_t, v_BODY_10002_n__0_p0_o));
        int32_t v_LoopB_10003_n__0_I = 0;
        (v_LoopB_10003_n__0_I = SISAL_CAST(int32_t, v_BODY_10002_n__2_I));
        sisal_array_t v_LoopB_10003_n__0_INPUT = {0};
        (v_LoopB_10003_n__0_INPUT = SISAL_CAST(sisal_array_t, v_BODY_10002_n__0_INPUT));
        sisal_array_t v_LoopB_10003_n__0_OLD_A = {0};
        (v_LoopB_10003_n__0_OLD_A = SISAL_CAST(sisal_array_t, v_BODY_10002_n__0_OLD_A));
        int32_t v_LoopB_10003_n__0_OLD_I = 0;
        (v_LoopB_10003_n__0_OLD_I = SISAL_CAST(int32_t, v_BODY_10002_n__0_OLD_I));
        sisal_array_t v_INIT_10007_n__0_A = {0};
        sisal_array_t v_INIT_10007_n__0_B = {0};
        int32_t v_INIT_10007_n__0_I = 0;
        sisal_array_t v_INIT_10007_n__0_INPUT = {0};
        int32_t v_INIT_10007_n__0_J = 0;
        sisal_array_t v_INIT_10007_n__0_OLD_A = {0};
        sisal_array_t v_INIT_10007_n__0_OLD_B = {0};
        int32_t v_INIT_10007_n__0_OLD_I = 0;
        int32_t v_INIT_10007_n__0_OLD_J = 0;
        (v_INIT_10007_n__0_A = SISAL_CAST(sisal_array_t, v_LoopB_10003_n__0_A));
        (v_INIT_10007_n__0_OLD_J = SISAL_CAST(int32_t, v_LoopB_10003_n__0_I));
        (v_INIT_10007_n__0_INPUT = SISAL_CAST(sisal_array_t, v_LoopB_10003_n__0_INPUT));
        (v_INIT_10007_n__0_OLD_B = SISAL_CAST(sisal_array_t, v_LoopB_10003_n__0_OLD_A));
        (v_INIT_10007_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_10003_n__0_OLD_I));
        bool v_INIT_10007_n__1_p0_o = 0;
        (v_INIT_10007_n__1_p0_o = SISAL_CAST(bool, true));
        (v_LoopB_10003_n__5_MERGE_B = v_INIT_10007_n__0_OLD_B);
        (v_LoopB_10003_n__6_MERGE_J = v_INIT_10007_n__0_OLD_J);
        (v_LoopB_10003_n__7_MERGE_OLD_B = v_INIT_10007_n__0_OLD_B);
        (v_LoopB_10003_n__8_MERGE_OLD_J = v_INIT_10007_n__0_OLD_J);
        (v_LoopB_10003_n__9_MERGE_first = v_INIT_10007_n__1_p0_o);
        sisal_array_t v_TEST_10006_n__0_A = {0};
        sisal_array_t v_TEST_10006_n__0_B = {0};
        int32_t v_TEST_10006_n__0_I = 0;
        sisal_array_t v_TEST_10006_n__0_INPUT = {0};
        int32_t v_TEST_10006_n__0_J = 0;
        sisal_array_t v_TEST_10006_n__0_OLD_A = {0};
        sisal_array_t v_TEST_10006_n__0_OLD_B = {0};
        int32_t v_TEST_10006_n__0_OLD_I = 0;
        int32_t v_TEST_10006_n__0_OLD_J = 0;
        (v_TEST_10006_n__0_A = SISAL_CAST(sisal_array_t, v_LoopB_10003_n__0_A));
        (v_TEST_10006_n__0_B = SISAL_CAST(sisal_array_t, v_LoopB_10003_n__5_MERGE_B));
        (v_TEST_10006_n__0_I = SISAL_CAST(int32_t, v_LoopB_10003_n__0_I));
        (v_TEST_10006_n__0_INPUT = SISAL_CAST(sisal_array_t, v_LoopB_10003_n__0_INPUT));
        (v_TEST_10006_n__0_J = SISAL_CAST(int32_t, v_LoopB_10003_n__6_MERGE_J));
        (v_TEST_10006_n__0_OLD_A = SISAL_CAST(sisal_array_t, v_LoopB_10003_n__0_OLD_A));
        (v_TEST_10006_n__0_OLD_B = SISAL_CAST(sisal_array_t, v_LoopB_10003_n__7_MERGE_OLD_B));
        (v_TEST_10006_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_10003_n__0_OLD_I));
        (v_TEST_10006_n__0_OLD_J = SISAL_CAST(int32_t, v_LoopB_10003_n__8_MERGE_OLD_J));
        int32_t v_TEST_10006_n__1_p0_o = 0;
        (v_TEST_10006_n__1_p0_o = SISAL_CAST(int32_t, ((int32_t)SISAL_CAST(sisal_array_t, v_TEST_10006_n__0_INPUT).lower_bound[0])));
        bool v_TEST_10006_n__2_p0_o = 0;
        (v_TEST_10006_n__2_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_TEST_10006_n__0_J) > SISAL_CAST(int32_t, v_TEST_10006_n__1_p0_o))));
        double v_TEST_10006_n__4_p0_o = 0;
        (v_TEST_10006_n__4_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_TEST_10006_n__0_B).data)[(SISAL_CAST(int32_t, v_TEST_10006_n__0_J) - SISAL_CAST(sisal_array_t, v_TEST_10006_n__0_B).lower_bound[0])]));
        int32_t v_TEST_10006_n__5_p0_o = 0;
        (v_TEST_10006_n__5_p0_o = SISAL_CAST(int32_t, 1));
        int32_t v_TEST_10006_n__6_p0_o = 0;
        (v_TEST_10006_n__6_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_TEST_10006_n__0_J) - SISAL_CAST(int32_t, v_TEST_10006_n__5_p0_o))));
        double v_TEST_10006_n__7_p0_o = 0;
        (v_TEST_10006_n__7_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_TEST_10006_n__0_B).data)[(SISAL_CAST(int32_t, v_TEST_10006_n__6_p0_o) - SISAL_CAST(sisal_array_t, v_TEST_10006_n__0_B).lower_bound[0])]));
        bool v_TEST_10006_n__8_p0_o = 0;
        (v_TEST_10006_n__8_p0_o = SISAL_CAST(bool, (SISAL_CAST(double, v_TEST_10006_n__4_p0_o) < SISAL_CAST(double, v_TEST_10006_n__7_p0_o))));
        bool v_TEST_10006_n__10_p0_o = 0;
        (v_TEST_10006_n__10_p0_o = SISAL_CAST(bool, (SISAL_CAST(bool, v_TEST_10006_n__2_p0_o) && SISAL_CAST(bool, v_TEST_10006_n__8_p0_o))));
        while (v_TEST_10006_n__10_p0_o) {
          sisal_array_t v_BODY_10004_n__0_A = {0};
          sisal_array_t v_BODY_10004_n__5_B = {0};
          int32_t v_BODY_10004_n__0_I = 0;
          sisal_array_t v_BODY_10004_n__0_INPUT = {0};
          int32_t v_BODY_10004_n__2_J = 0;
          sisal_array_t v_BODY_10004_n__0_OLD_A = {0};
          sisal_array_t v_BODY_10004_n__0_OLD_B = {0};
          int32_t v_BODY_10004_n__0_OLD_I = 0;
          int32_t v_BODY_10004_n__0_OLD_J = 0;
          (v_BODY_10004_n__0_A = SISAL_CAST(sisal_array_t, v_LoopB_10003_n__0_A));
          sisal_array_t v_BODY_10004_n__0_p1_o = {0};
          (v_BODY_10004_n__0_p1_o = SISAL_CAST(sisal_array_t, v_LoopB_10003_n__5_MERGE_B));
          (v_BODY_10004_n__0_I = SISAL_CAST(int32_t, v_LoopB_10003_n__0_I));
          (v_BODY_10004_n__0_INPUT = SISAL_CAST(sisal_array_t, v_LoopB_10003_n__0_INPUT));
          int32_t v_BODY_10004_n__0_p4_o = 0;
          (v_BODY_10004_n__0_p4_o = SISAL_CAST(int32_t, v_LoopB_10003_n__6_MERGE_J));
          (v_BODY_10004_n__0_OLD_A = SISAL_CAST(sisal_array_t, v_LoopB_10003_n__0_OLD_A));
          (v_BODY_10004_n__0_OLD_B = SISAL_CAST(sisal_array_t, v_LoopB_10003_n__7_MERGE_OLD_B));
          (v_BODY_10004_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_10003_n__0_OLD_I));
          (v_BODY_10004_n__0_OLD_J = SISAL_CAST(int32_t, v_LoopB_10003_n__8_MERGE_OLD_J));
          int32_t v_BODY_10004_n__1_p0_o = 0;
          (v_BODY_10004_n__1_p0_o = SISAL_CAST(int32_t, 1));
          (v_BODY_10004_n__2_J = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_10004_n__0_OLD_J) - SISAL_CAST(int32_t, v_BODY_10004_n__1_p0_o))));
          double v_BODY_10004_n__3_p0_o = 0;
          (v_BODY_10004_n__3_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_10004_n__0_OLD_B).data)[(SISAL_CAST(int32_t, v_BODY_10004_n__0_OLD_J) - SISAL_CAST(sisal_array_t, v_BODY_10004_n__0_OLD_B).lower_bound[0])]));
          double v_BODY_10004_n__4_p0_o = 0;
          (v_BODY_10004_n__4_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_10004_n__0_OLD_B).data)[(SISAL_CAST(int32_t, v_BODY_10004_n__2_J) - SISAL_CAST(sisal_array_t, v_BODY_10004_n__0_OLD_B).lower_bound[0])]));
          (v_BODY_10004_n__5_B = SISAL_CAST(sisal_array_t, sisal_array_replace_f64(sisal_array_replace_f64(SISAL_CAST(sisal_array_t, v_BODY_10004_n__0_OLD_B), ((int64_t)SISAL_CAST(int32_t, v_BODY_10004_n__2_J)), SISAL_CAST(double, v_BODY_10004_n__3_p0_o)), (((int64_t)SISAL_CAST(int32_t, v_BODY_10004_n__2_J)) + 1), SISAL_CAST(double, v_BODY_10004_n__4_p0_o))));
          bool v_BODY_10004_n__6_p0_o = 0;
          (v_BODY_10004_n__6_p0_o = SISAL_CAST(bool, false));
          (v_LoopB_10003_bodycap_n2_p0 = v_BODY_10004_n__2_J);
          (v_LoopB_10003_bodycap_n5_p0 = v_BODY_10004_n__5_B);
          (v_LoopB_10003_bodycap_n6_p0 = v_BODY_10004_n__6_p0_o);
          (v_LoopB_10003_n__5_MERGE_B = v_LoopB_10003_bodycap_n5_p0);
          (v_LoopB_10003_n__6_MERGE_J = v_LoopB_10003_bodycap_n2_p0);
          (v_LoopB_10003_n__7_MERGE_OLD_B = v_LoopB_10003_bodycap_n5_p0);
          (v_LoopB_10003_n__8_MERGE_OLD_J = v_LoopB_10003_bodycap_n2_p0);
          (v_LoopB_10003_n__9_MERGE_first = v_LoopB_10003_bodycap_n6_p0);
          (v_TEST_10006_n__0_A = SISAL_CAST(sisal_array_t, v_LoopB_10003_n__0_A));
          (v_TEST_10006_n__0_B = SISAL_CAST(sisal_array_t, v_LoopB_10003_n__5_MERGE_B));
          (v_TEST_10006_n__0_I = SISAL_CAST(int32_t, v_LoopB_10003_n__0_I));
          (v_TEST_10006_n__0_INPUT = SISAL_CAST(sisal_array_t, v_LoopB_10003_n__0_INPUT));
          (v_TEST_10006_n__0_J = SISAL_CAST(int32_t, v_LoopB_10003_n__6_MERGE_J));
          (v_TEST_10006_n__0_OLD_A = SISAL_CAST(sisal_array_t, v_LoopB_10003_n__0_OLD_A));
          (v_TEST_10006_n__0_OLD_B = SISAL_CAST(sisal_array_t, v_LoopB_10003_n__7_MERGE_OLD_B));
          (v_TEST_10006_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_10003_n__0_OLD_I));
          (v_TEST_10006_n__0_OLD_J = SISAL_CAST(int32_t, v_LoopB_10003_n__8_MERGE_OLD_J));
          (v_TEST_10006_n__1_p0_o = SISAL_CAST(int32_t, ((int32_t)SISAL_CAST(sisal_array_t, v_TEST_10006_n__0_INPUT).lower_bound[0])));
          (v_TEST_10006_n__2_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_TEST_10006_n__0_J) > SISAL_CAST(int32_t, v_TEST_10006_n__1_p0_o))));
          (v_TEST_10006_n__4_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_TEST_10006_n__0_B).data)[(SISAL_CAST(int32_t, v_TEST_10006_n__0_J) - SISAL_CAST(sisal_array_t, v_TEST_10006_n__0_B).lower_bound[0])]));
          (v_TEST_10006_n__5_p0_o = SISAL_CAST(int32_t, 1));
          (v_TEST_10006_n__6_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_TEST_10006_n__0_J) - SISAL_CAST(int32_t, v_TEST_10006_n__5_p0_o))));
          (v_TEST_10006_n__7_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_TEST_10006_n__0_B).data)[(SISAL_CAST(int32_t, v_TEST_10006_n__6_p0_o) - SISAL_CAST(sisal_array_t, v_TEST_10006_n__0_B).lower_bound[0])]));
          (v_TEST_10006_n__8_p0_o = SISAL_CAST(bool, (SISAL_CAST(double, v_TEST_10006_n__4_p0_o) < SISAL_CAST(double, v_TEST_10006_n__7_p0_o))));
          (v_TEST_10006_n__10_p0_o = SISAL_CAST(bool, (SISAL_CAST(bool, v_TEST_10006_n__2_p0_o) && SISAL_CAST(bool, v_TEST_10006_n__8_p0_o))));
        }
        sisal_array_t v_RETURNS_10005_n__0_p0_o = {0};
        (v_RETURNS_10005_n__0_p0_o = SISAL_CAST(sisal_array_t, v_LoopB_10003_bodycap_n5_p0));
        sisal_array_t v_RETURNS_10005_n__1_p0_o = {0};
        (v_RETURNS_10005_n__1_p0_o = SISAL_CAST(sisal_array_t, SISAL_CAST(sisal_array_t, v_RETURNS_10005_n__0_p0_o)));
        (v_BODY_10002_n__3_A = SISAL_CAST(sisal_array_t, v_RETURNS_10005_n__1_p0_o));
      }
      bool v_BODY_10002_n__5_p0_o = 0;
      (v_BODY_10002_n__5_p0_o = SISAL_CAST(bool, false));
      (v_LoopB_10001_bodycap_n2_p0 = v_BODY_10002_n__2_I);
      (v_LoopB_10001_bodycap_n3_p0 = v_BODY_10002_n__3_A);
      (v_LoopB_10001_bodycap_n5_p0 = v_BODY_10002_n__5_p0_o);
      (v_LoopB_10001_n__5_MERGE_A = v_LoopB_10001_bodycap_n3_p0);
      (v_LoopB_10001_n__6_MERGE_I = v_LoopB_10001_bodycap_n2_p0);
      (v_LoopB_10001_n__7_MERGE_OLD_A = v_LoopB_10001_bodycap_n3_p0);
      (v_LoopB_10001_n__8_MERGE_OLD_I = v_LoopB_10001_bodycap_n2_p0);
      (v_LoopB_10001_n__9_MERGE_first = v_LoopB_10001_bodycap_n5_p0);
      (v_TEST_10009_n__0_A = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__5_MERGE_A));
      (v_TEST_10009_n__0_I = SISAL_CAST(int32_t, v_LoopB_10001_n__6_MERGE_I));
      (v_TEST_10009_n__0_INPUT = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__0_INPUT));
      (v_TEST_10009_n__0_OLD_A = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__7_MERGE_OLD_A));
      (v_TEST_10009_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_10001_n__8_MERGE_OLD_I));
      (v_TEST_10009_n__1_p0_o = SISAL_CAST(int32_t, ((int32_t)((SISAL_CAST(sisal_array_t, v_TEST_10009_n__0_INPUT).lower_bound[0] + ((SISAL_CAST(sisal_array_t, v_TEST_10009_n__0_INPUT).dims[0] > 0) ? SISAL_CAST(sisal_array_t, v_TEST_10009_n__0_INPUT).dims[0] : ((int64_t)SISAL_CAST(sisal_array_t, v_TEST_10009_n__0_INPUT).size))) - 1))));
      (v_TEST_10009_n__2_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_TEST_10009_n__0_I) < SISAL_CAST(int32_t, v_TEST_10009_n__1_p0_o))));
    }
    sisal_array_t v_RETURNS_10008_n__0_p0_o = {0};
    (v_RETURNS_10008_n__0_p0_o = SISAL_CAST(sisal_array_t, v_LoopB_10001_bodycap_n3_p0));
    sisal_array_t v_RETURNS_10008_n__1_p0_o = {0};
    (v_RETURNS_10008_n__1_p0_o = SISAL_CAST(sisal_array_t, SISAL_CAST(sisal_array_t, v_RETURNS_10008_n__0_p0_o)));
    (v_g1_n__1_p0_o = SISAL_CAST(sisal_array_t, v_RETURNS_10008_n__1_p0_o));
  }
  (v_g1_n__0_p0_i = SISAL_CAST(sisal_array_t, v_g1_n__1_p0_o));
  return SISAL_CAST(sisal_array_t, v_g1_n__0_p0_i);
}
