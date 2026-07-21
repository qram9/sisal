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

extern "C" sisal_array_t func_BUBBLE(int32_t N, sisal_array_t AIN);

extern "C" sisal_array_t func_BUBBLE(int32_t N, sisal_array_t AIN) {
  sisal_array_t v_g1_n__0_AIN = {0};
  int32_t v_g1_n__0_N = 0;
  (v_g1_n__0_N = SISAL_CAST(int32_t, N));
  (v_g1_n__0_AIN = SISAL_CAST(sisal_array_t, AIN));
  sisal_array_t v_g1_n__0_p0_i = {0};
  sisal_array_t v_g1_n__1_p0_o = {0};
  {
    sisal_array_t v_LoopB_10001_n__5_MERGE_A = {0};
    int32_t v_LoopB_10001_n__6_MERGE_LIMIT = 0;
    sisal_array_t v_LoopB_10001_n__7_MERGE_OLD_A = {0};
    int32_t v_LoopB_10001_n__8_MERGE_OLD_LIMIT = 0;
    bool v_LoopB_10001_n__9_MERGE_first = 0;
    int32_t v_LoopB_10001_bodycap_n2_p0 = 0;
    sisal_array_t v_LoopB_10001_bodycap_n3_p0 = {0};
    bool v_LoopB_10001_bodycap_n5_p0 = 0;
    sisal_array_t v_LoopB_10001_n__0_AIN = {0};
    (v_LoopB_10001_n__0_AIN = SISAL_CAST(sisal_array_t, v_g1_n__0_AIN));
    int32_t v_LoopB_10001_n__0_N = 0;
    (v_LoopB_10001_n__0_N = SISAL_CAST(int32_t, v_g1_n__0_N));
    sisal_array_t v_INIT_10014_n__0_A = {0};
    sisal_array_t v_INIT_10014_n__0_AIN = {0};
    int32_t v_INIT_10014_n__0_LIMIT = 0;
    int32_t v_INIT_10014_n__0_N = 0;
    sisal_array_t v_INIT_10014_n__0_OLD_A = {0};
    int32_t v_INIT_10014_n__0_OLD_LIMIT = 0;
    (v_INIT_10014_n__0_OLD_A = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__0_AIN));
    (v_INIT_10014_n__0_OLD_LIMIT = SISAL_CAST(int32_t, v_LoopB_10001_n__0_N));
    bool v_INIT_10014_n__1_p0_o = 0;
    (v_INIT_10014_n__1_p0_o = SISAL_CAST(bool, true));
    (v_LoopB_10001_n__5_MERGE_A = v_INIT_10014_n__0_OLD_A);
    (v_LoopB_10001_n__6_MERGE_LIMIT = v_INIT_10014_n__0_OLD_LIMIT);
    (v_LoopB_10001_n__7_MERGE_OLD_A = v_INIT_10014_n__0_OLD_A);
    (v_LoopB_10001_n__8_MERGE_OLD_LIMIT = v_INIT_10014_n__0_OLD_LIMIT);
    (v_LoopB_10001_n__9_MERGE_first = v_INIT_10014_n__1_p0_o);
    sisal_array_t v_TEST_10013_n__0_A = {0};
    sisal_array_t v_TEST_10013_n__0_AIN = {0};
    int32_t v_TEST_10013_n__0_LIMIT = 0;
    int32_t v_TEST_10013_n__0_N = 0;
    sisal_array_t v_TEST_10013_n__0_OLD_A = {0};
    int32_t v_TEST_10013_n__0_OLD_LIMIT = 0;
    (v_TEST_10013_n__0_A = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__5_MERGE_A));
    (v_TEST_10013_n__0_AIN = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__0_AIN));
    (v_TEST_10013_n__0_LIMIT = SISAL_CAST(int32_t, v_LoopB_10001_n__6_MERGE_LIMIT));
    (v_TEST_10013_n__0_N = SISAL_CAST(int32_t, v_LoopB_10001_n__0_N));
    (v_TEST_10013_n__0_OLD_A = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__7_MERGE_OLD_A));
    (v_TEST_10013_n__0_OLD_LIMIT = SISAL_CAST(int32_t, v_LoopB_10001_n__8_MERGE_OLD_LIMIT));
    int32_t v_TEST_10013_n__1_p0_o = 0;
    (v_TEST_10013_n__1_p0_o = SISAL_CAST(int32_t, 1));
    bool v_TEST_10013_n__2_p0_o = 0;
    (v_TEST_10013_n__2_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_TEST_10013_n__0_LIMIT) > SISAL_CAST(int32_t, v_TEST_10013_n__1_p0_o))));
    while (v_TEST_10013_n__2_p0_o) {
      sisal_array_t v_BODY_10002_n__3_A = {0};
      sisal_array_t v_BODY_10002_n__0_AIN = {0};
      int32_t v_BODY_10002_n__2_LIMIT = 0;
      int32_t v_BODY_10002_n__0_N = 0;
      sisal_array_t v_BODY_10002_n__0_OLD_A = {0};
      int32_t v_BODY_10002_n__0_OLD_LIMIT = 0;
      sisal_array_t v_BODY_10002_n__0_p0_o = {0};
      (v_BODY_10002_n__0_p0_o = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__5_MERGE_A));
      (v_BODY_10002_n__0_AIN = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__0_AIN));
      int32_t v_BODY_10002_n__0_p2_o = 0;
      (v_BODY_10002_n__0_p2_o = SISAL_CAST(int32_t, v_LoopB_10001_n__6_MERGE_LIMIT));
      (v_BODY_10002_n__0_N = SISAL_CAST(int32_t, v_LoopB_10001_n__0_N));
      (v_BODY_10002_n__0_OLD_A = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__7_MERGE_OLD_A));
      (v_BODY_10002_n__0_OLD_LIMIT = SISAL_CAST(int32_t, v_LoopB_10001_n__8_MERGE_OLD_LIMIT));
      int32_t v_BODY_10002_n__1_p0_o = 0;
      (v_BODY_10002_n__1_p0_o = SISAL_CAST(int32_t, 1));
      (v_BODY_10002_n__2_LIMIT = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_10002_n__0_OLD_LIMIT) - SISAL_CAST(int32_t, v_BODY_10002_n__1_p0_o))));
      {
        sisal_array_t v_LoopB_10003_n__5_MERGE_A1 = {0};
        int32_t v_LoopB_10003_n__6_MERGE_J = 0;
        sisal_array_t v_LoopB_10003_n__7_MERGE_OLD_A1 = {0};
        int32_t v_LoopB_10003_n__8_MERGE_OLD_J = 0;
        bool v_LoopB_10003_n__9_MERGE_first = 0;
        int32_t v_LoopB_10003_bodycap_n2_p0 = 0;
        sisal_array_t v_LoopB_10003_bodycap_n3_p0 = {0};
        bool v_LoopB_10003_bodycap_n5_p0 = 0;
        sisal_array_t v_LoopB_10003_n__0_A = {0};
        (v_LoopB_10003_n__0_A = SISAL_CAST(sisal_array_t, v_BODY_10002_n__0_p0_o));
        sisal_array_t v_LoopB_10003_n__0_AIN = {0};
        (v_LoopB_10003_n__0_AIN = SISAL_CAST(sisal_array_t, v_BODY_10002_n__0_AIN));
        int32_t v_LoopB_10003_n__0_LIMIT = 0;
        (v_LoopB_10003_n__0_LIMIT = SISAL_CAST(int32_t, v_BODY_10002_n__2_LIMIT));
        int32_t v_LoopB_10003_n__0_N = 0;
        (v_LoopB_10003_n__0_N = SISAL_CAST(int32_t, v_BODY_10002_n__0_N));
        sisal_array_t v_LoopB_10003_n__0_OLD_A = {0};
        (v_LoopB_10003_n__0_OLD_A = SISAL_CAST(sisal_array_t, v_BODY_10002_n__0_OLD_A));
        int32_t v_LoopB_10003_n__0_OLD_LIMIT = 0;
        (v_LoopB_10003_n__0_OLD_LIMIT = SISAL_CAST(int32_t, v_BODY_10002_n__0_OLD_LIMIT));
        sisal_array_t v_INIT_10011_n__0_A = {0};
        sisal_array_t v_INIT_10011_n__0_A1 = {0};
        sisal_array_t v_INIT_10011_n__0_AIN = {0};
        int32_t v_INIT_10011_n__1_J = 0;
        int32_t v_INIT_10011_n__0_LIMIT = 0;
        int32_t v_INIT_10011_n__0_N = 0;
        sisal_array_t v_INIT_10011_n__0_OLD_A = {0};
        sisal_array_t v_INIT_10011_n__0_OLD_A1 = {0};
        int32_t v_INIT_10011_n__1_OLD_J = 0;
        int32_t v_INIT_10011_n__0_OLD_LIMIT = 0;
        (v_INIT_10011_n__0_A = SISAL_CAST(sisal_array_t, v_LoopB_10003_n__0_A));
        (v_INIT_10011_n__0_AIN = SISAL_CAST(sisal_array_t, v_LoopB_10003_n__0_AIN));
        (v_INIT_10011_n__0_LIMIT = SISAL_CAST(int32_t, v_LoopB_10003_n__0_LIMIT));
        (v_INIT_10011_n__0_N = SISAL_CAST(int32_t, v_LoopB_10003_n__0_N));
        (v_INIT_10011_n__0_OLD_A1 = SISAL_CAST(sisal_array_t, v_LoopB_10003_n__0_OLD_A));
        (v_INIT_10011_n__0_OLD_LIMIT = SISAL_CAST(int32_t, v_LoopB_10003_n__0_OLD_LIMIT));
        (v_INIT_10011_n__1_OLD_J = SISAL_CAST(int32_t, 0));
        bool v_INIT_10011_n__2_p0_o = 0;
        (v_INIT_10011_n__2_p0_o = SISAL_CAST(bool, true));
        (v_LoopB_10003_n__5_MERGE_A1 = v_INIT_10011_n__0_OLD_A1);
        (v_LoopB_10003_n__6_MERGE_J = v_INIT_10011_n__1_OLD_J);
        (v_LoopB_10003_n__7_MERGE_OLD_A1 = v_INIT_10011_n__0_OLD_A1);
        (v_LoopB_10003_n__8_MERGE_OLD_J = v_INIT_10011_n__1_OLD_J);
        (v_LoopB_10003_n__9_MERGE_first = v_INIT_10011_n__2_p0_o);
        sisal_array_t v_TEST_10010_n__0_A = {0};
        sisal_array_t v_TEST_10010_n__0_A1 = {0};
        sisal_array_t v_TEST_10010_n__0_AIN = {0};
        int32_t v_TEST_10010_n__0_J = 0;
        int32_t v_TEST_10010_n__0_LIMIT = 0;
        int32_t v_TEST_10010_n__0_N = 0;
        sisal_array_t v_TEST_10010_n__0_OLD_A = {0};
        sisal_array_t v_TEST_10010_n__0_OLD_A1 = {0};
        int32_t v_TEST_10010_n__0_OLD_J = 0;
        int32_t v_TEST_10010_n__0_OLD_LIMIT = 0;
        (v_TEST_10010_n__0_A = SISAL_CAST(sisal_array_t, v_LoopB_10003_n__0_A));
        (v_TEST_10010_n__0_A1 = SISAL_CAST(sisal_array_t, v_LoopB_10003_n__5_MERGE_A1));
        (v_TEST_10010_n__0_AIN = SISAL_CAST(sisal_array_t, v_LoopB_10003_n__0_AIN));
        (v_TEST_10010_n__0_J = SISAL_CAST(int32_t, v_LoopB_10003_n__6_MERGE_J));
        (v_TEST_10010_n__0_LIMIT = SISAL_CAST(int32_t, v_LoopB_10003_n__0_LIMIT));
        (v_TEST_10010_n__0_N = SISAL_CAST(int32_t, v_LoopB_10003_n__0_N));
        (v_TEST_10010_n__0_OLD_A = SISAL_CAST(sisal_array_t, v_LoopB_10003_n__0_OLD_A));
        (v_TEST_10010_n__0_OLD_A1 = SISAL_CAST(sisal_array_t, v_LoopB_10003_n__7_MERGE_OLD_A1));
        (v_TEST_10010_n__0_OLD_J = SISAL_CAST(int32_t, v_LoopB_10003_n__8_MERGE_OLD_J));
        (v_TEST_10010_n__0_OLD_LIMIT = SISAL_CAST(int32_t, v_LoopB_10003_n__0_OLD_LIMIT));
        bool v_TEST_10010_n__1_p0_o = 0;
        (v_TEST_10010_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_TEST_10010_n__0_J) < SISAL_CAST(int32_t, v_TEST_10010_n__0_LIMIT))));
        while (v_TEST_10010_n__1_p0_o) {
          sisal_array_t v_BODY_10004_n__0_A = {0};
          sisal_array_t v_BODY_10004_n__3_A1 = {0};
          sisal_array_t v_BODY_10004_n__0_AIN = {0};
          int32_t v_BODY_10004_n__2_J = 0;
          int32_t v_BODY_10004_n__0_LIMIT = 0;
          int32_t v_BODY_10004_n__0_N = 0;
          sisal_array_t v_BODY_10004_n__0_OLD_A = {0};
          sisal_array_t v_BODY_10004_n__0_OLD_A1 = {0};
          int32_t v_BODY_10004_n__0_OLD_J = 0;
          int32_t v_BODY_10004_n__0_OLD_LIMIT = 0;
          (v_BODY_10004_n__0_A = SISAL_CAST(sisal_array_t, v_LoopB_10003_n__0_A));
          sisal_array_t v_BODY_10004_n__0_p1_o = {0};
          (v_BODY_10004_n__0_p1_o = SISAL_CAST(sisal_array_t, v_LoopB_10003_n__5_MERGE_A1));
          (v_BODY_10004_n__0_AIN = SISAL_CAST(sisal_array_t, v_LoopB_10003_n__0_AIN));
          int32_t v_BODY_10004_n__0_p3_o = 0;
          (v_BODY_10004_n__0_p3_o = SISAL_CAST(int32_t, v_LoopB_10003_n__6_MERGE_J));
          (v_BODY_10004_n__0_LIMIT = SISAL_CAST(int32_t, v_LoopB_10003_n__0_LIMIT));
          (v_BODY_10004_n__0_N = SISAL_CAST(int32_t, v_LoopB_10003_n__0_N));
          (v_BODY_10004_n__0_OLD_A = SISAL_CAST(sisal_array_t, v_LoopB_10003_n__0_OLD_A));
          (v_BODY_10004_n__0_OLD_A1 = SISAL_CAST(sisal_array_t, v_LoopB_10003_n__7_MERGE_OLD_A1));
          (v_BODY_10004_n__0_OLD_J = SISAL_CAST(int32_t, v_LoopB_10003_n__8_MERGE_OLD_J));
          (v_BODY_10004_n__0_OLD_LIMIT = SISAL_CAST(int32_t, v_LoopB_10003_n__0_OLD_LIMIT));
          int32_t v_BODY_10004_n__1_p0_o = 0;
          (v_BODY_10004_n__1_p0_o = SISAL_CAST(int32_t, 1));
          (v_BODY_10004_n__2_J = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_10004_n__0_OLD_J) + SISAL_CAST(int32_t, v_BODY_10004_n__1_p0_o))));
          sisal_array_t v_IF_array_INTEGRAL____10005_n__0_OLD_A1 = {0};
          (v_IF_array_INTEGRAL____10005_n__0_OLD_A1 = SISAL_CAST(sisal_array_t, v_BODY_10004_n__0_OLD_A1));
          int32_t v_IF_array_INTEGRAL____10005_n__0_J = 0;
          (v_IF_array_INTEGRAL____10005_n__0_J = SISAL_CAST(int32_t, v_BODY_10004_n__2_J));
          {
            int32_t v_PREDICATE_10006_n__0_J = 0;
            sisal_array_t v_PREDICATE_10006_n__0_OLD_A1 = {0};
            (v_PREDICATE_10006_n__0_OLD_A1 = SISAL_CAST(sisal_array_t, v_IF_array_INTEGRAL____10005_n__0_OLD_A1));
            (v_PREDICATE_10006_n__0_J = SISAL_CAST(int32_t, v_IF_array_INTEGRAL____10005_n__0_J));
            int32_t v_PREDICATE_10006_n__1_p0_o = 0;
            (v_PREDICATE_10006_n__1_p0_o = SISAL_CAST(int32_t, ((int32_t *)SISAL_CAST(sisal_array_t, v_PREDICATE_10006_n__0_OLD_A1).data)[(SISAL_CAST(int32_t, v_PREDICATE_10006_n__0_J) - SISAL_CAST(sisal_array_t, v_PREDICATE_10006_n__0_OLD_A1).lower_bound[0])]));
            int32_t v_PREDICATE_10006_n__2_p0_o = 0;
            (v_PREDICATE_10006_n__2_p0_o = SISAL_CAST(int32_t, 1));
            int32_t v_PREDICATE_10006_n__3_p0_o = 0;
            (v_PREDICATE_10006_n__3_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_PREDICATE_10006_n__0_J) + SISAL_CAST(int32_t, v_PREDICATE_10006_n__2_p0_o))));
            int32_t v_PREDICATE_10006_n__4_p0_o = 0;
            (v_PREDICATE_10006_n__4_p0_o = SISAL_CAST(int32_t, ((int32_t *)SISAL_CAST(sisal_array_t, v_PREDICATE_10006_n__0_OLD_A1).data)[(SISAL_CAST(int32_t, v_PREDICATE_10006_n__3_p0_o) - SISAL_CAST(sisal_array_t, v_PREDICATE_10006_n__0_OLD_A1).lower_bound[0])]));
            bool v_PREDICATE_10006_n__5_p0_o = 0;
            (v_PREDICATE_10006_n__5_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_PREDICATE_10006_n__1_p0_o) > SISAL_CAST(int32_t, v_PREDICATE_10006_n__4_p0_o))));
            if (v_PREDICATE_10006_n__5_p0_o) {
              int32_t v_THEN_10008_n__0_J = 0;
              sisal_array_t v_THEN_10008_n__0_OLD_A1 = {0};
              (v_THEN_10008_n__0_OLD_A1 = SISAL_CAST(sisal_array_t, v_IF_array_INTEGRAL____10005_n__0_OLD_A1));
              (v_THEN_10008_n__0_J = SISAL_CAST(int32_t, v_IF_array_INTEGRAL____10005_n__0_J));
              int32_t v_THEN_10008_n__1_p0_o = 0;
              (v_THEN_10008_n__1_p0_o = SISAL_CAST(int32_t, 1));
              int32_t v_THEN_10008_n__2_p0_o = 0;
              (v_THEN_10008_n__2_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_THEN_10008_n__0_J) + SISAL_CAST(int32_t, v_THEN_10008_n__1_p0_o))));
              int32_t v_THEN_10008_n__3_p0_o = 0;
              (v_THEN_10008_n__3_p0_o = SISAL_CAST(int32_t, ((int32_t *)SISAL_CAST(sisal_array_t, v_THEN_10008_n__0_OLD_A1).data)[(SISAL_CAST(int32_t, v_THEN_10008_n__2_p0_o) - SISAL_CAST(sisal_array_t, v_THEN_10008_n__0_OLD_A1).lower_bound[0])]));
              int32_t v_THEN_10008_n__4_p0_o = 0;
              (v_THEN_10008_n__4_p0_o = SISAL_CAST(int32_t, ((int32_t *)SISAL_CAST(sisal_array_t, v_THEN_10008_n__0_OLD_A1).data)[(SISAL_CAST(int32_t, v_THEN_10008_n__0_J) - SISAL_CAST(sisal_array_t, v_THEN_10008_n__0_OLD_A1).lower_bound[0])]));
              sisal_array_t v_THEN_10008_n__5_p0_o = {0};
              (v_THEN_10008_n__5_p0_o = SISAL_CAST(sisal_array_t, sisal_array_replace_i32(sisal_array_replace_i32(SISAL_CAST(sisal_array_t, v_THEN_10008_n__0_OLD_A1), ((int64_t)SISAL_CAST(int32_t, v_THEN_10008_n__0_J)), SISAL_CAST(int32_t, v_THEN_10008_n__3_p0_o)), (((int64_t)SISAL_CAST(int32_t, v_THEN_10008_n__0_J)) + 1), SISAL_CAST(int32_t, v_THEN_10008_n__4_p0_o))));
              (v_BODY_10004_n__3_A1 = SISAL_CAST(sisal_array_t, v_THEN_10008_n__5_p0_o));
            }
            else {
              sisal_array_t v_ELSE_10007_n__0_OLD_A1 = {0};
              (v_ELSE_10007_n__0_OLD_A1 = SISAL_CAST(sisal_array_t, v_IF_array_INTEGRAL____10005_n__0_OLD_A1));
              (v_BODY_10004_n__3_A1 = SISAL_CAST(sisal_array_t, v_ELSE_10007_n__0_OLD_A1));
            }
          }
          bool v_BODY_10004_n__5_p0_o = 0;
          (v_BODY_10004_n__5_p0_o = SISAL_CAST(bool, false));
          (v_LoopB_10003_bodycap_n2_p0 = v_BODY_10004_n__2_J);
          (v_LoopB_10003_bodycap_n3_p0 = v_BODY_10004_n__3_A1);
          (v_LoopB_10003_bodycap_n5_p0 = v_BODY_10004_n__5_p0_o);
          (v_LoopB_10003_n__5_MERGE_A1 = v_LoopB_10003_bodycap_n3_p0);
          (v_LoopB_10003_n__6_MERGE_J = v_LoopB_10003_bodycap_n2_p0);
          (v_LoopB_10003_n__7_MERGE_OLD_A1 = v_LoopB_10003_bodycap_n3_p0);
          (v_LoopB_10003_n__8_MERGE_OLD_J = v_LoopB_10003_bodycap_n2_p0);
          (v_LoopB_10003_n__9_MERGE_first = v_LoopB_10003_bodycap_n5_p0);
          (v_TEST_10010_n__0_A = SISAL_CAST(sisal_array_t, v_LoopB_10003_n__0_A));
          (v_TEST_10010_n__0_A1 = SISAL_CAST(sisal_array_t, v_LoopB_10003_n__5_MERGE_A1));
          (v_TEST_10010_n__0_AIN = SISAL_CAST(sisal_array_t, v_LoopB_10003_n__0_AIN));
          (v_TEST_10010_n__0_J = SISAL_CAST(int32_t, v_LoopB_10003_n__6_MERGE_J));
          (v_TEST_10010_n__0_LIMIT = SISAL_CAST(int32_t, v_LoopB_10003_n__0_LIMIT));
          (v_TEST_10010_n__0_N = SISAL_CAST(int32_t, v_LoopB_10003_n__0_N));
          (v_TEST_10010_n__0_OLD_A = SISAL_CAST(sisal_array_t, v_LoopB_10003_n__0_OLD_A));
          (v_TEST_10010_n__0_OLD_A1 = SISAL_CAST(sisal_array_t, v_LoopB_10003_n__7_MERGE_OLD_A1));
          (v_TEST_10010_n__0_OLD_J = SISAL_CAST(int32_t, v_LoopB_10003_n__8_MERGE_OLD_J));
          (v_TEST_10010_n__0_OLD_LIMIT = SISAL_CAST(int32_t, v_LoopB_10003_n__0_OLD_LIMIT));
          (v_TEST_10010_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_TEST_10010_n__0_J) < SISAL_CAST(int32_t, v_TEST_10010_n__0_LIMIT))));
        }
        sisal_array_t v_RETURNS_10009_n__0_p0_o = {0};
        (v_RETURNS_10009_n__0_p0_o = SISAL_CAST(sisal_array_t, v_LoopB_10003_bodycap_n3_p0));
        sisal_array_t v_RETURNS_10009_n__1_p0_o = {0};
        (v_RETURNS_10009_n__1_p0_o = SISAL_CAST(sisal_array_t, SISAL_CAST(sisal_array_t, v_RETURNS_10009_n__0_p0_o)));
        (v_BODY_10002_n__3_A = SISAL_CAST(sisal_array_t, v_RETURNS_10009_n__1_p0_o));
      }
      bool v_BODY_10002_n__5_p0_o = 0;
      (v_BODY_10002_n__5_p0_o = SISAL_CAST(bool, false));
      (v_LoopB_10001_bodycap_n2_p0 = v_BODY_10002_n__2_LIMIT);
      (v_LoopB_10001_bodycap_n3_p0 = v_BODY_10002_n__3_A);
      (v_LoopB_10001_bodycap_n5_p0 = v_BODY_10002_n__5_p0_o);
      (v_LoopB_10001_n__5_MERGE_A = v_LoopB_10001_bodycap_n3_p0);
      (v_LoopB_10001_n__6_MERGE_LIMIT = v_LoopB_10001_bodycap_n2_p0);
      (v_LoopB_10001_n__7_MERGE_OLD_A = v_LoopB_10001_bodycap_n3_p0);
      (v_LoopB_10001_n__8_MERGE_OLD_LIMIT = v_LoopB_10001_bodycap_n2_p0);
      (v_LoopB_10001_n__9_MERGE_first = v_LoopB_10001_bodycap_n5_p0);
      (v_TEST_10013_n__0_A = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__5_MERGE_A));
      (v_TEST_10013_n__0_AIN = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__0_AIN));
      (v_TEST_10013_n__0_LIMIT = SISAL_CAST(int32_t, v_LoopB_10001_n__6_MERGE_LIMIT));
      (v_TEST_10013_n__0_N = SISAL_CAST(int32_t, v_LoopB_10001_n__0_N));
      (v_TEST_10013_n__0_OLD_A = SISAL_CAST(sisal_array_t, v_LoopB_10001_n__7_MERGE_OLD_A));
      (v_TEST_10013_n__0_OLD_LIMIT = SISAL_CAST(int32_t, v_LoopB_10001_n__8_MERGE_OLD_LIMIT));
      (v_TEST_10013_n__1_p0_o = SISAL_CAST(int32_t, 1));
      (v_TEST_10013_n__2_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_TEST_10013_n__0_LIMIT) > SISAL_CAST(int32_t, v_TEST_10013_n__1_p0_o))));
    }
    sisal_array_t v_RETURNS_10012_n__0_p0_o = {0};
    (v_RETURNS_10012_n__0_p0_o = SISAL_CAST(sisal_array_t, v_LoopB_10001_bodycap_n3_p0));
    sisal_array_t v_RETURNS_10012_n__1_p0_o = {0};
    (v_RETURNS_10012_n__1_p0_o = SISAL_CAST(sisal_array_t, SISAL_CAST(sisal_array_t, v_RETURNS_10012_n__0_p0_o)));
    (v_g1_n__1_p0_o = SISAL_CAST(sisal_array_t, v_RETURNS_10012_n__1_p0_o));
  }
  (v_g1_n__0_p0_i = SISAL_CAST(sisal_array_t, v_g1_n__1_p0_o));
  return SISAL_CAST(sisal_array_t, v_g1_n__0_p0_i);
}
